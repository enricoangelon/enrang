//! Fitting (A:1356-1358; M3 plan d.10; owner 2F): each recorded satisfaction,
//! override and role against what it stands for, EN0615 and EN0714, and EN0418's
//! phase-3 part. Sites in `ItemPath` order of the fitting definition, each once.

use std::collections::BTreeMap;

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, DiagCtx};
use enrang_hir::{
    CheckedProgram, ConstValue, Contract, DefId, LangItem, ModuleId, Perm, ResultPerm, RetSources,
    Store, Tcx, Ty, TyKind,
};
use enrang_mir::{
    Bodies, Body, BodyOwner, Callee, ClosureFn, ConstKind, Local, Operand, Rvalue, StatementKind,
    TerminatorKind,
};

use crate::cx::{BodyCx, SccState};
use crate::declared::{as_virtual, declared, is_role, perm_slots, row};
use crate::held::HeldResults;
use crate::loans::LoanKey;
use crate::r3::arg_tys;

/// A function whose contract does not fit what it stands for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FitError {
    pub code: Code,
    pub found: DefId,
    pub member: DefId,
    pub site: Span,
    /// For a local function passed as a closure (EN0616, A:1360): the captured
    /// variable its store names, and whether the store goes into it.
    pub captured: Option<(enrang_base::Symbol, bool)>,
    /// For a body containing `unsafe` (N12, S:1133): the argument, `this` first,
    /// whose `const` mark its safe operations break, transitively.
    pub marked: Option<u32>,
    /// For an `fn` value or closure value (A:1356): its slot's row and its own.
    pub slot: Option<Box<SlotFit>>,
}

/// An `fn` value or closure value against its slot's row (A:1356, A:1365): the
/// slot's function type with the parameter names its declaration kept (D14),
/// the value's own parameter names, the parameter each contract slot belongs to,
/// and the two contracts, so the report can name what does not fit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotFit {
    pub ty: Ty,
    pub names: Option<Vec<Symbol>>,
    pub params: Vec<Symbol>,
    pub slots: Vec<Symbol>,
    pub imp: Contract,
    pub row: Contract,
}

/// The nearest base declaration an override stands for.
pub fn base_decl(tcx: &Tcx, d: DefId) -> Option<DefId> {
    let data = tcx.def(d);
    if !data.flags.is_override {
        return None;
    }
    let class = tcx.adt(tcx.adt_of(data.parent?)?).as_class()?;
    let TyKind::Adt(base, args) = tcx.kind(class.base?) else {
        return None;
    };
    tcx.find_method(base, args, *data.path.segments.last()?)
}

/// N12's transitive check (S:1133, A:1353): in a body containing `unsafe`, a
/// `const`-marked reference or `this` is Read, and the body's safe operations
/// are checked as if it were shared, so one that a safe operation writes, by
/// itself or by handing it to a callee counting as a writer, is EN0615 at that
/// operation (its witness's first step).
fn const_writes(tcx: &Tcx, bodies: &Bodies, module: ModuleId) -> Vec<FitError> {
    let mut out = Vec::new();
    for b in bodies.values() {
        let BodyOwner::Fn(d) = b.owner else {
            continue;
        };
        if tcx.def(d).module != module || !crate::r3::is_unsafe(tcx, b) || is_role(tcx, d) {
            continue;
        }
        let marks = crate::declared::sig_args(tcx, d);
        let slots = perm_slots(tcx, &arg_tys(b));
        let w = crate::wlive::WLive::compute(tcx, b, bodies, None, None);
        for (q, (i, path)) in slots.iter().enumerate() {
            let local = Local(*i as u32 + 1);
            if marks.get(*i).map(|m| m.1) != Some(enrang_hir::Mark::Const)
                || !w.live_at_entry(local, path)
            {
                continue;
            }
            let scc = SccState::default();
            let site = crate::witness::of_param(
                tcx,
                bodies,
                &scc,
                d,
                (q as u32, local, path),
                &BTreeMap::new(),
            )
            .and_then(|w| w.steps.first().map(|s| s.span))
            .unwrap_or(tcx.def(d).name_span);
            out.push(FitError {
                code: Code::EN0615,
                found: d,
                member: d,
                site,
                captured: None,
                marked: Some(*i as u32),
                slot: None,
            });
            break;
        }
    }
    out
}

/// Whether `d` is a `fmt` a class or an enum writes for printing: a method named
/// `fmt` with `Display`'s signature, `fmt(f: &Formatter): void` (S:644).
fn writes_fmt(tcx: &Tcx, d: DefId) -> bool {
    let data = tcx.def(d);
    let formatter = |t: Ty| match tcx.kind(t) {
        TyKind::Ref(f) => matches!(tcx.kind(f), TyKind::Adt(a, _)
            if Some(a) == tcx.lang_adt(LangItem::Formatter)),
        _ => false,
    };
    data.name().is_some_and(|n| n.as_str() == "fmt")
        && tcx.takes_this(d)
        && tcx.sig_opt(d).is_some_and(|s| {
            matches!(s.params.as_slice(), [p] if formatter(p.ty)) && tcx.kind(s.ret) == TyKind::Void
        })
        && data
            .parent
            .and_then(|p| tcx.adt_of(p))
            .is_some_and(|a| tcx.adt(a).as_interface().is_none())
}

/// `read_set_only < fields_only < whole` (L:83).
fn rank(s: &Store) -> u8 {
    match (s.read_set_only, s.fields_only) {
        (true, _) => 0,
        (_, true) => 1,
        _ => 2,
    }
}

/// Whether `imp` fits `decl` (A:1356): EN0615 for a permission above the declared
/// one, `move` not matched, a read-only result for a writable one, or a store the
/// declared stores do not cover with its bits; else EN0714 for a source outside
/// the declared ones.
pub fn fits(imp: &Contract, decl: &Contract) -> Option<Code> {
    let perms = (0..imp.perms.len().max(decl.perms.len())).all(|i| {
        let a = imp.perms.get(i).copied().unwrap_or(Perm::Read);
        let b = decl.perms.get(i).copied().unwrap_or(Perm::Read);
        (a == Perm::Own) == (b == Perm::Own) && a <= b
    });
    let result =
        !(decl.result == ResultPerm::Writable && matches!(imp.result, ResultPerm::ReadOnly(_)));
    let stores = imp.stores.iter().all(|s| {
        decl.stores.iter().any(|d| {
            d.from == s.from && d.into == s.into && rank(d) >= rank(s) && (d.read || !s.read)
        })
    });
    let srcs = |c: &Contract| match &c.sources {
        RetSources::Params(v) => v.clone(),
        RetSources::NoLoans => Vec::new(),
    };
    let within = srcs(imp).iter().all(|i| srcs(decl).contains(i));
    match (perms && result && stores, within) {
        (false, _) => Some(Code::EN0615),
        (true, false) => Some(Code::EN0714),
        (true, true) => None,
    }
}

/// Where a misfit is reported (plan e, G18): EN0615 at the write in the body that
/// makes the first permission above the declared one Write (its witness's first
/// step), EN0714 at the first `return` holding a key outside the declared
/// sources; `None` when the body shows neither.
fn misfit_site(
    tcx: &Tcx,
    bodies: &Bodies,
    code: Code,
    found: DefId,
    decl: &Contract,
) -> Option<Span> {
    let b = bodies.get(&BodyOwner::Fn(found))?;
    let imp = (*crate::contract(tcx, found)).clone();
    match code {
        Code::EN0615 => {
            let slots = perm_slots(tcx, &arg_tys(b));
            let q = (0..imp.perms.len()).find(|&q| {
                let decl = decl.perms.get(q).copied().unwrap_or(Perm::Read);
                imp.perms[q] == Perm::Write && decl < Perm::Write
            })?;
            let (i, path) = slots.get(q)?;
            let scc = SccState::default();
            let local = Local(*i as u32 + 1);
            let w = crate::witness::of_param(
                tcx,
                bodies,
                &scc,
                found,
                (q as u32, local, path),
                &BTreeMap::new(),
            )?;
            w.steps.first().map(|s| s.span)
        }
        Code::EN0714 => {
            let cx = BodyCx::new(tcx, bodies, b, None);
            let held = HeldResults::run(&cx, false);
            held.ret_at_returns().into_iter().find_map(|(p, set)| {
                set.keys()
                    .any(|k| match *k {
                        LoanKey::Param(i) => crate::r3::outside(decl, i, true, *k),
                        LoanKey::Fields(i) | LoanKey::RFields(i) => {
                            crate::r3::outside(decl, i, false, *k)
                        }
                        _ => false,
                    })
                    .then(|| b.blocks[p.block].term.span)
            })
        }
        _ => None,
    }
}

/// Whether a satisfaction of `iface` by `ty` is structural: no `implements` of it
/// on `ty`'s class or a base (FIT-structural reports at the class).
fn structural(tcx: &Tcx, ty: Ty, iface: Ty) -> bool {
    let TyKind::Adt(want, _) = tcx.kind(iface) else {
        return false;
    };
    let mut cur = Some(ty);
    while let Some(t) = cur {
        let TyKind::Adt(a, _) = tcx.kind(t) else {
            return false;
        };
        let Some(class) = tcx.adt(a).as_class() else {
            return false;
        };
        let named = |i: &Ty| matches!(tcx.kind(*i), TyKind::Adt(x, _) if x == want);
        if class.implements.iter().any(named) {
            return false;
        }
        cur = class.base;
    }
    true
}

/// What a coercion makes a function value of: a named function, or an arrow's
/// body.
#[derive(Copy, Clone)]
enum Source {
    Named(DefId),
    Arrow(BodyOwner),
}

/// An arrow's contract, which inference never makes (arrows return no
/// references): a declared parameter is Write when write-live at entry (N3), and
/// its stores are those between its declared parameters, its env left out.
fn arrow_contract(tcx: &Tcx, bodies: &Bodies, ab: &Body) -> Contract {
    let first = match ab.locals.get(Local(1)).map(|d| d.kind) {
        Some(enrang_mir::LocalKind::ClosureEnv) => 1,
        _ => 0,
    };
    let tys = arg_tys(ab);
    let declared = &tys[first.min(tys.len())..];
    let w = crate::wlive::WLive::compute(tcx, ab, bodies, None, None);
    let perms = perm_slots(tcx, declared)
        .iter()
        .map(
            |(i, path)| match w.live_at_entry(Local((first + i) as u32 + 1), path) {
                true => Perm::Write,
                false => Perm::Read,
            },
        )
        .collect();
    let cx = BodyCx::new(tcx, bodies, ab, None);
    let held = HeldResults::run(&cx, true);
    let (_, _, _, stores) = crate::r3::found(&cx, &held, &|a| {
        crate::class_contract(tcx, a).writes_through_fields
    });
    let shift = first as u32;
    let stores = (stores.into_iter())
        .filter(|s| s.from >= shift && s.into >= shift)
        .map(|s| Store {
            from: s.from - shift,
            into: s.into - shift,
            ..s
        })
        .collect();
    Contract {
        perms,
        sources: RetSources::NoLoans,
        result: ResultPerm::None,
        through_fields: Vec::new(),
        through_read: Vec::new(),
        stores,
        moves_or_writes: Vec::new(),
    }
}

/// The `fn` coercions of `b` (plan d.10): a function name as an `fn` value
/// (`const fn f`), an arrow as an `fn` value (`arrow_fn#k`), and a named function
/// or an arrow as a closure value (C12), each with the target row its type gives
/// and the coercion's span; an arrow also with the result its own type gives,
/// since it has no contract of its own to infer one (S:682).
type Slot = (Ty, Option<Vec<Symbol>>);

fn coercions(tcx: &Tcx, b: &Body) -> Vec<(Source, Contract, Span, Option<ResultPerm>, Slot)> {
    let target = |ty: Ty| match tcx.kind(ty) {
        TyKind::FnPtr(_, s) | TyKind::Closure(s) => {
            let sig = tcx.fn_sig(s);
            let marks: Vec<_> = sig.params.iter().map(|&(t, m)| (t, m, false)).collect();
            Some(row(tcx, &marks, false, sig.ret, sig.ret_readonly))
        }
        _ => None,
    };
    let top = match b.owner {
        BodyOwner::Fn(d) => Some(enrang_hir::BodyOwner::Fn(d)),
        BodyOwner::Test(d) => Some(enrang_hir::BodyOwner::Test(d)),
        BodyOwner::Statements(m) => Some(enrang_hir::BodyOwner::Statements(m)),
        BodyOwner::Arrow(p, _) => Some(p),
        BodyOwner::Shim(_) => None,
    };
    let arrow = |a| top.map(|p| Source::Arrow(BodyOwner::Arrow(p, a)));
    // The type a call's parameter declares, before substitution: the row of an
    // `fn` or closure type written with a type parameter is computed generically
    // (S:4.10, T:982 `S2-12-growVia`), so `fn(a: &T) => &T`'s result is writable
    // at `T := string` too, where the substituted type's would be a string part.
    let declared = |callee: &Callee, i: usize| -> Option<(Contract, Slot)> {
        let f = match callee {
            Callee::Fn(f) | Callee::Virtual { method: f, .. } => f.def,
            _ => return None,
        };
        let k = i.checked_sub(usize::from(tcx.takes_this(f)))?;
        let p = tcx.sig_opt(f)?.params.get(k)?;
        Some((target(p.ty)?, (p.ty, p.fn_names.clone())))
    };
    let mut passed: BTreeMap<Local, (Contract, Slot)> = BTreeMap::new();
    for blk in b.blocks.iter() {
        if let TerminatorKind::Call { callee, args, .. } = &blk.term.kind {
            for (i, a) in args.iter().enumerate() {
                if let Some(p) = a.place().filter(|p| p.is_local())
                    && let Some(row) = declared(callee, i)
                {
                    passed.insert(p.local, row);
                }
            }
        }
    }
    let mut out = Vec::new();
    let mut operand = |op: &Operand, span: Span, generic: Option<(Contract, Slot)>| {
        if let Operand::Const(c) = op
            && let ConstKind::Value(ConstValue::FnAddr(f)) = c.kind
            && let Some((row, slot)) = generic.or_else(|| Some((target(c.ty)?, (c.ty, None))))
        {
            out.push((Source::Named(f.def), row, span, None, slot));
        }
    };
    for blk in b.blocks.iter() {
        for st in &blk.stmts {
            if let StatementKind::Assign { value, .. } = &st.kind {
                crate::init::operands(value)
                    .into_iter()
                    .for_each(|o| operand(o, st.span, None));
            }
        }
        if let TerminatorKind::Call { callee, args, .. } = &blk.term.kind {
            for (i, o) in args.iter().enumerate() {
                operand(o, blk.term.span, declared(callee, i));
            }
        }
    }
    for blk in b.blocks.iter() {
        for st in &blk.stmts {
            let StatementKind::Assign { dest, value } = &st.kind else {
                continue;
            };
            let source = match value {
                Rvalue::ClosureValue {
                    func: ClosureFn::Named(f),
                    ..
                } => Some(Source::Named(f.def)),
                Rvalue::ClosureValue {
                    func: ClosureFn::Arrow(a),
                    ..
                }
                | Rvalue::ArrowFn(a) => arrow(*a),
                _ => None,
            };
            let generic = dest
                .is_local()
                .then(|| passed.get(&dest.local).cloned())
                .flatten();
            let dest_ty = b.place_ty(tcx, *dest).map(|t| t.ty);
            let own = dest_ty.and_then(target);
            let own_slot = dest_ty.map(|t| (t, None));
            if let Some(source) = source
                && let Some((row, slot)) = generic.or_else(|| Some((own.clone()?, own_slot?)))
            {
                out.push((source, row, st.span, own.map(|c| c.result), slot));
            }
        }
    }
    out
}

/// The module's fitting sites (plan d.10): satisfactions [K6], overrides, roles,
/// `fn` coercions, and `implements Copy` on a class whose flag is set (EN0418).
pub fn fit_module(
    tcx: &Tcx,
    program: &CheckedProgram,
    bodies: &Bodies,
    module: ModuleId,
    _dcx: &mut DiagCtx,
) -> Vec<FitError> {
    let mut out = Vec::new();
    let mut push = |code: Option<Code>, found: DefId, member: DefId, site: Span| {
        if let Some(code) = code {
            out.push(FitError {
                code,
                found,
                member,
                site,
                captured: None,
                marked: None,
                slot: None,
            });
        }
    };
    let mut captured = Vec::new();
    let contract = |d: DefId| (*crate::contract(tcx, d)).clone();
    let site = |code: Option<Code>, found: DefId, decl: &Contract, at: Span| {
        code.and_then(|c| misfit_site(tcx, bodies, c, found, decl))
            .unwrap_or(at)
    };
    for r in &program.satisfactions {
        if tcx.def(r.found).module == module {
            let decl = as_virtual(contract(r.member));
            let code = fits(&contract(r.found), &decl);
            let at = match (code, structural(tcx, r.ty, r.iface)) {
                // A structural satisfaction is reported at its class
                // (FIT-structural), an `implements` one in the body (G18).
                (Some(Code::EN0615), true) => tcx
                    .adt_of(tcx.def(r.found).parent.expect("a method's class"))
                    .map_or(r.site, |a| tcx.def(tcx.adt(a).def).name_span),
                _ => site(code, r.found, &decl, r.site),
            };
            push(code, r.found, r.member, at);
        }
    }
    // Every type meets `Display` by the compiler's own rule, so no satisfaction
    // records a written `fmt`: each one, an override or one that also meets a
    // user interface too, fits `Display`'s member always, since printing calls
    // it (S:644 N11, plan d.10's choice "`fmt` always"); a misfit there is the
    // one report, before its base's.
    let display_fmt = tcx
        .lang_adt(LangItem::Display)
        .and_then(|a| tcx.adt(a).as_interface()?.methods.first().copied());
    for (d, data) in tcx.defs().filter(|(_, x)| x.module == module) {
        let mut fitted = false;
        if let Some(m) = display_fmt
            && writes_fmt(tcx, d)
        {
            let decl = as_virtual(contract(m));
            let code = fits(&contract(d), &decl);
            fitted = code.is_some();
            push(code, d, m, site(code, d, &decl, data.name_span));
        }
        if let Some(b) = base_decl(tcx, d)
            && !fitted
        {
            // A body's EN0714 is the definition check's, at its `return` (r3).
            let decl = as_virtual(contract(b));
            let code =
                fits(&contract(d), &decl).filter(|&c| c != Code::EN0714 || !data.flags.has_body);
            push(code, d, b, site(code, d, &decl, data.name_span));
        }
        if is_role(tcx, d) && tcx.contract_memo(d).is_some() {
            let decl = declared(tcx, d);
            let code = fits(&contract(d), &decl);
            push(code, d, d, site(code, d, &decl, data.name_span));
        }
    }
    // An `fn` value or closure value made from a named function: its contract
    // against the row its type declares, which has no stores (A:1356, INF-04).
    for b in bodies.values() {
        for (source, row, at, own, slot) in coercions(tcx, b) {
            // The value's own parameters, named, each with its type.
            let mut params: Vec<(Symbol, Ty)> = Vec::new();
            let (mut imp, f) = match source {
                Source::Named(f) => {
                    if let Some(sig) = tcx.sig_opt(f) {
                        params = sig.params.iter().map(|p| (p.name, p.ty)).collect();
                    }
                    (contract(f), f)
                }
                Source::Arrow(owner) => {
                    let Some(ab) = bodies.get(&owner) else {
                        continue;
                    };
                    // An arrow that repoints a captured reference is EN0616 there
                    // (S:972), which is also what makes the parameter it stores
                    // count as written: one report for the one mistake.
                    if !crate::rebind::check(tcx, ab).is_empty() {
                        continue;
                    }
                    let owner = match b.owner {
                        BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(d),
                        _ => tcx.module(module).def,
                    };
                    let Some(f) = owner else {
                        continue;
                    };
                    let mut c = arrow_contract(tcx, bodies, ab);
                    c.result = own.unwrap_or(ResultPerm::None);
                    let first = usize::from(
                        ab.locals.get(Local(1)).map(|d| d.kind)
                            == Some(enrang_mir::LocalKind::ClosureEnv),
                    );
                    params = (ab.args().skip(first))
                        .map(|l| {
                            (
                                ab.locals[l]
                                    .name
                                    .unwrap_or_else(|| enrang_base::intern("_")),
                                ab.locals[l].ty,
                            )
                        })
                        .collect();
                    (c, f)
                }
            };
            // A local function as a closure captures its hidden arguments and may
            // store nothing through them: EN0616 at the argument, as the same
            // store in an arrow is (A:1360, S:981).
            if let Source::Named(f) = source
                && let Some(hidden) = program.hidden_args.get(&f).filter(|h| !h.is_empty())
            {
                let n = tcx.sig_opt(f).map_or(0, |s| s.params.len()) as u32;
                let name = |i: u32| {
                    let v = hidden.get((i - n) as usize)?;
                    Some(program.top_vars.get(enrang_base::Idx::index(*v))?.name)
                };
                let hit = imp
                    .stores
                    .iter()
                    .find_map(|s| match (s.into >= n, s.from >= n) {
                        (true, _) => name(s.into).map(|x| (x, true)),
                        (false, true) => name(s.from).map(|x| (x, false)),
                        _ => None,
                    });
                if let Some(c) = hit {
                    captured.push(FitError {
                        code: Code::EN0616,
                        found: f,
                        member: f,
                        site: at,
                        captured: Some(c),
                        marked: None,
                        slot: None,
                    });
                    continue;
                }
            }
            imp.perms.truncate(row.perms.len());
            if let Some(code) = fits(&imp, &row) {
                let slots = (params.iter())
                    .flat_map(|(n, t)| std::iter::repeat_n(*n, perm_slots(tcx, &[*t]).len()))
                    .collect();
                // Sorted with the others below.
                captured.push(FitError {
                    code,
                    found: f,
                    member: f,
                    site: at,
                    captured: None,
                    marked: None,
                    slot: Some(Box::new(SlotFit {
                        ty: slot.0,
                        names: slot.1,
                        params: params.iter().map(|(n, _)| *n).collect(),
                        slots,
                        imp: imp.clone(),
                        row: row.clone(),
                    })),
                });
            }
        }
    }
    for (a, adt) in tcx.adts() {
        let data = tcx.def(adt.def);
        if data.module == module
            && adt.as_class().is_some_and(|c| c.copy)
            && crate::class_contract(tcx, a).writes_through_fields
        {
            push(Some(Code::EN0418), adt.def, adt.def, data.name_span);
        }
    }
    out.extend(captured);
    out.extend(const_writes(tcx, bodies, module));
    out.sort_by(|x, y| {
        (&tcx.def(x.found).path, x.site.lo).cmp(&(&tcx.def(y.found).path, y.site.lo))
    });
    out
}
