//! The permission rows of `fn` and closure values (S:682, T:583; M3 plan d.10).
//! Phase 2's type identity ignores rows, so a value of one function type reaches
//! a slot of another that differs only in them; phase 3 compares them wherever a
//! value flows: an assignment, an aggregate's operand, a call's argument and its
//! result. At the top of a site a value's row may allow fewer writes than the
//! slot's, never more; below the top, under `&`, `T[]`, `T | null`, a field, a
//! generic argument or another function type's parameter or result, rows must be
//! equal, since code holding the outer value may store into it or call through it
//! with either row. Into an `fn` type a conversion that changes a `&string` form
//! needs a static source, a function name or a non-capturing arrow (S:682,
//! `S2-13-value`). A named function and an arrow at the top are fitted by their
//! contracts ([`crate::fit`]); the rows nested in their signatures, and in an
//! override's or an implementation's, are compared here ([`check_signatures`]).

use enrang_base::{Idx, Span, Symbol};
use enrang_hir::{
    CheckedProgram, ConstValue, Contract, DefId, FieldIdx, FnPtrSig, FnRef, ModuleId, Perm,
    ResultPerm, Tcx, Ty, TyKind,
};
use enrang_mir::{
    AggregateKind, Bodies, Body, Callee, ClosureFn, ConstKind, Local, LocalKind, Operand, Place,
    Rvalue, StatementKind, TerminatorKind,
};

use crate::declared::{perm_slots, row};

/// How a value's function type misses its slot's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowKind {
    /// At the top: the value may write through parameter `param`, which the
    /// slot's row only reads, or return a read-only result as a writable one.
    Writes { param: Option<usize> },
    /// Below the top: the rows differ.
    Nested,
    /// At the top, into an `fn` type, from a value that is no function name or
    /// non-capturing arrow: parameter `param`, a `&string`, changes its form.
    StringForm { param: usize },
    /// A function's own parameter `param` (or its result, `None`) holds rows
    /// that differ from those of what it stands for: the member it overrides or
    /// implements, or the function type it is converted to (`member` `None`).
    Signature {
        found: DefId,
        member: Option<DefId>,
        param: Option<usize>,
    },
    /// An arrow's own parameter `param` (or its result, `None`) holds rows that
    /// differ from those of the function type it becomes.
    Arrow { param: Option<Symbol> },
}

/// A value of a function type converted where its rows do not fit (EN0615).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RowError {
    pub kind: RowKind,
    /// The function types that differ, innermost: the value's and the slot's.
    pub from: Ty,
    pub to: Ty,
    /// The slot's whole type, with the parameter names its declaration kept.
    pub slot: Ty,
    pub slot_names: Option<Vec<Symbol>>,
    /// What the source code calls the value.
    pub source: String,
    pub site: Span,
}

/// A row of a function type, as the declared contract of its marks.
fn sig_row(tcx: &Tcx, s: &FnPtrSig) -> Contract {
    let marks: Vec<_> = s.params.iter().map(|&(t, m)| (t, m, false)).collect();
    row(tcx, &marks, false, s.ret, s.ret_readonly)
}

/// Whether two rows are the same: their permissions and their result.
fn same_row(a: &Contract, b: &Contract) -> bool {
    a.perms == b.perms && a.result == b.result
}

/// The first misfit of the rows inside `from` against those inside `to`; `top`
/// when `from` is the value's type at the top of its site. `fixed` when the
/// value is a function name or a non-capturing arrow, which needs no adapter.
fn misfit(tcx: &Tcx, from: Ty, to: Ty, top: bool, fixed: bool) -> Option<(RowKind, Ty, Ty)> {
    if from == to {
        return None;
    }
    let nested = |a: Ty, b: Ty| misfit(tcx, a, b, false, fixed);
    let lists = |x: &[Ty], y: &[Ty]| {
        (x.len() == y.len())
            .then(|| x.iter().zip(y).find_map(|(&a, &b)| nested(a, b)))
            .flatten()
    };
    match (tcx.kind(from), tcx.kind(to)) {
        (TyKind::Array(x), TyKind::Array(y))
        | (TyKind::Slice(x), TyKind::Slice(y))
        | (TyKind::Boxed(x), TyKind::Boxed(y))
        | (TyKind::Nullable(x), TyKind::Nullable(y))
        | (TyKind::Ref(x), TyKind::Ref(y))
        | (TyKind::Raw(x), TyKind::Raw(y))
        | (TyKind::Fixed(x, _), TyKind::Fixed(y, _)) => nested(x, y),
        // A view of an array (C18) holds its elements.
        (TyKind::Array(x) | TyKind::Fixed(x, _), TyKind::Slice(y)) => nested(x, y),
        (TyKind::Tuple(x), TyKind::Tuple(y)) => lists(&tcx.list(x), &tcx.list(y)),
        (TyKind::Adt(p, x), TyKind::Adt(q, y)) if p == q => lists(&tcx.list(x), &tcx.list(y)),
        (TyKind::Object(x), TyKind::Object(y)) => {
            let (x, y) = (tcx.shape(x), tcx.shape(y));
            let xs: Vec<Ty> = x.fields.iter().map(|f| f.1).collect();
            let ys: Vec<Ty> = y.fields.iter().map(|f| f.1).collect();
            lists(&xs, &ys)
        }
        (TyKind::FnPtr(_, x), TyKind::FnPtr(_, y)) | (TyKind::Closure(x), TyKind::Closure(y)) => {
            let ptr = matches!(tcx.kind(to), TyKind::FnPtr(..));
            let (x, y) = (tcx.fn_sig(x), tcx.fn_sig(y));
            if x.params.len() != y.params.len() {
                return None;
            }
            let (rx, ry) = (sig_row(tcx, &x), sig_row(tcx, &y));
            let tys: Vec<Ty> = x.params.iter().map(|p| p.0).collect();
            let slots = perm_slots(tcx, &tys);
            let param = |q: usize| slots.get(q).map(|s| s.0);
            let here = match top {
                true => {
                    let more = (0..rx.perms.len().max(ry.perms.len())).find(|&q| {
                        let a = rx.perms.get(q).copied().unwrap_or(Perm::Read);
                        let b = ry.perms.get(q).copied().unwrap_or(Perm::Read);
                        a > b
                    });
                    let result = ry.result == ResultPerm::Writable
                        && matches!(rx.result, ResultPerm::ReadOnly(_));
                    // A `&string` parameter that only reads is a pointer and a
                    // length, one that writes the whole string (S:682).
                    let form = (!fixed && ptr)
                        .then(|| {
                            (0..rx.perms.len().min(ry.perms.len())).find(|&q| {
                                rx.perms[q] != ry.perms[q]
                                    && param(q).is_some_and(|i| is_string_ref(tcx, tys[i]))
                            })
                        })
                        .flatten();
                    match (more, result, form) {
                        (Some(q), _, _) => Some(RowKind::Writes { param: param(q) }),
                        (None, true, _) => Some(RowKind::Writes { param: None }),
                        (None, false, Some(q)) => {
                            param(q).map(|i| RowKind::StringForm { param: i })
                        }
                        _ => None,
                    }
                }
                false => (!same_row(&rx, &ry)).then_some(RowKind::Nested),
            };
            if let Some(kind) = here {
                return Some((kind, from, to));
            }
            let ys: Vec<Ty> = y.params.iter().map(|p| p.0).collect();
            lists(&tys, &ys).or_else(|| nested(x.ret, y.ret))
        }
        _ => None,
    }
}

/// Whether `t` is `&string`.
fn is_string_ref(tcx: &Tcx, t: Ty) -> bool {
    matches!(tcx.kind(t), TyKind::Ref(s) if matches!(tcx.kind(s), TyKind::Str))
}

/// `f`'s own parameter types, its type arguments substituted, and its result.
fn own_types(tcx: &Tcx, f: FnRef) -> Option<(Vec<Ty>, Ty)> {
    let sig = tcx.sig_opt(f.def)?;
    let params = tcx.all_params(sig.generics);
    let args = tcx.list(f.args);
    let s = |t: Ty| match params.len() == args.len() {
        true => tcx.subst(t, &params, &args),
        false => t,
    };
    Some((sig.params.iter().map(|p| s(p.ty)).collect(), s(sig.ret)))
}

/// The first parameter (or the result, `None`) of `found` whose rows, read
/// below the top of the signature, differ from `want`'s: the types of what it
/// stands for.
fn signature_misfit(
    tcx: &Tcx,
    found: FnRef,
    want: &[Ty],
    want_ret: Ty,
) -> Option<(Option<usize>, Ty, Ty)> {
    let (own, ret) = own_types(tcx, found)?;
    if own.len() != want.len() {
        return None;
    }
    let nested = |a: Ty, b: Ty| misfit(tcx, a, b, false, true).map(|(_, x, y)| (x, y));
    (own.iter().zip(want).enumerate())
        .find_map(|(i, (&a, &b))| nested(a, b).map(|(x, y)| (Some(i), x, y)))
        .or_else(|| nested(ret, want_ret).map(|(x, y)| (None, x, y)))
}

/// The module's overrides and satisfactions whose signatures nest rows other
/// than those of what they stand for (S:682: a row nested inside the signature
/// must be equal), each at the overriding or implementing method's name.
pub fn check_signatures(tcx: &Tcx, program: &CheckedProgram, module: ModuleId) -> Vec<RowError> {
    let site = |found: DefId, member: DefId| {
        let none = tcx.empty_list();
        let want = own_types(
            tcx,
            FnRef {
                def: member,
                args: none,
            },
        )?;
        let (param, x, y) = signature_misfit(
            tcx,
            FnRef {
                def: found,
                args: none,
            },
            &want.0,
            want.1,
        )?;
        Some(RowError {
            kind: RowKind::Signature {
                found,
                member: Some(member),
                param,
            },
            from: x,
            to: y,
            slot: y,
            slot_names: None,
            source: String::new(),
            site: tcx.def(found).name_span,
        })
    };
    let mut out = Vec::new();
    for r in &program.satisfactions {
        if tcx.def(r.found).module == module {
            out.extend(site(r.found, r.member));
        }
    }
    for (d, _) in tcx.defs().filter(|(_, x)| x.module == module) {
        if let Some(b) = crate::fit::base_decl(tcx, d) {
            out.extend(site(d, b));
        }
    }
    out.sort_by_key(|e| e.site.lo);
    out.dedup_by_key(|e| e.site);
    out
}

/// The type of an operand of `b`.
fn operand_ty(tcx: &Tcx, b: &Body, op: &Operand) -> Option<Ty> {
    match op {
        Operand::Const(c) => Some(c.ty),
        Operand::Copy(p) | Operand::Move(p) => b.place_ty(tcx, *p).map(|t| t.ty),
    }
}

/// The local a temporary-free operand names, if it is a whole local.
fn whole_local(op: &Operand) -> Option<Local> {
    op.place().filter(|p| p.is_local()).map(|p| p.local)
}

/// Whether an operand of `b` is a function name or a non-capturing arrow as an
/// `fn` value, through the temporaries that carry it.
fn is_fixed(b: &Body, op: &Operand) -> bool {
    if let Operand::Const(c) = op {
        return matches!(c.kind, ConstKind::Value(ConstValue::FnAddr(_)));
    }
    let Some(l) = whole_local(op).filter(|l| b.locals[*l].kind == LocalKind::Temp) else {
        return false;
    };
    b.blocks.iter().flat_map(|blk| &blk.stmts).any(|s| {
        matches!(&s.kind, StatementKind::Assign { dest, value }
        if *dest == Place::local(l) && match value {
            Rvalue::ArrowFn(_) => true,
            Rvalue::Use(o) => is_fixed(b, o),
            _ => false,
        })
    })
}

/// Whether `op` is a function name, or a temporary holding a closure value or an
/// `fn` value made in this body from a function name or an arrow, which
/// [`crate::fit`] fits by its contract where it is made; a closure made from an
/// `fn` value (`closure(fn_value, _e)`) is not, and its row is compared here.
fn made_here(b: &Body, op: &Operand) -> bool {
    if let Operand::Const(c) = op {
        return matches!(c.kind, ConstKind::Value(ConstValue::FnAddr(_)));
    }
    let Some(l) = whole_local(op).filter(|l| b.locals[*l].kind == LocalKind::Temp) else {
        return false;
    };
    b.blocks.iter().flat_map(|blk| &blk.stmts).any(|s| {
        matches!(&s.kind, StatementKind::Assign { dest, value }
        if *dest == Place::local(l)
            && matches!(value, Rvalue::ArrowFn(_) | Rvalue::ClosureValue {
                func: ClosureFn::Named(_) | ClosureFn::Arrow(_),
                ..
            }))
    })
}

/// What the source calls an operand, and where it stands: a named local's name,
/// found in the site after its first `(` for a call's argument, else the text of
/// what made the temporary that holds it, else the site.
fn source_of(tcx: &Tcx, b: &Body, op: &Operand, site: Span) -> (String, Span) {
    let map = tcx.map();
    let text = |s: Span| map.text(s).to_owned();
    let inside = |s: Span| s.lo >= site.lo && s.hi <= site.hi;
    let Some(l) = whole_local(op) else {
        return (text(site), site);
    };
    if let Some(n) = b.locals[l].name {
        let name = n.as_str().to_owned();
        let t = text(site);
        let from = t.find('(').map_or(0, |i| i + 1);
        let ident = |c: char| c.is_alphanumeric() || c == '_' || c == '$';
        let at = t[from..]
            .match_indices(&name)
            .map(|(i, _)| i + from)
            .find(|&i| {
                !t[..i].chars().next_back().is_some_and(ident)
                    && !t[i + name.len()..].chars().next().is_some_and(ident)
            });
        let span = at.map_or(site, |i| Span {
            lo: enrang_base::BytePos(site.lo.0 + i as u32),
            hi: enrang_base::BytePos(site.lo.0 + (i + name.len()) as u32),
        });
        return (name, span);
    }
    let made = b.blocks.iter().find_map(|blk| {
        let st = blk.stmts.iter().find(
            |s| matches!(&s.kind, StatementKind::Assign { dest, .. } if *dest == Place::local(l)),
        );
        match (st, &blk.term.kind) {
            (Some(s), _) => Some(s.span),
            (None, TerminatorKind::Call { dest, .. }) if *dest == Place::local(l) => {
                Some(blk.term.span)
            }
            _ => None,
        }
    });
    match made {
        Some(s) if inside(s) => (text(s), s),
        Some(s) => (text(s), site),
        None => (text(site), site),
    }
}

/// One flow of a value into a slot: the operand, the slot's type, the names its
/// declaration kept, and the site.
struct Flow<'a> {
    /// The value's type, and its operand when it is one.
    from: Option<Ty>,
    op: Option<&'a Operand>,
    to: Ty,
    names: Option<Vec<Symbol>>,
    site: Span,
}

/// The operands of `value`, assigned into a slot of type `dest`, each with the
/// type it lands at.
fn aggregate_flows<'a>(tcx: &Tcx, value: &'a Rvalue, dest: Ty) -> Vec<(&'a Operand, Ty)> {
    let Rvalue::Aggregate(kind, ops) = value else {
        return Vec::new();
    };
    let tys: Vec<Option<Ty>> = match (kind, tcx.kind(dest)) {
        (AggregateKind::Present, TyKind::Nullable(t)) => vec![Some(t)],
        (
            AggregateKind::Fixed(_) | AggregateKind::Repeat(_),
            TyKind::Fixed(t, _) | TyKind::Array(t),
        ) => {
            vec![Some(t); ops.len()]
        }
        (AggregateKind::Tuple, TyKind::Tuple(l)) => tcx.list(l).iter().map(|&t| Some(t)).collect(),
        (AggregateKind::Adt { adt, variant, args }, _) => (0..ops.len())
            .map(|i| Some(tcx.field_ty(*adt, *variant, FieldIdx::new(i), *args)))
            .collect(),
        (AggregateKind::Object(_), TyKind::Object(s)) => {
            tcx.shape(s).fields.iter().map(|f| Some(f.1)).collect()
        }
        _ => Vec::new(),
    };
    ops.iter()
        .zip(tys)
        .filter_map(|(o, t)| t.map(|t| (o, t)))
        .collect()
}

/// Every flow of a value into a slot in `b`, and the named functions made
/// closure values whose nested rows differ from their closure type's.
fn flows<'a>(tcx: &Tcx, bodies: &Bodies, b: &'a Body) -> (Vec<Flow<'a>>, Vec<RowError>) {
    let mut out = Vec::new();
    let mut named = Vec::new();
    for blk in b.blocks.iter() {
        for st in &blk.stmts {
            let StatementKind::Assign { dest, value } = &st.kind else {
                continue;
            };
            let Some(to) = b.place_ty(tcx, *dest).map(|t| t.ty) else {
                continue;
            };
            let names = (*dest == Place::local(Local::RETURN))
                .then(|| ret_names(tcx, b))
                .flatten();
            let of_op = |op: &'a Operand, to: Ty, names| Flow {
                from: operand_ty(tcx, b, op),
                op: Some(op),
                to,
                names,
                site: st.span,
            };
            match value {
                Rvalue::Use(op) | Rvalue::Convert(_, op) => out.push(of_op(op, to, names)),
                // `&p` is a value of type `&T` for `p: T`.
                Rvalue::Ref { place, .. } => out.push(Flow {
                    from: b.place_ty(tcx, *place).map(|t| tcx.mk_ref(t.ty)),
                    op: None,
                    to,
                    names,
                    site: st.span,
                }),
                Rvalue::ClosureValue {
                    func: enrang_mir::ClosureFn::Named(f),
                    ..
                } => named.extend(named_sig_misfit(tcx, *f, to, st.span)),
                Rvalue::ClosureValue {
                    func: enrang_mir::ClosureFn::Arrow(a),
                    ..
                }
                | Rvalue::ArrowFn(a) => {
                    named.extend(arrow_sig_misfit(tcx, bodies, b, *a, to, st.span))
                }
                Rvalue::Aggregate(..) => {
                    for (op, t) in aggregate_flows(tcx, value, to) {
                        out.push(of_op(op, t, None));
                    }
                }
                _ => {}
            }
        }
        if let TerminatorKind::Call {
            callee, args, dest, ..
        } = &blk.term.kind
        {
            let (params, ret) = enrang_mir::callee_types(tcx, b, callee, args);
            // The result into its destination.
            if let (Some(ret), Some(to)) = (ret, b.place_ty(tcx, *dest).map(|t| t.ty)) {
                out.push(Flow {
                    from: Some(ret),
                    op: None,
                    to,
                    names: None,
                    site: blk.term.span,
                });
            }
            let names = |i: usize| match callee {
                Callee::Fn(f) | Callee::Virtual { method: f, .. } => {
                    let this = usize::from(tcx.takes_this(f.def));
                    let sig = tcx.sig_opt(f.def)?;
                    sig.params.get(i.checked_sub(this)?)?.fn_names.clone()
                }
                _ => None,
            };
            // The parameter's type as declared, before substitution: the row of
            // an `fn` or closure type written with a type parameter is computed
            // generically (SPEC 4.10, A:1363), so `fn(a: &T) => &T` keeps its
            // writable result at `T := string`. A function name or an arrow made
            // for the argument is fitted by its contract instead (`crate::fit`).
            let generic = |i: usize| match callee {
                Callee::Fn(f) | Callee::Virtual { method: f, .. } => {
                    let this = usize::from(tcx.takes_this(f.def));
                    let t = tcx.sig_opt(f.def)?.params.get(i.checked_sub(this)?)?.ty;
                    matches!(tcx.kind(t), TyKind::FnPtr(..) | TyKind::Closure(_)).then_some(t)
                }
                _ => None,
            };
            for (i, (op, to)) in args.iter().zip(params.unwrap_or_default()).enumerate() {
                out.push(Flow {
                    from: operand_ty(tcx, b, op),
                    op: Some(op),
                    to,
                    names: names(i),
                    site: blk.term.span,
                });
                if let Some(g) = generic(i).filter(|&g| g != to && !made_here(b, op)) {
                    out.push(Flow {
                        from: operand_ty(tcx, b, op),
                        op: Some(op),
                        to: g,
                        names: names(i),
                        site: blk.term.span,
                    });
                }
            }
        }
    }
    (out, named)
}

/// The names the owner's declaration kept for a function type it returns.
fn ret_names(tcx: &Tcx, b: &Body) -> Option<Vec<Symbol>> {
    match b.owner {
        enrang_mir::BodyOwner::Fn(d) => tcx.sig_opt(d)?.ret_fn_names.clone(),
        _ => None,
    }
}

/// A function name converted to an `fn` type whose rows, nested in its
/// parameters or result, differ from the function's own (S:682).
fn named_misfit(tcx: &Tcx, op: &Operand, to: Ty, site: Span) -> Option<RowError> {
    let Operand::Const(c) = op else {
        return None;
    };
    let ConstKind::Value(ConstValue::FnAddr(f)) = c.kind else {
        return None;
    };
    named_sig_misfit(tcx, f, to, site)
}

/// `f`, converted to `to`, against the function type's parameters and result.
fn named_sig_misfit(tcx: &Tcx, f: FnRef, to: Ty, site: Span) -> Option<RowError> {
    let (TyKind::FnPtr(_, s) | TyKind::Closure(s)) = tcx.kind(to) else {
        return None;
    };
    let sig = tcx.fn_sig(s);
    let want: Vec<Ty> = sig.params.iter().map(|p| p.0).collect();
    let (param, x, y) = signature_misfit(tcx, f, &want, sig.ret)?;
    Some(RowError {
        kind: RowKind::Signature {
            found: f.def,
            member: None,
            param,
        },
        from: x,
        to: y,
        slot: to,
        slot_names: None,
        source: String::new(),
        site,
    })
}

/// An arrow made a closure or `fn` value of type `to` whose own parameter or
/// result types nest rows other than `to`'s (S:682: an arrow is fitted as a
/// function is, wherever it becomes one).
fn arrow_sig_misfit(
    tcx: &Tcx,
    bodies: &Bodies,
    b: &Body,
    a: enrang_hir::ArrowId,
    to: Ty,
    site: Span,
) -> Option<RowError> {
    let (TyKind::FnPtr(_, s) | TyKind::Closure(s)) = tcx.kind(to) else {
        return None;
    };
    let parent = match b.owner {
        enrang_mir::BodyOwner::Fn(d) => enrang_hir::BodyOwner::Fn(d),
        enrang_mir::BodyOwner::Test(d) => enrang_hir::BodyOwner::Test(d),
        enrang_mir::BodyOwner::Statements(m) => enrang_hir::BodyOwner::Statements(m),
        enrang_mir::BodyOwner::Arrow(p, _) => p,
        enrang_mir::BodyOwner::Shim(_) => return None,
    };
    let ab = bodies.get(&enrang_mir::BodyOwner::Arrow(parent, a))?;
    let first = match ab.locals.get(Local(1)).map(|d| d.kind) {
        Some(LocalKind::ClosureEnv) => 1,
        _ => 0,
    };
    let own: Vec<(Ty, Option<Symbol>)> = (first + 1..=ab.arg_count as usize)
        .map(|i| {
            (
                ab.locals[Local(i as u32)].ty,
                ab.locals[Local(i as u32)].name,
            )
        })
        .collect();
    let sig = tcx.fn_sig(s);
    if own.len() != sig.params.len() {
        return None;
    }
    let nested = |x: Ty, y: Ty| misfit(tcx, x, y, false, true).map(|(_, p, q)| (p, q));
    let (name, x, y) = (own.iter().zip(&sig.params))
        .find_map(|(&(t, n), &(w, _))| nested(t, w).map(|(p, q)| (n, p, q)))
        .or_else(|| nested(ab.locals[Local::RETURN].ty, sig.ret).map(|(p, q)| (None, p, q)))?;
    Some(RowError {
        kind: RowKind::Arrow { param: name },
        from: x,
        to: y,
        slot: to,
        slot_names: None,
        source: String::new(),
        site,
    })
}

/// Every value of `bodies` converted where its function rows do not fit.
pub fn check_bodies(tcx: &Tcx, bodies: &Bodies) -> Vec<RowError> {
    let mut out = Vec::new();
    for b in bodies.values() {
        let (list, named) = flows(tcx, bodies, b);
        out.extend(named);
        for f in list {
            let Some(from) = f.from else {
                continue;
            };
            let fixed = f.op.is_some_and(|op| is_fixed(b, op));
            if let Some(e) = f.op.and_then(|op| named_misfit(tcx, op, f.to, f.site)) {
                out.push(e);
                continue;
            }
            if let Some((kind, x, y)) = misfit(tcx, from, f.to, true, fixed) {
                let (source, site) = match f.op {
                    Some(op) => source_of(tcx, b, op, f.site),
                    None => (tcx.map().text(f.site).to_owned(), f.site),
                };
                out.push(RowError {
                    kind,
                    from: x,
                    to: y,
                    slot: f.to,
                    slot_names: f.names,
                    source,
                    site,
                });
            }
        }
    }
    out.sort_by_key(|e| e.site.lo);
    out.dedup_by_key(|e| e.site);
    out
}
