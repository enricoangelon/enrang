//! Declared contracts (A:1354, A:1358; M3 plan d.8; owner 2F): what a definition
//! with no body to read gets from its marks and SPEC 5.4's defaults (stubs,
//! interface members, `abstract` and `declare` functions, `fn` types, closures),
//! the forms' table (D19), the contract a call applies (A:1176-1179), and the
//! contract indices every contract uses.
//!
//! **Contract indices (A:292, A:311).** Index `i` is argument `i`, `this` 0,
//! hidden arguments after the declared ones, so `sources`, `stores`, the through
//! sets and the `Param(i)` keys name argument positions and `args_map` is the
//! identity; `perms` holds one entry per `&` argument (a reference or a nullable
//! one) in order, then one per reference part of each by-value borrowing tuple
//! argument (`perm_slots`).

use enrang_hir::{
    Contract, DefId, Mark, Perm, Reason, Receiver, ResultPerm, RetSources, Tcx, Ty, TyKind,
};
use enrang_mir::{Body, Callee, FormCall, Operand};

use crate::cx::{CallInfo, SccState};

/// Whether a value of `ty` carries loans (A:1036).
pub fn carrying(tcx: &Tcx, ty: Ty) -> bool {
    tcx.is_slot_type(ty) && !tcx.is_value_type(ty)
}

/// The paths of `ty`'s reference parts: `[[]]` for a reference, each tuple part's
/// index path for a tuple, a nullable's payload looked through, none for a class.
pub fn ref_parts(tcx: &Tcx, ty: Ty) -> Vec<Vec<u32>> {
    fn go(tcx: &Tcx, ty: Ty, path: &mut Vec<u32>, out: &mut Vec<Vec<u32>>) {
        match tcx.kind(ty) {
            TyKind::Nullable(t) => go(tcx, t, path, out),
            TyKind::Ref(_) => out.push(path.clone()),
            TyKind::Tuple(parts) => {
                for (k, &p) in tcx.list(parts).iter().enumerate() {
                    path.push(k as u32);
                    go(tcx, p, path, out);
                    path.pop();
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(tcx, ty, &mut Vec::new(), &mut out);
    out
}

fn is_tuple(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Nullable(t) => is_tuple(tcx, t),
        k => matches!(k, TyKind::Tuple(_)),
    }
}

/// What each permission is of, in `perms` order: each `&` argument `(i, [])`,
/// then each reference part `(i, path)` of each by-value borrowing tuple argument.
pub fn perm_slots(tcx: &Tcx, tys: &[Ty]) -> Vec<(usize, Vec<u32>)> {
    let mut out: Vec<(usize, Vec<u32>)> = (0..tys.len())
        .filter(|&i| is_ref_arg(tcx, tys[i]))
        .map(|i| (i, Vec::new()))
        .collect();
    for (i, &t) in tys.iter().enumerate() {
        if is_tuple(tcx, t) && carrying(tcx, t) {
            out.extend(ref_parts(tcx, t).into_iter().map(|p| (i, p)));
        }
    }
    out
}

/// The permission of `&` argument `i`.
pub fn perm_of(slots: &[(usize, Vec<u32>)], perms: &[Perm], i: usize) -> Option<Perm> {
    let k = slots.iter().position(|(j, p)| *j == i && p.is_empty())?;
    perms.get(k).copied()
}

fn is_string_ref(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Nullable(t) => is_string_ref(tcx, t),
        TyKind::Ref(t) => matches!(tcx.kind(t), TyKind::Str),
        TyKind::Tuple(ps) => tcx.list(ps).iter().any(|&p| is_string_ref(tcx, p)),
        _ => false,
    }
}

/// A `&` argument: a reference or a nullable one.
pub fn is_ref_arg(tcx: &Tcx, ty: Ty) -> bool {
    match tcx.kind(ty) {
        TyKind::Nullable(t) => matches!(tcx.kind(t), TyKind::Ref(_)),
        k => matches!(k, TyKind::Ref(_)),
    }
}

/// Every one of `n` contract indices Read, no sources, no stores, no result.
pub fn all_read(n: usize) -> Contract {
    Contract {
        perms: vec![Perm::Read; n],
        sources: RetSources::NoLoans,
        result: ResultPerm::None,
        through_fields: Vec::new(),
        through_read: Vec::new(),
        stores: Vec::new(),
        moves_or_writes: Vec::new(),
    }
}

/// A row from argument types, marks and the result (N10): Read but `let`
/// (`Write`) and `move` (`Own`), SPEC 5.4's default sources (rule 1 `this` when
/// `method`, rule 2 every reference argument, rule 3 none), no stores, and a
/// writable result unless `readonly` or a `&string` one that may be a part.
pub fn row(tcx: &Tcx, args: &[(Ty, Mark, bool)], method: bool, ret: Ty, ret_ro: bool) -> Contract {
    let tys: Vec<Ty> = args.iter().map(|a| a.0).collect();
    let slots = perm_slots(tcx, &tys);
    let mut c = all_read(slots.len());
    for (k, (i, path)) in slots.iter().enumerate() {
        c.perms[k] = match args[*i] {
            (_, _, true) => Perm::Own,
            (_, Mark::Let, _) if path.is_empty() => Perm::Write,
            _ => Perm::Read,
        };
    }
    if !carrying(tcx, ret) {
        return c;
    }
    let srcs: Vec<u32> = match method {
        true => vec![0],
        false => (0..tys.len() as u32)
            .filter(|&i| is_ref_arg(tcx, tys[i as usize]))
            .collect(),
    };
    let part = srcs.iter().any(|&i| {
        let (t, m, _) = args[i as usize];
        is_string_ref(tcx, t) && m != Mark::Let
    });
    c.result = match (ret_ro, part && is_string_ref(tcx, ret)) {
        (true, _) => ResultPerm::ReadOnly(Reason::Declared),
        (_, true) => ResultPerm::ReadOnly(Reason::StringPart),
        _ => ResultPerm::Writable,
    };
    if !srcs.is_empty() {
        c.sources = RetSources::Params(srcs);
    }
    c
}

/// Whether `def` is a role whose parameters are declared Read (N11).
pub fn is_role(tcx: &Tcx, def: DefId) -> bool {
    let a = &tcx.def(def).attrs;
    a.entry || a.panic_handler || a.interrupt.is_some()
}

/// `def`'s arguments as `(type, mark, own)`, `this` first (its type a reference to
/// `void` stands in: only its being a reference matters).
pub fn sig_args(tcx: &Tcx, def: DefId) -> Vec<(Ty, Mark, bool)> {
    let Some(sig) = tcx.sig_opt(def) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if tcx.takes_this(def) {
        let this = tcx.mk_ref(tcx.common().void);
        out.push(match sig.receiver {
            Some(Receiver::Move) => (this, Mark::None, true),
            Some(Receiver::Ref(m)) => (this, m, false),
            // A constructor writes the object it builds (plan i.28).
            _ => (this, Mark::Let, false),
        });
    }
    out.extend(sig.params.iter().map(|p| (p.ty, p.mark, false)));
    if is_role(tcx, def) {
        out.iter_mut().for_each(|a| a.1 = Mark::None);
    }
    out
}

/// The contract `def`'s marks declare (A:1354).
pub fn declared(tcx: &Tcx, def: DefId) -> Contract {
    let Some(sig) = tcx.sig_opt(def) else {
        return all_read(0);
    };
    let method = matches!(sig.receiver, Some(Receiver::Ref(_) | Receiver::Move));
    row(tcx, &sig_args(tcx, def), method, sig.ret, sig.ret_readonly)
}

/// The contract a call sees: the SCC's current one, else the memo, else the
/// declared one (plan d.8).
pub fn current(tcx: &Tcx, scc: Option<&SccState>, def: DefId) -> Contract {
    match scc.and_then(|s| s.current.get(&def)) {
        Some(c) => c.clone(),
        None => (*crate::contract(tcx, def)).clone(),
    }
}

/// An overridable method's declared contract from its body's: `this` added to
/// the sources and taken out of the through sets (A:1279).
pub fn as_virtual(mut c: Contract) -> Contract {
    if !matches!(c.result, ResultPerm::None) {
        let mut s = match c.sources {
            RetSources::Params(s) => s,
            RetSources::NoLoans => Vec::new(),
        };
        if !s.contains(&0) {
            s.insert(0, 0);
        }
        c.sources = RetSources::Params(s);
        c.through_fields.retain(|&i| i != 0);
        c.through_read.retain(|&i| i != 0);
    }
    c
}

/// The type of an operand in `body`.
pub fn operand_ty(tcx: &Tcx, body: &Body, op: &Operand) -> Option<Ty> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => body.place_ty(tcx, *p).map(|t| t.ty),
        Operand::Const(c) => Some(c.ty),
    }
}

/// The contract a call applies, mapped to its arguments (A:1176-1179): the
/// callee's for `Fn` and `Foreign`; for `Virtual` the method's with `this` added
/// to its sources and taken out of its through sets (A:1279); an `fn` value's or a
/// closure's row from its marks; the forms' table (all Read but `Append`'s target
/// and `writeTo`'s `Formatter`, D19, S:1203); none for `NamedFill` and
/// `ImplicitCtor` (D20).
/// A call of a callee with defaulted parameters that leaves some out passes the
/// arguments supplied, then the hidden ones, then their count (A:937), while the
/// callee's contract indices are its parameters, the omitted ones included, then
/// its hidden ones. `c` is mapped from the callee's indices to the call's
/// arguments, so contract index = argument position holds at the call as
/// everywhere else: each permission to the argument or part it is of, an omitted
/// parameter's dropped (it holds no loan of the caller's), and the sources, the
/// through sets and the stores renumbered, a store with an omitted end dropped.
fn omitted_defaults(tcx: &Tcx, def: DefId, args: &[Operand], tys: &[Ty], c: Contract) -> Contract {
    let Some(sig) = tcx.sig_opt(def) else {
        return c;
    };
    if !sig.params.iter().any(|p| p.has_default) {
        return c;
    }
    let Some(Operand::Const(k)) = args.last() else {
        return c;
    };
    let enrang_mir::ConstKind::Value(enrang_hir::ConstValue::Int(supplied, _)) = k.kind else {
        return c;
    };
    let skip = usize::from(tcx.takes_this(def));
    let (supplied, declared) = (skip + supplied as usize, skip + sig.params.len());
    if supplied >= declared || args.len() < supplied + 1 {
        return c;
    }
    let hidden = args.len() - 1 - supplied;
    // The argument each contract index names, and the types the callee's
    // permissions are laid out over.
    let map: Vec<Option<usize>> = (0..declared + hidden)
        .map(|i| match i {
            i if i < supplied => Some(i),
            i if i < declared => None,
            i => Some(supplied + (i - declared)),
        })
        .collect();
    let contract_tys: Vec<Ty> = (0..declared + hidden)
        .map(|i| match map[i] {
            Some(a) => tys[a],
            None => sig.params[i - skip].ty,
        })
        .collect();
    let theirs = perm_slots(tcx, &contract_tys);
    let ours = perm_slots(tcx, tys);
    let perms = ours
        .iter()
        .map(|(a, path)| {
            (0..map.len())
                .find(|&i| map[i] == Some(*a))
                .and_then(|i| theirs.iter().position(|(j, q)| *j == i && q == path))
                .and_then(|k| c.perms.get(k).copied())
                .unwrap_or(Perm::Read)
        })
        .collect();
    let at = |i: u32| map.get(i as usize).copied().flatten().map(|a| a as u32);
    let renumber = |v: &[u32]| v.iter().filter_map(|&i| at(i)).collect::<Vec<u32>>();
    Contract {
        perms,
        sources: match &c.sources {
            RetSources::Params(v) => RetSources::Params(renumber(v)),
            RetSources::NoLoans => RetSources::NoLoans,
        },
        through_fields: renumber(&c.through_fields),
        through_read: renumber(&c.through_read),
        stores: (c.stores.iter())
            .filter_map(|s| {
                Some(enrang_hir::Store {
                    from: at(s.from)?,
                    into: at(s.into)?,
                    ..s.clone()
                })
            })
            .collect(),
        ..c
    }
}

pub fn call_info(
    tcx: &Tcx,
    body: &Body,
    scc: Option<&SccState>,
    callee: &Callee,
    args: &[Operand],
) -> CallInfo {
    let tys: Vec<Ty> = args
        .iter()
        .map(|a| operand_ty(tcx, body, a).unwrap_or(tcx.common().void))
        .collect();
    let args_map: Vec<usize> = (0..args.len()).collect();
    let n = perm_slots(tcx, &tys).len();
    let fn_row = |op: Option<&Operand>| {
        let sig = match op
            .and_then(|o| operand_ty(tcx, body, o))
            .map(|t| tcx.kind(t))
        {
            Some(TyKind::FnPtr(_, s) | TyKind::Closure(s)) => tcx.fn_sig(s),
            _ => return all_read(n),
        };
        let marks: Vec<_> = sig.params.iter().map(|&(t, m)| (t, m, false)).collect();
        row(tcx, &marks, false, sig.ret, sig.ret_readonly)
    };
    let mut c = match callee {
        Callee::Fn(f) => current(tcx, scc, f.def),
        Callee::Foreign(f) => current(tcx, scc, f.def),
        Callee::Virtual { method, .. } => as_virtual(current(tcx, scc, method.def)),
        Callee::FnPtr(op) => fn_row(Some(op)),
        Callee::ClosureLocal(l) => fn_row(Some(&Operand::Copy((*l).into()))),
        // Every reference parameter Read but the one a form writes: `Append`'s
        // string and `writeTo`'s `Formatter` (S:1203, as `Formatter.write`'s `let`
        // receiver), its first operand also when a template passed directly makes
        // the call `FormParts`.
        Callee::Form(form) | Callee::FormParts { form, .. } => {
            let mut c = all_read(n);
            if matches!(form, FormCall::Append | FormCall::WriteTo) && n > 0 {
                c.perms[0] = Perm::Write;
            }
            c
        }
        Callee::NamedFill { .. } | Callee::ImplicitCtor { .. } => all_read(n),
    };
    c.perms.resize(n.max(c.perms.len()), Perm::Read);
    if let Some(def) = match callee {
        Callee::Fn(f) | Callee::Virtual { method: f, .. } => Some(f.def),
        _ => None,
    } {
        c = omitted_defaults(tcx, def, args, &tys, c);
    }
    CallInfo {
        perms: c.perms,
        sources: c.sources,
        through_fields: c.through_fields,
        through_read: c.through_read,
        stores: c.stores,
        result: c.result,
        args_map,
    }
}
