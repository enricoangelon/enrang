//! Where a program starts (plan d.17; SPEC 7, S:1143; owner 4F).
//!
//! The entry module's top-level statements, when it has any; then a `function
//! main` beside them, a local function among them or an item after them, is
//! warning EN0314 and not the entry. In a file with no statements, `main` is the
//! entry when it is `(): void`, `(): i32` or `(): Result<void, E>`; any other
//! `main` is EN0436, at its name, whose head names what is wrong: the result (plan
//! e's head), or parameters or type parameters (**choice**: heads of their own,
//! since the plan's speaks of the result only). Of several overloads of `main`,
//! each invalid one is EN0436 and the first valid one is the entry. A file with
//! neither statements nor `main` has no entry, as a module checked on its own (the
//! M1 near-misses). Only the entry module's own `main` counts, never an imported
//! one. `@entry` and EN0809 are M9's.
//!
//! Run once every body is typed (plan d.1 step 7), so the top-level `assert`s among
//! a program's statements whose condition is constant are evaluated here too
//! (`consteval::check_statement_asserts`, EN0415, A:918).

use enrang_base::intern;
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{DefId, DefKind, Entry, IntTy, LangItem, TyKind};

use crate::consteval;
use crate::cx::Sema;

pub(crate) fn check(sema: &mut Sema) {
    consteval::check_statement_asserts(sema);
    let index = sema.program.entry;
    let module = sema.module_id(index);
    let mains: Vec<DefId> = sema.res.scopes[index]
        .names
        .get(&intern("main"))
        .map(|defs| {
            defs.iter()
                .copied()
                .filter(|&d| matches!(sema.tcx.def(d).kind, DefKind::Fn | DefKind::LocalFn))
                .collect()
        })
        .unwrap_or_default();
    if !sema.program.modules[index].ast.stmts.is_empty() {
        sema.entry = Entry::Statements(module);
        for main in mains {
            let span = sema.tcx.def(main).name_span;
            sema.emit(
                Diagnostic::new(
                    Code::EN0314,
                    "`main` beside top-level statements is not the entry point",
                    span,
                    "the top-level statements run instead",
                )
                .with_help(Help::text(
                    "call `main()` from the statements, or move the statements into `main`",
                )),
            );
        }
        return;
    }
    let mut entry = None;
    for main in mains {
        match invalid(sema, main) {
            Some(diag) => sema.emit(diag),
            None => {
                entry.get_or_insert(main);
            }
        }
    }
    if let Some(main) = entry {
        sema.entry = Entry::Main(main);
    }
}

/// EN0436 for a `main` that is not `(): void`, `(): i32` or `(): Result<void, E>`;
/// `None` for one that is, or whose signature holds an error already reported.
fn invalid(sema: &Sema, main: DefId) -> Option<Diagnostic> {
    let tcx = &*sema.tcx;
    let sig = tcx.sig_opt(main)?;
    let span = tcx.def(main).name_span;
    if !sig.params.is_empty() {
        let count = sig.params.len();
        let label = match count {
            1 => "this `main` takes 1 parameter".to_owned(),
            _ => format!("this `main` takes {count} parameters"),
        };
        return Some(
            Diagnostic::new(Code::EN0436, "`main` takes no parameters", span, label)
                .with_help(Help::text("read the command line with `os.args()`")),
        );
    }
    if !tcx.all_params(sig.generics).is_empty() {
        return Some(Diagnostic::new(
            Code::EN0436,
            "`main` can't be generic",
            span,
            "the entry point is called with no type arguments",
        ));
    }
    let ret = sig.ret;
    let fits = match tcx.kind(ret) {
        TyKind::Void | TyKind::Int(IntTy::I32) | TyKind::Error => true,
        TyKind::Adt(adt, args) => {
            tcx.is_lang_adt(adt, LangItem::Result)
                && tcx
                    .list(args)
                    .first()
                    .is_some_and(|&ok| matches!(tcx.kind(ok), TyKind::Void | TyKind::Error))
        }
        _ => tcx.references_error(ret),
    };
    if fits {
        return None;
    }
    Some(Diagnostic::new(
        Code::EN0436,
        "`main` must return `void`, `i32` or `Result<void, E>`",
        span,
        format!("this `main` returns `{}`", tcx.ty_string(ret)),
    ))
}
