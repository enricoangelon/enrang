//! Reporting an unresolved name (A:886): EN0301 for a value, EN0302 for a type,
//! each with "did you mean" over the names in scope at the error site; a SPEC 16
//! code for the deferred names; EN0313 for a top-level variable seen from where it
//! is not visible.
//!
//! "Did you mean" runs `enrang_diag::did_you_mean_ordered` (Damerau-Levenshtein,
//! threshold `max(1, len/3)`) over the locals in scope, innermost first, then the
//! names `scope::candidates` lists, each name once, the nearest kept, and of two
//! equally near the first in that order, so a local beats a module's item. The help
//! replaces the name (G06); a secondary label names the candidate's kind where it is
//! declared in user code: `a local with a similar name is declared here` (G06), and,
//! plan choice, `a function ...`, `a class ...`, `an enum ...`, `an interface ...`,
//! `a type ...`, `a constant ...`, `an \`unsafe let\` ...`, `a type parameter ...`,
//! `a similar name is imported here`. A name from the preludes, a form or a
//! primitive type gets the help alone.
//!
//! The deferred names of SPEC 16 (S:3455-3482) get their own code instead, only when
//! they resolve to nothing (plan choice: a program's own `Map` wins): `Worker`,
//! `spawn` (EN1003); `Rc`, `Arc`, `Cell`, `RefCell` (EN1004); `str` (EN1011); `Map`,
//! `Set` (EN1012); `char` (EN1019); `Math` (EN1026); `JSON` (EN1027); `fetch`,
//! `WebSocket` (EN1028); `Object`, `Reflect` (EN1029); `union`, `transmute`
//! (EN1033). Each has the table's message head, a `= note:` with the reason and the
//! table's help (S:3449).

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Edit, Help, did_you_mean_ordered};
use enrang_hir::{DefKind, Tcx};
use enrang_syntax::ast::Ident;

use crate::cx::Sema;
use crate::load::graph;
use crate::resolve::ScopeAt;
use crate::resolve::scope::{Candidate, candidates, member_candidates};
use crate::resolve::toplevel;

/// Which namespace a name was looked up in.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum NameKind {
    Value,
    Type,
    /// The first name of a type path, before a `.` (`d` of `d.Port`): a namespace.
    Namespace,
}

/// Reports `name` as unresolved at `at`, with no local in scope.
pub(crate) fn unresolved(sema: &mut Sema, at: ScopeAt, name: Ident, kind: NameKind) {
    unresolved_with(sema, at, name, kind, &[]);
}

/// Reports `name` as unresolved at `at`, where `locals` (innermost first, with the
/// places they are declared) are the locals in scope: the candidates "did you mean"
/// tries first.
pub(crate) fn unresolved_with(
    sema: &mut Sema,
    at: ScopeAt,
    name: Ident,
    kind: NameKind,
    locals: &[(Symbol, Span)],
) {
    // An import of this name failed and was reported there (EN0305, EN0311).
    if sema.res.import_failed(at, name.name) {
        return;
    }
    if let Some(code) = deferred_code(name.name.as_str()) {
        sema.emit(deferred(code, name.span));
        return;
    }
    if kind == NameKind::Value
        && let Some(diag) = toplevel::invisible_var(sema, at, name)
    {
        sema.emit(diag);
        return;
    }
    let (code, message) = match kind {
        NameKind::Value => (
            Code::EN0301,
            format!("cannot find `{}` in this scope", name.name),
        ),
        NameKind::Type => (
            Code::EN0302,
            format!("cannot find type `{}` in this scope", name.name),
        ),
        NameKind::Namespace => (
            Code::EN0302,
            format!("cannot find `{}` in this scope", name.name),
        ),
    };
    let mut diag = Diagnostic::new(code, message, name.span, "not found");
    if let Some((found, place)) = suggestion(sema, at, name, kind, locals) {
        if let Some((span, label)) = secondary(sema.tcx, place) {
            diag = diag.with_secondary(span, label);
        }
        diag = diag.with_help(Help::machine(
            format!("did you mean `{found}`?"),
            vec![Edit::replace(name.span, found.as_str())],
        ));
    }
    sema.emit(diag);
}

/// The closest name in scope, and what it is.
fn suggestion(
    sema: &Sema,
    at: ScopeAt,
    name: Ident,
    kind: NameKind,
    locals: &[(Symbol, Span)],
) -> Option<(Symbol, Candidate)> {
    let mut all: Vec<(Symbol, Candidate)> = Vec::new();
    if kind == NameKind::Value {
        all.extend(locals.iter().map(|&(n, s)| (n, Candidate::Local(s))));
    }
    all.extend(candidates(sema, at, kind));
    closest(name.name, all)
}

/// The closest of `all` to `name` (each name once, the first kept), a tie going to
/// the first in `all`.
fn closest(name: Symbol, mut all: Vec<(Symbol, Candidate)>) -> Option<(Symbol, Candidate)> {
    let mut seen = std::collections::BTreeSet::new();
    all.retain(|(n, _)| *n != name && seen.insert(*n));
    let names: Vec<&str> = all.iter().map(|(n, _)| n.as_str()).collect();
    let found = did_you_mean_ordered(name.as_str(), &names)?;
    all.into_iter().find(|(n, _)| n.as_str() == found)
}

/// Reports `segment` of a type path as no public member of the namespace for the
/// module at load index `index`, written `prefix` (`d.serial`): EN0311 when it is
/// a `private` item there, as importing it would be (S:801); otherwise EN0302,
/// `` cannot find type `X` in `d` `` for the last segment (`last`) or `` cannot
/// find `x` in `d` `` for one a `.` follows, with "did you mean" over the
/// namespace's members (plan d.3, choice for the wording).
pub(crate) fn unresolved_member(
    sema: &mut Sema,
    index: usize,
    prefix: &str,
    segment: Ident,
    last: bool,
) {
    if !sema.program.modules[index].folder
        && sema.res.scopes[index]
            .names
            .get(&segment.name)
            .is_some_and(|defs| !defs.is_empty())
    {
        let shown = graph::file_name(sema, index);
        sema.err(
            Code::EN0311,
            format!("`{}` is private to `{shown}`", segment.name),
            segment.span,
            "a private item",
        );
        return;
    }
    let message = if last {
        format!("cannot find type `{}` in `{prefix}`", segment.name)
    } else {
        format!("cannot find `{}` in `{prefix}`", segment.name)
    };
    let mut diag = Diagnostic::new(Code::EN0302, message, segment.span, "not found");
    if let Some((found, place)) = closest(segment.name, member_candidates(sema, index, last)) {
        if let Some((span, label)) = secondary(sema.tcx, place) {
            diag = diag.with_secondary(span, label);
        }
        diag = diag.with_help(Help::machine(
            format!("did you mean `{found}`?"),
            vec![Edit::replace(segment.span, found.as_str())],
        ));
    }
    sema.emit(diag);
}

/// The secondary label of a candidate declared in user code.
fn secondary(tcx: &Tcx, place: Candidate) -> Option<(Span, String)> {
    match place {
        Candidate::Local(span) => Some((
            span,
            "a local with a similar name is declared here".to_owned(),
        )),
        Candidate::TyParam(span) if !span.is_dummy() => Some((
            span,
            "a type parameter with a similar name is declared here".to_owned(),
        )),
        Candidate::Import(span) => Some((span, "a similar name is imported here".to_owned())),
        Candidate::Item(def) => {
            let data = tcx.def(def);
            if tcx.module(data.module).library {
                return None;
            }
            let what = match data.kind {
                DefKind::Fn | DefKind::LocalFn | DefKind::DeclareFn => "a function",
                DefKind::Adt(adt) => match tcx.adt(adt).kind {
                    enrang_hir::AdtKind::Class(_) => "a class",
                    enrang_hir::AdtKind::Enum(_) => "an enum",
                    enrang_hir::AdtKind::Interface(_) => "an interface",
                },
                DefKind::TypeAlias | DefKind::StrUnion(_) => "a type",
                DefKind::Const => "a constant",
                DefKind::Static => "an `unsafe let`",
                _ => return None,
            };
            Some((
                data.name_span,
                format!("{what} with a similar name is declared here"),
            ))
        }
        Candidate::TyParam(_) | Candidate::Elsewhere => None,
    }
}

/// The SPEC 16 code of a deferred name, if `name` is one.
pub(crate) fn deferred_code(name: &str) -> Option<Code> {
    Some(match name {
        "Worker" | "spawn" => Code::EN1003,
        "Rc" | "Arc" | "Cell" | "RefCell" => Code::EN1004,
        "str" => Code::EN1011,
        "Map" | "Set" => Code::EN1012,
        "char" => Code::EN1019,
        "Math" => Code::EN1026,
        "JSON" => Code::EN1027,
        "fetch" | "WebSocket" => Code::EN1028,
        "Object" | "Reflect" => Code::EN1029,
        "union" | "transmute" => Code::EN1033,
        _ => return None,
    })
}

/// A SPEC 16 row's message head, the reason for the `= note:` (plan choice) and the
/// table's help, for the deferred codes phase 2 reports.
pub(crate) fn deferred_text(code: Code) -> (&'static str, &'static str, Option<&'static str>) {
    match code {
        Code::EN1003 => (
            "threads are not supported yet",
            "a program runs on one thread; there is no thread or worker to start yet.",
            Some("`Atomic` exists only for interrupt sharing"),
        ),
        Code::EN1004 => (
            "shared ownership types are not supported yet",
            "every value has one owner, and other code refers to it with `&`.",
            Some("Own the value in one place and pass `&T`, or use an arena with integer handles"),
        ),
        Code::EN1011 => (
            "range indexing is not supported yet",
            "a part of an array or a string is taken with `slice`, not with a range.",
            Some(
                "`xs.slice(a, b)` gives a `&Slice<T>`; `s.slice(a, b)` a read-only `&string` part",
            ),
        ),
        Code::EN1012 => (
            "`Map` and `Set` are not supported yet",
            "the standard library has no hashed or ordered collections yet.",
            Some("Use a sorted `T[]`"),
        ),
        Code::EN1014 => (
            "this generic feature is not supported yet",
            "a type parameter stands for one type and takes no type arguments or members of its own.",
            None,
        ),
        Code::EN1019 => (
            "a character type is not supported yet",
            "a string is UTF-8 bytes, read by index as bytes or code points.",
            Some("`s.codePointAt(i)`, `s.byteAt(i)`"),
        ),
        Code::EN1026 => (
            "`Math` does not exist",
            "the math functions are methods of the number types, and constants such as `PI` are read through the type's name.",
            Some("`x.sqrt()`, `f64.PI`, `a.max(b)`"),
        ),
        Code::EN1027 => (
            "`JSON` is not supported yet",
            "the standard library has no JSON parser or printer yet.",
            None,
        ),
        Code::EN1028 => (
            "network APIs are not supported yet",
            "the standard library has no sockets or HTTP yet.",
            None,
        ),
        Code::EN1029 => (
            "reflection is not supported yet",
            "types exist only at compile time; a value carries no list of its fields to inspect.",
            None,
        ),
        Code::EN1030 => (
            "this foreign ABI is not supported yet",
            "foreign code is called with `win64` or `sysv`, passing scalars and pointers.",
            Some("Use scalars and pointers"),
        ),
        Code::EN1033 => (
            "unchecked reinterpretation is not supported yet",
            "a value's bits are read as another type only through the checked conversions.",
            Some("`toBits`, `wrap`, raw-pointer casts in `unsafe`"),
        ),
        _ => ("this is not supported yet", "", None),
    }
}

/// The diagnostic of a deferred feature at `span`, with its note and help.
pub(crate) fn deferred(code: Code, span: Span) -> Diagnostic {
    // `Math` is no deferred feature but a name Enrang never has (SPEC 16's head).
    let label = match code {
        Code::EN1026 => "no such namespace",
        _ => "not supported yet",
    };
    deferred_labeled(code, span, label)
}

/// [`deferred`] with its own label.
pub(crate) fn deferred_labeled(code: Code, span: Span, label: &str) -> Diagnostic {
    let (message, note, help) = deferred_text(code);
    let diag = Diagnostic::new(code, message, span, label).note(note);
    match help {
        Some(help) => diag.with_help(Help::text(help)),
        None => diag,
    }
}
