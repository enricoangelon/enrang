//! R1/R2 position checks (plan d.15; SPEC 4.1 S:560, 4.3 S:590, S:606, 4.4 S:631,
//! S:764, 5.1 S:845-847; A:892; owner 4E), on resolved types, so an alias cannot
//! hide a reference:
//!
//! - every element (`T[]`, `T[N]`, `Slice<T>`), payload field, generic argument and
//!   object-type field must be in `V` (`is_value_type`), except that `Box<I>` takes
//!   an interface: a reference, a borrowing class or a borrowing tuple there is
//!   EN0701 (G19: `` an array can't hold a `Lexer`, because `Lexer` holds a
//!   reference ``, labelled `` `Lexer` borrows through its field `src` ``, with the
//!   rule and `` help: own the data: `private src: string;` ``, built from the
//!   reference field); EN0701 comes first, so `Result<i64, &AgeError>` gets no
//!   EN0454 (lowering leaves an `E` outside `V` alone);
//! - a reference field, one whose type is `&T`, `&T | null`, a borrowing tuple or a
//!   nullable one (`readonly &` included: it is a reference field too), must be
//!   `private` (EN0701), a parameter property included;
//! - a class bound that names a borrowing class is EN0701, `` `T` can't stand for a
//!   `Lexer`, because `Lexer` holds a reference `` (S:764);
//! - `Slice<T>` without `&`, as a variable, field, element, tuple part, result,
//!   parameter, or behind a raw pointer, is EN0401 `` `Slice<u8>` is a view, so it
//!   exists only behind `&` `` (S:606); a view or `string` written as the type
//!   argument of a class, enum or interface waits in `ViewUses::written` for the
//!   facts of its parameter, which `views.rs` computes once every body is typed;
//! - an interface type by value in a variable, result, field, element, tuple part
//!   or generic argument is EN1006 in SPEC 16's form: its head, a note naming the
//!   case and one help, the row's `` `&Speaker` to refer to one, `Box<Speaker>` to
//!   own one ``, or for `Result<T, Error>` the row's help for errors (S:631,
//!   S:3458; the plan's two helps `use &Speaker` / `use Box<Speaker>` would break
//!   S:3449's one `help:`), and so is an unannotated local inferred as one (T:862);
//! - a `Box<I>`, or an `&I` anywhere but at the top of a parameter, of an interface
//!   whose table can't serve a member (a by-value `Self`, or a member compiled once
//!   per type: 4C's `two_word_need`) is EN1006 at that part of the written type,
//!   with the member named in the note (T:1000, T:1007);
//! - `&&T` and `&(&T | null)` are EN0702 wherever they are written, a body's
//!   annotations and casts included, which lowering reports as it lowers them
//!   (S:847); an inferred one comes from a type argument bound to a reference,
//!   which is 4A's EN0703, or from `&r` on an `r: &T | null`, which typeck
//!   reports at the `&` (EN0702), so inferred types are not checked for it here
//!   (plan choice: one mistake, one diagnostic).
//!
//! **Where the checks look** (plan d.15), so that one mistake gives one diagnostic:
//! every type written in a declaration of a user module (parameters, results,
//! fields, parameter properties, enum case fields, constants, `unsafe let`s, class
//! bounds) and in a body (annotations of named locals, casts, arrow parameters and
//! results, field initialisers included), aliases at their use, and the inferred
//! type of each unannotated local (a `for...of` or destructuring binding and an
//! arrow parameter included) unless its initialiser only copies a type written
//! elsewhere (a local, a field, a cast, a call whose declared result names no type
//! parameter), which that position checks. The type of an arbitrary expression is
//! never checked (`[lx]` in G19 is not; its annotation `Lexer[]` is). A written
//! type gets at most one diagnostic, at the constructor that directly holds the
//! offender, so that its message names the offender itself (plan d.15 as amended
//! by stage 6: `&Lexer[][]` reports `an array can't hold a `Lexer`` at the inner
//! `Lexer[]`), found top-down. Type arguments at a call or `new`,
//! written or inferred, are 4A's (`Deferred::Bounds`: EN0701, EN0703, EN1006), and a
//! C20/C22 conversion is 4C's and 3A's (EN0440, EN0701, EN1006), so neither is
//! looked at here. Library declarations are trusted (plan choice).

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::{Span, Symbol};
use enrang_diag::{Code, Diagnostic, Help};
use enrang_hir::{
    AdtId, ArrowId, Body, Bound, DefId, ExprKind, Implicit, LocalId, LocalKind, ParamId, Ty,
    TyKind, Vis,
};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::ItemAstKind;
use crate::passes::views::WrittenArg;
use crate::passes::{AstNode, BodyAst, for_each_expr, walk_body_ast};
use crate::typeck::iface::{iface_unsupported, need_note, two_word_need};

/// G19's rule, for a borrowing class.
const CLASS_RULE: &str = "a class that holds a reference lives only where a reference can: in locals, parameters, return values and fields of another such class.";
/// The same rule for a reference.
const REF_RULE: &str = "a reference lives only in locals, parameters, return values, tuple parts and `private` fields of a class that holds references.";
/// The same rule for a tuple with a reference part.
const TUPLE_RULE: &str = "a tuple that holds a reference lives only where a reference can: in locals, parameters, return values and `private` fields of a class that holds references.";

/// Where a type stands, for what may stand at its top.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Pos {
    /// A parameter's type: a closure type or a by-value interface may stand here.
    Param,
    /// A local, a constant or an `unsafe let`.
    Local,
    Result,
    /// `readonly` is the modifier before the name, which the help keeps.
    Field {
        vis: Vis,
        name: Symbol,
        readonly: bool,
    },
    /// An enum case's field: a value position.
    Payload,
    /// The target of a cast, or a static path's type (`Stack<&i64>.empty()`): only
    /// what is inside it is checked.
    Cast,
    /// The type of `sizeOf`, `alignOf` or `offsetOf`, which must have a size.
    Form,
}

impl Pos {
    /// The place, for EN1006's label.
    fn place(self) -> &'static str {
        match self {
            Pos::Param => "a parameter",
            Pos::Local => "a variable",
            Pos::Result => "a result",
            Pos::Field { .. } => "a field",
            Pos::Payload => "an enum case",
            Pos::Cast => "a cast",
            Pos::Form => "a size form",
        }
    }
}

/// What holds a value position, for EN0701's message.
#[derive(Clone)]
enum Container {
    Array,
    /// A generic class, enum or interface, `Box` and `Slice` included.
    Named(String),
    Object,
    Case,
}

impl Container {
    fn noun(&self) -> String {
        match self {
            Container::Array => "an array".to_owned(),
            Container::Named(name) => format!("{} `{name}`", article(name)),
            Container::Object => "an object type".to_owned(),
            Container::Case => "an enum case".to_owned(),
        }
    }

    /// The place, for EN1006's label.
    fn place(&self) -> String {
        match self {
            Container::Array => "an array".to_owned(),
            Container::Named(_) => "a type argument".to_owned(),
            Container::Object => "an object type".to_owned(),
            Container::Case => "an enum case".to_owned(),
        }
    }
}

/// `a` or `an` before `word` (`classes::sig::article`).
fn article(word: &str) -> &'static str {
    crate::classes::sig::article(word)
}

// ---------------------------------------------------------------------------------
// Declarations.

/// The positions of every type written in a user module's declarations.
pub(crate) fn check_decls(sema: &mut Sema) {
    let items = sema.decls.items.clone();
    for item in &items {
        if sema.tcx.module(item.module).library {
            continue;
        }
        match &item.kind {
            ItemAstKind::Function(d) | ItemAstKind::LocalFn(d) => {
                sig(sema, item.def, &d.params, d.ret.as_ref().map(|r| &r.ty));
                fn_bounds(sema, item.def, &d.type_params);
            }
            // A `declare function`'s types are lowering's EN0816 and EN1030, which
            // reject everything a position check would.
            ItemAstKind::Declare(d) => fn_bounds(sema, item.def, &d.type_params),
            ItemAstKind::Class(adt, decl, members) => {
                adt_bounds(sema, *adt, &decl.type_params);
                for (member, def) in decl.members.iter().zip(members) {
                    match (&member.kind, def) {
                        (ast::ClassMemberKind::Field(f), _) => {
                            field(sema, *adt, f.name.name, &f.ty, f.optional);
                        }
                        (ast::ClassMemberKind::Method(m), Some(def)) => method(sema, *def, m),
                        (ast::ClassMemberKind::Constructor(c), Some(def)) => {
                            ctor(sema, *adt, *def, c);
                        }
                        _ => {}
                    }
                }
            }
            ItemAstKind::Enum(adt, decl, methods) => {
                adt_bounds(sema, *adt, &decl.type_params);
                payloads(sema, *adt, decl);
                for (m, def) in decl.methods.iter().zip(methods) {
                    method(sema, *def, m);
                }
            }
            ItemAstKind::Interface(adt, decl, members) => {
                adt_bounds(sema, *adt, &decl.type_params);
                for (member, def) in decl.members.iter().zip(members) {
                    if let (ast::IfaceMember::Method(m), Some(def)) = (member, def) {
                        method(sema, *def, m);
                    }
                }
            }
            ItemAstKind::Extend(e, defs) => {
                for (m, def) in e.members.iter().zip(defs) {
                    method(sema, *def, &m.method);
                }
            }
            ItemAstKind::Const(c) => {
                if let (Some(t), Some(ty)) = (&c.ty, sema.tcx.item_ty(item.def)) {
                    written(sema, ty, t, Pos::Local, false);
                }
            }
            ItemAstKind::Static(u) => {
                if let Some(ty) = sema.tcx.item_ty(item.def) {
                    written(sema, ty, &u.ty, Pos::Local, false);
                }
            }
            ItemAstKind::FieldsInterface(_)
            | ItemAstKind::Alias(_)
            | ItemAstKind::StrUnion
            | ItemAstKind::StaticAssert
            | ItemAstKind::Test => {}
        }
    }
}

/// A method's signature, its own bounds and its `where` clause's.
fn method(sema: &mut Sema, def: DefId, m: &ast::MethodDecl) {
    sig(sema, def, &m.params, m.ret.as_ref().map(|r| &r.ty));
    fn_bounds(sema, def, &m.type_params);
    where_bounds(sema, def, &m.where_clause);
}

/// The bounds a method's `where` clause adds (S:323), checked as written ones.
fn where_bounds(sema: &mut Sema, def: DefId, clause: &[ast::WherePred]) {
    let Some(sig) = sema.tcx.sig_opt(def).cloned() else {
        return;
    };
    for (p, lowered) in &sig.where_bounds {
        let name = sema.tcx.param(*p).name;
        let Some(pred) = clause.iter().find(|w| w.param.name == name) else {
            continue;
        };
        if lowered.len() != pred.bounds.len() {
            continue;
        }
        for (&b, written_bound) in lowered.iter().zip(&pred.bounds) {
            borrowing_bound(sema, name, b, written_bound.span);
        }
    }
}

/// The parameters and result of `def`'s signature, against their AST.
fn sig(sema: &mut Sema, def: DefId, params: &[ast::Param], ret: Option<&ast::TypeExpr>) {
    let Some(sig) = sema.tcx.sig_opt(def).cloned() else {
        return;
    };
    for (p, lowered) in params.iter().zip(&sig.params) {
        written(sema, lowered.ty, &p.ty, Pos::Param, p.optional);
    }
    if let Some(ret) = ret {
        written(sema, sig.ret, ret, Pos::Result, false);
        if sig.ret_readonly {
            readonly_result(sema, sig.ret, ret.span);
        }
    }
}

/// EN0803 at a local function with hidden arguments that became an `fn` value
/// with no `fn` type expected, `const f = grow;` (S:983): typing checks the name
/// only at an `fn` or closure type, and a call through such a value would pass
/// none of the hidden arguments.
pub(crate) fn hidden_fn_values(sema: &mut Sema, b: &Body) {
    let mut found: Vec<(Span, DefId)> = Vec::new();
    for_each_expr(b, &mut |e| {
        if let ExprKind::Const(enrang_hir::ConstValue::FnAddr(f)) = &e.kind
            && !e.adjust.contains(&enrang_hir::Adjust::ArrowToClosure)
            && matches!(sema.tcx.kind(e.ty), TyKind::FnPtr(..))
            && sema.tcx.def(f.def).kind == enrang_hir::DefKind::LocalFn
        {
            found.push((e.span, f.def));
        }
    });
    for (span, def) in found {
        let vars: Vec<String> = crate::resolve::toplevel::hidden_args(sema, def)
            .iter()
            .filter_map(|v| sema.res.toplevel.vars.get(v.0 as usize))
            .map(|v| format!("`{}`", v.name))
            .collect();
        if vars.is_empty() {
            continue;
        }
        let what = match vars.len() {
            1 => "a hidden argument",
            _ => "hidden arguments",
        };
        let text = sema.tcx.map().text(span).to_owned();
        sema.emit(
            Diagnostic::new(
                Code::EN0803,
                format!("`{text}` uses top-level variables, so it can't become an `fn`"),
                span,
                format!("it takes {} as {what}", vars.join(", ")),
            )
            .with_help(Help::text(
                "pass it where a closure parameter is expected, which may use them",
            )),
        );
    }
}

/// Whether `t` is a reference or holds one as a tuple part or payload.
fn holds_ref(tcx: &enrang_hir::Tcx, t: Ty) -> bool {
    match tcx.kind(t) {
        TyKind::Ref(_) => true,
        TyKind::Nullable(inner) => holds_ref(tcx, inner),
        TyKind::Tuple(parts) => tcx.list(parts).iter().any(|&p| holds_ref(tcx, p)),
        _ => false,
    }
}

/// EN0214 at a `readonly` before a result type, a name, that resolves to no type
/// a `readonly` may stand before: a reference, a tuple with a reference part or a
/// borrowing class, each maybe `| null` (S:253-257; the parser checks the written
/// types that are no names, `RR-05`).
fn readonly_result(sema: &mut Sema, ret: Ty, at: Span) {
    let tcx = &*sema.tcx;
    let mut t = ret;
    while let TyKind::Nullable(inner) = tcx.kind(t) {
        t = inner;
    }
    let takes = match tcx.kind(t) {
        TyKind::Ref(_) | TyKind::Error => true,
        TyKind::Tuple(_) => holds_ref(tcx, t),
        TyKind::Adt(adt, _) => tcx.adt(adt).is_class() && tcx.is_borrowing_class(adt),
        _ => false,
    };
    if takes || at.is_dummy() {
        return;
    }
    // The keyword: the last `readonly` before the type, on its line.
    let file = tcx.map().file_of(at.lo);
    let upto = (at.lo.0 - file.start.0) as usize;
    let Some(word) = file.text[..upto]
        .trim_end()
        .strip_suffix("readonly")
        .map(str::len)
    else {
        return;
    };
    let lo = enrang_base::BytePos(file.start.0 + word as u32);
    let keyword = Span {
        lo,
        hi: lo + "readonly".len() as u32,
    };
    let shown = tcx.ty_string(ret);
    let rest = upto - (word + "readonly".len());
    let delete = Span {
        lo,
        hi: keyword.hi + rest as u32,
    };
    sema.emit(
        Diagnostic::new(
            Code::EN0214,
            "`readonly` before a return type that holds no reference",
            keyword,
            format!("`{shown}` holds no reference for `readonly` to make read-only"),
        )
        .with_help(Help::machine(
            "remove `readonly`",
            vec![enrang_diag::Edit::delete(delete)],
        )),
    );
}

/// A constructor's parameters, each parameter property also as its field.
fn ctor(sema: &mut Sema, adt: AdtId, def: DefId, c: &ast::Constructor) {
    let Some(sig) = sema.tcx.sig_opt(def).cloned() else {
        return;
    };
    for (p, lowered) in c.params.iter().zip(&sig.params) {
        if p.property.is_some() {
            field(sema, adt, p.name.name, &p.ty, p.optional);
        } else {
            written(sema, lowered.ty, &p.ty, Pos::Param, p.optional);
        }
    }
}

/// The class field `name` that `adt` declares, written `t`.
fn field(sema: &mut Sema, adt: AdtId, name: Symbol, t: &ast::TypeExpr, optional: bool) {
    let found = sema.tcx.adt(adt).as_class().and_then(|class| {
        class
            .own_fields()
            .find(|(_, f)| f.name == name)
            .map(|(_, f)| (f.ty, f.vis, f.readonly))
    });
    if let Some((ty, vis, readonly)) = found {
        let pos = Pos::Field {
            vis,
            name,
            readonly,
        };
        written(sema, ty, t, pos, optional);
    }
}

/// Every enum case's fields, value positions.
fn payloads(sema: &mut Sema, adt: AdtId, decl: &ast::EnumDecl) {
    let Some(e) = sema.tcx.adt(adt).as_enum().cloned() else {
        return;
    };
    for (variant, ast_variant) in e.variants.iter().zip(&decl.variants) {
        let ast::VariantPayload::Fields(fields) = &ast_variant.payload else {
            continue;
        };
        for (f, ast_field) in variant.fields.iter().zip(fields) {
            written(sema, f.ty, &ast_field.ty, Pos::Payload, false);
        }
    }
}

/// A function's or method's own class bounds.
fn fn_bounds(sema: &mut Sema, def: DefId, type_params: &[ast::TypeParam]) {
    let Some(sig) = sema.tcx.sig_opt(def) else {
        return;
    };
    let params = sema.tcx.generics(sig.generics).params.clone();
    bounds(sema, &params, type_params);
}

/// A class's, enum's or interface's class bounds.
fn adt_bounds(sema: &mut Sema, adt: AdtId, type_params: &[ast::TypeParam]) {
    let params = sema.tcx.generics(sema.tcx.adt(adt).generics).params.clone();
    bounds(sema, &params, type_params);
}

/// EN0701 for a bound naming a borrowing class (S:764). The written parameters
/// come first in a generics list; the compiler's implicit ones follow.
fn bounds(sema: &mut Sema, params: &[ParamId], type_params: &[ast::TypeParam]) {
    let written: Vec<ParamId> = params
        .iter()
        .copied()
        .filter(|&p| sema.tcx.param(p).implicit.is_none())
        .collect();
    for (&p, tp) in written.iter().zip(type_params) {
        let lowered = sema.tcx.param(p).bounds.clone();
        if lowered.len() != tp.bounds.len() {
            continue;
        }
        for (&b, written_bound) in lowered.iter().zip(&tp.bounds) {
            borrowing_bound(sema, tp.name.name, b, written_bound.span);
        }
    }
}

/// EN0701 at `span` when bound `b` of parameter `name` is a borrowing class.
fn borrowing_bound(sema: &mut Sema, name: Symbol, b: enrang_hir::BoundId, span: Span) {
    let Bound::Class { adt, args } = sema.tcx.bound(b).clone() else {
        return;
    };
    let ty = sema.tcx.intern_ty(TyKind::Adt(adt, args));
    if !sema.tcx.is_borrowing(ty) {
        return;
    }
    let shown = sema.tcx.ty_string(ty);
    let mut diag = Diagnostic::new(
        Code::EN0701,
        format!(
            "`{name}` can't stand for {} `{shown}`, because `{shown}` holds a reference",
            article(&shown)
        ),
        span,
        borrow_label(sema, ty),
    )
    .rule(CLASS_RULE);
    if let Some(help) = own_help(sema, ty) {
        diag = diag.with_help(Help::text(help));
    }
    sema.emit(diag);
}

// ---------------------------------------------------------------------------------
// Bodies.

/// The positions of one body's written types and of its unannotated locals.
pub(crate) fn check_body(sema: &mut Sema, b: &Body) {
    let Some(ast_body) = sema.decls.body_ast(b.owner) else {
        return;
    };
    check_body_asts(sema, b, &[ast_body]);
}

/// [`check_body`] for a class's field initialisers, whose class-level body
/// (`BodyOwner::Const` of the class) has one written expression per initialiser,
/// `values`, and no entry of its own among the declarations' bodies.
pub(crate) fn check_field_inits(sema: &mut Sema, b: &Body, values: &[&ast::Expr]) {
    let asts: Vec<BodyAst<'_>> = values.iter().map(|&e| BodyAst::Const(e)).collect();
    check_body_asts(sema, b, &asts);
}

fn check_body_asts<'a>(sema: &mut Sema, b: &Body, asts: &[BodyAst<'a>]) {
    let module = match b.owner {
        enrang_hir::BodyOwner::Statements(m) => m,
        enrang_hir::BodyOwner::Fn(d)
        | enrang_hir::BodyOwner::Const(d)
        | enrang_hir::BodyOwner::Test(d) => sema.tcx.def(d).module,
    };
    if sema.tcx.module(module).library {
        return;
    }
    let locals: BTreeMap<Span, LocalId> = b
        .locals
        .iter_enumerated()
        .filter(|(_, l)| l.name.is_some())
        .map(|(id, l)| (l.span, id))
        .collect();
    let arrows: BTreeMap<Span, ArrowId> = b
        .arrows
        .iter_enumerated()
        .map(|(id, a)| (a.span, id))
        .collect();
    let mut casts: BTreeMap<Span, Ty> = BTreeMap::new();
    // Whether the outermost expression at a span only carries a type written
    // elsewhere (`copies_written`).
    let mut copies: BTreeMap<Span, bool> = BTreeMap::new();
    for_each_expr(b, &mut |e| {
        if let ExprKind::Cast(..) = e.kind {
            casts.entry(e.span).or_insert(e.ty);
        }
        copies
            .entry(e.span)
            .or_insert_with(|| copies_written(sema.tcx, e));
    });
    // The written types of the body, in source order, and the locals they annotate.
    let mut found: Vec<(Ty, &ast::TypeExpr, Pos)> = Vec::new();
    let mut annotated: BTreeSet<LocalId> = BTreeSet::new();
    // Unannotated locals whose initialiser copies a written type, which that
    // position checks: one report per mistake (A:1159).
    let mut copied: BTreeSet<LocalId> = BTreeSet::new();
    let mut new_types: Vec<(Span, Span)> = Vec::new();
    let mut visit = |node| match node {
        AstNode::VarDecl(d) => {
            if let (ast::Binding::Name(name), Some(t)) = (&d.binding, &d.ty)
                && let Some(&local) = locals.get(&name.span)
            {
                annotated.insert(local);
                found.push((b.locals[local].ty, t, Pos::Local));
            }
            if let (ast::Binding::Name(name), None, Some(init)) = (&d.binding, &d.ty, &d.init)
                && let Some(&local) = locals.get(&name.span)
                && copies.get(&init.span).copied().unwrap_or(false)
            {
                copied.insert(local);
            }
        }
        AstNode::Expr(e) => match &e.kind {
            ast::ExprKind::Cast(_, t) => {
                if let Some(&ty) = casts.get(&e.span) {
                    found.push((ty, t, Pos::Cast));
                }
            }
            // `new Keeper<string> {}`: a binding there is reported at the type.
            ast::ExprKind::New { ty, .. } => {
                if let ast::TypeExprKind::Named { args, .. } = &ty.kind
                    && !args.is_empty()
                {
                    new_types.push((e.span, ty.span));
                }
            }
            _ => {}
        },
        AstNode::Arrow(a) => {
            let Some(&id) = arrows.get(&a.span) else {
                return;
            };
            let arrow = &b.arrows[id];
            for (p, &local) in a.params.iter().zip(&arrow.params) {
                if let Some(t) = &p.ty {
                    annotated.insert(local);
                    found.push((b.locals[local].ty, t, Pos::Param));
                }
            }
            if let Some(r) = &a.ret {
                found.push((arrow.ret, &r.ty, Pos::Result));
            }
        }
    };
    for &ast_body in asts {
        walk_body_ast(ast_body, &mut visit);
    }
    sema.views.new_types.extend(new_types);
    for (ty, t, pos) in found {
        written(sema, ty, t, pos, false);
    }
    for (id, local) in b.locals.iter_enumerated() {
        let inferred = matches!(
            local.kind,
            LocalKind::User
                | LocalKind::TopVar(_)
                | LocalKind::ForBinding
                | LocalKind::PatBinding
                | LocalKind::Arrow(_)
        );
        if inferred && !annotated.contains(&id) && !copied.contains(&id) && local.name.is_some() {
            inferred_local(sema, local.ty, local.span);
        }
    }
}

/// A named local's annotation `t`, lowered to `ty`, checked as [`check_body`]
/// would check it, while typing the body: when a position rule rejects it, its
/// diagnostics are reported now and `true` comes back, so typing reads the local
/// as `Error` and nothing typed against the annotation reports the same mistake
/// again (`const b: Box<&i64> = new Box(n);` is EN0701 alone); [`check_body`]
/// then skips it, as it skips every type holding `Error`. Otherwise nothing is
/// kept, and [`check_body`] checks it at its turn.
pub(crate) fn rejects_local_annotation(sema: &mut Sema, ty: Ty, t: &ast::TypeExpr) -> bool {
    let mut scratch = enrang_diag::DiagCtx::new();
    std::mem::swap(&mut *sema.dcx, &mut scratch);
    let views = sema.views.written.len();
    written(sema, ty, t, Pos::Local, false);
    std::mem::swap(&mut *sema.dcx, &mut scratch);
    let rejected = scratch.has_errors();
    if rejected {
        for diag in scratch.take() {
            sema.emit(diag);
        }
    } else {
        sema.views.written.truncate(views);
    }
    rejected
}

/// A type written in a body outside any annotation, checked while typing: a static
/// path's type (`Stack<&i64>.empty()`), whose generic arguments are positions as
/// any written type's are (EN0701, EN0703, EN1006, EN0401 for a view; S:845,
/// S:560, S:606), or with `form`, the type of `sizeOf`, `alignOf` or `offsetOf`,
/// which must also have a size itself (an interface or a view at the top is EN1006
/// or EN0401). Whether it was rejected; library code is exempt.
pub(crate) fn rejects_body_type(sema: &mut Sema, ty: Ty, t: &ast::TypeExpr, form: bool) -> bool {
    if sema.tcx.references_error(ty) {
        return false;
    }
    let mut scratch = enrang_diag::DiagCtx::new();
    std::mem::swap(&mut *sema.dcx, &mut scratch);
    let pos = if form { Pos::Form } else { Pos::Cast };
    written(sema, ty, t, pos, false);
    std::mem::swap(&mut *sema.dcx, &mut scratch);
    let rejected = scratch.has_errors();
    for diag in scratch.take() {
        sema.emit(diag);
    }
    rejected
}

/// Whether `e` only carries a type written elsewhere, whose own position reports
/// it: a local, a static, a field, a cast (through `&`, `*`, a narrowed payload),
/// or a call whose declared result names no type parameter. A literal, a generic
/// call or a method of a generic class builds its type here.
fn copies_written(tcx: &enrang_hir::Tcx, e: &enrang_hir::Expr) -> bool {
    match &e.kind {
        ExprKind::Borrow(inner)
        | ExprKind::Deref(inner)
        | ExprKind::NarrowedPayload(inner, ..)
        | ExprKind::NonNull(inner) => copies_written(tcx, inner),
        ExprKind::Local(_) | ExprKind::Static(_) | ExprKind::Field(..) | ExprKind::Cast(..) => true,
        ExprKind::Call { callee, .. } => {
            let def = match callee {
                enrang_hir::Callee::Fn(f) | enrang_hir::Callee::Super(f) => f.def,
                enrang_hir::Callee::Foreign(def) => *def,
                _ => return false,
            };
            tcx.sig_opt(def).is_some_and(|sig| {
                !tcx.any_ty(sig.ret, &mut |tcx, t| {
                    matches!(tcx.kind(t), TyKind::Param(_))
                })
            })
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------------
// The checks.

/// `t` without its parentheses.
fn peel(t: &ast::TypeExpr) -> &ast::TypeExpr {
    match &t.kind {
        ast::TypeExprKind::Paren(inner) => peel(inner),
        _ => t,
    }
}

/// A type written as `t` at `pos`; `optional` for `x?: T`, whose type lowering made
/// `T | null`.
fn written(sema: &mut Sema, ty: Ty, t: &ast::TypeExpr, pos: Pos, optional: bool) {
    let t = peel(t);
    let ty = match sema.tcx.kind(ty) {
        TyKind::Nullable(inner)
            if optional && !matches!(t.kind, ast::TypeExprKind::Nullable(_)) =>
        {
            inner
        }
        _ => ty,
    };
    if sema.tcx.references_error(ty) {
        return;
    }
    if pos == Pos::Payload {
        if !value_pos(sema, &Container::Case, ty, Some(t), t.span) {
            two_word(sema, ty, Some(t), t.span, false);
        }
        return;
    }
    // A view or an interface at the top, `| null` included, is reported at the
    // whole written type, in its position's words.
    if top_value(sema, ty, t, pos)
        || inner(sema, ty, Some(t), t.span)
        || top_field(sema, ty, t.span, pos)
    {
        return;
    }
    two_word(sema, ty, Some(t), t.span, pos == Pos::Param);
}

/// EN1006 for a `Box<I>`, or an `&I` anywhere but at the top of a parameter, of an
/// interface whose table can't serve a member (4C's `two_word_need`; S:631, A:894,
/// T:1000, T:1007): at the first such part of a written type, top-down; whether it
/// reported.
fn two_word(sema: &mut Sema, ty: Ty, t: Option<&ast::TypeExpr>, span: Span, param: bool) -> bool {
    let tcx = &*sema.tcx;
    let span = t.map_or(span, |t| t.span);
    let exempt = param && matches!(tcx.kind(ty), TyKind::Ref(_));
    if !exempt && let Some((adt, member, need)) = two_word_need(tcx, ty) {
        let diag = iface_unsupported(
            span,
            format!("this `{}` needs its class's table", tcx.ty_string(ty)),
            need_note(tcx, adt, member, need),
            Some(format!(
                "use a type parameter `T extends {}`",
                tcx.adt(adt).name
            )),
        );
        sema.emit(diag);
        return true;
    }
    let kind = tcx.kind(ty);
    for (i, c) in tcx.children(ty).into_iter().enumerate() {
        if two_word(sema, c, child(t, kind, i), span, false) {
            return true;
        }
    }
    false
}

/// An unannotated local's inferred type, reported at its name.
/// An interface by value that typing gave a local, as `const d = b.unbox();`, is
/// EN1006 at the local's name when it is the local's whole type, itself or under
/// `| null` (T:862; typing reports it only where it meets a site of another type);
/// a type holding one deeper is not checked here.
fn inferred_local(sema: &mut Sema, ty: Ty, span: Span) {
    let tcx = &*sema.tcx;
    if tcx.references_error(ty) || tcx.has_infer(ty) {
        return;
    }
    if iface_by_value(tcx, ty) {
        if let Some(iface) = iface_of(sema, ty) {
            report_iface(sema, iface, span, Pos::Local.place(), None);
        }
        return;
    }
    // A view or `string` among an inferred type's arguments was bound where the
    // type was made (a call or a `new`, which 4A records), so it is not one more
    // written argument here.
    let written = sema.views.written.len();
    let reported = inner(sema, ty, None, span);
    sema.views.written.truncate(written);
    if reported {
        return;
    }
    if view_of(sema, ty).is_some() {
        report_view(sema, ty, span);
    }
}

/// Whether `t` holds an interface by value anywhere but behind `&` or in a `Box`.
fn iface_by_value(tcx: &enrang_hir::Tcx, t: Ty) -> bool {
    if tcx.is_interface_ty(t) {
        return true;
    }
    match tcx.kind(t) {
        TyKind::Ref(e) | TyKind::Boxed(e) if tcx.is_interface_ty(e) => false,
        TyKind::FnPtr(..) | TyKind::Closure(_) => false,
        _ => tcx.children(t).into_iter().any(|c| iface_by_value(tcx, c)),
    }
}

/// What `t` (written or not) gives for child `i` of a type of kind `kind`.
fn child<'t>(t: Option<&'t ast::TypeExpr>, kind: TyKind, i: usize) -> Option<&'t ast::TypeExpr> {
    let t = peel(t?);
    match (kind, &t.kind) {
        (TyKind::Array(_), ast::TypeExprKind::Array(inner))
        | (TyKind::Fixed(..), ast::TypeExprKind::Fixed(inner, _))
        | (TyKind::Nullable(_), ast::TypeExprKind::Nullable(inner))
        | (TyKind::Raw(_), ast::TypeExprKind::Raw(inner))
        | (TyKind::Ref(_), ast::TypeExprKind::Ref(inner) | ast::TypeExprKind::ReadonlyRef(inner)) => {
            Some(inner)
        }
        (TyKind::Tuple(_), ast::TypeExprKind::Tuple(parts)) => parts.get(i),
        (
            TyKind::Slice(_) | TyKind::Boxed(_) | TyKind::Adt(..),
            ast::TypeExprKind::Named { args, .. },
        ) => args.get(i),
        _ => None,
    }
}

/// The written field `name` of an object type.
fn object_field<'t>(t: Option<&'t ast::TypeExpr>, name: Symbol) -> Option<&'t ast::TypeExpr> {
    match &peel(t?).kind {
        ast::TypeExprKind::Object(fields) => fields
            .iter()
            .find(|(n, _, _)| n.name == name)
            .map(|(_, _, ty)| ty),
        _ => None,
    }
}

/// The value positions inside `ty`, top-down: whether one reported.
fn inner(sema: &mut Sema, ty: Ty, t: Option<&ast::TypeExpr>, span: Span) -> bool {
    let tcx = &*sema.tcx;
    let kind = tcx.kind(ty);
    let span = t.map_or(span, |t| t.span);
    match kind {
        TyKind::Array(e) | TyKind::Fixed(e, _) => {
            value_pos(sema, &Container::Array, e, child(t, kind, 0), span)
        }
        TyKind::Slice(e) => value_pos(
            sema,
            &Container::Named("Slice".to_owned()),
            e,
            child(t, kind, 0),
            span,
        ),
        TyKind::Boxed(e) => {
            if tcx.is_interface_ty(e) {
                return false;
            }
            value_pos(
                sema,
                &Container::Named("Box".to_owned()),
                e,
                child(t, kind, 0),
                span,
            )
        }
        TyKind::Adt(adt, args) => {
            let name = tcx.adt(adt).name.as_str().to_owned();
            let params = tcx.generics(tcx.adt(adt).generics).params.clone();
            let args = tcx.list(args);
            let container = Container::Named(name);
            // `Result<T, Error>` is lowering's EN1006 (its `E` is then `Error`).
            for (i, &a) in args.iter().enumerate() {
                let at = child(t, kind, i);
                // A view or `string` for a type parameter waits for its facts.
                if let (TyKind::Slice(_) | TyKind::Str, Some(&param)) =
                    (sema.tcx.kind(a), params.get(i))
                {
                    // A view is reported where it is written, a `string` at the
                    // instance (`Keeper<string>`, T:1048).
                    let at_span = match sema.tcx.kind(a) {
                        TyKind::Slice(_) => at.map_or(span, |a| a.span),
                        _ => span,
                    };
                    sema.views.written.push(WrittenArg {
                        span: at_span,
                        param,
                        arg: a,
                    });
                    continue;
                }
                if value_pos(sema, &container, a, at, span) {
                    return true;
                }
            }
            false
        }
        TyKind::Tuple(parts) => {
            let parts = tcx.list(parts);
            for (i, &p) in parts.iter().enumerate() {
                if part(sema, p, child(t, kind, i), span, "a tuple part") {
                    return true;
                }
            }
            false
        }
        TyKind::Nullable(e) => part(sema, e, child(t, kind, 0), span, "a nullable"),
        TyKind::Ref(e) => {
            let at = child(t, kind, 0);
            inner(sema, e, at, at.map_or(span, |a| a.span))
        }
        TyKind::Raw(e) => {
            let at = child(t, kind, 0);
            let at_span = at.map_or(span, |a| a.span);
            if view_of(sema, e).is_some() {
                report_view(sema, e, at_span);
                return true;
            }
            inner(sema, e, at, at_span)
        }
        TyKind::Object(shape) => {
            let fields = tcx.shape(shape).fields.clone();
            for (name, f) in fields {
                if value_pos(sema, &Container::Object, f, object_field(t, name), span) {
                    return true;
                }
            }
            false
        }
        // An object-type parameter is an implicit parameter bounded by its shape
        // (A:892), whose fields are written as an object type's.
        TyKind::Param(p) => match tcx.param(p).implicit {
            Some(Implicit::Shape(shape)) => {
                let fields = tcx.shape(shape).fields.clone();
                for (name, f) in fields {
                    if value_pos(sema, &Container::Object, f, object_field(t, name), span) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        },
        TyKind::Bool
        | TyKind::Int(_)
        | TyKind::Float(_)
        | TyKind::Void
        | TyKind::Never
        | TyKind::Str
        | TyKind::FnPtr(..)
        | TyKind::Closure(_)
        | TyKind::Infer(_)
        | TyKind::Error => false,
    }
}

/// A tuple part or the inside of a nullable, which may hold a reference or a
/// borrowing value but no view or interface by value.
fn part(sema: &mut Sema, p: Ty, t: Option<&ast::TypeExpr>, holder: Span, place: &str) -> bool {
    let span = t.map_or(holder, |t| t.span);
    if view_of(sema, p).is_some() {
        report_view(sema, p, span);
        return true;
    }
    if sema.tcx.is_interface_ty(p) {
        report_iface(sema, p, span, place, None);
        return true;
    }
    inner(sema, p, t, span)
}

/// The view `Slice<U>` that `t` is by value, itself or under `| null`.
fn view_of(sema: &Sema, t: Ty) -> Option<Ty> {
    match sema.tcx.kind(t) {
        TyKind::Slice(_) => Some(t),
        TyKind::Nullable(inner) => match sema.tcx.kind(inner) {
            TyKind::Slice(_) => Some(inner),
            _ => None,
        },
        _ => None,
    }
}

/// The interface type `t` is by value, itself or under `| null`.
fn iface_of(sema: &Sema, t: Ty) -> Option<Ty> {
    let tcx = &*sema.tcx;
    if tcx.is_interface_ty(t) {
        return Some(t);
    }
    match tcx.kind(t) {
        TyKind::Nullable(inner) if tcx.is_interface_ty(inner) => Some(inner),
        _ => None,
    }
}

/// Why a value position cannot hold `e`.
enum Offender {
    Ref,
    Class,
    Tuple,
    /// Something deeper inside `e` that no constructor of it holds directly.
    Deeper,
}

/// A value position of `container` holding `e`, written `t` (or nothing): whether
/// it reported. EN0701 points at the holder, the view and interface codes at `e`.
fn value_pos(
    sema: &mut Sema,
    container: &Container,
    e: Ty,
    t: Option<&ast::TypeExpr>,
    holder: Span,
) -> bool {
    let tcx = &*sema.tcx;
    if tcx.references_error(e) {
        return false;
    }
    let e_span = t.map_or(holder, |t| t.span);
    if view_of(sema, e).is_some() {
        report_view(sema, e, e_span);
        return true;
    }
    if let Some(iface) = iface_of(sema, e) {
        report_iface(sema, iface, e_span, &container.place(), None);
        return true;
    }
    let bare = match tcx.kind(e) {
        TyKind::Nullable(inner) => inner,
        _ => e,
    };
    let offender = match tcx.kind(bare) {
        TyKind::Ref(_) => Some(Offender::Ref),
        TyKind::Closure(_) => return false,
        TyKind::Adt(..) if tcx.is_borrowing(bare) => Some(Offender::Class),
        TyKind::Tuple(_) if tcx.is_borrowing(bare) => Some(Offender::Tuple),
        _ => None,
    };
    if let Some(offender) = offender {
        report_held(sema, container, e, bare, offender, holder);
        return true;
    }
    if tcx.is_value_type(e) {
        return false;
    }
    if inner(sema, e, t, e_span) {
        return true;
    }
    report_held(sema, container, e, bare, Offender::Deeper, holder);
    true
}

/// EN0701: `container` can't hold `e` (`bare` without its `| null`).
fn report_held(
    sema: &mut Sema,
    container: &Container,
    e: Ty,
    bare: Ty,
    offender: Offender,
    holder: Span,
) {
    let shown = sema.tcx.ty_string(e);
    let noun = container.noun();
    let (message, label, rule) = match offender {
        Offender::Ref => (
            format!(
                "{noun} can't hold {} `{shown}`, because `{shown}` is a reference",
                article(&shown)
            ),
            "a reference".to_owned(),
            REF_RULE,
        ),
        Offender::Class => {
            let class = sema.tcx.ty_string(bare);
            (
                format!(
                    "{noun} can't hold {} `{shown}`, because `{class}` holds a reference",
                    article(&shown)
                ),
                borrow_label(sema, bare),
                CLASS_RULE,
            )
        }
        Offender::Tuple => (
            format!(
                "{noun} can't hold {} `{shown}`, because `{shown}` holds a reference",
                article(&shown)
            ),
            "a tuple with a reference part".to_owned(),
            TUPLE_RULE,
        ),
        Offender::Deeper => (
            format!(
                "{noun} can't hold {} `{shown}`, because `{shown}` holds a reference",
                article(&shown)
            ),
            "this holds a reference".to_owned(),
            REF_RULE,
        ),
    };
    let mut diag = Diagnostic::new(Code::EN0701, message, holder, label).rule(rule);
    if let Some(help) = own_help(sema, bare) {
        diag = diag.with_help(Help::text(help));
    }
    sema.emit(diag);
}

/// The first field of the borrowing class `ty` outside `V`, with its type.
fn ref_field(sema: &Sema, ty: Ty) -> Option<(Symbol, Ty, Vis)> {
    let tcx = &*sema.tcx;
    let TyKind::Adt(adt, args) = tcx.kind(ty) else {
        return None;
    };
    let class = tcx.adt(adt).as_class()?;
    let tys = tcx.adt_field_tys(adt, args);
    class
        .fields
        .iter()
        .zip(tys)
        .find(|(_, t)| !tcx.is_value_type(*t))
        .map(|(f, t)| (f.name, t, f.vis))
}

/// `` `Lexer` borrows through its field `src` `` (G19).
fn borrow_label(sema: &Sema, ty: Ty) -> String {
    let shown = sema.tcx.ty_string(ty);
    match ref_field(sema, ty) {
        Some((name, _, _)) => format!("`{shown}` borrows through its field `{name}`"),
        None => format!("`{shown}` holds a reference"),
    }
}

/// `` own the data: `private src: string;` ``, from a borrowing class's reference
/// field: the field with the owned type of what it refers to (an array for a view,
/// a `Box` for an interface); none when the field holds no plain reference.
fn own_help(sema: &Sema, ty: Ty) -> Option<String> {
    let (name, fty, vis) = ref_field(sema, ty)?;
    let tcx = &*sema.tcx;
    let owned = |pointee: Ty| -> Option<Ty> {
        match tcx.kind(pointee) {
            TyKind::Slice(e) => Some(tcx.mk_array(e)),
            _ if tcx.is_interface_ty(pointee) => Some(tcx.mk_box(pointee)),
            _ if tcx.is_value_type(pointee) => Some(pointee),
            _ => None,
        }
    };
    let owned = match tcx.kind(fty) {
        TyKind::Ref(p) => owned(p)?,
        TyKind::Nullable(n) => match tcx.kind(n) {
            TyKind::Ref(p) => tcx.mk_nullable(owned(p)?),
            _ => return None,
        },
        _ => return None,
    };
    let vis = match vis {
        Vis::Public => "public",
        Vis::Private => "private",
        Vis::Protected => "protected",
    };
    Some(format!(
        "own the data: `{vis} {name}: {};`",
        tcx.ty_string(owned)
    ))
}

/// EN0401 for the view `t` (or `t | null`) by value at `span` (S:606).
pub(crate) fn report_view(sema: &mut Sema, t: Ty, span: Span) {
    let Some(view) = view_of(sema, t) else {
        return;
    };
    let TyKind::Slice(elem) = sema.tcx.kind(view) else {
        return;
    };
    let shown = sema.tcx.ty_string(view);
    let array = sema.tcx.ty_string(sema.tcx.mk_array(elem));
    sema.emit(
        Diagnostic::new(
            Code::EN0401,
            format!("`{shown}` is a view, so it exists only behind `&`"),
            span,
            "a view by value",
        )
        .with_help(Help::text(format!(
            "write `&{shown}`, or `{array}` for an array of its own"
        ))),
    );
}

/// EN1006 for the interface `iface` by value in `place`, with SPEC 16's head, a
/// note naming the case and the row's help, or `help` in its place (S:631, S:3458).
pub(crate) fn report_iface(
    sema: &mut Sema,
    iface: Ty,
    span: Span,
    place: &str,
    help: Option<String>,
) {
    let shown = sema.tcx.ty_string(iface);
    let help =
        help.unwrap_or_else(|| format!("`&{shown}` to refer to one, `Box<{shown}>` to own one"));
    sema.emit(
        Diagnostic::new(
            Code::EN1006,
            "an interface type by value outside a parameter is not supported yet",
            span,
            format!("`{shown}` by value in {place}"),
        )
        .note(format!(
            "`{shown}` is an interface, so the size of {} in {place} isn't known",
            crate::classes::sig::a_ty(&shown)
        ))
        .with_help(Help::text(help)),
    );
}

/// Whether a field of type `t` is a reference field: a reference, a borrowing
/// tuple, or one of them `| null` (S:590, S:846).
fn is_ref_field(sema: &Sema, t: Ty) -> bool {
    let tcx = &*sema.tcx;
    match tcx.kind(t) {
        TyKind::Ref(_) => true,
        TyKind::Nullable(inner) => is_ref_field(sema, inner),
        TyKind::Tuple(_) => tcx.is_borrowing(t),
        _ => false,
    }
}

/// What may stand at the top of `pos`, itself or under `| null`, written `t`: no
/// view by value, and no interface by value outside a parameter, reported at the
/// type without its `| null`. A cast's target is checked inside only.
fn top_value(sema: &mut Sema, ty: Ty, t: &ast::TypeExpr, pos: Pos) -> bool {
    if pos == Pos::Cast {
        return false;
    }
    let (bare, span) = match sema.tcx.kind(ty) {
        TyKind::Nullable(inner) => (
            inner,
            child(Some(t), sema.tcx.kind(ty), 0).map_or(t.span, |c| c.span),
        ),
        _ => (ty, t.span),
    };
    if view_of(sema, bare).is_some() {
        report_view(sema, bare, span);
        return true;
    }
    if pos == Pos::Param || iface_of(sema, bare).is_none() {
        return false;
    }
    report_iface(sema, bare, span, pos.place(), None);
    true
}

/// A reference field only `private`.
fn top_field(sema: &mut Sema, ty: Ty, span: Span, pos: Pos) -> bool {
    if let Pos::Field {
        vis,
        name,
        readonly,
    } = pos
        && vis != Vis::Private
        && is_ref_field(sema, ty)
    {
        let readonly = if readonly { "readonly " } else { "" };
        let vis = match vis {
            Vis::Public => "public",
            Vis::Protected => "protected",
            Vis::Private => "private",
        };
        let written = sema.tcx.map().text(span).to_owned();
        sema.emit(
            Diagnostic::new(
                Code::EN0701,
                format!("`{name}` holds a reference, so it must be `private`"),
                span,
                format!("a reference in a `{vis}` field"),
            )
            .rule("a reference field is seen only inside its class, so the class can keep track of what it borrows.")
            .with_help(Help::text(format!(
                "make it `private`: `private {readonly}{name}: {written};`"
            ))),
        );
        return true;
    }
    false
}
