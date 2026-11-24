//! Decorators (SPEC 3.1's table, S:325-347): read into `Attrs`, then checked.
//! Arguments are literals, identifiers or object literals of literals (S:235), read
//! without typing.
//!
//! The checks ([`check`]), each EN0806 unless named: an unknown decorator; one on a
//! target the table does not give it (`@naked` and `@bits` need an `unsafe
//! function`); one written twice; arguments of the wrong shape (an unknown
//! `@intrinsic`, `@lang` or `@requires` name included, plan choice); the
//! library-only forms in user code, `@lang`, `@intrinsic`, `@hostCall`, `@owner`, a
//! method without a body that is not `abstract` (S:348; plan choice: the library may
//! leave any method bodyless, A:2014), with `@hostCall` kept to `os/vm` and `@owner`
//! to `alloc`; a decorator that makes the compiler, a runtime or foreign code the
//! caller (`@entry`, `@panicHandler`, `@interrupt`, `@naked`, `@abi`, `@devMigrate`)
//! on a local function with hidden arguments (S:981); `@devMigrate` on a function
//! with no object-typed parameter. Then: an `@abi` name other than `win64` and
//! `sysv` is EN0819, `cdecl` and `stdcall` EN1030 (S:1358); an `@interrupt`
//! signature other than `(&InterruptFrame[, usize]) => void | never` EN0808
//! (S:1324); a `@section` name a hosted target refuses, or `.bss.stack`, EN0814
//! (S:1330); a `declare function` without `@dll`, `@intrinsic` or `@hostCall` EN0815
//! (S:352, S:1359), and one passing anything but a scalar, a raw pointer or an `fn`
//! pointer EN0816, a class or another aggregate by value EN1030 (S:1357-1360); conflicting layout attributes EN0817 (S:1290:
//! `@packed` with `@align` or `@repr`, or one written twice); a layout decorator on
//! a class that is not `final`, that extends a class, or that holds inline a class
//! carrying a hidden pointer, directly or through other classes and enum cases,
//! EN0827 (S:1291); a `@packed` field that is not Copy or
//! is generic EN0826 (S:1289).

use std::collections::{BTreeMap, BTreeSet};

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Edit, Help, did_you_mean};
use enrang_hir::{
    Abi, AdtId, AdtKind, Attrs, ClassModifier, DefId, Implicit, IntrinsicName, LangItem, ParamEnv,
    Repr, Tcx, Ty, TyKind,
};
use enrang_syntax::ast;
use enrang_target::{Feature, FeatureSet, OsLayer};

use crate::cx::Sema;
use crate::lower::ItemAstKind;
use crate::lower::types::ffi_check;
use crate::resolve::{suggest, toplevel};

/// The attributes `decorators` give a definition.
pub(crate) fn read(tcx: &mut Tcx, decorators: &[ast::Decorator]) -> Attrs {
    let mut attrs = Attrs::default();
    for d in decorators {
        let args: &[ast::Expr] = d.args.as_deref().unwrap_or(&[]);
        let text = args.first().and_then(str_arg);
        let int = args.first().and_then(int_arg);
        match d.name.name.as_str() {
            "mustUse" => attrs.must_use = true,
            "requires" => {
                for arg in args {
                    if let Some(feature) = str_arg(arg).and_then(|s| Feature::from_name(&s)) {
                        attrs.requires = attrs.requires.union(FeatureSet::of(&[feature]));
                    }
                }
            }
            "section" => attrs.section = text.map(|s| enrang_base::intern(&s)),
            "at" => attrs.at = int.and_then(|v| u64::try_from(v).ok()),
            "abi" => {
                attrs.abi = match text.as_deref() {
                    Some("win64") => Some(Abi::Win64),
                    Some("sysv") => Some(Abi::Sysv),
                    _ => None,
                }
            }
            "dll" => attrs.dll = text.map(|s| enrang_base::intern(&s)),
            "intrinsic" => attrs.intrinsic = text.and_then(|s| IntrinsicName::from_name(&s)),
            "hostCall" => {
                attrs.host_call = text.map(|s| tcx.intern_host_call(enrang_base::intern(&s)))
            }
            "lang" => attrs.lang = text.and_then(|s| LangItem::from_name(&s)),
            "packed" => attrs.packed = true,
            "repr" => attrs.repr = text.and_then(|s| Repr::from_name(&s)),
            "align" => attrs.align = int.and_then(|v| u32::try_from(v).ok()),
            "entry" => attrs.entry = true,
            "panicHandler" => attrs.panic_handler = true,
            "interrupt" => attrs.interrupt = Some(args.first().is_some_and(error_code)),
            "naked" => attrs.naked = true,
            "bits" => attrs.bits = int.and_then(|v| u8::try_from(v).ok()),
            "globalAllocator" => attrs.global_allocator = true,
            "was" => attrs.was = text.map(|s| enrang_base::intern(&s)),
            "devMigrate" => attrs.dev_migrate = true,
            "owner" => attrs.owner = true,
            _ => {}
        }
    }
    attrs
}

fn str_arg(e: &ast::Expr) -> Option<String> {
    match &e.kind {
        ast::ExprKind::Str(s) => Some(s.as_str().to_owned()),
        ast::ExprKind::Paren(inner) => str_arg(inner),
        _ => None,
    }
}

fn int_arg(e: &ast::Expr) -> Option<u128> {
    match &e.kind {
        ast::ExprKind::Int { value, .. } => Some(*value),
        ast::ExprKind::Paren(inner) => int_arg(inner),
        _ => None,
    }
}

/// `{ errorCode: true }`.
fn error_code(e: &ast::Expr) -> bool {
    let ast::ExprKind::ObjectLit(fields) = &e.kind else {
        return false;
    };
    fields.iter().any(|f| {
        f.name.name.as_str() == "errorCode"
            && matches!(
                f.value.as_ref().map(|v| &v.kind),
                Some(ast::ExprKind::Bool(true))
            )
    })
}

/// Every decorator the table of SPEC 3.1 allows.
const DECORATORS: [&str; 21] = [
    "entry",
    "panicHandler",
    "globalAllocator",
    "interrupt",
    "naked",
    "bits",
    "requires",
    "mustUse",
    "section",
    "at",
    "packed",
    "repr",
    "align",
    "dll",
    "abi",
    "lang",
    "intrinsic",
    "hostCall",
    "was",
    "devMigrate",
    "owner",
];

/// What a decorator is written on.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Target {
    /// A `function`, or a local function among the statements.
    Function {
        is_unsafe: bool,
        local: Option<DefId>,
    },
    Declare,
    Method {
        bodyless: bool,
    },
    Constructor,
    Destructor,
    Field,
    Class,
    Enum,
    Interface,
    Alias,
    Const,
    Static,
    Variant,
    Extend,
    Test,
    Assert,
    FnType,
}

impl Target {
    fn name(self) -> &'static str {
        match self {
            Target::Function { .. } => "a function",
            Target::Declare => "a `declare function`",
            Target::Method { .. } => "a method",
            Target::Constructor => "a constructor",
            Target::Destructor => "a destructor",
            Target::Field => "a field",
            Target::Class => "a class",
            Target::Enum => "an enum",
            Target::Interface => "an interface",
            Target::Alias => "a type alias",
            Target::Const => "a constant",
            Target::Static => "an `unsafe let`",
            Target::Variant => "an enum case",
            Target::Extend => "an `extend` block",
            Target::Test => "a test",
            Target::Assert => "an `assert`",
            Target::FnType => "a function type",
        }
    }
}

/// Whether decorator `name` may stand on `target`, and what it goes on.
fn allowed(name: &str, target: Target) -> (bool, &'static str) {
    use Target as T;
    let function = matches!(target, T::Function { .. });
    match name {
        "entry" | "panicHandler" | "interrupt" => (function, "a function"),
        "globalAllocator" | "at" => (target == T::Static, "an `unsafe let`"),
        "naked" | "bits" => (function, "an `unsafe function`"),
        "requires" | "mustUse" => (
            function || matches!(target, T::Declare | T::Method { .. }),
            "a function or a method",
        ),
        "section" => (
            function || matches!(target, T::Static | T::Const),
            "a function, an `unsafe let` or a constant",
        ),
        "packed" | "repr" => (matches!(target, T::Class | T::Enum), "a class or an enum"),
        "align" => (
            matches!(target, T::Class | T::Enum | T::Static),
            "a class, an enum or an `unsafe let`",
        ),
        "dll" | "hostCall" => (target == T::Declare, "a `declare function`"),
        "abi" => (
            function || target == T::FnType,
            "a function or a function type",
        ),
        "intrinsic" => (
            matches!(target, T::Declare | T::Method { bodyless: true }),
            "a `declare function` or a member without a body",
        ),
        "was" => (
            function || matches!(target, T::Class | T::Enum | T::Field | T::Variant),
            "a class, an enum, a field, an enum case or a function",
        ),
        "devMigrate" => (function, "a function with an object-typed parameter"),
        _ => (true, ""),
    }
}

/// Where a list of decorators stands.
#[derive(Copy, Clone)]
struct Site {
    target: Target,
    /// The library module's path; `None` in user code.
    library: Option<&'static str>,
}

fn layer_is(library: Option<&str>, layer: &str) -> bool {
    library.is_some_and(|p| p == layer || p.starts_with(&format!("{layer}/")))
}

/// The ABI of a function type, after checking its decorators (`@abi` alone).
pub(crate) fn fn_type_abi(sema: &mut Sema, decorators: &[ast::Decorator]) -> Abi {
    // A library function type is written by the library: its decorators are read,
    // and checked like any other.
    check_site(
        sema,
        decorators,
        Site {
            target: Target::FnType,
            library: None,
        },
    );
    read(sema.tcx, decorators).abi.unwrap_or(Abi::Enrang)
}

/// Checks the decorators of every declaration, and the declarations whose rules the
/// decorators decide (EN0808, EN0815-EN0817, EN0826, EN0827).
pub(crate) fn check(sema: &mut Sema) {
    let program = sema.program;
    let kinds: BTreeMap<DefId, ItemAstKind> = sema
        .decls
        .items
        .iter()
        .map(|i| (i.def, i.kind.clone()))
        .collect();
    for module in &program.modules {
        let library = module.library.then_some(module.path.as_str());
        for stmt in &module.ast.stmts {
            if let ast::StmtKind::LocalFn { decorators, decl } = &stmt.kind {
                let def = sema.res.item_defs.get(&stmt.id).copied();
                let site = Site {
                    target: Target::Function {
                        is_unsafe: decl.is_unsafe,
                        local: def,
                    },
                    library,
                };
                check_site(sema, decorators, site);
                if let Some(def) = def {
                    check_function(sema, decorators, decl, def);
                }
            }
        }
        let parts =
            std::iter::once(&module.ast.items).chain(module.test_part.iter().map(|p| &p.ast.items));
        for items in parts {
            for item in items {
                check_item(sema, item, library, &kinds);
            }
        }
    }
}

fn check_item(
    sema: &mut Sema,
    item: &ast::Item,
    library: Option<&'static str>,
    kinds: &BTreeMap<DefId, ItemAstKind>,
) {
    let def = sema.res.item_defs.get(&item.id).copied();
    let target = match &item.kind {
        ast::ItemKind::Function(f) => Target::Function {
            is_unsafe: f.is_unsafe,
            local: None,
        },
        ast::ItemKind::Class(_) => Target::Class,
        ast::ItemKind::Enum(_) => Target::Enum,
        ast::ItemKind::Interface(i) => {
            if i.members
                .iter()
                .all(|m| matches!(m, ast::IfaceMember::Field(_)))
                && !i.members.is_empty()
            {
                Target::Alias
            } else {
                Target::Interface
            }
        }
        ast::ItemKind::TypeAlias(_) => Target::Alias,
        ast::ItemKind::TopConst(_) => Target::Const,
        ast::ItemKind::UnsafeLet(_) => Target::Static,
        ast::ItemKind::DeclareFn(_) => Target::Declare,
        ast::ItemKind::Extend(_) => Target::Extend,
        ast::ItemKind::StaticAssert { .. } => Target::Assert,
        ast::ItemKind::Describe(d) => {
            check_site(
                sema,
                &item.decorators,
                Site {
                    target: Target::Test,
                    library,
                },
            );
            for inner in &d.items {
                check_item(sema, inner, library, kinds);
            }
            return;
        }
        ast::ItemKind::Test(_) | ast::ItemKind::CompileCase(_) => Target::Test,
    };
    check_site(sema, &item.decorators, Site { target, library });
    let Some(def) = def else { return };
    match &item.kind {
        ast::ItemKind::Function(f) => check_function(sema, &item.decorators, f, def),
        ast::ItemKind::DeclareFn(d) => check_declare(sema, &item.decorators, d, def),
        ast::ItemKind::Class(c) => {
            let Some(ItemAstKind::Class(adt, _, _)) = kinds.get(&def) else {
                return;
            };
            for member in &c.members {
                let target = match &member.kind {
                    ast::ClassMemberKind::Field(_) => Target::Field,
                    ast::ClassMemberKind::Constructor(_) => Target::Constructor,
                    ast::ClassMemberKind::Destructor(_) => Target::Destructor,
                    ast::ClassMemberKind::Method(m) => Target::Method {
                        bodyless: m.body.is_none(),
                    },
                };
                check_site(sema, &member.decorators, Site { target, library });
                if let ast::ClassMemberKind::Method(m) = &member.kind {
                    bodyless_method(sema, m, library, true);
                }
            }
            check_layout(sema, &item.decorators, Some((*adt, c)));
        }
        ast::ItemKind::Enum(e) => {
            for v in &e.variants {
                check_site(
                    sema,
                    &v.decorators,
                    Site {
                        target: Target::Variant,
                        library,
                    },
                );
            }
            for m in &e.methods {
                bodyless_method(sema, m, library, false);
            }
            check_layout(sema, &item.decorators, None);
        }
        ast::ItemKind::UnsafeLet(_) => check_layout(sema, &item.decorators, None),
        ast::ItemKind::Extend(x) => {
            for member in &x.members {
                check_site(
                    sema,
                    &member.decorators,
                    Site {
                        target: Target::Method {
                            bodyless: member.method.body.is_none(),
                        },
                        library,
                    },
                );
            }
        }
        _ => {}
    }
}

/// A method written with `;` in user code that is not `abstract` (S:348).
fn bodyless_method(sema: &mut Sema, m: &ast::MethodDecl, library: Option<&str>, class: bool) {
    if library.is_some() || m.body.is_some() || m.is_abstract {
        return;
    }
    let label = if class {
        "write its body, or make it `abstract`"
    } else {
        "write its body"
    };
    sema.err(
        Code::EN0806,
        "a method without a body is a library-only form",
        m.name.span,
        label,
    );
}

/// Checks one list of decorators at `site`.
fn check_site(sema: &mut Sema, decorators: &[ast::Decorator], site: Site) {
    let mut seen: Vec<&ast::Decorator> = Vec::new();
    for d in decorators {
        let name = d.name.name.as_str();
        if !DECORATORS.contains(&name) {
            let mut diag = Diagnostic::new(
                Code::EN0806,
                format!("unknown decorator `@{name}`"),
                d.span,
                "not a decorator",
            );
            if let Some(found) = did_you_mean(name, &DECORATORS) {
                diag = diag.with_help(Help::machine(
                    format!("did you mean `@{found}`?"),
                    vec![Edit::replace(d.name.span, found)],
                ));
            }
            sema.emit(diag);
            continue;
        }
        let layout = matches!(name, "packed" | "repr" | "align");
        if let Some(first) = seen.iter().find(|s| s.name.name == d.name.name) {
            if !layout {
                sema.emit(
                    Diagnostic::new(
                        Code::EN0806,
                        format!("`@{name}` is written twice"),
                        d.span,
                        "written again here",
                    )
                    .with_secondary(first.span, "the first is here"),
                );
            }
            continue;
        }
        seen.push(d);
        if site.library.is_none() && matches!(name, "lang" | "intrinsic" | "hostCall" | "owner") {
            sema.err(
                Code::EN0806,
                format!("`@{name}` is a library-only form"),
                d.span,
                "only `core`, `alloc` and `os` may use it",
            );
            continue;
        }
        if name == "hostCall" && !layer_is(site.library, "os/vm") {
            sema.err(
                Code::EN0806,
                "`@hostCall` can be used only in `os/vm`",
                d.span,
                "a host call exists only on the VM",
            );
            continue;
        }
        if name == "owner" && !layer_is(site.library, "alloc") {
            sema.err(
                Code::EN0806,
                "`@owner` can be used only in `alloc`",
                d.span,
                "outside `alloc`",
            );
            continue;
        }
        let (ok, goes_on) = allowed(name, site.target);
        if !ok {
            sema.err(
                Code::EN0806,
                format!("`@{name}` can't be used on {}", site.target.name()),
                d.span,
                format!("`@{name}` goes on {goes_on}"),
            );
            continue;
        }
        if matches!(name, "naked" | "bits")
            && let Target::Function {
                is_unsafe: false, ..
            } = site.target
        {
            sema.err(
                Code::EN0806,
                format!("`@{name}` can be used only on an `unsafe function`"),
                d.span,
                "this function is not `unsafe`",
            );
            continue;
        }
        if !check_args(sema, d, site) {
            continue;
        }
        if matches!(
            name,
            "entry" | "panicHandler" | "interrupt" | "naked" | "abi" | "devMigrate"
        ) && let Target::Function { local: Some(f), .. } = site.target
        {
            hidden_caller(sema, d, f);
        }
    }
}

/// EN0806: a decorator that makes the compiler, a runtime or foreign code the
/// caller, on a local function with hidden arguments (S:981).
fn hidden_caller(sema: &mut Sema, d: &ast::Decorator, f: DefId) {
    let Some(&first) = toplevel::hidden_args(sema, f).first() else {
        return;
    };
    let var = sema.res.toplevel.vars[first.0 as usize].name;
    let data = sema.tcx.def(f);
    let fname = data.name().map(|n| n.as_str()).unwrap_or("_");
    let name_span = data.name_span;
    sema.emit(
        Diagnostic::new(
            Code::EN0806,
            format!(
                "`@{}` can't be used on a function that uses top-level variables",
                d.name.name
            ),
            d.span,
            "the compiler, a runtime or foreign code calls it, and nothing supplies its hidden arguments",
        )
        .with_secondary(
            name_span,
            format!("`{fname}` uses `{var}`, a top-level variable"),
        ),
    );
}

/// The arguments of `d`; reports a wrong shape and returns `false`.
fn check_args(sema: &mut Sema, d: &ast::Decorator, site: Site) -> bool {
    let name = d.name.name.as_str();
    let args: &[ast::Expr] = d.args.as_deref().unwrap_or(&[]);
    let bad = |sema: &mut Sema, msg: &str, span: Span, label: &str| {
        sema.err(Code::EN0806, msg.to_owned(), span, label.to_owned());
        false
    };
    let one_str = |args: &[ast::Expr]| match args {
        [a] => str_arg(a).map(|s| (s, a.span)),
        _ => None,
    };
    let one_int = |args: &[ast::Expr]| match args {
        [a] => int_arg(a).map(|v| (v, a.span)),
        _ => None,
    };
    match name {
        "entry" | "panicHandler" | "globalAllocator" | "naked" | "mustUse" | "packed"
        | "devMigrate" | "owner" => {
            if args.is_empty() {
                true
            } else {
                bad(
                    sema,
                    &format!("`@{name}` takes no arguments"),
                    d.span,
                    "remove the arguments",
                )
            }
        }
        "interrupt" => match args {
            [] => true,
            [a] if is_error_code_literal(a) => true,
            _ => bad(
                sema,
                "`@interrupt` takes `{ errorCode: true }` or nothing",
                d.span,
                "not an interrupt option",
            ),
        },
        "bits" => match one_int(args) {
            Some((16 | 32 | 64, _)) => true,
            _ => bad(
                sema,
                "`@bits` takes 16, 32 or 64",
                d.span,
                "not a code size",
            ),
        },
        "requires" => {
            if args.is_empty() {
                return bad(
                    sema,
                    "`@requires` takes CPU feature names",
                    d.span,
                    "no feature named",
                );
            }
            for a in args {
                match str_arg(a) {
                    Some(f) if Feature::from_cpu_has(&f).is_some() => {}
                    Some(f) => {
                        return bad(
                            sema,
                            &format!("unknown CPU feature `{f}`"),
                            a.span,
                            "not a feature name",
                        );
                    }
                    None => {
                        return bad(
                            sema,
                            "`@requires` takes CPU feature names",
                            a.span,
                            "not a string",
                        );
                    }
                }
            }
            true
        }
        "section" => match one_str(args) {
            Some((s, span)) => section(sema, &s, span),
            None => bad(sema, "`@section` takes a section name", d.span, "no name"),
        },
        "at" => match one_int(args) {
            Some(_) => true,
            None => bad(sema, "`@at` takes an address", d.span, "no address"),
        },
        "repr" => match one_str(args) {
            Some((s, span)) => match Repr::from_name(&s) {
                Some(Repr::C) => true,
                Some(_) if site.target == Target::Class => bad(
                    sema,
                    &format!("`@repr(\"{s}\")` can't be used on a class"),
                    span,
                    "a class takes `@repr(\"C\")`",
                ),
                Some(_) => true,
                None => bad(
                    sema,
                    "`@repr` takes `\"C\"`, `\"u8\"`, `\"u16\"` or `\"u32\"`",
                    span,
                    "not a representation",
                ),
            },
            None => bad(
                sema,
                "`@repr` takes `\"C\"`, `\"u8\"`, `\"u16\"` or `\"u32\"`",
                d.span,
                "no representation",
            ),
        },
        "align" => match one_int(args) {
            Some((n, _)) if n.is_power_of_two() && n <= 4096 => true,
            Some((_, span)) => bad(
                sema,
                "`@align` takes a power of two up to 4096",
                span,
                "not a power of two up to 4096",
            ),
            None => bad(
                sema,
                "`@align` takes a power of two up to 4096",
                d.span,
                "no alignment",
            ),
        },
        "dll" | "hostCall" | "was" => match one_str(args) {
            Some(_) => true,
            None => bad(
                sema,
                &format!("`@{name}` takes one string"),
                d.span,
                "not one string",
            ),
        },
        "abi" => match one_str(args) {
            Some((s, span)) => match s.as_str() {
                "win64" | "sysv" => true,
                "cdecl" | "stdcall" => {
                    sema.emit(suggest::deferred_labeled(
                        Code::EN1030,
                        span,
                        "a 32-bit Windows calling convention",
                    ));
                    false
                }
                other => {
                    sema.err(
                        Code::EN0819,
                        format!("unknown ABI `{other}`"),
                        span,
                        "`win64` or `sysv`",
                    );
                    false
                }
            },
            None => bad(sema, "`@abi` takes an ABI name", d.span, "no ABI named"),
        },
        "lang" => match one_str(args) {
            Some((s, span)) => {
                if LangItem::from_name(&s).is_some() {
                    true
                } else {
                    bad(
                        sema,
                        &format!("unknown lang item `{s}`"),
                        span,
                        "not a lang item",
                    )
                }
            }
            None => bad(sema, "`@lang` takes a lang item's name", d.span, "no name"),
        },
        "intrinsic" => match one_str(args) {
            Some((s, span)) => {
                if IntrinsicName::from_name(&s).is_some() {
                    true
                } else {
                    bad(
                        sema,
                        &format!("unknown intrinsic `{s}`"),
                        span,
                        "not an intrinsic",
                    )
                }
            }
            None => bad(
                sema,
                "`@intrinsic` takes an intrinsic's name",
                d.span,
                "no name",
            ),
        },
        _ => true,
    }
}

fn is_error_code_literal(e: &ast::Expr) -> bool {
    let ast::ExprKind::ObjectLit(fields) = &e.kind else {
        return false;
    };
    fields.iter().all(|f| {
        f.name.name.as_str() == "errorCode"
            && matches!(
                f.value.as_ref().map(|v| &v.kind),
                Some(ast::ExprKind::Bool(_))
            )
    })
}

/// EN0814: a hosted target takes only `.text.`, `.data.`, `.rodata.` and `.bss.`
/// names, and `.bss.stack` is the compiler's on every target (S:1330).
fn section(sema: &mut Sema, name: &str, span: Span) -> bool {
    let target = sema.tcx.target().name;
    if name == ".bss.stack" {
        sema.err(
            Code::EN0814,
            "section `.bss.stack` is reserved",
            span,
            "the compiler's stack lives there",
        );
        return false;
    }
    let hosted = !matches!(sema.tcx.target().os, OsLayer::None | OsLayer::Uefi);
    let allowed = [".text.", ".data.", ".rodata.", ".bss."]
        .iter()
        .any(|prefix| name.starts_with(prefix));
    if hosted && !allowed {
        sema.err(
            Code::EN0814,
            format!("section `{name}` is not allowed on `{target}`"),
            span,
            "a hosted target takes names starting with `.text.`, `.data.`, `.rodata.` or `.bss.`",
        );
        return false;
    }
    true
}

/// The checks of a function's decorators that read its signature: EN0808 and
/// `@devMigrate`'s object-typed parameter.
fn check_function(
    sema: &mut Sema,
    decorators: &[ast::Decorator],
    f: &ast::FunctionDecl,
    def: DefId,
) {
    let Some(sig) = sema.tcx.sig_opt(def).cloned() else {
        return;
    };
    for d in decorators {
        match d.name.name.as_str() {
            "interrupt" => {
                let error_code = d
                    .args
                    .as_deref()
                    .and_then(|a| a.first())
                    .is_some_and(error_code);
                interrupt_sig(sema, f, &sig, error_code);
            }
            "devMigrate" => {
                let tcx = &*sema.tcx;
                let object = sig.params.iter().any(|p| {
                    let inner = match tcx.kind(p.ty) {
                        TyKind::Ref(inner) => inner,
                        _ => p.ty,
                    };
                    match tcx.kind(inner) {
                        TyKind::Object(_) | TyKind::Error => true,
                        TyKind::Param(q) => {
                            matches!(tcx.param(q).implicit, Some(Implicit::Shape(_)))
                        }
                        _ => false,
                    }
                });
                if !object {
                    sema.err(
                        Code::EN0806,
                        "`@devMigrate` needs a function with an object-typed parameter",
                        d.span,
                        "no parameter has an object type",
                    );
                }
            }
            _ => {}
        }
    }
}

/// EN0808: `(frame: &InterruptFrame)`, or with `errorCode` `(frame:
/// &InterruptFrame, code: usize)`, returning `void` or `never` (S:1324).
fn interrupt_sig(
    sema: &mut Sema,
    f: &ast::FunctionDecl,
    sig: &enrang_hir::FnSig,
    error_code: bool,
) {
    let tcx = &*sema.tcx;
    let types = sig.params.iter().map(|p| p.ty).chain([sig.ret]);
    if types.into_iter().any(|t| tcx.references_error(t)) {
        return;
    }
    let frame = tcx.lang_adt(LangItem::InterruptFrame);
    let is_frame = |t: Ty| match tcx.kind(t) {
        TyKind::Ref(inner) => matches!(tcx.kind(inner), TyKind::Adt(a, _) if Some(a) == frame),
        _ => false,
    };
    let params_ok = match (sig.params.as_slice(), error_code) {
        ([p], false) => is_frame(p.ty),
        ([p, q], true) => is_frame(p.ty) && tcx.kind(q.ty) == TyKind::Int(enrang_hir::IntTy::Usize),
        _ => false,
    };
    let ret_ok = matches!(tcx.kind(sig.ret), TyKind::Void | TyKind::Never);
    if params_ok && ret_ok {
        return;
    }
    let end = f
        .ret
        .as_ref()
        .map(|r| r.ty.span)
        .or_else(|| f.params.last().map(|p| p.span))
        .unwrap_or(f.name.span);
    let shape = if error_code {
        "`(frame: &InterruptFrame, code: usize)`"
    } else {
        "`(frame: &InterruptFrame)`"
    };
    sema.err(
        Code::EN0808,
        Code::EN0808.title(),
        f.name.span.to(end),
        format!("an interrupt handler takes {shape} and returns `void` or `never`"),
    );
}

/// EN0815 and the foreign-type checks of a `declare function`. Library
/// `@intrinsic` and `@hostCall` declarations bind the compiler or the VM, not
/// foreign code, so neither applies to them (S:352; plan choice for EN0816).
fn check_declare(sema: &mut Sema, decorators: &[ast::Decorator], d: &ast::DeclareFn, def: DefId) {
    let named = |n: &str| decorators.iter().any(|x| x.name.name.as_str() == n);
    if named("intrinsic") || named("hostCall") {
        return;
    }
    if !named("dll") {
        sema.emit(
            Diagnostic::new(
                Code::EN0815,
                Code::EN0815.title(),
                d.span,
                "a foreign function needs the DLL that exports it",
            )
            .note("only a Windows DLL import is declared without a body; on Linux and freestanding targets there is no dynamic linker or libc, so reach the system with inline assembly (`asm`) in an `unsafe function`"),
        );
    }
    let Some(sig) = sema.tcx.sig_opt(def).cloned() else {
        return;
    };
    for (p, written) in sig.params.iter().zip(&d.params) {
        ffi_check(sema, p.ty, written.ty.span);
    }
    if let Some(ret) = &d.ret {
        ffi_check(sema, sig.ret, ret.span);
    }
}

/// EN0817 among the layout decorators of a class, enum or `unsafe let`; for a class,
/// EN0827 and EN0826.
fn check_layout(
    sema: &mut Sema,
    decorators: &[ast::Decorator],
    class: Option<(AdtId, &ast::ClassDecl)>,
) {
    let layout: Vec<&ast::Decorator> = decorators
        .iter()
        .filter(|d| matches!(d.name.name.as_str(), "packed" | "repr" | "align"))
        .collect();
    let spelled = |sema: &Sema, d: &ast::Decorator| sema.tcx.map().text(d.span).to_owned();
    for (i, d) in layout.iter().enumerate() {
        let name = d.name.name.as_str();
        let clash = layout[..i].iter().find(|prior| {
            let other = prior.name.name.as_str();
            other == name
                || matches!(
                    (name, other),
                    ("packed", "align" | "repr") | ("align" | "repr", "packed")
                )
        });
        if let Some(prior) = clash {
            let (this, that) = (spelled(sema, d), spelled(sema, prior));
            sema.emit(
                Diagnostic::new(
                    Code::EN0817,
                    Code::EN0817.title(),
                    d.span,
                    format!("`{this}` conflicts with `{that}`"),
                )
                .with_secondary(prior.span, format!("`{that}` is here")),
            );
        }
    }
    let Some((adt, decl)) = class else { return };
    // `@repr("u8")` on a class is EN0806 already; only the class layouts count.
    let first = layout.iter().find(|d| {
        d.name.name.as_str() != "repr"
            || d.args
                .as_deref()
                .and_then(|a| a.first())
                .and_then(str_arg)
                .is_some_and(|s| s == "C")
    });
    let Some(first) = first else { return };
    let shown = spelled(sema, first);
    let class_def = sema.tcx.adt(adt).as_class().cloned().expect("a class");
    let class_name = sema.tcx.adt(adt).name;
    if class_def.modifier != ClassModifier::Final {
        let vis = match sema.tcx.def(sema.tcx.adt(adt).def).vis {
            enrang_hir::Vis::Private => "private",
            _ => "public",
        };
        sema.emit(
            Diagnostic::new(
                Code::EN0827,
                format!("a `{shown}` class must be `final`"),
                first.span,
                "promises an exact layout, but a class that can be extended carries a hidden pointer",
            )
            .with_help(Help::text(format!(
                "write `{shown} {vis} final class {class_name}`"
            ))),
        );
    } else if let Some(base) = &decl.extends {
        let base_name = sema.tcx.map().text(base.span).to_owned();
        sema.emit(
            Diagnostic::new(
                Code::EN0827,
                format!("a `{shown}` class can't extend another class"),
                base.span,
                format!("`{base_name}` gives it a hidden method-table pointer"),
            )
            .with_help(Help::text(format!("remove `extends {base_name}`"))),
        );
    }
    let packed = layout.iter().any(|d| d.name.name.as_str() == "packed");
    let own: Vec<(Ty, Span)> = own_field_types(sema, adt, decl);
    for (ty, span) in own {
        if let Some(inner) = hidden_inline(sema.tcx, ty, &mut BTreeSet::from([adt])) {
            let inner_name = sema.tcx.ty_string(inner);
            sema.err(
                Code::EN0827,
                format!("a `{shown}` class can't hold `{inner_name}` inline"),
                span,
                format!("`{inner_name}` carries a hidden method-table pointer"),
            );
            continue;
        }
        if packed {
            let tcx = &*sema.tcx;
            let label = if tcx.has_params(ty) {
                Some(format!("`{}` is generic", tcx.ty_string(ty)))
            } else if !tcx.is_copy(ty, &ParamEnv::empty()) {
                Some(format!("`{}` is not Copy", tcx.ty_string(ty)))
            } else {
                None
            };
            if let Some(label) = label {
                sema.err(Code::EN0826, Code::EN0826.title(), span, label);
            }
        }
    }
}

/// The types of the fields a class declares, with the spans of their written types.
fn own_field_types(sema: &Sema, adt: AdtId, decl: &ast::ClassDecl) -> Vec<(Ty, Span)> {
    let class = sema.tcx.adt(adt).as_class().expect("a class");
    let mut spans = Vec::new();
    for member in &decl.members {
        match &member.kind {
            ast::ClassMemberKind::Field(f) if !f.is_override => {
                spans.push((f.name.name, f.ty.span))
            }
            ast::ClassMemberKind::Constructor(c) => {
                for p in c.params.iter().filter(|p| p.property.is_some()) {
                    spans.push((p.name.name, p.ty.span));
                }
            }
            _ => {}
        }
    }
    class
        .fields
        .iter()
        .skip(class.own_from as usize)
        .filter_map(|f| {
            spans
                .iter()
                .find(|(n, _)| *n == f.name)
                .map(|&(_, span)| (f.ty, span))
        })
        .collect()
}

/// A class with a hidden table pointer that `ty` holds inline, not behind a
/// pointer: itself, or one held through the fields of a class without a table,
/// an enum's cases, tuples, fixed arrays, objects or `T | null` (S:1291: any such
/// pointer lies inside the exact layout).
fn hidden_inline(tcx: &Tcx, ty: Ty, visiting: &mut BTreeSet<AdtId>) -> Option<Ty> {
    match tcx.kind(ty) {
        TyKind::Adt(adt, args) => match &tcx.adt(adt).kind {
            AdtKind::Class(class) if class.hidden_table => Some(ty),
            AdtKind::Class(_) | AdtKind::Enum(_) => {
                if !visiting.insert(adt) {
                    return None;
                }
                tcx.adt_field_tys(adt, args)
                    .into_iter()
                    .find_map(|f| hidden_inline(tcx, f, visiting))
            }
            AdtKind::Interface(_) => None,
        },
        TyKind::Fixed(inner, _) | TyKind::Nullable(inner) => hidden_inline(tcx, inner, visiting),
        TyKind::Tuple(parts) => tcx
            .list(parts)
            .iter()
            .find_map(|&p| hidden_inline(tcx, p, visiting)),
        TyKind::Object(shape) => tcx
            .shape(shape)
            .fields
            .iter()
            .find_map(|&(_, f)| hidden_inline(tcx, f, visiting)),
        _ => None,
    }
}
