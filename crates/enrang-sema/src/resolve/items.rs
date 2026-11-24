//! Pass 1 of resolution (plan d.3): a `DefId` with its `ItemPath` for every item and
//! member of every module, each module's scope, the `@lang` registrations, the test
//! items, and the list of bodies to type, in source order: the entry's statements,
//! then items, then the `.test.en` part. Library bodies are never typed at M2.
//!
//! Functions and methods of one name form an overload set; any other second
//! declaration of a name in one scope is EN0307: items of a module, members of a
//! class or interface (a second `destructor` included), cases of an enum. An
//! interface that mixes fields and methods is EN0417, whose fix-it turns its first
//! field into a method (S:629).

use std::collections::BTreeMap;

use enrang_base::{Span, Symbol, intern};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{
    AdtDecl, AdtId, AdtKind, Attrs, BodyOwner, CTOR_SEGMENT, ClassDef, ClassModifier, DTOR_SEGMENT,
    DefData, DefFlags, DefId, DefKind, EnumDef, EnumValues, IfaceDef, ItemPath, ModuleId, ParamId,
    TestItem, TestItemKind, VariantDef, VariantValue, Vis,
};
use enrang_syntax::ast;

use crate::cx::Sema;
use crate::lower::decorators;
use crate::lower::{BodyAst, ItemAst, ItemAstKind};

/// Collects every module's items.
pub(crate) fn collect(sema: &mut Sema) {
    let program = sema.program;
    for (index, loaded) in program.modules.iter().enumerate() {
        let module = sema.module_id(index);
        let entry = index == program.entry;
        let mut collector = Collector {
            sema: &mut *sema,
            module,
            index,
            library: loaded.library,
            test_part: false,
            extends: 0,
            tests: 0,
            asserts: 0,
        };
        if entry && !loaded.ast.stmts.is_empty() && !loaded.library {
            collector.owner(
                BodyOwner::Statements(module),
                BodyAst::Statements(&loaded.ast.stmts),
            );
        }
        for stmt in &loaded.ast.stmts {
            if let ast::StmtKind::LocalFn { decorators, decl } = &stmt.kind {
                let def = collector.local_fn(decorators, decl, stmt.span);
                collector.sema.res.item_defs.insert(stmt.id, def);
            }
        }
        for item in &loaded.ast.items {
            collector.item(item, "");
        }
        if let Some(part) = &loaded.test_part {
            collector.test_part = true;
            for item in &part.ast.items {
                collector.item(item, "");
            }
        }
    }
}

struct Collector<'s, 'a> {
    sema: &'s mut Sema<'a>,
    module: ModuleId,
    index: usize,
    library: bool,
    test_part: bool,
    extends: usize,
    tests: usize,
    asserts: usize,
}

fn vis_of(v: Option<ast::Visibility>) -> Vis {
    match v {
        Some(ast::Visibility::Private) => Vis::Private,
        Some(ast::Visibility::Protected) => Vis::Protected,
        Some(ast::Visibility::Public) | None => Vis::Public,
    }
}

fn is_fn_kind(kind: DefKind) -> bool {
    matches!(kind, DefKind::Fn | DefKind::LocalFn | DefKind::DeclareFn)
}

impl<'a> Collector<'_, 'a> {
    fn path(&self, segments: &[Symbol]) -> ItemPath {
        ItemPath {
            module: self.sema.tcx.module(self.module).path,
            segments: segments.to_vec(),
            overload: None,
        }
    }

    fn data(
        &self,
        segments: &[Symbol],
        kind: DefKind,
        vis: Vis,
        name_span: Span,
        span: Span,
    ) -> DefData {
        let mut data = DefData::new(self.path(segments), kind, self.module, span);
        data.vis = vis;
        data.name_span = name_span;
        data.test_part = self.test_part;
        data
    }

    /// Defines `data`; `@lang` registers the item only in a library module (in user
    /// code it is EN0806, `lower/decorators.rs`).
    fn define(&mut self, mut data: DefData) -> DefId {
        if !self.library {
            data.attrs.lang = None;
        }
        let lang = data.attrs.lang;
        let def = self.sema.tcx.define_def(data);
        if let Some(item) = lang {
            self.sema.tcx.set_lang(item, def);
        }
        def
    }

    fn record(&mut self, def: DefId, kind: ItemAstKind<'a>) {
        self.sema.decls.items.push(ItemAst {
            def,
            module: self.module,
            test_part: self.test_part,
            kind,
        });
    }

    /// Registers a body to type; library bodies are never typed at M2.
    fn owner(&mut self, owner: BodyOwner, body: BodyAst<'a>) {
        if self.library {
            return;
        }
        self.sema
            .decls
            .owners
            .entry(self.module)
            .or_default()
            .push(owner);
        self.sema.decls.bodies.insert(owner, body);
    }

    /// Binds `name` in the module's scope; a second non-overload declaration is
    /// EN0307.
    fn bind(&mut self, name: ast::Ident, def: DefId) {
        let tcx = &*self.sema.tcx;
        let scope = &mut self.sema.res.scopes[self.index];
        let names = if self.test_part {
            &mut scope.test_names
        } else {
            &mut scope.names
        };
        let Some(existing) = names.get_mut(&name.name) else {
            names.insert(name.name, vec![def]);
            return;
        };
        let overload = is_fn_kind(tcx.def(def).kind)
            && existing
                .iter()
                .all(|&d| tcx.def(d).kind == tcx.def(def).kind);
        if overload {
            existing.push(def);
            return;
        }
        let first = tcx.def(existing[0]).name_span;
        self.sema.emit(defined_twice(name, first));
    }

    fn attrs(&mut self, decorators: &[ast::Decorator]) -> Attrs {
        decorators::read(self.sema.tcx, decorators)
    }

    fn local_fn(
        &mut self,
        decs: &'a [ast::Decorator],
        decl: &'a ast::FunctionDecl,
        span: Span,
    ) -> DefId {
        let mut data = self.data(
            &[decl.name.name],
            DefKind::LocalFn,
            Vis::Private,
            decl.name.span,
            span,
        );
        data.attrs = self.attrs(decs);
        data.flags.has_body = true;
        let def = self.define(data);
        self.bind(decl.name, def);
        self.record(def, ItemAstKind::LocalFn(decl));
        self.owner(BodyOwner::Fn(def), BodyAst::Function(decl));
        def
    }

    fn item(&mut self, item: &'a ast::Item, prefix: &str) {
        let vis = vis_of(item.visibility);
        let attrs = self.attrs(&item.decorators);
        let def = match &item.kind {
            ast::ItemKind::Function(f) => {
                let mut data = self.data(&[f.name.name], DefKind::Fn, vis, f.name.span, item.span);
                data.attrs = attrs;
                data.flags.has_body = true;
                let def = self.define(data);
                self.bind(f.name, def);
                self.record(def, ItemAstKind::Function(f));
                self.owner(BodyOwner::Fn(def), BodyAst::Function(f));
                def
            }
            ast::ItemKind::Class(c) => self.class(item, c, vis, attrs),
            ast::ItemKind::Enum(e) => self.enumeration(item, e, vis, attrs),
            ast::ItemKind::Interface(i) => self.interface(item, i, vis, attrs),
            ast::ItemKind::TypeAlias(a) => self.alias(item, a, vis, attrs),
            ast::ItemKind::TopConst(c) => {
                let mut data =
                    self.data(&[c.name.name], DefKind::Const, vis, c.name.span, item.span);
                data.attrs = attrs;
                let def = self.define(data);
                self.bind(c.name, def);
                self.record(def, ItemAstKind::Const(c));
                self.owner(BodyOwner::Const(def), BodyAst::Const(&c.value));
                def
            }
            ast::ItemKind::UnsafeLet(u) => {
                let mut data =
                    self.data(&[u.name.name], DefKind::Static, vis, u.name.span, item.span);
                data.attrs = attrs;
                let def = self.define(data);
                self.bind(u.name, def);
                self.record(def, ItemAstKind::Static(u));
                if let Some(value) = &u.value {
                    self.owner(BodyOwner::Const(def), BodyAst::Const(value));
                }
                def
            }
            ast::ItemKind::DeclareFn(d) => {
                let mut data = self.data(
                    &[d.name.name],
                    DefKind::DeclareFn,
                    vis,
                    d.name.span,
                    item.span,
                );
                data.attrs = attrs;
                let def = self.define(data);
                self.bind(d.name, def);
                self.record(def, ItemAstKind::Declare(d));
                def
            }
            ast::ItemKind::Extend(x) => self.extend(item, x, attrs),
            ast::ItemKind::StaticAssert { cond, .. } => {
                let segment = ItemPath::assert_segment(self.asserts);
                self.asserts += 1;
                let mut data = self.data(
                    &[segment],
                    DefKind::StaticAssert,
                    Vis::Private,
                    item.span,
                    item.span,
                );
                data.attrs = attrs;
                let def = self.define(data);
                self.record(def, ItemAstKind::StaticAssert);
                self.owner(BodyOwner::Const(def), BodyAst::Const(cond));
                def
            }
            ast::ItemKind::Describe(d) => {
                let prefix = format!("{prefix}{} > ", d.name.value);
                for inner in &d.items {
                    self.item(inner, &prefix);
                }
                return;
            }
            ast::ItemKind::Test(t) => {
                let def = self.test(
                    item.span,
                    &format!("{prefix}{}", t.name.value),
                    TestItemKind::Test { mode: t.mode },
                );
                if let Some(body) = &t.body {
                    self.owner(BodyOwner::Test(def), BodyAst::Test(body));
                }
                if let Some(ast::TestExtra::Cases(cases)) = &t.extra
                    && !self.library
                {
                    self.sema.decls.test_cases.insert(def, cases);
                }
                def
            }
            ast::ItemKind::CompileCase(c) => self.test(
                item.span,
                &format!("{prefix}{}", c.name.value),
                TestItemKind::Compile(c.kind),
            ),
        };
        self.sema.res.item_defs.insert(item.id, def);
    }

    fn test(&mut self, span: Span, id: &str, kind: TestItemKind) -> DefId {
        let segment = ItemPath::test_segment(self.tests);
        self.tests += 1;
        let data = self.data(&[segment], DefKind::Test, Vis::Private, span, span);
        let def = self.define(data);
        self.record(def, ItemAstKind::Test);
        self.sema.tests.push(TestItem {
            id: id.to_owned(),
            def,
            module: self.module,
            kind,
            span,
        });
        def
    }

    fn adt(
        &mut self,
        name: ast::Ident,
        span: Span,
        vis: Vis,
        attrs: Attrs,
        kind: AdtKind,
    ) -> AdtId {
        let mut data = self.data(&[name.name], DefKind::TypeAlias, vis, name.span, span);
        data.attrs = attrs;
        if !self.library {
            data.attrs.lang = None;
        }
        let lang = data.attrs.lang;
        let generics = self.sema.tcx.empty_generics();
        let adt = self.sema.tcx.define_adt(AdtDecl {
            data,
            name: name.name,
            generics,
            kind,
        });
        let def = self.sema.tcx.adt(adt).def;
        if let Some(item) = lang {
            self.sema.tcx.set_lang(item, def);
        }
        self.bind(name, def);
        adt
    }

    /// A member of an ADT or `extend` block.
    #[allow(clippy::too_many_arguments)]
    fn member(
        &mut self,
        parent: DefId,
        name: Symbol,
        kind: DefKind,
        vis: Vis,
        name_span: Span,
        span: Span,
        attrs: Attrs,
        flags: DefFlags,
    ) -> DefId {
        let mut segments = self.sema.tcx.def(parent).path.segments.clone();
        segments.push(name);
        let mut data = self.data(&segments, kind, vis, name_span, span);
        data.parent = Some(parent);
        data.attrs = attrs;
        data.flags = flags;
        self.define(data)
    }

    fn method(
        &mut self,
        parent: DefId,
        m: &'a ast::MethodDecl,
        vis: Vis,
        decs: &[ast::Decorator],
        span: Span,
    ) -> DefId {
        let attrs = self.attrs(decs);
        let flags = DefFlags {
            is_abstract: m.is_abstract,
            is_override: m.is_override,
            has_body: m.body.is_some(),
        };
        let def = self.member(
            parent,
            m.name.name,
            DefKind::Method,
            vis,
            m.name.span,
            span,
            attrs,
            flags,
        );
        if m.body.is_some() {
            self.owner(BodyOwner::Fn(def), BodyAst::Method(m));
        }
        def
    }

    fn class(
        &mut self,
        item: &'a ast::Item,
        c: &'a ast::ClassDecl,
        vis: Vis,
        attrs: Attrs,
    ) -> DefId {
        let modifier = match c.modifier {
            ast::ClassModifier::Plain => ClassModifier::Plain,
            ast::ClassModifier::Abstract => ClassModifier::Abstract,
            ast::ClassModifier::Final => ClassModifier::Final,
        };
        let adt = self.adt(
            c.name,
            item.span,
            vis,
            attrs,
            AdtKind::Class(ClassDef::new(modifier)),
        );
        let parent = self.sema.tcx.adt(adt).def;
        let mut members = Vec::new();
        let mut seen: BTreeMap<Symbol, (Span, bool)> = BTreeMap::new();
        let (mut methods, mut ctors, mut dtor) = (Vec::new(), Vec::new(), None);
        for member in &c.members {
            let def = match &member.kind {
                ast::ClassMemberKind::Field(f) => {
                    self.member_name(&mut seen, f.name, false);
                    None
                }
                ast::ClassMemberKind::Constructor(ctor) => {
                    for p in ctor.params.iter().filter(|p| p.property.is_some()) {
                        self.member_name(&mut seen, p.name, false);
                    }
                    let attrs = self.attrs(&member.decorators);
                    let flags = DefFlags {
                        has_body: true,
                        ..DefFlags::default()
                    };
                    let d = self.member(
                        parent,
                        intern(CTOR_SEGMENT),
                        DefKind::Ctor,
                        vis_of(ctor.visibility),
                        member.span,
                        member.span,
                        attrs,
                        flags,
                    );
                    self.owner(BodyOwner::Fn(d), BodyAst::Ctor(ctor));
                    ctors.push(d);
                    Some(d)
                }
                ast::ClassMemberKind::Destructor(d) => {
                    // A class has one destructor (SPEC 3.1): a second is EN0307 at
                    // its keyword, and the first stays the class's.
                    let keyword = self.destructor_keyword(member);
                    if let Some(first) = dtor {
                        let name = ast::Ident {
                            name: intern("destructor"),
                            span: keyword,
                        };
                        let first = self.sema.tcx.def(first).name_span;
                        self.sema.emit(defined_twice(name, first));
                    }
                    let attrs = self.attrs(&member.decorators);
                    let flags = DefFlags {
                        has_body: true,
                        ..DefFlags::default()
                    };
                    let def = self.member(
                        parent,
                        intern(DTOR_SEGMENT),
                        DefKind::Dtor,
                        vis_of(d.visibility),
                        keyword,
                        member.span,
                        attrs,
                        flags,
                    );
                    self.owner(BodyOwner::Fn(def), BodyAst::Dtor(d));
                    dtor.get_or_insert(def);
                    Some(def)
                }
                ast::ClassMemberKind::Method(m) => {
                    self.member_name(&mut seen, m.name, true);
                    let d = self.method(
                        parent,
                        m,
                        vis_of(m.visibility),
                        &member.decorators,
                        member.span,
                    );
                    methods.push(d);
                    Some(d)
                }
            };
            members.push(def);
        }
        if let AdtKind::Class(class) = &mut self.sema.tcx.adt_mut(adt).kind {
            class.methods = methods;
            class.ctors = ctors;
            class.dtor = dtor;
        }
        self.record(parent, ItemAstKind::Class(adt, c, members));
        parent
    }

    /// The `destructor` keyword of a class member, after its decorators and
    /// visibility.
    fn destructor_keyword(&self, member: &ast::ClassMember) -> Span {
        let after = member
            .decorators
            .last()
            .map_or(member.span.lo, |d| d.span.hi.max(member.span.lo));
        let rest = Span {
            lo: after,
            hi: member.span.hi,
        };
        let text = self.sema.tcx.map().text(rest);
        match text.find("destructor") {
            Some(at) => {
                let lo = after + at as u32;
                Span {
                    lo,
                    hi: lo + "destructor".len() as u32,
                }
            }
            None => member.span,
        }
    }

    /// EN0307 for a member name used twice, unless both are methods (overloads).
    fn member_name(
        &mut self,
        seen: &mut BTreeMap<Symbol, (Span, bool)>,
        name: ast::Ident,
        method: bool,
    ) {
        match seen.get(&name.name) {
            Some(&(first, was_method)) if !(method && was_method) => {
                self.sema.emit(defined_twice(name, first));
            }
            Some(_) => {}
            None => {
                seen.insert(name.name, (name.span, method));
            }
        }
    }

    fn enumeration(
        &mut self,
        item: &'a ast::Item,
        e: &'a ast::EnumDecl,
        vis: Vis,
        attrs: Attrs,
    ) -> DefId {
        let mut variants = Vec::new();
        let mut seen: BTreeMap<Symbol, (Span, bool)> = BTreeMap::new();
        for v in &e.variants {
            self.member_name(&mut seen, v.name, false);
            if let ast::VariantPayload::Fields(fields) = &v.payload {
                let mut names: BTreeMap<Symbol, (Span, bool)> = BTreeMap::new();
                for f in fields {
                    self.member_name(&mut names, f.name, false);
                }
            }
            let mut variant = VariantDef::new(v.name.name);
            variant.span = v.span;
            variants.push(variant);
        }
        let mut def = EnumDef::new(variants);
        def.repr = attrs.repr;
        let adt = self.adt(e.name, item.span, vis, attrs, AdtKind::Enum(def));
        let parent = self.sema.tcx.adt(adt).def;
        let mut methods = Vec::new();
        for m in &e.methods {
            self.member_name(&mut seen, m.name, true);
            methods.push(self.method(parent, m, vis_of(m.visibility), &[], m.span));
        }
        if let AdtKind::Enum(def) = &mut self.sema.tcx.adt_mut(adt).kind {
            def.methods = methods.clone();
        }
        self.record(parent, ItemAstKind::Enum(adt, e, methods));
        parent
    }

    fn interface(
        &mut self,
        item: &'a ast::Item,
        i: &'a ast::InterfaceDecl,
        vis: Vis,
        attrs: Attrs,
    ) -> DefId {
        let has_methods = i
            .members
            .iter()
            .any(|m| matches!(m, ast::IfaceMember::Method(_)));
        let first_field = i.members.iter().find_map(|m| match m {
            ast::IfaceMember::Field(f) => Some(f),
            ast::IfaceMember::Method(_) => None,
        });
        let mut field_names: BTreeMap<Symbol, (Span, bool)> = BTreeMap::new();
        for m in &i.members {
            if let ast::IfaceMember::Field(f) = m {
                self.member_name(&mut field_names, f.name, false);
            }
        }
        if !has_methods && let Some(_) = first_field {
            let mut data = self.data(
                &[i.name.name],
                DefKind::TypeAlias,
                vis,
                i.name.span,
                item.span,
            );
            data.attrs = attrs;
            let def = self.define(data);
            self.bind(i.name, def);
            self.record(def, ItemAstKind::FieldsInterface(i));
            return def;
        }
        if let Some(field) = first_field {
            let method = as_method(self.sema.tcx.map(), field);
            self.sema.emit(
                Diagnostic::new(
                    Code::EN0417,
                    format!("interface `{}` mixes fields and methods", i.name.name),
                    field.span,
                    "a field in an interface with methods",
                )
                .with_help(Help::machine(
                    format!("make it a method: `{method}`"),
                    vec![Edit::replace(field.span, method.clone())],
                )),
            );
        }
        let sealed = attrs.lang.filter(|l| l.is_sealed() && self.library);
        let kind = AdtKind::Interface(IfaceDef {
            methods: Vec::new(),
            sealed,
            self_param: ParamId(u32::MAX),
        });
        let adt = self.adt(i.name, item.span, vis, attrs, kind);
        let parent = self.sema.tcx.adt(adt).def;
        let mut members = Vec::new();
        let mut methods = Vec::new();
        let mut seen: BTreeMap<Symbol, (Span, bool)> = BTreeMap::new();
        for member in &i.members {
            match member {
                ast::IfaceMember::Method(m) => {
                    self.member_name(&mut seen, m.name, true);
                    let flags = DefFlags {
                        has_body: false,
                        ..DefFlags::default()
                    };
                    let d = self.member(
                        parent,
                        m.name.name,
                        DefKind::Method,
                        Vis::Public,
                        m.name.span,
                        m.span,
                        Attrs::default(),
                        flags,
                    );
                    methods.push(d);
                    members.push(Some(d));
                }
                ast::IfaceMember::Field(_) => members.push(None),
            }
        }
        if let AdtKind::Interface(iface) = &mut self.sema.tcx.adt_mut(adt).kind {
            iface.methods = methods;
        }
        self.record(parent, ItemAstKind::Interface(adt, i, members));
        parent
    }

    fn alias(
        &mut self,
        item: &'a ast::Item,
        a: &'a ast::TypeAlias,
        vis: Vis,
        attrs: Attrs,
    ) -> DefId {
        if let ast::TypeExprKind::StrUnion(literals) = &a.ty.kind {
            let mut variants = Vec::new();
            for lit in literals {
                let mut variant = VariantDef::new(lit.value);
                variant.span = lit.span;
                variant.value = Some(VariantValue::Text(
                    self.sema.tcx.intern_str(lit.value.as_str()),
                ));
                variants.push(variant);
            }
            let mut def = EnumDef::new(variants);
            def.str_union = true;
            def.values = EnumValues::Texts;
            let adt = self.adt(a.name, item.span, vis, attrs, AdtKind::Enum(def));
            let parent = self.sema.tcx.adt(adt).def;
            self.record(parent, ItemAstKind::StrUnion);
            return parent;
        }
        let mut data = self.data(
            &[a.name.name],
            DefKind::TypeAlias,
            vis,
            a.name.span,
            item.span,
        );
        data.attrs = attrs;
        let def = self.define(data);
        self.bind(a.name, def);
        self.record(def, ItemAstKind::Alias(a));
        def
    }

    fn extend(&mut self, item: &'a ast::Item, x: &'a ast::ExtendDecl, attrs: Attrs) -> DefId {
        let segment = ItemPath::extend_segment(self.extends);
        self.extends += 1;
        let mut data = self.data(
            &[segment],
            DefKind::Extend,
            Vis::Public,
            item.span,
            item.span,
        );
        data.attrs = attrs;
        let def = self.define(data);
        let mut members = Vec::new();
        for member in &x.members {
            let m = &member.method;
            members.push(self.method(
                def,
                m,
                vis_of(m.visibility),
                &member.decorators,
                member.span,
            ));
        }
        self.record(def, ItemAstKind::Extend(x, members));
        def
    }
}

/// EN0307 at a second declaration of `name`.
/// EN0417's fix-it (S:629): the interface field `name: T` as the method
/// `name(): &T`; `x?: T` and `x: T | null` give `x(): &T | null`, a field that is
/// already a reference keeps its type, and a type that `&` would split is
/// parenthesised.
fn as_method(map: &enrang_base::SourceMap, f: &ast::IfaceField) -> String {
    use ast::TypeExprKind as K;
    let borrowed = |t: &ast::TypeExpr| -> String {
        let text = map.text(t.span);
        match &t.kind {
            K::Ref(_) | K::ReadonlyRef(_) => text.to_owned(),
            K::Union(_) | K::Nullable(_) | K::FnPtr(_) | K::Closure(_) | K::StrUnion(_) => {
                format!("&({text})")
            }
            _ => format!("&{text}"),
        }
    };
    let ty = match &f.ty.kind {
        K::Nullable(inner) => format!("{} | null", borrowed(inner)),
        _ if f.optional => format!("{} | null", borrowed(&f.ty)),
        _ => borrowed(&f.ty),
    };
    format!("{}(): {ty}", f.name.name)
}

fn defined_twice(name: ast::Ident, first: Span) -> Diagnostic {
    Diagnostic::new(
        Code::EN0307,
        format!("`{}` is defined twice", name.name),
        name.span,
        "defined again here",
    )
    .with_secondary(first, format!("the first `{}` is here", name.name))
}
