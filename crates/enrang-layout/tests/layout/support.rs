//! What the cases share: a hand-built program on a target, defined through the
//! public `Tcx::define_*` API as a MIR fixture would with no front end; a reader
//! for SPEC's Markdown tables; and a reader for the type and declaration spellings
//! SPEC 11 writes, so its rows can be laid out as written.
//!
//! The spelling reader is not Enrang's parser (a layout test cannot parse source,
//! plan 0.4): it reads only what SPEC 11's tables and examples write, types such as
//! `&i64[]`, `i64 | null`, `{ found: bool, index: i32, last: bool }`, `[bool, i32]`,
//! `fn(i64) => void` and `Box<T>`, and declarations of classes with fields, enums
//! with cases and method interfaces with no members.

use std::collections::BTreeMap;
use std::fs;
use std::sync::{Arc, OnceLock};

use enrang_base::{FileId, SourceMap, Span, intern};
use enrang_hir::{
    AdtDecl, AdtId, AdtKind, Attrs, ClassDef, ClassModifier, DefData, DefKind, EnumDef, EnumValues,
    FieldDef, FnPtrSig, Generics, IfaceDef, Implicit, ItemPath, ModuleId, ModuleInfo, ModulePath,
    ParamId, Repr, Tcx, Ty, TyKind, TyParamDef, VariantDef, VariantValue, Vis,
};
use enrang_layout::{Layout, LayoutCx, LayoutError, layout_of};
use enrang_target::{TargetOpts, resolve};
use enrang_testkit::workspace_root;

/// An enum case: its name, its fields, and its written value.
pub type Case<'a> = (&'a str, Vec<(&'a str, Ty)>, Option<VariantValue>);

/// The two data layouts SPEC 11 states, by a target of each width.
pub const TARGETS: [&str; 2] = ["i386-linux", "x86_64-linux"];

/// `docs/SPEC.md`, read once.
pub fn spec() -> &'static str {
    static SPEC: OnceLock<String> = OnceLock::new();
    SPEC.get_or_init(|| {
        fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("docs/SPEC.md")
    })
}

/// The cells of one table line, split at every `|` that is not escaped, each
/// trimmed and with `\|` read back as `|`.
pub fn cells(line: &str) -> Vec<String> {
    let inner = line.trim().trim_start_matches('|');
    let mut cells = Vec::new();
    let mut cell = String::new();
    let mut chars = inner.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'|') => {
                cell.push('|');
                chars.next();
            }
            '|' => cells.push(std::mem::take(&mut cell).trim().to_owned()),
            _ => cell.push(c),
        }
    }
    if !cell.trim().is_empty() {
        cells.push(cell.trim().to_owned());
    }
    cells
}

/// The rows of the table whose header line is `header`, each split into cells.
pub fn table_after(doc: &str, header: &str) -> Vec<Vec<String>> {
    let mut lines = doc.lines().skip_while(|line| line.trim() != header);
    assert!(
        lines.next().is_some(),
        "SPEC has no table headed {header:?}"
    );
    let separator = lines.next().expect("a separator line");
    assert!(separator.starts_with("|---"), "{separator:?}");
    lines
        .take_while(|line| line.starts_with('|'))
        .map(cells)
        .collect()
}

/// The text between backticks in `text`, each item once, in order.
pub fn backticked(text: &str) -> Vec<String> {
    text.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// A size or alignment as SPEC 11 writes it, at pointer width `p`: `1`, `` `P` ``,
/// `` `2P` (code, env), stack only ``, or `` 4 when `P == 4`, 8 when `P == 8` ``.
pub fn amount(cell: &str, p: u64) -> u64 {
    if cell.contains(" when ") {
        for choice in cell.split(',') {
            let (value, condition) = choice.split_once(" when ").expect("`x when P == y`");
            let width = backticked(condition)[0]
                .strip_prefix("P == ")
                .expect("`P == y`")
                .parse::<u64>()
                .expect("a width");
            if width == p {
                return value.trim().parse().expect("a number");
            }
        }
        panic!("{cell:?} names no value for P == {p}");
    }
    let word = backticked(cell)
        .into_iter()
        .next()
        .unwrap_or_else(|| cell.trim().to_owned());
    match word.strip_suffix('P') {
        Some("") => p,
        Some(n) => n.parse::<u64>().expect("a multiple of P") * p,
        None => word.parse().expect("a number"),
    }
}

/// Asserts that SPEC still says `sentence`, word for word, so a case built from it
/// cannot drift from the document.
pub fn spec_says(sentence: &str) {
    assert!(spec().contains(sentence), "SPEC no longer says: {sentence}");
}

/// A program under construction on one target.
pub struct World {
    pub tcx: Tcx,
    module: ModuleId,
    /// The classes, enums and interfaces defined so far, by name.
    names: BTreeMap<String, Ty>,
    /// Definitions made so far, to give each its own path.
    count: usize,
}

impl World {
    pub fn new(target: &str) -> World {
        let (spec, _) = resolve(target, &TargetOpts::default()).expect("a target");
        let mut tcx = Tcx::new(Arc::new(spec), Arc::new(SourceMap::new()));
        let module = tcx.define_module(ModuleInfo::new(
            ModulePath::new("src/main"),
            false,
            FileId(0),
        ));
        World {
            tcx,
            module,
            names: BTreeMap::new(),
            count: 0,
        }
    }

    /// `P` on this world's target.
    pub fn p(&self) -> u64 {
        u64::from(self.tcx.target().layout.ptr_bytes)
    }

    pub fn layout(&self, ty: Ty) -> Result<Arc<Layout>, LayoutError> {
        layout_of(&self.tcx, ty)
    }

    /// The layout of `ty`, which must have one.
    pub fn ok(&self, ty: Ty) -> Arc<Layout> {
        self.layout(ty)
            .unwrap_or_else(|e| panic!("{} has no layout: {e:?}", self.tcx.ty_string(ty)))
    }

    /// `(size, align)` of `ty`.
    pub fn size_align(&self, ty: Ty) -> (u64, u32) {
        let layout = self.ok(ty);
        (layout.size, layout.align)
    }

    pub fn offset(&self, ty: Ty, field: &str) -> u64 {
        LayoutCx::new(&self.tcx)
            .offset_of(ty, field)
            .expect("a layout")
            .unwrap_or_else(|| panic!("no field {field}"))
    }

    /// The type a name stands for.
    pub fn named(&self, name: &str) -> Ty {
        *self
            .names
            .get(name)
            .unwrap_or_else(|| panic!("nothing is named {name}"))
    }

    fn data(&mut self, name: &str, kind: DefKind, attrs: Attrs) -> DefData {
        self.count += 1;
        let path = ItemPath {
            module: self.tcx.module(self.module).path,
            segments: vec![intern(&format!("{name}#{}", self.count))],
            overload: None,
        };
        let mut data = DefData::new(path, kind, self.module, Span::DUMMY);
        data.attrs = attrs;
        data
    }

    /// Defines a class, enum or interface named `name` with type parameters
    /// `params`; returns it and its parameters as types.
    fn adt(
        &mut self,
        name: &str,
        kind: AdtKind,
        attrs: Attrs,
        params: &[&str],
    ) -> (AdtId, Vec<Ty>) {
        let generics = self.tcx.empty_generics();
        let data = self.data(name, DefKind::TypeAlias, attrs);
        let adt = self.tcx.define_adt(AdtDecl {
            data,
            name: intern(name),
            generics,
            kind,
        });
        let owner = self.tcx.adt(adt).def;
        let ids: Vec<ParamId> = params
            .iter()
            .enumerate()
            .map(|(i, param)| {
                self.tcx.define_param(TyParamDef {
                    name: intern(param),
                    owner,
                    index: i as u32,
                    bounds: Vec::new(),
                    implicit: None,
                    span: Span::DUMMY,
                })
            })
            .collect();
        let g = self.tcx.define_generics(Generics::new(None, ids.clone()));
        self.tcx.adt_mut(adt).generics = g;
        let tys = ids.iter().map(|&p| self.tcx.mk_param(p)).collect();
        let identity = self.tcx.adt_identity(adt);
        self.names.insert(name.to_owned(), identity);
        (adt, tys)
    }

    /// A class with no field yet.
    pub fn class(
        &mut self,
        name: &str,
        modifier: ClassModifier,
        attrs: Attrs,
        params: &[&str],
    ) -> (AdtId, Vec<Ty>) {
        self.adt(name, AdtKind::Class(ClassDef::new(modifier)), attrs, params)
    }

    /// Adds a public field to a class.
    pub fn field(&mut self, class: AdtId, name: &str, ty: Ty) {
        let field = FieldDef::new(intern(name), ty, class);
        let AdtKind::Class(def) = &mut self.tcx.adt_mut(class).kind else {
            panic!("a class");
        };
        def.fields.push(field);
    }

    /// Makes `base`, a class type, the base of `class`, flattening its fields in
    /// front at its arguments, as sema does (plan c.1), and keeping its hidden
    /// pointer.
    pub fn extends(&mut self, class: AdtId, base: Ty) {
        let TyKind::Adt(base_adt, base_args) = self.tcx.kind(base) else {
            panic!("a class base");
        };
        let params = self
            .tcx
            .generics(self.tcx.adt(base_adt).generics)
            .params
            .clone();
        let args = self.tcx.list(base_args);
        let base_def = self.tcx.adt(base_adt).as_class().expect("a class").clone();
        let inherited: Vec<FieldDef> = base_def
            .fields
            .iter()
            .map(|f| FieldDef {
                ty: self.tcx.subst(f.ty, &params, &args),
                ..f.clone()
            })
            .collect();
        let AdtKind::Class(def) = &mut self.tcx.adt_mut(class).kind else {
            panic!("a class");
        };
        def.base = Some(base);
        def.hidden_table |= base_def.hidden_table;
        def.own_from = inherited.len() as u32;
        let own = std::mem::take(&mut def.fields);
        def.fields = inherited;
        def.fields.extend(own);
    }

    /// An enum with these cases, each with its fields and its written value.
    pub fn enumeration(
        &mut self,
        name: &str,
        params: &[&str],
        repr: Option<Repr>,
        cases: &[Case<'_>],
    ) -> (AdtId, Vec<Ty>) {
        let mut def = EnumDef::new(Vec::new());
        def.repr = repr;
        let attrs = Attrs {
            repr,
            ..Attrs::default()
        };
        let (adt, tys) = self.adt(name, AdtKind::Enum(def), attrs, params);
        self.set_cases(adt, cases);
        (adt, tys)
    }

    /// Replaces an enum's cases, setting its `values` from theirs.
    pub fn set_cases(&mut self, adt: AdtId, cases: &[Case<'_>]) {
        let variants: Vec<VariantDef> = cases
            .iter()
            .map(|(case, fields, value)| {
                let mut variant = VariantDef::new(intern(case));
                variant.fields = fields
                    .iter()
                    .map(|&(field, ty)| FieldDef::new(intern(field), ty, adt))
                    .collect();
                variant.value = *value;
                variant
            })
            .collect();
        let values = match variants.iter().find_map(|v| v.value) {
            Some(VariantValue::Int(_)) => EnumValues::Ints,
            Some(VariantValue::Text(_)) => EnumValues::Texts,
            None => EnumValues::None,
        };
        let AdtKind::Enum(e) = &mut self.tcx.adt_mut(adt).kind else {
            panic!("an enum");
        };
        e.variants = variants;
        e.values = values;
    }

    /// A method interface with no member.
    pub fn interface(&mut self, name: &str) -> Ty {
        let placeholder = ParamId(u32::MAX);
        let (adt, _) = self.adt(
            name,
            AdtKind::Interface(IfaceDef {
                methods: Vec::new(),
                sealed: None,
                self_param: placeholder,
            }),
            Attrs::default(),
            &[],
        );
        let owner = self.tcx.adt(adt).def;
        let self_param = self.tcx.define_param(TyParamDef {
            name: intern("Self"),
            owner,
            index: 0,
            bounds: Vec::new(),
            implicit: Some(Implicit::Interface(adt)),
            span: Span::DUMMY,
        });
        if let AdtKind::Interface(i) = &mut self.tcx.adt_mut(adt).kind {
            i.self_param = self_param;
        }
        self.tcx.mk_adt(adt, &[])
    }

    /// A type parameter of a fresh function.
    pub fn param(&mut self, name: &str) -> Ty {
        let data = self.data(&format!("f_{name}"), DefKind::Fn, Attrs::default());
        let owner = self.tcx.define_def(data);
        let p = self.tcx.define_param(TyParamDef {
            name: intern(name),
            owner,
            index: 0,
            bounds: Vec::new(),
            implicit: None,
            span: Span::DUMMY,
        });
        self.tcx.mk_param(p)
    }

    /// The type SPEC spells `text`, such as `&i64[]` or `{ found: bool }`.
    pub fn ty(&mut self, text: &str) -> Ty {
        let mut reader = Reader::new(self, text);
        let ty = reader.ty();
        reader.end();
        ty
    }

    /// Defines the class, enum or interface SPEC declares in `text`, such as
    /// `@packed public final class GdtPointer { public limit: u16; public base: u32; }`,
    /// and returns its type at its own parameters.
    pub fn declare(&mut self, text: &str) -> Ty {
        let mut reader = Reader::new(self, text);
        let ty = reader.declaration();
        reader.end();
        ty
    }

    /// The type of a row of SPEC 11's worked sizes: a declaration or a type.
    pub fn declare_or_ty(&mut self, text: &str) -> Ty {
        let declaration = text.starts_with('@')
            || text
                .split_whitespace()
                .any(|w| matches!(w, "class" | "enum" | "interface"));
        if declaration {
            self.declare(text)
        } else {
            self.ty(text)
        }
    }

    /// A safe function pointer type.
    pub fn fn_ptr(&self, params: &[Ty], ret: Ty) -> Ty {
        self.tcx
            .mk_fn_ptr(enrang_hir::Abi::Enrang, FnPtrSig::new(params, ret))
    }

    /// A closure parameter type.
    pub fn closure(&self, params: &[Ty], ret: Ty) -> Ty {
        self.tcx.mk_closure(FnPtrSig::new(params, ret))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Ident(String),
    Num(u64),
    Str(String),
    Punct(&'static str),
}

/// The punctuation the spellings use, longest first where one starts another.
const PUNCT: [&str; 18] = [
    "=>", "&", "*", "|", "[", "]", "{", "}", "(", ")", "<", ">", ",", ":", ";", "@", "=", "-",
];

fn tokens(text: &str) -> Vec<Token> {
    let mut out = Vec::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        if c.is_whitespace() {
            rest = &rest[c.len_utf8()..];
        } else if c.is_ascii_alphabetic() || c == '_' {
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            out.push(Token::Ident(rest[..end].to_owned()));
            rest = &rest[end..];
        } else if c.is_ascii_digit() {
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            let digits = rest[..end].replace('_', "");
            let value = match digits.strip_prefix("0x") {
                Some(hex) => u64::from_str_radix(hex, 16),
                None => digits.parse(),
            };
            out.push(Token::Num(value.expect("a number")));
            rest = &rest[end..];
        } else if c == '"' {
            let end = rest[1..].find('"').expect("a closing quote") + 1;
            out.push(Token::Str(rest[1..end].to_owned()));
            rest = &rest[end + 1..];
        } else {
            let punct = PUNCT
                .iter()
                .find(|p| rest.starts_with(**p))
                .unwrap_or_else(|| panic!("unexpected {c:?} in {text:?}"));
            out.push(Token::Punct(punct));
            rest = &rest[punct.len()..];
        }
    }
    out
}

/// Reads one spelling against a world, defining what it declares.
struct Reader<'w> {
    world: &'w mut World,
    text: String,
    tokens: Vec<Token>,
    at: usize,
    /// The type parameters in scope, innermost last.
    scope: Vec<(String, Ty)>,
}

impl<'w> Reader<'w> {
    fn new(world: &'w mut World, text: &str) -> Reader<'w> {
        Reader {
            world,
            text: text.to_owned(),
            tokens: tokens(text),
            at: 0,
            scope: Vec::new(),
        }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.at)
    }

    fn next(&mut self) -> Token {
        let token = self
            .tokens
            .get(self.at)
            .cloned()
            .unwrap_or_else(|| panic!("{:?} ends too soon", self.text));
        self.at += 1;
        token
    }

    fn is(&self, punct: &str) -> bool {
        self.peek() == Some(&Token::Punct(match_punct(punct)))
    }

    fn is_word(&self, word: &str) -> bool {
        matches!(self.peek(), Some(Token::Ident(w)) if w == word)
    }

    fn eat(&mut self, punct: &str) -> bool {
        let found = self.is(punct);
        if found {
            self.at += 1;
        }
        found
    }

    fn expect(&mut self, punct: &str) {
        assert!(self.eat(punct), "expected `{punct}` in {:?}", self.text);
    }

    fn word(&mut self) -> String {
        match self.next() {
            Token::Ident(word) => word,
            other => panic!("expected a name, found {other:?} in {:?}", self.text),
        }
    }

    fn keyword(&mut self, word: &str) {
        let found = self.word();
        assert_eq!(found, word, "in {:?}", self.text);
    }

    fn number(&mut self) -> u64 {
        match self.next() {
            Token::Num(n) => n,
            other => panic!("expected a number, found {other:?} in {:?}", self.text),
        }
    }

    fn end(&self) {
        assert!(
            self.at == self.tokens.len(),
            "{:?} has more after {:?}",
            self.text,
            self.tokens.get(self.at)
        );
    }

    fn list<T>(&mut self, close: &str, mut item: impl FnMut(&mut Self) -> T) -> Vec<T> {
        let mut items = Vec::new();
        while !self.eat(close) {
            items.push(item(self));
            if !self.eat(",") {
                self.expect(close);
                break;
            }
        }
        items
    }

    // Types.

    fn ty(&mut self) -> Ty {
        let mut ty = self.unary();
        while self.eat("|") {
            self.keyword("null");
            ty = self.world.tcx.mk_nullable(ty);
        }
        ty
    }

    fn unary(&mut self) -> Ty {
        if self.eat("&") {
            let inner = self.unary();
            self.world.tcx.mk_ref(inner)
        } else if self.eat("*") {
            let inner = self.unary();
            self.world.tcx.mk_raw(inner)
        } else {
            self.postfix()
        }
    }

    fn postfix(&mut self) -> Ty {
        let mut ty = self.primary();
        while self.eat("[") {
            if self.eat("]") {
                ty = self.world.tcx.mk_array(ty);
            } else {
                let n = self.number();
                self.expect("]");
                ty = self.world.tcx.mk_fixed(ty, n);
            }
        }
        ty
    }

    fn primary(&mut self) -> Ty {
        if self.eat("(") {
            let ty = self.ty();
            self.expect(")");
            return ty;
        }
        if self.eat("{") {
            let fields = self.list("}", |r| {
                let name = r.word();
                r.expect(":");
                (intern(&name), r.ty())
            });
            return self.world.tcx.mk_object(fields);
        }
        if self.eat("[") {
            let parts = self.list("]", |r| r.ty());
            return self.world.tcx.mk_tuple(&parts);
        }
        let name = self.word();
        let common = *self.world.tcx.common();
        let prim = match name.as_str() {
            "bool" => Some(common.bool),
            "i8" => Some(common.i8),
            "i16" => Some(common.i16),
            "i32" | "int" => Some(common.i32),
            "i64" => Some(common.i64),
            "u8" => Some(common.u8),
            "u16" => Some(common.u16),
            "u32" => Some(common.u32),
            "u64" => Some(common.u64),
            "isize" => Some(common.isize),
            "usize" => Some(common.usize),
            "f32" => Some(common.f32),
            "f64" => Some(common.f64),
            "void" => Some(common.void),
            "never" => Some(common.never),
            "string" => Some(common.str),
            _ => None,
        };
        if let Some(prim) = prim {
            return prim;
        }
        if name == "fn" {
            self.expect("(");
            let params = self.list(")", |r| r.ty());
            self.expect("=>");
            let ret = self.ty();
            return self.world.fn_ptr(&params, ret);
        }
        if let Some((_, ty)) = self.scope.iter().rev().find(|(n, _)| *n == name) {
            return *ty;
        }
        let args = if self.eat("<") {
            self.list(">", |r| r.ty())
        } else {
            Vec::new()
        };
        match name.as_str() {
            "Box" => return self.world.tcx.mk_box(args[0]),
            "Slice" => return self.world.tcx.mk_slice(args[0]),
            _ => {}
        }
        let named = self.world.named(&name);
        let TyKind::Adt(adt, _) = self.world.tcx.kind(named) else {
            return named;
        };
        if args.is_empty() {
            named
        } else {
            self.world.tcx.mk_adt(adt, &args)
        }
    }

    // Declarations.

    fn attrs(&mut self) -> Attrs {
        let mut attrs = Attrs::default();
        while self.eat("@") {
            match self.word().as_str() {
                "packed" => attrs.packed = true,
                "align" => {
                    self.expect("(");
                    attrs.align = Some(self.number() as u32);
                    self.expect(")");
                }
                "repr" => {
                    self.expect("(");
                    let Token::Str(name) = self.next() else {
                        panic!("@repr takes a string");
                    };
                    attrs.repr = Some(Repr::from_name(&name).expect("a repr"));
                    self.expect(")");
                }
                other => panic!("no decorator @{other} here"),
            }
        }
        attrs
    }

    fn params(&mut self) -> Vec<String> {
        if self.eat("<") {
            self.list(">", |r| r.word())
        } else {
            Vec::new()
        }
    }

    fn declaration(&mut self) -> Ty {
        let attrs = self.attrs();
        self.keyword("public");
        let mut modifier = ClassModifier::Plain;
        loop {
            match self.word().as_str() {
                "final" => modifier = ClassModifier::Final,
                "abstract" => modifier = ClassModifier::Abstract,
                "class" => return self.class(attrs, modifier),
                "enum" => return self.enumeration(attrs),
                "interface" => {
                    let name = self.word();
                    self.expect("{");
                    self.expect("}");
                    return self.world.interface(&name);
                }
                other => panic!("unexpected `{other}` in {:?}", self.text),
            }
        }
    }

    fn class(&mut self, attrs: Attrs, modifier: ClassModifier) -> Ty {
        let name = self.word();
        let params = self.params();
        let names: Vec<&str> = params.iter().map(String::as_str).collect();
        let (adt, tys) = self.world.class(&name, modifier, attrs, &names);
        self.scope
            .extend(params.iter().cloned().zip(tys.iter().copied()));
        if self.is_word("extends") {
            self.at += 1;
            let base = self.ty();
            self.world.extends(adt, base);
        }
        self.expect("{");
        while !self.eat("}") {
            let vis = self.word();
            assert!(matches!(vis.as_str(), "public" | "private"), "{vis}");
            let mut field = self.word();
            if field == "readonly" {
                field = self.word();
            }
            self.expect(":");
            let ty = self.ty();
            self.expect(";");
            self.world.field(adt, &field, ty);
            if vis == "private"
                && let AdtKind::Class(def) = &mut self.world.tcx.adt_mut(adt).kind
            {
                def.fields.last_mut().expect("the field").vis = Vis::Private;
            }
        }
        self.scope.clear();
        self.world.tcx.adt_identity(adt)
    }

    fn enumeration(&mut self, attrs: Attrs) -> Ty {
        let name = self.word();
        let params = self.params();
        let names: Vec<&str> = params.iter().map(String::as_str).collect();
        let (adt, tys) = self.world.enumeration(&name, &names, attrs.repr, &[]);
        self.scope
            .extend(params.iter().cloned().zip(tys.iter().copied()));
        self.expect("{");
        let cases = self.list("}", |r| {
            let case = r.word();
            let fields = if r.eat("{") {
                r.list("}", |r| {
                    let field = r.word();
                    r.expect(":");
                    (field, r.ty())
                })
            } else {
                Vec::new()
            };
            let value = if r.eat("=") {
                Some(match r.next() {
                    Token::Num(n) => VariantValue::Int(i128::from(n)),
                    Token::Punct("-") => VariantValue::Int(-i128::from(r.number())),
                    Token::Str(text) => VariantValue::Text(r.world.tcx.intern_str(&text)),
                    other => panic!("no case value {other:?}"),
                })
            } else {
                None
            };
            (case, fields, value)
        });
        let cases: Vec<Case<'_>> = cases
            .iter()
            .map(|(case, fields, value)| {
                (
                    case.as_str(),
                    fields.iter().map(|(f, t)| (f.as_str(), *t)).collect(),
                    *value,
                )
            })
            .collect();
        self.world.set_cases(adt, &cases);
        self.scope.clear();
        self.world.tcx.adt_identity(adt)
    }
}

fn match_punct(punct: &str) -> &'static str {
    PUNCT
        .iter()
        .find(|p| **p == punct)
        .copied()
        .unwrap_or_else(|| panic!("no punctuation `{punct}`"))
}
