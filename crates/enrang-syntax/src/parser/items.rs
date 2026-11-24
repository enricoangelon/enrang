//! SPEC 3.1 files and items, and SPEC 3.6 test items: imports, then top-level
//! statements and local functions, then declarations; decorators, visibility,
//! classes, enums, interfaces, aliases, `extend`, `declare function`, `unsafe let`,
//! top-level `const` and `assert`, and the `describe`, `test`, `compileFails` and
//! `compileOk` items.
//!
//! A file whose top level holds no statement but local functions and `assert`s is
//! no program (SPEC 3.1, 6): its unmarked functions and asserts become items, in
//! source order among the others, and its `stmts` stay empty.

use enrang_base::{BytePos, Span};
use enrang_diag::{Code, Diagnostic, Edit, Help};

use super::{Parser, Sig, hints, is_named, recover};
use crate::ast::{
    ArrowBody, Block, ClassDecl, ClassMember, ClassMemberKind, ClassModifier, CompileCase,
    CompileKind, Constructor, CtorParam, DeclareFn, Decorator, DescribeItem, Destructor, EnumDecl,
    EnumField, Expr, ExprKind, ExtendDecl, ExtendMember, FieldDecl, FieldInit, File, FunctionDecl,
    Ident, IfaceField, IfaceMember, Import, ImportKind, ImportName, InterfaceDecl, Item, ItemKind,
    MethodDecl, Param, ParamMark, Receiver, Stmt, StmtKind, StrLit, TestDecl, TestExtra, TestMode,
    TopConst, TypeAlias, TypeExpr, TypeParam, UnsafeLet, Variant, VariantPayload, Visibility,
    WherePred,
};
use crate::token::{Contextual, Keyword, Punct, Reserved, TokenKind};

/// Where the top level of a file has got to: `File = { Import } { TopStmt } { Item }`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
enum Stage {
    Imports,
    Stmts,
    Items,
}

/// The top level of a file as it is read.
struct Top {
    stage: Stage,
    imports: Vec<Import>,
    stmts: Vec<Stmt>,
    items: Vec<Item>,
    /// The local functions among `stmts`, whose diagnostics wait for the end of the
    /// file: only then is it known whether the file is a program.
    local_fns: Vec<LocalFn>,
    /// The first statement and the first item, for EN0110's and EN0115's labels.
    first_stmt: Option<Span>,
    first_item: Option<Span>,
}

/// A local function of the top level, as `Top::local_fns` keeps it.
struct LocalFn {
    /// Its first token, `function` or `unsafe`, where a visibility would go.
    keyword: Span,
    span: Span,
    /// Whether it came after the first item.
    after_item: bool,
}

/// The modifiers before a member's name, each with its token, in the order written.
#[derive(Default)]
struct Modifiers {
    words: Vec<(Keyword, Span)>,
}

impl Modifiers {
    fn has(&self, k: Keyword) -> bool {
        self.words.iter().any(|&(word, _)| word == k)
    }

    /// The receiver mark, `let`, `const` or `move`, if one is written.
    fn receiver(&self) -> Option<Receiver> {
        self.words.iter().find_map(|&(word, _)| match word {
            Keyword::Let => Some(Receiver::Let),
            Keyword::Const => Some(Receiver::Const),
            Keyword::Move => Some(Receiver::Move),
            _ => None,
        })
    }
}

/// Where a modifier stands among the others: SPEC 3.1 writes `MethodDecl`'s as
/// `[ "static" | "abstract" ] [ "override" ] [ "let" | "const" | "move" ]
/// [ "unsafe" ]`, `FieldDecl`'s as `[ "override" ] [ "readonly" ]`, and
/// `IfaceMember`'s as `[ "static" ] [ "let" | "move" ] [ "unsafe" ]`. Ranks rise
/// left to right, and two words of one rank exclude each other. Which words a kind
/// of member takes at all is `reject_modifiers`'s check.
fn modifier_rank(k: Keyword) -> u8 {
    match k {
        Keyword::Static | Keyword::Abstract => 0,
        Keyword::Override => 1,
        Keyword::Readonly | Keyword::Let | Keyword::Const | Keyword::Move => 2,
        _ => 3,
    }
}

/// The words that may modify a class or interface member.
const MODIFIERS: &[Keyword] = &[
    Keyword::Static,
    Keyword::Abstract,
    Keyword::Override,
    Keyword::Let,
    Keyword::Const,
    Keyword::Move,
    Keyword::Unsafe,
    Keyword::Readonly,
];

impl Parser<'_> {
    /// `File = { Import } { TopStmt } { Item }`.
    pub(super) fn parse_file(&mut self) -> File {
        let mut top = Top {
            stage: Stage::Imports,
            imports: Vec::new(),
            stmts: Vec::new(),
            items: Vec::new(),
            local_fns: Vec::new(),
            first_stmt: None,
            first_item: None,
        };
        while !self.at_eof() {
            let before = self.pos;
            self.parse_top(&mut top);
            if self.pos == before {
                self.expected("a declaration or a statement");
                self.bump();
            }
        }
        let Top {
            imports,
            mut stmts,
            mut items,
            local_fns,
            first_item,
            ..
        } = top;
        let program = stmts.iter().any(|stmt| {
            !matches!(
                stmt.kind,
                StmtKind::LocalFn { .. } | StmtKind::Assert { .. }
            )
        });
        for local in local_fns {
            if program && local.after_item {
                self.statement_after_item(local.span, first_item);
            } else if !program {
                // SPEC 3.1: an unmarked function in a file with no statements is a
                // declaration with no visibility, never EN0115.
                self.missing_item_visibility(local.keyword);
            }
        }
        if !program && !stmts.is_empty() {
            let moved: Vec<Item> = stmts.drain(..).filter_map(stmt_to_item).collect();
            items = merge_by_position(items, moved);
        }
        File {
            imports,
            stmts,
            items,
            span: Span {
                lo: self.file.start,
                hi: self.file.end(),
            },
        }
    }

    fn parse_top(&mut self, top: &mut Top) {
        if self.at_import() {
            self.parse_top_import(top);
            return;
        }
        let lo = self.lo();
        let decorators = self.parse_decorators();
        if !decorators.is_empty() && self.at_import() {
            self.decorators_dropped(&decorators, "an `import`");
            self.parse_top_import(top);
            return;
        }
        if self.placement == super::Placement::TestPart && hints::at_lifecycle_hook(self) {
            self.decorators_dropped(&decorators, "a statement");
            hints::lifecycle_hook(self);
            return;
        }
        if self.at_test_item() {
            self.decorators_dropped(&decorators, "a test item");
            let item = self.parse_test_item(false);
            top.first_item.get_or_insert(item.span);
            top.items.push(item);
            top.stage = Stage::Items;
            return;
        }
        if self.at_word(Contextual::Assert) && self.nth_is(1, Punct::LParen) {
            self.decorators_dropped(&decorators, "an `assert`");
            let (cond, message) = self.parse_top_assert();
            let span = self.span_from(lo);
            if top.stage == Stage::Items {
                let id = self.ids.next_id();
                top.items.push(Item {
                    id,
                    decorators: Vec::new(),
                    visibility: None,
                    kind: ItemKind::StaticAssert { cond, message },
                    span,
                });
            } else {
                top.stage = Stage::Stmts;
                top.first_stmt.get_or_insert(span);
                top.stmts
                    .push(self.mk_stmt(StmtKind::Assert { cond, message }, span));
            }
            return;
        }
        hints::async_function(self);
        if self.at_kw(Keyword::Function)
            || (self.at_kw(Keyword::Unsafe) && self.nth_kw(1, Keyword::Function))
        {
            let keyword = self.peek().span;
            let decl = self.parse_function_decl();
            let span = self.span_from(lo);
            top.local_fns.push(LocalFn {
                keyword,
                span,
                after_item: top.stage == Stage::Items,
            });
            // A local function is a `TopStmt` (SPEC 3.1).
            top.first_stmt.get_or_insert(span);
            top.stage = top.stage.max(Stage::Stmts);
            top.stmts
                .push(self.mk_stmt(StmtKind::LocalFn { decorators, decl }, span));
            return;
        }
        // The stage moves only for what is kept: after a mistake that left nothing,
        // such as a stray `;` or a skipped `namespace`, an `import` is in place.
        if self.starts_item() {
            if let Some(item) = self.parse_item(lo, decorators, false) {
                top.first_item.get_or_insert(item.span);
                top.items.push(item);
                top.stage = Stage::Items;
            }
            return;
        }
        self.decorators_dropped(&decorators, "a statement");
        let after_item = top.stage == Stage::Items;
        if let Some(stmt) = self.parse_stmt() {
            if after_item {
                self.statement_after_item(stmt.span, top.first_item);
            }
            top.stage = top.stage.max(Stage::Stmts);
            top.first_stmt.get_or_insert(stmt.span);
            top.stmts.push(stmt);
        }
    }

    /// Whether `import` or `public import` starts here.
    fn at_import(&self) -> bool {
        self.at_kw(Keyword::Import)
            || (self.at_kw(Keyword::Public) && self.nth_kw(1, Keyword::Import))
    }

    /// A top-level `import`, kept in `imports` wherever it stands, with EN0110 after
    /// the first statement or item.
    fn parse_top_import(&mut self, top: &mut Top) {
        let lo = self.lo();
        let import = self.parse_import();
        if top.stage != Stage::Imports {
            let span = self.span_from(lo);
            self.import_after(span, top);
        }
        if let Some(import) = import {
            top.imports.push(import);
        }
    }

    /// EN0110 at an `import` after the first statement or item.
    fn import_after(&mut self, span: Span, top: &Top) {
        let (first, what) = match (top.first_item, top.first_stmt) {
            (Some(item), Some(stmt)) if stmt.lo < item.lo => (stmt, "statement"),
            (Some(item), _) => (item, "declaration"),
            (None, Some(stmt)) => (stmt, "statement"),
            (None, None) => (span, "statement"),
        };
        let mut diag = Diagnostic::new(
            Code::EN0110,
            format!("`import` after a {what}"),
            span,
            "imports go before every statement and declaration",
        );
        if first != span {
            diag = diag.with_secondary(first, format!("the first {what} is here"));
        }
        self.emit(diag.with_help(Help::text("move the import to the top of the file")));
    }

    /// EN0108 at each of `decorators`, written before `place`, which takes none.
    /// They are dropped.
    pub(super) fn decorators_dropped(&mut self, decorators: &[Decorator], place: &str) {
        for decorator in decorators {
            self.emit(Diagnostic::new(
                Code::EN0108,
                format!("a decorator cannot go before {place}"),
                decorator.span,
                "a decorator marks a declaration",
            ));
        }
    }

    /// EN0115 at a top-level statement written after a declaration, the first of
    /// which is at `first_item`.
    fn statement_after_item(&mut self, span: Span, first_item: Option<Span>) {
        let mut diag = Diagnostic::new(
            Code::EN0115,
            "top-level statement after a declaration",
            span,
            "this statement comes after a declaration",
        )
        .note("a file lists its imports, then its statements and local functions, then its classes and other declarations");
        if let Some(first) = first_item {
            diag = diag.with_secondary(first, "the first declaration is here");
        }
        self.emit(diag.with_help(Help::text(
            "move the statement before the first declaration",
        )));
    }

    /// EN0226 at `at`, where a top-level declaration's visibility goes.
    fn missing_item_visibility(&mut self, at: Span) {
        self.emit(
            Diagnostic::new(
                Code::EN0226,
                "this declaration needs `public` or `private`",
                at,
                "no visibility is stated",
            )
            .note("`public` lets other files import it; `private` keeps it to its own module")
            .with_help(Help::suggest(
                "keep it to this module",
                vec![Edit::insert(at.lo, "private ")],
            )),
        );
    }

    /// EN0226 when a member states no visibility (`Visibility`, SPEC 3.1), at the
    /// current token, where it goes. The fix-it writes TypeScript's default,
    /// `public`.
    fn require_visibility(&mut self, visibility: Option<Visibility>) {
        if visibility.is_some() {
            return;
        }
        let at = self.peek().span;
        self.emit(
            Diagnostic::new(
                Code::EN0226,
                "this member needs `public`, `private` or `protected`",
                at,
                "no visibility is stated",
            )
            .with_help(Help::suggest(
                "make it `public`, as TypeScript does",
                vec![Edit::insert(at.lo, "public ")],
            )),
        );
    }

    /// Whether a declaration starts here, after any decorators. A bare `const`,
    /// `let` or `function` is a statement; with a visibility it is an item. The
    /// contextual word `extend` starts one only when `extend [ TypeParams ] Type {`
    /// follows, which [`Parser::extend_ahead`] tries.
    pub(super) fn starts_item(&mut self) -> bool {
        let next = self.nth(1);
        match self.peek().kind {
            TokenKind::Keyword(Keyword::Public | Keyword::Private | Keyword::Protected) => true,
            TokenKind::Reserved(Reserved::Export) => true,
            TokenKind::Keyword(Keyword::Abstract | Keyword::Final) => {
                next.is_keyword(Keyword::Class)
            }
            TokenKind::Keyword(
                Keyword::Class | Keyword::Enum | Keyword::Interface | Keyword::Declare,
            ) => true,
            TokenKind::Keyword(Keyword::Type) => matches!(next.kind, TokenKind::Ident(_)),
            TokenKind::Keyword(Keyword::Unsafe) => next.is_keyword(Keyword::Let),
            TokenKind::Ident(_) if self.at_word(Contextual::Extend) => {
                matches!(
                    next.kind,
                    TokenKind::Ident(_)
                        | TokenKind::Punct(
                            Punct::Lt
                                | Punct::Amp
                                | Punct::AmpAmp
                                | Punct::Star
                                | Punct::StarStar
                                | Punct::At
                                | Punct::LParen
                                | Punct::LBracket
                        )
                        | TokenKind::Keyword(
                            Keyword::Null
                                | Keyword::Void
                                | Keyword::Never
                                | Keyword::Fn
                                | Keyword::Unsafe
                        )
                ) && self.extend_ahead()
            }
            _ => false,
        }
    }

    /// Whether `extend [ TypeParams ] Type "{"` starts at the current `extend`,
    /// tried quietly and undone either way. A contextual word is an identifier
    /// everywhere but the grammar position that names it (SPEC 2), so where no
    /// `ExtendDecl` derives, `extend<i64>(a, b);` and `extend * y;` are statements.
    fn extend_ahead(&mut self) -> bool {
        let cp = self.checkpoint();
        self.speculating += 1;
        self.bump();
        self.parse_type_params();
        self.parse_type();
        let found = self.at(Punct::LBrace) && self.fatal == cp.fatal;
        self.speculating -= 1;
        self.rewind(cp);
        found
    }

    /// An item inside a block, after its EN0109: parsed and dropped.
    pub(super) fn parse_item_in_block(&mut self, lo: BytePos) {
        self.parse_item(lo, Vec::new(), true);
    }

    /// `Item = { Decorator } ItemVis ItemKind | { Decorator } ExtendDecl`. In a
    /// block (`in_block`) a missing visibility is not reported: the item has its
    /// EN0109.
    fn parse_item(
        &mut self,
        lo: BytePos,
        decorators: Vec<Decorator>,
        in_block: bool,
    ) -> Option<Item> {
        let visibility = match self.peek().kind {
            TokenKind::Keyword(Keyword::Public) => {
                self.bump();
                Some(Visibility::Public)
            }
            TokenKind::Keyword(Keyword::Private) => {
                self.bump();
                Some(Visibility::Private)
            }
            TokenKind::Keyword(Keyword::Protected) => {
                let span = self.bump().span;
                self.unexpected(
                    span,
                    "expected `public` or `private`, found `protected`",
                    "only a class member can be `protected`",
                );
                Some(Visibility::Protected)
            }
            // In a block the item has its EN0109, and `export` says nothing more.
            TokenKind::Reserved(Reserved::Export) if in_block => {
                self.bump();
                Some(Visibility::Public)
            }
            TokenKind::Reserved(Reserved::Export) => match hints::item_word(self) {
                Some(hints::ItemWord::Visibility(visibility)) => Some(visibility),
                Some(hints::ItemWord::Skipped) | None => return None,
            },
            _ => {
                if !self.at_word(Contextual::Extend) && !in_block {
                    let at = self.peek().span;
                    self.missing_item_visibility(at);
                }
                None
            }
        };
        hints::async_function(self);
        let token = self.peek();
        let kind = match token.kind {
            TokenKind::Keyword(Keyword::Function) => ItemKind::Function(self.parse_function_decl()),
            TokenKind::Keyword(Keyword::Unsafe) if self.nth_kw(1, Keyword::Function) => {
                ItemKind::Function(self.parse_function_decl())
            }
            TokenKind::Keyword(Keyword::Unsafe) if self.nth_kw(1, Keyword::Let) => {
                ItemKind::UnsafeLet(self.parse_unsafe_let())
            }
            TokenKind::Keyword(Keyword::Abstract | Keyword::Final | Keyword::Class) => {
                ItemKind::Class(self.parse_class())
            }
            TokenKind::Keyword(Keyword::Enum) => ItemKind::Enum(self.parse_enum()),
            TokenKind::Keyword(Keyword::Interface) => ItemKind::Interface(self.parse_interface()),
            TokenKind::Keyword(Keyword::Type) => ItemKind::TypeAlias(self.parse_type_alias()),
            TokenKind::Keyword(Keyword::Const) => ItemKind::TopConst(self.parse_top_const()),
            TokenKind::Keyword(Keyword::Declare) => ItemKind::DeclareFn(self.parse_declare_fn()),
            TokenKind::Ident(_) if self.at_word(Contextual::Extend) => {
                ItemKind::Extend(self.parse_extend())
            }
            TokenKind::Reserved(Reserved::Namespace) => {
                hints::namespace(self);
                return None;
            }
            _ => {
                self.expected("a declaration");
                recover::skip_to_item(self);
                return None;
            }
        };
        let id = self.ids.next_id();
        Some(Item {
            id,
            decorators,
            visibility,
            kind,
            span: self.span_from(lo),
        })
    }

    /// `Import = [ "public" ] "import" ( "{" ImportName % "," "}" | "*" "as" Ident )
    /// "from" StringLit ";"`.
    pub(super) fn parse_import(&mut self) -> Option<Import> {
        let lo = self.lo();
        let public = self.eat_kw(Keyword::Public);
        self.bump();
        let kind = if self.eat(Punct::LBrace) {
            ImportKind::Named(self.comma_list(Punct::RBrace, |p| {
                let name = p.ident()?;
                let alias = if p.eat_kw(Keyword::As) {
                    p.ident()
                } else {
                    None
                };
                Some(ImportName { name, alias })
            }))
        } else if self.eat(Punct::Star) {
            self.expect_kw(Keyword::As);
            ImportKind::Namespace(self.ident_or_error())
        } else {
            // A default import, a side-effect import, `import x = require(...)` and
            // `import type`, to its `;` or the end of its line.
            recover::skip_line(self);
            let span = self.span_from(lo);
            hints::report_deferred(self, Code::EN1009, span, "not a named import");
            return None;
        };
        if !self.at_word(Contextual::From) {
            self.expected("`from`");
            recover::skip_stmt(self);
            return None;
        }
        self.bump();
        let Some(path) = self.parse_str_lit() else {
            recover::skip_stmt(self);
            return None;
        };
        recover::expect_semi(self);
        Some(Import {
            public,
            kind,
            path,
            span: self.span_from(lo),
        })
    }

    /// `{ Decorator }`, where `Decorator = "@" Ident [ "(" DecoratorArg % "," ")" ]`.
    pub(super) fn parse_decorators(&mut self) -> Vec<Decorator> {
        let mut decorators = Vec::new();
        while self.at(Punct::At) {
            let lo = self.lo();
            self.bump();
            let name = self.ident_or_error();
            let args = if self.eat(Punct::LParen) {
                Some(self.comma_list(Punct::RParen, |p| p.parse_decorator_arg()))
            } else {
                None
            };
            decorators.push(Decorator {
                name,
                args,
                span: self.span_from(lo),
            });
        }
        decorators
    }

    /// `DecoratorArg = Literal | ObjectLit | Ident`, where the object literal holds
    /// literals and arrays of literals; `-` before a number, and an array of literals,
    /// are taken too. `...` is no spread here (EN1013).
    fn parse_decorator_arg(&mut self) -> Option<Expr> {
        if !self.enter() {
            return None;
        }
        let arg = self.parse_decorator_arg_inner();
        self.leave();
        arg
    }

    fn parse_decorator_arg_inner(&mut self) -> Option<Expr> {
        let lo = self.lo();
        let token = self.peek();
        match token.kind {
            TokenKind::Int { .. }
            | TokenKind::Float(_)
            | TokenKind::Str(_)
            | TokenKind::NoSubTemplate(_)
            | TokenKind::TemplateHead(_)
            | TokenKind::RawTemplate(_)
            | TokenKind::Ident(_)
            | TokenKind::Keyword(Keyword::True | Keyword::False | Keyword::Null) => {
                Some(self.parse_primary())
            }
            TokenKind::Punct(Punct::Minus)
                if matches!(
                    self.nth(1).kind,
                    TokenKind::Int { .. } | TokenKind::Float(_)
                ) =>
            {
                self.bump();
                let number = self.parse_primary();
                let span = self.span_from(lo);
                Some(self.mk_expr(
                    ExprKind::Unary(crate::ast::UnOp::Neg, Box::new(number)),
                    span,
                ))
            }
            TokenKind::Punct(Punct::LBrace) => {
                self.bump();
                let fields = self.comma_list(Punct::RBrace, |p| {
                    if p.at(Punct::DotDotDot) {
                        hints::spread_outside_array(p);
                    }
                    let field_lo = p.lo();
                    let name = p.member_name()?;
                    let value = if p.eat(Punct::Colon) {
                        p.parse_decorator_arg()
                    } else {
                        None
                    };
                    Some(FieldInit {
                        name,
                        value,
                        span: p.span_from(field_lo),
                    })
                });
                let span = self.span_from(lo);
                Some(self.mk_expr(ExprKind::ObjectLit(fields), span))
            }
            TokenKind::Punct(Punct::LBracket) => {
                self.bump();
                let elems = self.comma_list(Punct::RBracket, |p| {
                    if p.at(Punct::DotDotDot) {
                        hints::spread_outside_array(p);
                    }
                    p.parse_decorator_arg().map(crate::ast::ArrayElem::Item)
                });
                let span = self.span_from(lo);
                Some(self.mk_expr(ExprKind::Array(elems), span))
            }
            _ => {
                self.expected("a literal, a name or an object literal");
                None
            }
        }
    }

    /// `FunctionDecl = [ "unsafe" ] "function" Ident [ TypeParams ] "(" Param % ","
    /// ")" [ ":" RetType ] Block`; a library module may name it with any `MemberName`.
    pub(super) fn parse_function_decl(&mut self) -> FunctionDecl {
        let lo = self.lo();
        let is_unsafe = self.eat_kw(Keyword::Unsafe);
        self.expect_kw(Keyword::Function);
        hints::generator_star(self);
        let name = self.function_name();
        if !self.at(Punct::Lt) && !self.at(Punct::LParen) {
            // The header lost its `(`: the rest of it and the body go as one bad
            // item, so none of it is read again as a statement (ARCHITECTURE 4).
            self.expected("`(`");
            recover::skip_to_item(self);
            let end = self.prev_hi();
            return FunctionDecl {
                is_unsafe,
                name,
                type_params: Vec::new(),
                params: Vec::new(),
                ret: None,
                body: Block {
                    stmts: Vec::new(),
                    span: Span { lo: end, hi: end },
                },
                span: self.span_from(lo),
            };
        }
        let (type_params, params) = self.parse_signature(name.span.hi);
        let ret = self.eat(Punct::Colon).then(|| self.parse_ret_type());
        self.where_on_function();
        let body = self.parse_fn_body();
        FunctionDecl {
            is_unsafe,
            name,
            type_params,
            params,
            ret,
            body,
            span: self.span_from(lo),
        }
    }

    /// A `where` clause after a function's result, which SPEC 3.1 gives only to a
    /// method, for its class's type parameters: EN0100 at `where`, with a help that
    /// moves each bound onto its type parameter, and the clause read, so the body
    /// still parses and nothing after it is reported (one mistake, one diagnostic).
    fn where_on_function(&mut self) {
        if !self.at_word(Contextual::Where) {
            return;
        }
        let at = self.peek().span;
        let preds = self.parse_where();
        let moved: Vec<String> = preds
            .iter()
            .map(|pred| {
                let bounds: Vec<&str> = pred.bounds.iter().map(|b| self.text(b.span)).collect();
                format!("{} extends {}", pred.param.name, bounds.join(" & "))
            })
            .collect();
        let (bound, parameter) = match moved.len() {
            1 => ("bound", "type parameter"),
            _ => ("bounds", "type parameters"),
        };
        self.emit(
            Diagnostic::new(
                Code::EN0100,
                "expected `{`, found `where`",
                at,
                "a function's bounds go on its type parameters",
            )
            .note(
                "a `where` clause belongs to a method, and bounds the type parameters of its class",
            )
            .with_help(Help::text(format!(
                "move the {bound} onto the {parameter}: `<{}>`",
                moved.join(", ")
            ))),
        );
    }

    /// A function's name: an identifier, or in a library module any `MemberName`
    /// (SPEC 3.1). Elsewhere a keyword or reserved word, `match` or `delete`, is
    /// EN0100 and still taken as the name, so the signature and body after it parse
    /// as written.
    fn function_name(&mut self) -> Ident {
        let token = self.peek();
        let Some(name) = super::word(token) else {
            self.expected("an identifier");
            return self.error_ident();
        };
        if !self.library && !matches!(token.kind, TokenKind::Ident(_)) {
            self.expected("an identifier");
        }
        self.bump();
        Ident {
            name,
            span: token.span,
        }
    }

    /// `[ TypeParams ] "(" Param % "," ")"` of a function or method named up to
    /// `name_hi`, which EN0205's fix-it reads.
    fn parse_signature(&mut self, name_hi: BytePos) -> (Vec<TypeParam>, Vec<Param>) {
        let angle = self.at(Punct::Lt);
        let type_params = self.parse_type_params();
        let angle = angle.then(|| {
            let last = self.tokens[self.pos.saturating_sub(1)];
            let (close, before) = if last.is(Punct::Gt) {
                (last.span.lo, self.tokens[self.pos.saturating_sub(2)])
            } else {
                (self.prev_hi(), last)
            };
            let insert = if type_params.is_empty() {
                "T"
            } else if before.is(Punct::Comma) {
                " T"
            } else {
                ", T"
            };
            (close, insert)
        });
        let saved = self.sig.replace(Sig { name_hi, angle });
        let params = self.parse_params();
        self.sig = saved;
        (type_params, params)
    }

    /// `"(" Param % "," ")"`. A parameter with neither a default nor `?` after one
    /// with either is EN0229.
    pub(super) fn parse_params(&mut self) -> Vec<Param> {
        if !self.expect(Punct::LParen) {
            return Vec::new();
        }
        let params = self.comma_list(Punct::RParen, |p| p.parse_param());
        let defaults: Vec<(Span, bool)> = params
            .iter()
            .map(|param| (param.span, param.optional || param.default.is_some()))
            .collect();
        self.check_defaults(&defaults);
        params
    }

    /// EN0229 at each parameter of `params`, `(span, has a default or ?)`, that has
    /// neither after one that has either (SPEC 3.1, 4.14).
    fn check_defaults(&mut self, params: &[(Span, bool)]) {
        let mut earlier: Option<Span> = None;
        for &(span, defaulted) in params {
            if defaulted {
                earlier = Some(span);
                continue;
            }
            let Some(earlier) = earlier else {
                continue;
            };
            let name = param_name(self.text(span));
            let before = param_name(self.text(earlier));
            self.emit(
                Diagnostic::new(
                    Code::EN0229,
                    format!("`{name}` has no default, so it can't follow `{before}`, which has one"),
                    span,
                    "no default here",
                )
                .with_secondary(earlier, format!("`{before}` has a default"))
                .note("only the last parameters may have defaults, because there is no `undefined` to skip one")
                .with_help(Help::text(format!(
                    "give `{name}` a default, or move it before `{before}`"
                ))),
            );
        }
    }

    /// EN0227 at `eq`, the `=` of a parameter or field that also has the `?` at
    /// `question`.
    fn optional_with_default(&mut self, question: Span, eq: Span, what: &str) {
        self.emit(
            Diagnostic::new(
                Code::EN0227,
                format!("a {what} with `?` cannot also have a default"),
                eq,
                "this default",
            )
            .with_secondary(question, "`?` already gives it the default `null`")
            .with_help(Help::suggest(
                "remove the `?`",
                vec![Edit::delete(question)],
            )),
        );
    }

    /// `Param = [ "let" | "const" ] Binding [ "?" ] ":" ParamType [ "=" Expr ]`.
    fn parse_param(&mut self) -> Option<Param> {
        let decorators = self.parse_decorators();
        self.decorators_dropped(&decorators, "a parameter");
        if self.at(Punct::DotDotDot) {
            hints::spread_outside_array(self);
        }
        let lo = self.lo();
        let mark = if self.eat_kw(Keyword::Let) {
            ParamMark::Let
        } else if self.eat_kw(Keyword::Const) {
            ParamMark::Const
        } else {
            ParamMark::Plain
        };
        let binding = self.parse_binding();
        let question = self.peek().span;
        let optional = self.eat(Punct::Question);
        let ty = if self.expect(Punct::Colon) {
            let saved = self.param_ty.replace(self.lo());
            let ty = self.parse_type();
            self.param_ty = saved;
            ty
        } else {
            self.error_ty()
        };
        let eq = self.peek().span;
        let default = self.eat(Punct::Eq).then(|| self.parse_expr());
        if optional && default.is_some() {
            self.optional_with_default(question, eq, "parameter");
        }
        Some(Param {
            mark,
            binding,
            optional,
            ty,
            default,
            span: self.span_from(lo),
        })
    }

    /// `[ TypeParams ]`, where `TypeParams = "<" TypeParam % "," ">"` and
    /// `TypeParam = Ident [ "extends" Bound { "&" Bound } ]`.
    pub(super) fn parse_type_params(&mut self) -> Vec<TypeParam> {
        if !self.eat(Punct::Lt) {
            return Vec::new();
        }
        let mut params = Vec::new();
        loop {
            if self.eat_closing_angle() || self.at_eof() {
                break;
            }
            if matches!(self.peek().kind, TokenKind::Lifetime(_)) {
                hints::lifetime(self);
                if self.eat(Punct::Comma) {
                    continue;
                }
                self.eat_closing_angle();
                break;
            }
            let Some(name) = self.ident() else {
                recover::skip_until(self, &[Punct::Comma, Punct::Gt]);
                if self.eat(Punct::Comma) {
                    continue;
                }
                self.eat_closing_angle();
                break;
            };
            let bounds = if self.at_word(Contextual::Extends) {
                self.bump();
                self.parse_bounds()
            } else {
                Vec::new()
            };
            params.push(TypeParam { name, bounds });
            if self.eat(Punct::Comma) {
                continue;
            }
            if !self.eat_closing_angle() {
                // TypeScript's `<T = string>`: one EN0100, and the rest of this
                // parameter skipped, so the header after the list parses as written.
                self.expected("`,` or `>`");
                self.skip_type_param_rest();
                if self.eat(Punct::Comma) {
                    continue;
                }
                self.eat_closing_angle();
            }
            break;
        }
        params
    }

    /// Skips the rest of a bad type parameter: to the list's next `,` or its closing
    /// `>`, which it leaves for the caller, past the angle brackets and groups that
    /// nest in between, as in `<T = Map<K, V>>`. It stops without consuming at a
    /// `(`, `{` or `;` outside any angle bracket, where the list must have ended, and
    /// at a closer it did not open, or at the end of the file.
    fn skip_type_param_rest(&mut self) {
        let mut angles = 0usize;
        loop {
            match self.peek().kind {
                TokenKind::Eof
                | TokenKind::Punct(Punct::RParen | Punct::RBracket | Punct::RBrace) => return,
                TokenKind::Punct(Punct::Comma) if angles == 0 => return,
                TokenKind::Punct(Punct::LParen | Punct::LBrace | Punct::Semi) if angles == 0 => {
                    return;
                }
                TokenKind::Punct(
                    Punct::Gt | Punct::Shr | Punct::Shr3 | Punct::Ge | Punct::ShrEq,
                ) if angles == 0 => {
                    return;
                }
                TokenKind::Punct(Punct::Shr | Punct::Shr3 | Punct::Ge | Punct::ShrEq) => {
                    if !self.split_current() {
                        self.bump();
                    }
                }
                TokenKind::Punct(Punct::Gt) => {
                    angles -= 1;
                    self.bump();
                }
                TokenKind::Punct(Punct::Lt) => {
                    angles += 1;
                    self.bump();
                }
                TokenKind::Punct(Punct::LParen | Punct::LBracket | Punct::LBrace) => {
                    recover::skip_group(self);
                }
                _ => {
                    self.bump();
                }
            }
        }
    }

    /// `Bound { "&" Bound }`, each a `NamedType`.
    fn parse_bounds(&mut self) -> Vec<TypeExpr> {
        let mut bounds = vec![self.parse_named_type(false)];
        while self.eat(Punct::Amp) {
            bounds.push(self.parse_named_type(false));
        }
        bounds
    }

    /// `[ WhereClause ]`, where `WhereClause = "where" WherePred { "," WherePred }`.
    fn parse_where(&mut self) -> Vec<WherePred> {
        if !self.at_word(Contextual::Where) {
            return Vec::new();
        }
        self.bump();
        let mut preds = Vec::new();
        loop {
            let param = self.ident_or_error();
            if self.at_word(Contextual::Extends) {
                self.bump();
            } else {
                self.expected("`extends`");
            }
            let bounds = self.parse_bounds();
            preds.push(WherePred { param, bounds });
            if !self.eat(Punct::Comma) {
                break;
            }
        }
        preds
    }

    /// `TopConst = "const" Ident [ ":" Type ] "=" ConstExpr ";"`.
    fn parse_top_const(&mut self) -> TopConst {
        self.bump();
        let name = self.ident_or_error();
        let ty = self.eat(Punct::Colon).then(|| self.parse_type());
        let value = if self.eat(Punct::Eq) {
            self.parse_expr()
        } else {
            self.const_without_value(&crate::ast::Binding::Name(name));
            self.error_expr()
        };
        recover::expect_semi(self);
        TopConst { name, ty, value }
    }

    /// `UnsafeLet = "unsafe" "let" Ident ":" Type [ "=" ConstExpr ] ";"`.
    fn parse_unsafe_let(&mut self) -> UnsafeLet {
        self.bump();
        self.bump();
        let name = self.ident_or_error();
        let ty = if self.expect(Punct::Colon) {
            self.parse_type()
        } else {
            self.error_ty()
        };
        let value = self.eat(Punct::Eq).then(|| self.parse_expr());
        recover::expect_semi(self);
        UnsafeLet { name, ty, value }
    }

    /// `DeclareFn = "declare" "function" Ident [ TypeParams ] "(" Param % "," ")"
    /// [ ":" Type ] ";"`.
    fn parse_declare_fn(&mut self) -> DeclareFn {
        let lo = self.lo();
        self.bump();
        if !self.expect_kw(Keyword::Function) {
            // TypeScript's `declare module "x" {}`: the rest goes as one bad item, so
            // none of it is read again as a function (ARCHITECTURE 4).
            let name = self.error_ident();
            recover::skip_to_item(self);
            return DeclareFn {
                name,
                type_params: Vec::new(),
                params: Vec::new(),
                ret: None,
                span: self.span_from(lo),
            };
        }
        let name = self.ident_or_error();
        let (type_params, params) = self.parse_signature(name.span.hi);
        let ret = self.eat(Punct::Colon).then(|| self.parse_type());
        let span = self.span_from(lo);
        recover::expect_semi(self);
        DeclareFn {
            name,
            type_params,
            params,
            ret,
            span,
        }
    }

    /// `TopAssert = "assert" "(" Expr [ "," StringLit ] [ "," ] ")" ";"`.
    fn parse_top_assert(&mut self) -> (Expr, Option<StrLit>) {
        self.bump();
        self.bump();
        let cond = self.parse_expr();
        let mut message = None;
        if self.eat(Punct::Comma) && matches!(self.peek().kind, TokenKind::Str(_)) {
            message = self.parse_str_lit();
            self.eat(Punct::Comma);
        }
        self.expect(Punct::RParen);
        recover::expect_semi(self);
        (cond, message)
    }

    /// `ClassDecl = [ "abstract" | "final" ] "class" Ident [ TypeParams ]
    /// [ "extends" NamedType ] [ "implements" NamedType { "," NamedType } ]
    /// "{" { ClassMember } "}"`.
    fn parse_class(&mut self) -> ClassDecl {
        let lo = self.lo();
        let modifier = if self.eat_kw(Keyword::Abstract) {
            ClassModifier::Abstract
        } else if self.eat_kw(Keyword::Final) {
            ClassModifier::Final
        } else {
            ClassModifier::Plain
        };
        self.expect_kw(Keyword::Class);
        let name = self.ident_or_error();
        let type_params = self.parse_type_params();
        let extends = if self.at_word(Contextual::Extends) {
            self.bump();
            let base = self.parse_named_type(false);
            while self.at(Punct::Comma) {
                let span = self.bump().span;
                self.unexpected(
                    span,
                    "expected `implements` or `{`, found `,`",
                    "a class extends one class",
                );
                self.parse_named_type(false);
            }
            Some(base)
        } else {
            None
        };
        let mut implements = Vec::new();
        if self.eat_kw(Keyword::Implements) {
            implements.push(self.parse_named_type(false));
            while self.eat(Punct::Comma) {
                implements.push(self.parse_named_type(false));
            }
        }
        let members = self.parse_members(|p| p.parse_class_member());
        ClassDecl {
            modifier,
            name,
            type_params,
            extends,
            implements,
            members,
            span: self.span_from(lo),
        }
    }

    /// `"{" { member } "}"`, each member parsed by `member`, which consumes at least
    /// one token or is skipped past.
    fn parse_members<T>(&mut self, mut member: impl FnMut(&mut Self) -> Option<T>) -> Vec<T> {
        let mut members = Vec::new();
        if !self.expect(Punct::LBrace) {
            return members;
        }
        while !self.at(Punct::RBrace) && !self.at_eof() {
            let before = self.pos;
            if let Some(m) = member(self) {
                members.push(m);
            }
            if self.pos == before {
                self.expected("a member");
                recover::skip_stmt(self);
                if self.pos == before {
                    self.bump();
                }
            }
        }
        self.expect(Punct::RBrace);
        members
    }

    /// `ClassMember = { Decorator } ( FieldDecl | Constructor | Destructor |
    /// MethodDecl )`.
    fn parse_class_member(&mut self) -> Option<ClassMember> {
        let lo = self.lo();
        let decorators = self.parse_decorators();
        let decl_lo = self.lo();
        let visibility = self.parse_visibility();
        self.require_visibility(visibility);
        let kind = if self.at_kw(Keyword::Constructor) && self.nth_is(1, Punct::LParen) {
            ClassMemberKind::Constructor(self.parse_constructor(visibility))
        } else if self.at_kw(Keyword::Destructor) && self.nth_is(1, Punct::LParen) {
            ClassMemberKind::Destructor(self.parse_destructor(visibility))
        } else {
            let modifiers = self.parse_modifiers();
            self.member_habits();
            let Some(name) = self.member_name() else {
                recover::skip_stmt(self);
                return None;
            };
            let name = self.setter(name);
            if self.operator_method(&name) {
                self.parse_method(decl_lo, visibility, &modifiers, name);
                return None;
            }
            let field_start = self.at(Punct::Question)
                || self.at(Punct::Colon)
                || (self.at(Punct::Eq) && modifiers.has(Keyword::Static));
            if self.at(Punct::LParen) || self.at(Punct::Lt) {
                ClassMemberKind::Method(self.parse_method(decl_lo, visibility, &modifiers, name))
            } else if field_start {
                ClassMemberKind::Field(self.parse_field(visibility, &modifiers, name))
            } else {
                self.expected("`(` or `:`");
                recover::skip_stmt(self);
                return None;
            }
        };
        Some(ClassMember {
            decorators,
            kind,
            span: self.span_from(lo),
        })
    }

    /// TypeScript words before a member's name: `async` (EN1001) and the `*` of a
    /// generator method (EN1002), each skipped.
    fn member_habits(&mut self) {
        let token = self.peek();
        if token.kind == TokenKind::Reserved(Reserved::Async) && super::word(self.nth(1)).is_some()
        {
            self.bump();
            hints::report_deferred(self, Code::EN1001, token.span, "an async method");
        }
        if self.at(Punct::Star) && super::word(self.nth(1)).is_some() {
            hints::generator_star(self);
        }
    }

    /// `set x(v)`: EN1017 at `set`, and the method takes the name after it. A
    /// getter, `get x()`, is EN0100 (`get` is an ordinary name, SPEC 3.4), with a
    /// fix-it that makes it the method it can be.
    fn setter(&mut self, name: crate::ast::Ident) -> crate::ast::Ident {
        let word = name.name.as_str();
        if !matches!(word, "set" | "get")
            || super::word(self.peek()).is_none()
            || !self.nth_is(1, Punct::LParen)
        {
            return name;
        }
        let Some(real) = self.member_name() else {
            return name;
        };
        if word == "set" {
            hints::report_deferred(self, Code::EN1017, name.span.to(real.span), "a setter");
        } else {
            let span = self.with_trailing_space(name.span);
            self.emit(
                Diagnostic::new(
                    Code::EN0100,
                    "getters do not exist in Enrang",
                    name.span.to(real.span),
                    format!("write a method named `{}`", real.name),
                )
                .with_help(Help::suggest("make it a method", vec![Edit::delete(span)])),
            );
        }
        real
    }

    /// `operator +(o: V): V`: EN1018 at `operator` and its punctuator, which is
    /// skipped; the method is parsed and dropped.
    fn operator_method(&mut self, name: &crate::ast::Ident) -> bool {
        if name.name.as_str() != "operator" || !matches!(self.peek().kind, TokenKind::Punct(_)) {
            return false;
        }
        if self.at(Punct::LParen) || self.at(Punct::Lt) || !self.nth_is(1, Punct::LParen) {
            return false;
        }
        let punct = self.bump();
        hints::report_deferred(
            self,
            Code::EN1018,
            name.span.to(punct.span),
            "an operator method",
        );
        true
    }

    fn parse_visibility(&mut self) -> Option<Visibility> {
        let visibility = match self.peek().kind {
            TokenKind::Keyword(Keyword::Public) => Visibility::Public,
            TokenKind::Keyword(Keyword::Private) => Visibility::Private,
            TokenKind::Keyword(Keyword::Protected) => Visibility::Protected,
            _ => return None,
        };
        self.bump();
        Some(visibility)
    }

    /// The modifiers before a member's name. A modifier word is one only when a
    /// `MemberName` follows it, so `public move(): void` is a method named `move`
    /// (SPEC 3.4). SPEC 3.1 fixes their order (see [`modifier_rank`]); a word out
    /// of order, written twice, or beside another of its rank is EN0100.
    fn parse_modifiers(&mut self) -> Modifiers {
        let mut modifiers = Modifiers::default();
        while let TokenKind::Keyword(k) = self.peek().kind
            && MODIFIERS.contains(&k)
            && super::word(self.nth(1)).is_some()
        {
            let span = self.bump().span;
            if let Some(&(last, _)) = modifiers.words.last() {
                let (word, before) = (k.as_str(), last.as_str());
                if k == last {
                    self.unexpected(
                        span,
                        format!("`{word}` is written twice"),
                        "already written before",
                    );
                } else if modifier_rank(k) == modifier_rank(last) {
                    self.unexpected(
                        span,
                        format!("`{before}` and `{word}` cannot both modify a member"),
                        format!("remove `{word}` or `{before}`"),
                    );
                } else if modifier_rank(k) < modifier_rank(last) {
                    self.unexpected(
                        span,
                        format!("`{word}` goes before `{before}`"),
                        "out of order",
                    );
                }
            }
            modifiers.words.push((k, span));
        }
        modifiers
    }

    /// EN0100 at each modifier of `modifiers` that is not in `allowed`.
    fn reject_modifiers(&mut self, modifiers: &Modifiers, allowed: &[Keyword], place: &str) {
        for &(word, span) in &modifiers.words {
            if !allowed.contains(&word) {
                self.unexpected(
                    span,
                    format!("`{}` cannot modify {place}", word.as_str()),
                    "not allowed here",
                );
            }
        }
    }

    /// The rest of `MethodDecl` after its name: `[ TypeParams ] "(" Param % "," ")"
    /// [ ":" RetType ] [ WhereClause ] ( Block | ";" )`.
    fn parse_method(
        &mut self,
        lo: BytePos,
        visibility: Option<Visibility>,
        modifiers: &Modifiers,
        name: crate::ast::Ident,
    ) -> MethodDecl {
        self.reject_modifiers(
            modifiers,
            &[
                Keyword::Static,
                Keyword::Abstract,
                Keyword::Override,
                Keyword::Let,
                Keyword::Const,
                Keyword::Move,
                Keyword::Unsafe,
            ],
            "a method",
        );
        let is_static = modifiers.has(Keyword::Static);
        let is_abstract = modifiers.has(Keyword::Abstract);
        let receiver = match (is_static, modifiers.receiver()) {
            (true, Some(_)) => {
                // SPEC 3.1 allows `static let m()`, which the tree cannot hold (plan
                // 0.1 item 18).
                self.unexpected(
                    name.span,
                    "a `static` method has no `this` to mark with `let`, `const` or `move`",
                    "this method",
                );
                Receiver::Static
            }
            (true, None) => Receiver::Static,
            (false, Some(receiver)) => receiver,
            (false, None) => Receiver::Plain,
        };
        let (type_params, params) = self.parse_signature(name.span.hi);
        let ret = self.eat(Punct::Colon).then(|| self.parse_ret_type());
        let where_clause = self.parse_where();
        // `;` in place of the body is sema's to judge (EN0806).
        let body = if self.at(Punct::LBrace) {
            Some(self.parse_fn_body())
        } else {
            if !self.eat(Punct::Semi) {
                self.expected("`{` or `;`");
            }
            None
        };
        MethodDecl {
            visibility,
            is_abstract,
            is_override: modifiers.has(Keyword::Override),
            receiver,
            is_unsafe: modifiers.has(Keyword::Unsafe),
            name,
            type_params,
            params,
            ret,
            where_clause,
            body,
            span: self.span_from(lo),
        }
    }

    /// The rest of `FieldDecl` after its name: `[ "?" ] ":" FieldType [ "=" Expr ]
    /// ";"`.
    fn parse_field(
        &mut self,
        visibility: Option<Visibility>,
        modifiers: &Modifiers,
        name: crate::ast::Ident,
    ) -> FieldDecl {
        // `static` is EN1021, and dropped.
        let mut kept = Modifiers::default();
        for &(word, span) in &modifiers.words {
            if word == Keyword::Static {
                hints::report_deferred(self, Code::EN1021, span, "a static field");
            } else {
                kept.words.push((word, span));
            }
        }
        self.reject_modifiers(&kept, &[Keyword::Override, Keyword::Readonly], "a field");
        let question = self.peek().span;
        let optional = self.eat(Punct::Question);
        let ty = if self.eat(Punct::Colon) {
            self.parse_field_type()
        } else {
            if !(modifiers.has(Keyword::Static) && self.at(Punct::Eq)) {
                self.expected("`:`");
            }
            self.error_ty()
        };
        let eq = self.peek().span;
        let default = self.eat(Punct::Eq).then(|| self.parse_expr());
        if optional && default.is_some() {
            self.optional_with_default(question, eq, "field");
        }
        recover::expect_semi(self);
        FieldDecl {
            visibility,
            is_override: modifiers.has(Keyword::Override),
            is_readonly: modifiers.has(Keyword::Readonly),
            name,
            optional,
            ty,
            default,
        }
    }

    /// `Constructor = Visibility "constructor" "(" CtorParam % "," ")" Block`.
    fn parse_constructor(&mut self, visibility: Option<Visibility>) -> Constructor {
        self.bump();
        self.bump();
        let params = self.comma_list(Punct::RParen, |p| p.parse_ctor_param());
        let defaults: Vec<(Span, bool)> = params
            .iter()
            .map(|param| (param.span, param.optional || param.default.is_some()))
            .collect();
        self.check_defaults(&defaults);
        let body = self.parse_fn_body();
        Constructor {
            visibility,
            params,
            body,
        }
    }

    /// `CtorParam = [ Visibility [ "readonly" ] ] [ "let" | "const" ] Ident [ "?" ]
    /// ":" FieldType [ "=" Expr ]`.
    fn parse_ctor_param(&mut self) -> Option<CtorParam> {
        let decorators = self.parse_decorators();
        self.decorators_dropped(&decorators, "a parameter");
        if self.at(Punct::DotDotDot) {
            hints::spread_outside_array(self);
        }
        let lo = self.lo();
        let property = self.parse_visibility();
        let is_readonly = self.at_kw(Keyword::Readonly);
        if is_readonly {
            let span = self.bump().span;
            if property.is_none() {
                hints::readonly_parameter(self, span);
            }
        }
        let mark = if self.eat_kw(Keyword::Let) {
            ParamMark::Let
        } else if self.eat_kw(Keyword::Const) {
            ParamMark::Const
        } else {
            ParamMark::Plain
        };
        let name = self.ident()?;
        let question = self.peek().span;
        let optional = self.eat(Punct::Question);
        // Only a parameter that is a field takes a field's type, `readonly` and all.
        let ty = if !self.expect(Punct::Colon) {
            self.error_ty()
        } else if property.is_some() {
            self.parse_field_type()
        } else {
            self.parse_type()
        };
        let eq = self.peek().span;
        let default = self.eat(Punct::Eq).then(|| self.parse_expr());
        if optional && default.is_some() {
            self.optional_with_default(question, eq, "parameter");
        }
        Some(CtorParam {
            property,
            is_readonly: is_readonly && property.is_some(),
            mark,
            name,
            optional,
            ty,
            default,
            span: self.span_from(lo),
        })
    }

    /// `Destructor = "public" "destructor" "(" ")" Block`.
    fn parse_destructor(&mut self, visibility: Option<Visibility>) -> Destructor {
        let keyword = self.bump().span;
        if matches!(
            visibility,
            Some(Visibility::Private | Visibility::Protected)
        ) {
            self.unexpected(
                keyword,
                "a destructor is always `public`",
                "this destructor",
            );
        }
        self.bump();
        if !self.at(Punct::RParen) {
            self.expected("`)`: a destructor takes no parameters");
            recover::skip_until(self, &[Punct::RParen]);
        }
        self.expect(Punct::RParen);
        let body = self.parse_fn_body();
        Destructor { visibility, body }
    }

    /// `EnumDecl = "enum" Ident [ TypeParams ] "{" Variant % "," [ ";" { MethodDecl } ]
    /// "}"`.
    fn parse_enum(&mut self) -> EnumDecl {
        let lo = self.lo();
        self.bump();
        let name = self.ident_or_error();
        let type_params = self.parse_type_params();
        let mut variants = Vec::new();
        let mut methods = Vec::new();
        if self.expect(Punct::LBrace) {
            loop {
                if self.at(Punct::RBrace) || self.at(Punct::Semi) || self.at_eof() {
                    break;
                }
                let before = self.pos;
                if let Some(variant) = self.parse_variant() {
                    variants.push(variant);
                }
                if self.eat(Punct::Comma) {
                    continue;
                }
                if self.at(Punct::RBrace) || self.at(Punct::Semi) {
                    break;
                }
                self.expected("`,`, `;` or `}`");
                recover::skip_until(self, &[Punct::Comma, Punct::Semi, Punct::RBrace]);
                if !self.eat(Punct::Comma) && self.pos == before {
                    break;
                }
            }
            if self.eat(Punct::Semi) {
                while !self.at(Punct::RBrace) && !self.at_eof() {
                    let before = self.pos;
                    if let Some(method) = self.parse_enum_method() {
                        methods.push(method);
                    }
                    if self.pos == before {
                        self.expected("a method");
                        recover::skip_stmt(self);
                        if self.pos == before {
                            self.bump();
                        }
                    }
                }
            }
            self.expect(Punct::RBrace);
        }
        EnumDecl {
            name,
            type_params,
            variants,
            methods,
            span: self.span_from(lo),
        }
    }

    /// `Variant = { Decorator } Ident [ "{" EnumField % "," "}" | "=" ( ConstExpr |
    /// StringLit ) ]`.
    fn parse_variant(&mut self) -> Option<Variant> {
        let lo = self.lo();
        let decorators = self.parse_decorators();
        let name = self.ident()?;
        let payload = if self.eat(Punct::LBrace) {
            VariantPayload::Fields(self.comma_list(Punct::RBrace, |p| {
                let name = p.member_name()?;
                let ty = if p.expect(Punct::Colon) {
                    p.parse_type()
                } else {
                    p.error_ty()
                };
                Some(EnumField { name, ty })
            }))
        } else if self.eat(Punct::Eq) {
            VariantPayload::Value(self.parse_expr())
        } else {
            VariantPayload::Unit
        };
        Some(Variant {
            decorators,
            name,
            payload,
            span: self.span_from(lo),
        })
    }

    /// A `MethodDecl` after an enum's `;`; it takes no decorator.
    fn parse_enum_method(&mut self) -> Option<MethodDecl> {
        let decorators = self.parse_decorators();
        self.decorators_dropped(&decorators, "an enum method");
        let lo = self.lo();
        let visibility = self.parse_visibility();
        self.require_visibility(visibility);
        let modifiers = self.parse_modifiers();
        let name = self.member_name()?;
        Some(self.parse_method(lo, visibility, &modifiers, name))
    }

    /// `InterfaceDecl = "interface" Ident [ TypeParams ] "{" { IfaceMember } "}"`.
    fn parse_interface(&mut self) -> InterfaceDecl {
        let lo = self.lo();
        self.bump();
        let name = self.ident_or_error();
        let type_params = self.parse_type_params();
        if self.at_word(Contextual::Extends) {
            let lo = self.lo();
            recover::skip_until(self, &[Punct::LBrace]);
            let span = self.span_from(lo);
            self.emit(
                Diagnostic::new(
                    Code::EN0220,
                    "`interface ... extends` does not exist in Enrang",
                    span,
                    "an interface lists no bases",
                )
                .with_help(Help::text(
                    "require both where the interface is used: `T extends A & B`",
                )),
            );
        }
        let members = self.parse_members(|p| p.parse_iface_member());
        InterfaceDecl {
            name,
            type_params,
            members,
            span: self.span_from(lo),
        }
    }

    /// `IfaceMember = [ "static" ] [ "let" | "move" ] [ "unsafe" ] MemberName
    /// [ TypeParams ] "(" Param % "," ")" [ ":" RetType ] [ WhereClause ] ";"
    /// | MemberName [ "?" ] ":" Type ";"`. A field that ends in `,` is EN0100 with a
    /// fix-it to `;`.
    fn parse_iface_member(&mut self) -> Option<IfaceMember> {
        let decorators = self.parse_decorators();
        self.decorators_dropped(&decorators, "an interface member");
        let lo = self.lo();
        if self.at_kw(Keyword::Public)
            || self.at_kw(Keyword::Private)
            || self.at_kw(Keyword::Protected)
        {
            let span = self.bump().span;
            self.unexpected(
                span,
                "an interface member states no visibility",
                "remove it",
            );
        }
        let modifiers = self.parse_modifiers();
        self.member_habits();
        let name = self.member_name()?;
        let name = self.setter(name);
        if self.at(Punct::LParen) || self.at(Punct::Lt) {
            self.reject_modifiers(
                &modifiers,
                &[
                    Keyword::Static,
                    Keyword::Let,
                    Keyword::Move,
                    Keyword::Unsafe,
                ],
                "an interface method",
            );
            let static_receiver = modifiers.has(Keyword::Static);
            let receiver = match (static_receiver, modifiers.receiver()) {
                (true, Some(_)) => {
                    // SPEC 3.1 allows `static let m()`, which the tree cannot hold
                    // (plan 0.1 item 18).
                    self.unexpected(
                        name.span,
                        "a `static` method has no `this` to mark with `let` or `move`",
                        "this method",
                    );
                    crate::ast::Receiver::Static
                }
                (true, None) => crate::ast::Receiver::Static,
                (false, Some(receiver)) => receiver,
                (false, None) => crate::ast::Receiver::Plain,
            };
            let (type_params, params) = self.parse_signature(name.span.hi);
            let ret = self.eat(Punct::Colon).then(|| self.parse_ret_type());
            let where_clause = self.parse_where();
            if self.at(Punct::LBrace) {
                let span = self.peek().span;
                self.unexpected(span, "an interface method has no body", "expected `;`");
                self.parse_block();
            } else {
                recover::expect_semi(self);
            }
            return Some(IfaceMember::Method(MethodDecl {
                visibility: None,
                is_abstract: false,
                is_override: false,
                receiver,
                is_unsafe: modifiers.has(Keyword::Unsafe),
                name,
                type_params,
                params,
                ret,
                where_clause,
                body: None,
                span: self.span_from(lo),
            }));
        }
        self.reject_modifiers(&modifiers, &[], "an interface field");
        let optional = self.eat(Punct::Question);
        let ty = if self.expect(Punct::Colon) {
            self.parse_type()
        } else {
            self.error_ty()
        };
        let span = self.span_from(lo);
        if self.at(Punct::Comma) {
            self.wrong_separator(Punct::Comma, Punct::Semi);
            self.bump();
        } else {
            recover::expect_semi(self);
        }
        Some(IfaceMember::Field(IfaceField {
            name,
            optional,
            ty,
            span,
        }))
    }

    /// `TypeAlias = "type" Ident [ TypeParams ] "=" ( Type | StringLit { "|"
    /// StringLit } ) ";"`.
    fn parse_type_alias(&mut self) -> TypeAlias {
        self.bump();
        let name = self.ident_or_error();
        let type_params = self.parse_type_params();
        let ty = if !self.expect(Punct::Eq) {
            self.error_ty()
        } else if matches!(self.peek().kind, TokenKind::Str(_)) {
            let lo = self.lo();
            let mut members: Vec<StrLit> = self.parse_str_lit().into_iter().collect();
            let mut mixed = false;
            while self.eat(Punct::Pipe) {
                if matches!(self.peek().kind, TokenKind::Str(_)) {
                    members.extend(self.parse_str_lit());
                } else {
                    let other = self.parse_type_operand();
                    if !mixed {
                        hints::not_a_string_member(self, other.span);
                    }
                    mixed = true;
                }
            }
            let span = self.span_from(lo);
            let kind = if mixed {
                crate::ast::TypeExprKind::Error
            } else {
                crate::ast::TypeExprKind::StrUnion(members)
            };
            self.mk_ty(kind, span)
        } else {
            let saved = std::mem::replace(&mut self.in_alias, true);
            let ty = self.parse_type();
            self.in_alias = saved;
            ty
        };
        recover::expect_semi(self);
        TypeAlias {
            name,
            type_params,
            ty,
        }
    }

    /// `ExtendDecl = "extend" [ TypeParams ] Type "{" { { Decorator } MethodDecl }
    /// "}"`. Library only, which sema checks (EN0806).
    fn parse_extend(&mut self) -> ExtendDecl {
        self.bump();
        let type_params = self.parse_type_params();
        let ty = self.parse_type();
        let members = self.parse_members(|p| {
            let lo = p.lo();
            let decorators = p.parse_decorators();
            let decl_lo = p.lo();
            let visibility = p.parse_visibility();
            // `MethodDecl` starts with a `Visibility` here too.
            p.require_visibility(visibility);
            let modifiers = p.parse_modifiers();
            let Some(name) = p.member_name() else {
                recover::skip_stmt(p);
                return None;
            };
            let method = p.parse_method(decl_lo, visibility, &modifiers, name);
            Some(ExtendMember {
                decorators,
                method,
                span: p.span_from(lo),
            })
        });
        ExtendDecl {
            type_params,
            ty,
            members,
        }
    }

    /// `describe`, `test`, `compileFails` or `compileOk` followed by `(` or `.`
    /// (SPEC 3.4).
    fn at_test_item(&self) -> bool {
        let token = self.peek();
        ["describe", "test", "compileFails", "compileOk"]
            .into_iter()
            .any(|word| is_named(token, word))
            && (self.nth_is(1, Punct::LParen) || self.nth_is(1, Punct::Dot))
    }

    /// `TestItem = DescribeItem | TestDecl | CompileCase`. Outside a `*.test.en`
    /// file only an item at the top level gets EN1112: moving it moves the items
    /// nested in it too.
    fn parse_test_item(&mut self, nested: bool) -> Item {
        let lo = self.lo();
        let token = self.peek();
        if !nested {
            hints::test_item_placement(self, token.span);
        }
        let kind = if is_named(token, "describe") {
            ItemKind::Describe(self.parse_describe())
        } else if is_named(token, "test") {
            ItemKind::Test(self.parse_test_decl())
        } else {
            ItemKind::CompileCase(self.parse_compile_case())
        };
        let span = self.span_from(lo);
        let id = self.ids.next_id();
        Item {
            id,
            decorators: Vec::new(),
            visibility: None,
            kind,
            span,
        }
    }

    /// `DescribeItem = "describe" "(" StringLit "," "(" ")" "=>" "{" { DescribeItem |
    /// TestDecl | CompileCase } "}" [ "," ] ")" ";"`.
    fn parse_describe(&mut self) -> DescribeItem {
        self.bump();
        self.expect(Punct::LParen);
        let name = self.str_lit_or_error();
        self.expect(Punct::Comma);
        self.expect(Punct::LParen);
        self.expect(Punct::RParen);
        self.expect(Punct::FatArrow);
        let mut items = Vec::new();
        if self.expect(Punct::LBrace) {
            while !self.at(Punct::RBrace) && !self.at_eof() {
                let before = self.pos;
                if self.at_test_item() && self.enter() {
                    items.push(self.parse_test_item(true));
                    self.leave();
                } else if hints::at_lifecycle_hook(self) {
                    hints::lifecycle_hook(self);
                } else {
                    let first = self.peek().span;
                    recover::skip_stmt(self);
                    let span = self.span_from(first.lo).to(first);
                    self.emit(
                        Diagnostic::new(
                            Code::EN1102,
                            "a `describe` body holds only `describe`, `test`, `compileFails` and `compileOk`",
                            span,
                            "not a test item",
                        )
                        .with_help(Help::text(
                            "move it into a test's body, or out of the `describe`",
                        )),
                    );
                }
                if self.pos == before {
                    self.bump();
                }
            }
            self.expect(Punct::RBrace);
        }
        self.eat(Punct::Comma);
        self.expect(Punct::RParen);
        recover::expect_semi(self);
        DescribeItem { name, items }
    }

    /// `TestDecl = "test" [ "." TestMode ] "(" StringLit [ "," TestExtra ]
    /// [ "," TestBody ] [ "," ObjectLit ] [ "," ] ")" ";"`.
    fn parse_test_decl(&mut self) -> TestDecl {
        self.bump();
        let mode = if self.eat(Punct::Dot) {
            let token = self.peek();
            let mode = [
                ("only", TestMode::Only),
                ("skip", TestMode::Skip),
                ("todo", TestMode::Todo),
                ("panics", TestMode::Panics),
                ("each", TestMode::Each),
            ]
            .into_iter()
            .find(|(word, _)| is_named(token, word))
            .map(|(_, mode)| mode);
            if mode.is_some() {
                self.bump();
            } else {
                self.expected("`only`, `skip`, `todo`, `panics` or `each`");
            }
            mode
        } else {
            None
        };
        self.expect(Punct::LParen);
        let name = self.str_lit_or_error();
        let mut extra = None;
        let mut body = None;
        let mut options = None;
        // Which arguments have been read: 1 the extra, 2 the body, 3 the options.
        let mut reached = 0;
        while self.eat(Punct::Comma) {
            if self.at(Punct::RParen) {
                break;
            }
            let token = self.peek();
            let (place, ok) = if matches!(token.kind, TokenKind::Str(_)) {
                let message = self.str_lit_or_error();
                let ok = reached < 1;
                if ok {
                    extra = Some(TestExtra::Message(message));
                }
                (1, ok)
            } else if token.is(Punct::LBrace) {
                let lo = self.lo();
                self.bump();
                let fields = self.comma_list(Punct::RBrace, |p| p.parse_field_init());
                let span = self.span_from(lo);
                let literal = self.mk_expr(ExprKind::ObjectLit(fields), span);
                let ok = reached < 3;
                if ok {
                    options = Some(literal);
                }
                (3, ok)
            } else {
                let arg = self.parse_expr();
                match arg.kind {
                    ExprKind::Arrow(arrow) if matches!(arrow.body, ArrowBody::Block(_)) => {
                        if let Some(extra) = arrow.params.get(1) {
                            // `TestBody` takes at most one `ArrowParam` (SPEC 3.6).
                            let span = extra.name.span;
                            self.unexpected(
                                span,
                                "expected `)`: a test body takes at most one parameter",
                                "a second parameter",
                            );
                        }
                        let ok = reached < 2;
                        if ok {
                            body = Some(arrow);
                        }
                        (2, ok)
                    }
                    ExprKind::Arrow(arrow) if arrow.params.is_empty() => {
                        let ok = reached < 1;
                        if ok {
                            extra = Some(TestExtra::Cases(arrow));
                        }
                        (1, ok)
                    }
                    _ => {
                        self.unexpected(
                            arg.span,
                            "expected a test body, `() => { ... }`",
                            "not a test body",
                        );
                        (reached, true)
                    }
                }
            };
            if !ok {
                let span = self.span_from(token.span.lo);
                self.unexpected(
                    span,
                    "this argument of `test` is out of place",
                    "the order is name, extra, body, options",
                );
            }
            reached = reached.max(place);
        }
        self.expect(Punct::RParen);
        recover::expect_semi(self);
        TestDecl {
            mode,
            name,
            extra,
            body,
            options,
        }
    }

    /// `CompileCase = ("compileFails" | "compileOk") "(" StringLit "," RawTemplate
    /// [ "," ObjectLit ] [ "," ] ")" ";"`.
    fn parse_compile_case(&mut self) -> CompileCase {
        let kind = if is_named(self.bump(), "compileOk") {
            CompileKind::Ok
        } else {
            CompileKind::Fails
        };
        self.expect(Punct::LParen);
        let name = self.str_lit_or_error();
        self.expect(Punct::Comma);
        let token = self.peek();
        let source = match token.kind {
            TokenKind::RawTemplate(value) => {
                self.bump();
                StrLit {
                    value,
                    span: token.span,
                }
            }
            _ => {
                self.expected("a `raw` template");
                StrLit {
                    value: enrang_base::intern(""),
                    span: self.here(),
                }
            }
        };
        let mut options = None;
        if self.eat(Punct::Comma) && self.at(Punct::LBrace) {
            let lo = self.lo();
            self.bump();
            let fields = self.comma_list(Punct::RBrace, |p| p.parse_field_init());
            let span = self.span_from(lo);
            options = Some(self.mk_expr(ExprKind::ObjectLit(fields), span));
            self.eat(Punct::Comma);
        }
        self.expect(Punct::RParen);
        recover::expect_semi(self);
        CompileCase {
            kind,
            name,
            source,
            options,
        }
    }

    /// A string literal, or after EN0100 an empty one at the current token.
    fn str_lit_or_error(&mut self) -> StrLit {
        self.parse_str_lit().unwrap_or_else(|| StrLit {
            value: enrang_base::intern(""),
            span: self.here(),
        })
    }
}

/// A local function or `assert` of a file that turned out to be no program, as the
/// item it then is.
fn stmt_to_item(stmt: Stmt) -> Option<Item> {
    let Stmt { id, kind, span } = stmt;
    let (decorators, kind) = match kind {
        StmtKind::LocalFn { decorators, decl } => (decorators, ItemKind::Function(decl)),
        StmtKind::Assert { cond, message } => {
            (Vec::new(), ItemKind::StaticAssert { cond, message })
        }
        _ => return None,
    };
    Some(Item {
        id,
        decorators,
        visibility: None,
        kind,
        span,
    })
}

/// Two lists of items, each in source order, as one in source order.
fn merge_by_position(first: Vec<Item>, second: Vec<Item>) -> Vec<Item> {
    let mut merged = Vec::with_capacity(first.len() + second.len());
    let mut first = first.into_iter().peekable();
    let mut second = second.into_iter().peekable();
    loop {
        let take_first = match (first.peek(), second.peek()) {
            (Some(a), Some(b)) => a.span.lo <= b.span.lo,
            (Some(_), None) => true,
            (None, Some(_)) => false,
            (None, None) => break,
        };
        let next = if take_first {
            first.next()
        } else {
            second.next()
        };
        merged.extend(next);
    }
    merged
}

/// The name a message calls a parameter by: a destructuring pattern as written,
/// or the last word before its `?`, `:` or `=`, past `let`, `const`, a visibility
/// and `readonly`.
fn param_name(source: &str) -> &str {
    let source = source.trim();
    if let Some(close) = match source.chars().next() {
        Some('{') => source.find('}'),
        Some('[') => source.find(']'),
        _ => None,
    } {
        return &source[..=close];
    }
    let end = source.find(['?', ':', '=']).unwrap_or(source.len());
    source[..end].split_whitespace().last().unwrap_or("")
}
