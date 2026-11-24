//! The syntax-level hints: TypeScript habits recognised at the token and given
//! EN02xx with recovery as the Enrang form, and the deferred features of SPEC 16
//! that phase 1 can see, EN10xx, each with its normative message head, a `= note:`
//! with the reason and the table's help (SPEC 16). The test-file codes EN1102,
//! EN1105 and EN1112 are here too.
//!
//! - [`stmt_start`]: `var` (EN0202), `using` (EN0213), `throw`, `try`, `catch`,
//!   `finally` (EN0207), `switch` and `case` (EN0209), `namespace` (EN0222), a
//!   `function` declaration in a body (EN1035), an item in a block (EN0109) and a
//!   decorator before a statement (EN0108).
//! - [`expr_start`]: `function` (EN0218) and `class` (EN1037) expressions, `/re/`
//!   (EN1025), `typeof` (EN0211), `delete` (EN0222), `await` and `async` (EN1001),
//!   `yield` (EN1002), `move` (EN0228), `undefined` (EN0206), a lifetime (EN1005),
//!   generic arrows (EN1036), a decorator (EN0108) and unary `+` (EN0100).
//! - [`type_start`]: `any` (EN0205), `unknown` (EN0210), `number` (EN0225),
//!   `undefined` (EN0206), `keyof` (EN1023), `typeof` (EN0211), a string literal
//!   (EN0216) and a lifetime (EN1005).
//! - [`binary_habit`] and [`binary_found`]: `===`, `!==` (EN0201), `>>>` (EN0208),
//!   `**` (EN1022) and `instanceof` (EN0211) in binary position.
//! - [`item_word`]: `export` (EN0226), `export default` and `export { ... }`
//!   (EN1009); [`async_function`] and [`generator_star`]: `async` and `*` before a
//!   function (EN1001, EN1002).
//! - The diagnostics `types` and `items` report where they build the node they
//!   inspect: `readonly` where no reference is (EN0214), object types joined by
//!   `|` (EN0215), string literals as types (EN0216), `A & B` (EN1024), `Promise`
//!   (EN1001), and the deferred features of SPEC 16 through [`report_deferred`].
//! - Test files: a test item outside a `*.test.en` part (EN1112) and a lifecycle
//!   hook in one (EN1105); `items` reports EN1102 in a `describe` body.

use enrang_base::{BytePos, Span};
use enrang_diag::{Code, Diagnostic, Edit, Help};

use super::exprs::Op;
use super::{Guess, Parser, recover};
use crate::ast::{
    ArrowBody, ArrowFn, ArrowParam, BinOp, Expr, ExprKind, Ident, Stmt, StmtKind, TypeExpr,
    TypeExprKind, Visibility,
};
use crate::token::{Keyword, Punct, Reserved, Token, TokenKind};

/// A deferred feature of SPEC 16: the normative message head, the reason for the
/// `= note:`, and the table's help, if it has one.
fn deferred_text(code: Code) -> (&'static str, &'static str, Option<&'static str>) {
    match code {
        Code::EN1001 => (
            "async functions are not supported yet",
            "Enrang has no event loop yet, so nothing can wait without blocking.",
            Some("Run blocking; threads and an event loop come later"),
        ),
        Code::EN1002 => (
            "generators are not supported yet",
            "a function runs to its end once called; nothing can suspend it halfway.",
            Some("Return an array, or keep state in a class"),
        ),
        Code::EN1005 => (
            "named lifetimes are not supported yet",
            "every reference's lifetime comes from the function body (5.4), so none is written.",
            Some(
                "Write no lifetime: a class may hold a `private` `&` field, and a returned reference's sources come from the function body",
            ),
        ),
        Code::EN1009 => (
            "this module form is not supported yet",
            "a module exports only named declarations, and an import names each one it takes.",
            Some("Use `import { name } from \"./file\"`"),
        ),
        Code::EN1010 => (
            "defaults in patterns are not supported yet",
            "a pattern only takes a value apart; it supplies nothing that is missing.",
            Some("Apply a default with `??` after destructuring"),
        ),
        Code::EN1017 => (
            "setters are not supported yet",
            "assigning a field never runs code.",
            Some("Write a method"),
        ),
        Code::EN1018 => (
            "operator overloading is not supported yet",
            "each operator has one meaning, on the built-in types.",
            Some("Write a named method"),
        ),
        Code::EN1021 => (
            "static fields are not supported yet",
            "a field belongs to each object; storage shared by all of them lives at the top level.",
            Some("Use a top-level `const` or `unsafe let`"),
        ),
        Code::EN1022 => (
            "the `**` operator is not supported yet",
            "a power is the `pow` method of the number types.",
            Some("`a.pow(b)`"),
        ),
        Code::EN1023 => (
            "type-level computation is not supported yet",
            "every type is written out; the compiler does not compute one type from another.",
            None,
        ),
        Code::EN1024 => (
            "intersection types are not supported yet",
            "a value has one type; `&` joins the bounds of a type parameter only.",
            Some("Use it in `T extends A & B`"),
        ),
        Code::EN1025 => (
            "regular expressions are not supported yet",
            "the standard library has no regular-expression engine yet.",
            Some("`indexOf`, `split`"),
        ),
        Code::EN1035 => (
            "nested functions are not supported yet",
            "functions are declared at the top level; an arrow is the function value a body can hold.",
            Some("Move it to the top level, or store an arrow in a local"),
        ),
        Code::EN1036 => (
            "generic arrows are not supported yet",
            "only a declared `function` takes type parameters.",
            Some("Use a generic `function`"),
        ),
        Code::EN1037 => (
            "class expressions are not supported yet",
            "every class is declared at the top level, with a name.",
            Some("Declare a class"),
        ),
        Code::EN1038 => (
            "labelled blocks are not supported yet",
            "`break` with a label leaves a loop; a block cannot be left that way.",
            Some("Label a loop"),
        ),
        Code::EN1039 => (
            "`as const` is not supported yet",
            "`const` already freezes the whole value, its fields and elements included.",
            Some("`const` is already deep"),
        ),
        _ => ("this is not supported yet", "", None),
    }
}

/// The diagnostic of a deferred feature at `span`, with its note and help.
fn deferred(code: Code, span: Span, label: &str) -> Diagnostic {
    let (message, note, help) = deferred_text(code);
    let diag = Diagnostic::new(code, message, span, label).note(note);
    match help {
        Some(help) => diag.with_help(Help::text(help)),
        None => diag,
    }
}

/// Reports the deferred feature `code` at `span`.
pub(super) fn report_deferred(p: &mut Parser, code: Code, span: Span, label: &str) {
    p.emit(deferred(code, span, label));
}

/// A TypeScript word or operator that does not exist: `` `word` does not exist in
/// Enrang ``, as G03 and G04 write it.
fn missing(code: Code, word: &str, span: Span, label: impl Into<String>) -> Diagnostic {
    Diagnostic::new(
        code,
        format!("`{word}` does not exist in Enrang"),
        span,
        label,
    )
}

/// Enrang has no exceptions: the entry EN0207 adds.
const NO_EXCEPTIONS: &str = "Enrang has no exceptions: a function that can fail returns `Result<T, E>`, `?` passes its error to the caller, and `panic` stops the program on a bug.";

/// EN1013 at the current `...`, which is skipped.
pub(super) fn spread_outside_array(p: &mut Parser) {
    let dots = p.bump().span;
    report_spread(p, dots);
}

/// EN1013 at `dots`: rest, and spread outside an array literal (SPEC 16).
pub(super) fn report_spread(p: &mut Parser, dots: Span) {
    p.emit(
        Diagnostic::new(
            Code::EN1013,
            "rest, and spread outside an array literal, are not supported yet",
            dots,
            "only an array literal's element may spread",
        )
        .note(
            "`...` copies the elements of an array into a new array literal, and does nothing else",
        )
        .with_help(Help::text("Pass an array; `[...a]` copies one")),
    );
}

/// EN1005 at the current lifetime token, which is skipped. Written `&'a b'`, it
/// was meant as a string, and the note says how to write one (SPEC 2).
pub(super) fn lifetime(p: &mut Parser) {
    let token = p.bump();
    let mut diag = deferred(Code::EN1005, token.span, "a named lifetime");
    let text = p.text(token.span);
    if text.len() > 2 && text.ends_with('\'') {
        let inner = &text[1..text.len() - 1];
        diag = diag.note(format!(
            "a string is written in double quotes here: `&\"{inner}\"`"
        ));
    }
    p.emit(diag);
}

/// Whether `token` can start an operand: a `Unary` or a `Primary`, the TypeScript
/// forms that get a hint included.
pub(super) fn can_start_operand(token: Token) -> bool {
    match token.kind {
        TokenKind::Ident(_)
        | TokenKind::Int { .. }
        | TokenKind::Float(_)
        | TokenKind::Str(_)
        | TokenKind::NoSubTemplate(_)
        | TokenKind::TemplateHead(_)
        | TokenKind::RawTemplate(_)
        | TokenKind::Lifetime(_) => true,
        TokenKind::Keyword(k) => matches!(
            k,
            Keyword::True
                | Keyword::False
                | Keyword::Null
                | Keyword::This
                | Keyword::Super
                | Keyword::New
                | Keyword::Match
                | Keyword::Asm
                | Keyword::Void
                | Keyword::Move
                | Keyword::Function
                | Keyword::Class
        ),
        TokenKind::Reserved(r) => matches!(
            r,
            Reserved::Typeof
                | Reserved::Await
                | Reserved::Yield
                | Reserved::Delete
                | Reserved::Undefined
                | Reserved::Async
        ),
        TokenKind::Punct(p) => matches!(
            p,
            Punct::LParen
                | Punct::LBracket
                | Punct::LBrace
                | Punct::Bang
                | Punct::Minus
                | Punct::Tilde
                | Punct::Star
                | Punct::Amp
                | Punct::PlusPlus
                | Punct::MinusMinus
                | Punct::StarStar
                | Punct::AmpAmp
                | Punct::DotDotDot
                | Punct::Lt
                | Punct::Plus
                | Punct::Slash
                | Punct::At
        ),
        _ => false,
    }
}

/// Whether `token` can be a binary operator after an operand.
pub(super) fn is_binary_operator(token: Token) -> bool {
    match token.kind {
        TokenKind::Punct(p) => {
            BinOp::from_punct(p).is_some()
                || matches!(
                    p,
                    Punct::AmpAmp
                        | Punct::PipePipe
                        | Punct::QuestionQuestion
                        | Punct::EqEqEq
                        | Punct::BangEqEq
                        | Punct::Shr3
                        | Punct::StarStar
                        | Punct::Plus
                )
        }
        TokenKind::Keyword(Keyword::As) | TokenKind::Reserved(Reserved::Instanceof) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------------
// Statements.

/// A TypeScript habit or deferred feature where a statement starts, inside a
/// block or among a program's top-level statements. `Some` is the statement it
/// recovered as (`None` inside when it dropped one).
pub(super) fn stmt_start(p: &mut Parser) -> Option<Option<Stmt>> {
    let lo = p.lo();
    let token = p.peek();
    match token.kind {
        TokenKind::Reserved(Reserved::Var) => {
            report_var(p);
            Some(Some(binding_as(p, lo, true)))
        }
        TokenKind::Reserved(Reserved::Using) => {
            p.emit(
                missing(
                    Code::EN0213,
                    "using",
                    token.span,
                    "every binding already drops at the end of its scope",
                )
                .note("to run code when a value drops, give its class a `destructor`")
                .with_help(Help::machine(
                    "replace `using` with `const`",
                    vec![Edit::replace(token.span, "const")],
                )),
            );
            Some(Some(binding_as(p, lo, false)))
        }
        TokenKind::Reserved(Reserved::Throw) => {
            p.emit(
                missing(Code::EN0207, "throw", token.span, "errors are values in Enrang")
                    .from_typescript(NO_EXCEPTIONS)
                    .with_help(Help::text(
                        "return `Err(...)` from a function that returns `Result`, or call `panic(...)` for a bug",
                    )),
            );
            recover::skip_stmt(p);
            Some(None)
        }
        TokenKind::Reserved(Reserved::Try) => Some(try_stmt(p)),
        TokenKind::Reserved(word @ (Reserved::Catch | Reserved::Finally)) => {
            p.emit(
                missing(
                    Code::EN0207,
                    word.as_str(),
                    token.span,
                    "errors are values in Enrang",
                )
                .from_typescript(NO_EXCEPTIONS),
            );
            p.bump();
            skip_handler(p);
            Some(None)
        }
        TokenKind::Reserved(Reserved::Switch) => {
            p.emit(
                missing(Code::EN0209, "switch", token.span, "use `match` here")
                    .note("a `match` arm never falls through, and a `match` on an enum names every case")
                    .with_help(Help::text(
                        "write `match (value) { 1 => ..., default => ... }`",
                    )),
            );
            p.bump();
            if p.at(Punct::LParen) {
                recover::skip_group(p);
            }
            if p.at(Punct::LBrace) {
                recover::skip_group(p);
            } else {
                recover::skip_stmt(p);
            }
            Some(None)
        }
        TokenKind::Reserved(Reserved::Case) => {
            report_case(p, token.span);
            recover::skip_stmt(p);
            Some(None)
        }
        TokenKind::Reserved(Reserved::Namespace) => {
            namespace(p);
            Some(None)
        }
        TokenKind::Punct(Punct::At) => {
            let decorators = p.parse_decorators();
            if starts_nested_function(p) {
                nested_function(p);
                return Some(None);
            }
            if p.starts_item() {
                item_in_block(p);
                return Some(None);
            }
            p.decorators_dropped(&decorators, "a statement");
            Some(p.parse_stmt())
        }
        _ if starts_nested_function(p) => {
            nested_function(p);
            Some(None)
        }
        TokenKind::Keyword(Keyword::Import) => {
            item_in_block(p);
            Some(None)
        }
        _ if p.starts_item() => {
            item_in_block(p);
            Some(None)
        }
        _ => None,
    }
}

/// EN0202 at the current `var`, which recovers as `let` (G04).
pub(super) fn report_var(p: &mut Parser) {
    let span = p.peek().span;
    p.emit(
        missing(
            Code::EN0202,
            "var",
            span,
            "use `let` for a binding that changes, `const` otherwise",
        )
        .with_help(Help::machine(
            "replace `var` with `let`",
            vec![Edit::replace(span, "let")],
        )),
    );
}

/// `var` or `using` and the rest of the declaration, recovered as `let` or
/// `const`.
fn binding_as(p: &mut Parser, lo: BytePos, mutable: bool) -> Stmt {
    p.bump();
    let binding = p.parse_binding();
    let decl = p.finish_var_decl(lo, mutable, binding);
    recover::expect_semi(p);
    let span = p.span_from(lo);
    p.mk_stmt(StmtKind::VarDecl(decl), span)
}

/// `try { } catch (e) { } finally { }`: EN0207 once, at `try`, and the `try` block
/// kept as a plain block.
fn try_stmt(p: &mut Parser) -> Option<Stmt> {
    let lo = p.lo();
    let keyword = p.bump().span;
    p.emit(
        missing(Code::EN0207, "try", keyword, "errors are values in Enrang")
            .from_typescript(NO_EXCEPTIONS)
            .with_help(Help::text(
                "call the function, and pass its error up with `?` or `match` on its `Result`",
            )),
    );
    let block = p.at(Punct::LBrace).then(|| p.parse_block());
    while matches!(
        p.peek().kind,
        TokenKind::Reserved(Reserved::Catch | Reserved::Finally)
    ) {
        p.bump();
        skip_handler(p);
    }
    let block = block?;
    let span = p.span_from(lo);
    Some(p.mk_stmt(StmtKind::Block(block), span))
}

/// What follows `catch` or `finally`: an optional `( ... )` and a block, dropped.
fn skip_handler(p: &mut Parser) {
    if p.at(Punct::LParen) {
        recover::skip_group(p);
    }
    if p.at(Punct::LBrace) {
        p.parse_block();
    }
}

/// EN0209 at a `case`.
pub(super) fn report_case(p: &mut Parser, span: Span) {
    p.emit(
        missing(
            Code::EN0209,
            "case",
            span,
            "a `match` arm is written `value => ...`",
        )
        .with_help(Help::text(
            "write `match (value) { 1 => ..., default => ... }`",
        )),
    );
}

/// `namespace X { ... }`: EN0222, and the whole of it skipped.
pub(super) fn namespace(p: &mut Parser) {
    let token = p.bump();
    p.emit(
        missing(Code::EN0222, "namespace", token.span, "a file is a module").with_help(Help::text(
            "move its contents to a file of their own, and `import` them",
        )),
    );
    while matches!(p.peek().kind, TokenKind::Ident(_)) || p.at(Punct::Dot) {
        p.bump();
    }
    if p.at(Punct::LBrace) {
        recover::skip_group(p);
    } else {
        recover::skip_stmt(p);
    }
}

/// Whether a function declaration starts here: `function`, `unsafe function`, or
/// `async function`.
fn starts_nested_function(p: &Parser) -> bool {
    p.at_kw(Keyword::Function)
        || (p.at_kw(Keyword::Unsafe) && p.nth_kw(1, Keyword::Function))
        || (p.peek().kind == TokenKind::Reserved(Reserved::Async)
            && (p.nth_kw(1, Keyword::Function) || p.nth_kw(1, Keyword::Unsafe)))
}

/// A function declared in a body: EN1035, parsed and dropped.
fn nested_function(p: &mut Parser) {
    async_function(p);
    let span = p.peek().span;
    let keyword = if p.at_kw(Keyword::Unsafe) {
        span.to(p.nth(1).span)
    } else {
        span
    };
    report_deferred(p, Code::EN1035, keyword, "a function inside a body");
    p.parse_function_decl();
}

/// An item in a block: EN0109 at its first token, parsed and dropped.
fn item_in_block(p: &mut Parser) {
    let lo = p.lo();
    let token = p.peek();
    p.emit(
        Diagnostic::new(
            Code::EN0109,
            "a declaration cannot go inside a block",
            token.span,
            "declarations go at the top level of a file",
        )
        .with_help(Help::text("move it to the top level")),
    );
    if token.is_keyword(Keyword::Import)
        || (token.is_keyword(Keyword::Public) && p.nth_kw(1, Keyword::Import))
    {
        p.parse_import();
    } else {
        p.parse_item_in_block(lo);
    }
}

// ---------------------------------------------------------------------------------
// Declarations.

/// What a TypeScript word before a declaration recovers as.
pub(super) enum ItemWord {
    /// Parse the declaration with this visibility.
    Visibility(Visibility),
    /// The whole form was skipped.
    Skipped,
}

/// `export` before a declaration: EN0226 with a fix-it to `public`; `export
/// default` is EN1009 and parses as `public`; `export { ... }` and `export * from`
/// are EN1009 and skipped.
pub(super) fn item_word(p: &mut Parser) -> Option<ItemWord> {
    let token = p.peek();
    if token.kind != TokenKind::Reserved(Reserved::Export) {
        return None;
    }
    let next = p.nth(1);
    if next.is_keyword(Keyword::Default) {
        let span = token.span.to(next.span);
        p.bump();
        p.bump();
        report_deferred(p, Code::EN1009, span, "a default export");
        return Some(ItemWord::Visibility(Visibility::Public));
    }
    if next.is(Punct::LBrace) || next.is(Punct::Star) {
        let lo = p.lo();
        recover::skip_line(p);
        let span = p.span_from(lo);
        report_deferred(p, Code::EN1009, span, "a re-export list");
        return Some(ItemWord::Skipped);
    }
    p.bump();
    p.emit(
        missing(Code::EN0226, "export", token.span, "use `public` here")
            .from_typescript(
                "a top-level declaration states `public` to be importable, or `private` to stay in its module.",
            )
            .with_help(Help::machine(
                "replace `export` with `public`",
                vec![Edit::replace(token.span, "public")],
            )),
    );
    Some(ItemWord::Visibility(Visibility::Public))
}

/// `async` before `function`: EN1001, and the word skipped.
pub(super) fn async_function(p: &mut Parser) {
    if p.peek().kind == TokenKind::Reserved(Reserved::Async)
        && (p.nth_kw(1, Keyword::Function) || p.nth_kw(1, Keyword::Unsafe))
    {
        let span = p.bump().span;
        report_deferred(p, Code::EN1001, span, "an async function");
    }
}

/// `*` after `function`: EN1002, and the `*` skipped.
pub(super) fn generator_star(p: &mut Parser) {
    if p.at(Punct::Star) {
        let span = p.bump().span;
        report_deferred(p, Code::EN1002, span, "a generator");
    }
}

/// A test item in a module's own file: EN1112 at its first word, `` tests go in
/// `math.test.en` `` (SPEC 12.1). A source that is no file has no test part to
/// name, so it takes test items.
pub(super) fn test_item_placement(p: &mut Parser, keyword: Span) {
    if p.placement != super::Placement::Module {
        return;
    }
    let name = p
        .file
        .path
        .file_name()
        .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
    let stem = name.strip_suffix(".en").unwrap_or(&name);
    let part = format!("{stem}.test.en");
    p.emit(
        Diagnostic::new(
            Code::EN1112,
            format!("tests go in `{part}`"),
            keyword,
            "a test outside a `*.test.en` file",
        )
        .note("`enrang build` and `enrang run` leave a module's test part out, so the module builds the same without its tests")
        .with_help(Help::text(format!(
            "move it to `{part}`, the test part of this module"
        ))),
    );
}

/// Whether a lifecycle hook call starts here: `beforeEach(`, and the others.
pub(super) fn at_lifecycle_hook(p: &Parser) -> bool {
    let TokenKind::Ident(name) = p.peek().kind else {
        return false;
    };
    ["beforeEach", "afterEach", "beforeAll", "afterAll"].contains(&name.as_str())
        && p.nth_is(1, Punct::LParen)
}

/// A lifecycle hook call in a test file: EN1105, with a fix-it that turns it into
/// a helper function, and the call dropped (SPEC 12.1).
pub(super) fn lifecycle_hook(p: &mut Parser) {
    let lo = p.lo();
    let name = p.peek();
    let word = p.text(name.span).to_owned();
    p.bump();
    let args = p.parse_call_args();
    recover::expect_semi(p);
    let end = p.prev_hi();
    let mut help = Help::text(
        "turn it into a helper function, and call it at the start of each test that needs it",
    );
    if let [arg] = args.as_slice()
        && let ExprKind::Arrow(ArrowFn {
            params,
            body: ArrowBody::Block(block),
            ..
        }) = &arg.kind
        && params.is_empty()
    {
        help = Help::suggest(
            help.message,
            vec![
                Edit::replace(
                    Span {
                        lo,
                        hi: block.span.lo,
                    },
                    format!("private function {word}(): void "),
                ),
                Edit::delete(Span {
                    lo: block.span.hi,
                    hi: end,
                }),
            ],
        );
    }
    p.emit(
        missing(Code::EN1105, &word, name.span, "each test runs on its own")
            .from_typescript(
                "a hook runs hidden code around every test; an Enrang test calls what it needs, so it reads on its own.",
            )
            .with_help(help),
    );
}

// ---------------------------------------------------------------------------------
// Expressions.

/// A TypeScript habit or deferred feature where an operand starts. `None` leaves
/// the token to EN0100.
pub(super) fn expr_start(p: &mut Parser) -> Option<Expr> {
    let lo = p.lo();
    let token = p.peek();
    match token.kind {
        TokenKind::Keyword(Keyword::Function) => Some(function_expr(p)),
        TokenKind::Keyword(Keyword::Class) => {
            report_deferred(p, Code::EN1037, token.span, "a class expression");
            skip_class(p);
            Some(error_from(p, lo))
        }
        TokenKind::Keyword(Keyword::Move) => {
            let span = p.with_trailing_space(token.span);
            p.bump();
            p.emit(
                Diagnostic::new(
                    Code::EN0228,
                    "`move` is not needed here",
                    token.span,
                    "a value moves wherever there is no `&`",
                )
                .with_help(Help::machine("remove `move`", vec![Edit::delete(span)])),
            );
            Some(p.parse_unary())
        }
        TokenKind::Punct(Punct::Slash | Punct::SlashEq) => Some(regex(p)),
        TokenKind::Punct(Punct::Plus) => {
            let span = p.with_trailing_space(token.span);
            p.bump();
            p.emit(
                Diagnostic::new(
                    Code::EN0100,
                    "unary `+` does not exist in Enrang",
                    token.span,
                    "a number needs no `+`; a conversion is a method call",
                )
                .with_help(Help::machine("remove the `+`", vec![Edit::delete(span)])),
            );
            Some(p.parse_unary())
        }
        TokenKind::Punct(Punct::At) => {
            let decorators = p.parse_decorators();
            p.decorators_dropped(&decorators, "an expression");
            Some(p.parse_unary())
        }
        TokenKind::Punct(Punct::Lt) => generic_arrow(p),
        TokenKind::Lifetime(_) => {
            lifetime(p);
            Some(error_from(p, lo))
        }
        TokenKind::Reserved(Reserved::Undefined) => {
            p.bump();
            let mut edits = Vec::new();
            if let Some((at, name_hi)) = p.undefined_init
                && at == token.span.lo
            {
                edits.push(Edit::insert(name_hi, ": i64 | null"));
            }
            edits.push(Edit::replace(token.span, "null"));
            p.emit(
                missing(
                    Code::EN0206,
                    "undefined",
                    token.span,
                    "absence has one spelling",
                )
                .with_help(Help::suggest(
                    "replace `undefined` with `null`, which needs a nullable type",
                    edits,
                )),
            );
            Some(p.mk_expr(ExprKind::Null, token.span))
        }
        TokenKind::Reserved(word @ (Reserved::Typeof | Reserved::Delete)) => {
            p.bump();
            let diag = if word == Reserved::Typeof {
                missing(
                    Code::EN0211,
                    "typeof",
                    token.span,
                    "a value's type is known when the program compiles",
                )
                .with_help(Help::text(
                    "keep the kinds of value in an enum, and `match` on it",
                ))
            } else {
                missing(
                    Code::EN0222,
                    "delete",
                    token.span,
                    "a field cannot be removed",
                )
                .with_help(Help::text("make the field nullable, and set it to `null`"))
            };
            p.emit(diag);
            if can_start_operand(p.peek()) {
                p.parse_unary();
            }
            Some(error_from(p, lo))
        }
        TokenKind::Reserved(Reserved::Await) => {
            p.bump();
            report_deferred(p, Code::EN1001, token.span, "waits for a promise");
            Some(p.parse_unary())
        }
        TokenKind::Reserved(Reserved::Async) => {
            p.bump();
            report_deferred(p, Code::EN1001, token.span, "an async function");
            Some(p.parse_expr())
        }
        TokenKind::Reserved(Reserved::Yield) => {
            p.bump();
            report_deferred(p, Code::EN1002, token.span, "yields a value");
            if can_start_operand(p.peek()) {
                Some(p.parse_unary())
            } else {
                Some(error_from(p, lo))
            }
        }
        _ => None,
    }
}

/// An `Error` expression spanning from `lo` to the last token consumed.
fn error_from(p: &mut Parser, lo: BytePos) -> Expr {
    let span = p.span_from(lo);
    p.mk_expr(ExprKind::Error, span)
}

/// `require(...)`, a call of the bare name `require`: EN1009, the call dropped.
pub(super) fn require_call(p: &mut Parser) -> Expr {
    let lo = p.lo();
    p.bump();
    p.parse_call_args();
    let span = p.span_from(lo);
    report_deferred(p, Code::EN1009, span, "`require` loads no module");
    p.mk_expr(ExprKind::Error, span)
}

/// A `function` expression: EN0218, recovered as the arrow it should be.
fn function_expr(p: &mut Parser) -> Expr {
    let lo = p.lo();
    let keyword = p.bump();
    generator_star(p);
    if matches!(p.peek().kind, TokenKind::Ident(_)) {
        p.bump();
    }
    let head = Span { lo, hi: p.lo() };
    p.parse_type_params();
    let params = if p.expect(Punct::LParen) {
        p.comma_list(Punct::RParen, arrow_param)
    } else {
        Vec::new()
    };
    let ret = p.eat(Punct::Colon).then(|| p.parse_ret_type());
    let block_lo = p.lo();
    let body = p.parse_fn_body();
    let mut diag = Diagnostic::new(
        Code::EN0218,
        "`function` expressions do not exist in Enrang",
        keyword.span,
        "use an arrow here",
    )
    .from_typescript("an arrow is the one function value, and it has no `this` of its own.");
    if p.text(Span {
        lo: block_lo,
        hi: block_lo + 1,
    }) == "{"
    {
        diag = diag.with_help(Help::suggest(
            "write it as an arrow",
            vec![Edit::delete(head), Edit::insert(block_lo, "=> ")],
        ));
    }
    p.emit(diag);
    let span = p.span_from(lo);
    let arrow = ArrowFn {
        params,
        ret,
        body: ArrowBody::Block(body),
        span,
    };
    p.mk_expr(ExprKind::Arrow(arrow), span)
}

/// A parameter of a `function` expression, as the arrow it becomes takes it:
/// `[ "let" | "const" ] Ident [ "?" ] [ ":" Type ] [ "=" Expr ]`, the `?` and the
/// default dropped.
fn arrow_param(p: &mut Parser) -> Option<ArrowParam> {
    if p.at(Punct::DotDotDot) {
        spread_outside_array(p);
    }
    let is_let = p.eat_kw(Keyword::Let);
    if !is_let {
        p.eat_kw(Keyword::Const);
    }
    let name = p.ident()?;
    p.eat(Punct::Question);
    let ty = p.eat(Punct::Colon).then(|| p.parse_type());
    if p.eat(Punct::Eq) {
        p.parse_expr();
    }
    Some(ArrowParam { is_let, name, ty })
}

/// Skips a class written as an expression: `class`, a name, type parameters,
/// heritage, and its balanced body.
pub(super) fn skip_class(p: &mut Parser) {
    p.bump();
    while !p.at(Punct::LBrace) && !p.at_eof() && !p.at(Punct::Semi) && !p.at(Punct::RParen) {
        if p.at(Punct::Lt) || p.at(Punct::LParen) || p.at(Punct::LBracket) {
            recover::skip_group(p);
        } else {
            p.bump();
        }
    }
    if p.at(Punct::LBrace) {
        recover::skip_group(p);
    }
}

/// `/re/flags` where an operand starts: EN1025, skipped to the next `/` on the
/// same line and the flags after it.
fn regex(p: &mut Parser) -> Expr {
    let lo = p.lo();
    let start = p.pos;
    let mut end = None;
    let mut index = start + 1;
    while index < p.tokens.len() && !p.line_break_before(index) {
        let token = p.tokens[index];
        if token.kind == TokenKind::Eof {
            break;
        }
        if token.is(Punct::Slash) || token.is(Punct::SlashEq) {
            end = Some(index);
            break;
        }
        index += 1;
    }
    match end {
        Some(end) => {
            while p.pos <= end {
                p.bump();
            }
            if matches!(p.peek().kind, TokenKind::Ident(_)) && !p.peek().space_before {
                p.bump();
            }
        }
        None => {
            p.bump();
        }
    }
    let span = p.span_from(lo);
    report_deferred(p, Code::EN1025, span, "a regular expression");
    p.mk_expr(ExprKind::Error, span)
}

/// `<T>(x: T) => x`: EN1036 at the type parameters, which are dropped, and the
/// arrow kept.
fn generic_arrow(p: &mut Parser) -> Option<Expr> {
    if !matches!(p.nth(1).kind, TokenKind::Ident(_)) {
        return None;
    }
    let lo = p.lo();
    let (params_span, arrow) = p.speculate_as(Guess::GenericArrow, |p| {
        p.parse_type_params();
        let params_span = p.span_from(lo);
        if !p.at(Punct::LParen) {
            return None;
        }
        let arrow = p.try_arrow(false)?;
        Some((params_span, arrow))
    })?;
    report_deferred(p, Code::EN1036, params_span, "type parameters on an arrow");
    Some(arrow)
}

// ---------------------------------------------------------------------------------
// Binary operators.

/// A TypeScript operator in binary position: its level and the operator it
/// recovers as. `**` sits between `as` and `*`, binding tighter than `*` as in
/// TypeScript, and associates to the right.
pub(super) fn binary_habit(token: Token) -> Option<(u8, Op)> {
    match token.kind {
        TokenKind::Punct(Punct::EqEqEq) => Some((8, Op::Bin(BinOp::Eq))),
        TokenKind::Punct(Punct::BangEqEq) => Some((8, Op::Bin(BinOp::Ne))),
        TokenKind::Punct(Punct::Shr3) => Some((6, Op::Bin(BinOp::Shr))),
        TokenKind::Punct(Punct::StarStar) => Some((3, Op::Pow)),
        TokenKind::Reserved(Reserved::Instanceof) => Some((7, Op::InstanceOf)),
        _ => None,
    }
}

/// Reports the TypeScript operator `token` once both its operands are parsed.
pub(super) fn binary_found(p: &mut Parser, token: Token, lhs: &Expr, rhs: &Expr) {
    match token.kind {
        TokenKind::Punct(op @ (Punct::EqEqEq | Punct::BangEqEq)) => {
            let (strict, plain) = if op == Punct::EqEqEq {
                ("===", "==")
            } else {
                ("!==", "!=")
            };
            p.emit(
                missing(
                    Code::EN0201,
                    strict,
                    token.span,
                    format!("use `{plain}` here"),
                )
                .from_typescript(format!(
                    "`{plain}` never coerces in Enrang, so the strict form is the only form."
                ))
                .with_help(Help::machine(
                    format!("replace `{strict}` with `{plain}`"),
                    vec![Edit::replace(token.span, plain)],
                )),
            );
        }
        TokenKind::Punct(Punct::Shr3) => {
            p.emit(
                missing(Code::EN0208, ">>>", token.span, "use `>>` here")
                    .from_typescript(
                        "`>>` shifts zeros in on an unsigned type and copies the sign bit on a signed one, so the operand's type picks the shift.",
                    )
                    .with_help(Help::suggest(
                        "replace `>>>` with `>>`, on an unsigned operand",
                        vec![Edit::replace(token.span, ">>")],
                    )),
            );
        }
        TokenKind::Punct(Punct::StarStar) => {
            let base = p.text(lhs.span);
            let base = if is_postfix_like(lhs) {
                base.to_owned()
            } else {
                format!("({base})")
            };
            let exponent = p.text(rhs.span);
            let mut diag = deferred(Code::EN1022, token.span, "a power");
            if !matches!(lhs.kind, ExprKind::Error) && !matches!(rhs.kind, ExprKind::Error) {
                diag.helps = vec![Help::suggest(
                    "`a.pow(b)`",
                    vec![Edit::replace(
                        lhs.span.to(rhs.span),
                        format!("{base}.pow({exponent})"),
                    )],
                )];
            }
            p.emit(diag);
        }
        _ => {}
    }
}

/// Whether `expr` can take `.pow(...)` with no parentheses around it.
fn is_postfix_like(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Ident(_)
            | ExprKind::Int { .. }
            | ExprKind::Float(_)
            | ExprKind::Paren(_)
            | ExprKind::Member { .. }
            | ExprKind::Call { .. }
            | ExprKind::Index(..)
            | ExprKind::This
            | ExprKind::Try(_)
            | ExprKind::NonNull(_)
    )
}

/// `x instanceof T`: EN0211, and the type dropped.
pub(super) fn instanceof(p: &mut Parser, token: Token) {
    p.emit(
        missing(
            Code::EN0211,
            "instanceof",
            token.span,
            "a value's class is known when the program compiles",
        )
        .with_help(Help::text(
            "keep the kinds of value in an enum, and `match` on it",
        )),
    );
    if matches!(p.peek().kind, TokenKind::Ident(_)) {
        p.parse_named_type(false);
    }
}

// ---------------------------------------------------------------------------------
// Types.

/// The help of EN0205 and EN0210: in a function's parameter, a type parameter
/// `T` added to the function and the word replaced by `&T` (the whole parameter's
/// type) or `T` (a part of it).
fn generic_help(p: &Parser, token: Token) -> Help {
    let message = "accept every value type with a generic";
    let (Some(sig), Some(start)) = (p.sig, p.param_ty) else {
        return Help::text(message);
    };
    let whole = start == token.span.lo
        && matches!(
            p.nth(1).kind,
            TokenKind::Punct(Punct::Comma | Punct::RParen | Punct::Eq)
        );
    let replacement = if whole { "&T" } else { "T" };
    let declare = match sig.angle {
        None => Edit::insert(sig.name_hi, "<T>"),
        Some((close, insert)) => Edit::insert(close, insert),
    };
    Help::suggest(
        message,
        vec![declare, Edit::replace(token.span, replacement)],
    )
}

/// A TypeScript word or form where a type starts. `None` leaves the token to
/// EN0100.
pub(super) fn type_start(p: &mut Parser) -> Option<TypeExpr> {
    let lo = p.lo();
    let token = p.peek();
    let diag = match token.kind {
        TokenKind::Reserved(Reserved::Any) => missing(
            Code::EN0205,
            "any",
            token.span,
            "every value has one known type",
        )
        .with_help(generic_help(p, token)),
        TokenKind::Reserved(Reserved::Unknown) => missing(
            Code::EN0210,
            "unknown",
            token.span,
            "every value has one known type",
        )
        .with_help(generic_help(p, token)),
        TokenKind::Reserved(Reserved::Number) => missing(
            Code::EN0225,
            "number",
            token.span,
            "every number type states its kind and size",
        )
        .note("use `f64`, or `int` for whole numbers")
        .with_help(Help::suggest(
            "replace `number` with `f64`",
            vec![Edit::replace(token.span, "f64")],
        )),
        TokenKind::Reserved(Reserved::Undefined) => {
            p.bump();
            p.emit(
                missing(
                    Code::EN0206,
                    "undefined",
                    token.span,
                    "absence has one spelling",
                )
                .with_help(Help::suggest(
                    "replace `undefined` with `null`",
                    vec![Edit::replace(token.span, "null")],
                )),
            );
            return Some(p.mk_ty(TypeExprKind::NullLit, token.span));
        }
        TokenKind::Reserved(Reserved::Keyof) => {
            p.bump();
            report_deferred(p, Code::EN1023, token.span, "computes a type");
            p.parse_type_operand();
            let span = p.span_from(lo);
            return Some(p.mk_ty(TypeExprKind::Error, span));
        }
        TokenKind::Reserved(Reserved::Typeof) => {
            p.bump();
            p.emit(
                missing(
                    Code::EN0211,
                    "typeof",
                    token.span,
                    "a type is written out, not read from a value",
                )
                .with_help(Help::text("write the type itself")),
            );
            while matches!(p.peek().kind, TokenKind::Ident(_))
                || (p.at(Punct::Dot) && matches!(p.nth(1).kind, TokenKind::Ident(_)))
            {
                p.bump();
            }
            let span = p.span_from(lo);
            return Some(p.mk_ty(TypeExprKind::Error, span));
        }
        TokenKind::Str(_) => {
            p.bump();
            string_type(p, token.span, false);
            return Some(p.mk_ty(TypeExprKind::Error, token.span));
        }
        TokenKind::Lifetime(_) => {
            lifetime(p);
            let span = p.span_from(lo);
            return Some(p.mk_ty(TypeExprKind::Error, span));
        }
        _ => return None,
    };
    p.bump();
    p.emit(diag);
    Some(p.mk_ty(TypeExprKind::Error, token.span))
}

/// EN0216 at a string literal in a type: outside a `type` alias, or mixed with
/// other types in one.
pub(super) fn string_type(p: &mut Parser, span: Span, in_alias: bool) {
    let diag = if in_alias {
        Diagnostic::new(
            Code::EN0216,
            "a string-literal union cannot mix with other types",
            span,
            "a string literal among other types",
        )
        .with_help(Help::text(
            "declare an enum whose cases carry the other types",
        ))
    } else {
        Diagnostic::new(
            Code::EN0216,
            "a string literal as a type goes only in a `type` alias",
            span,
            "a string literal as a type",
        )
        .with_help(Help::text(
            "declare `private type Name = \"a\" | \"b\";` and write `Name` here",
        ))
    };
    p.emit(diag);
}

/// EN0216 at a member of a string-literal alias that is no string literal.
pub(super) fn not_a_string_member(p: &mut Parser, span: Span) {
    p.emit(
        Diagnostic::new(
            Code::EN0216,
            "a string-literal union cannot mix with other types",
            span,
            "not a string literal",
        )
        .with_help(Help::text(
            "declare an enum whose cases carry the other types",
        )),
    );
}

/// EN0215 at the `|` that joins object types.
pub(super) fn object_union(p: &mut Parser, pipe: Span) {
    p.emit(
        Diagnostic::new(
            Code::EN0215,
            "`|` cannot join object types",
            pipe,
            "a union of object types",
        )
        .with_help(Help::text(
            "declare an enum with a case for each shape, or a class",
        )),
    );
}

/// EN0214 at a `readonly` that is not part of a type here: a parameter's, a
/// local's or a closure's type.
pub(super) fn readonly_misplaced(p: &mut Parser, keyword: Span) {
    let span = p.with_trailing_space(keyword);
    p.emit(
        Diagnostic::new(
            Code::EN0214,
            "`readonly` is not part of a type here",
            keyword,
            "only a reference field's type or a return type takes `readonly`",
        )
        .note("a reference is written `&T`, and what the function does through it is inferred from its body")
        .with_help(Help::machine("remove `readonly`", vec![Edit::delete(span)])),
    );
}

/// EN0214 at the `readonly` of a return type that holds no reference.
pub(super) fn readonly_return(p: &mut Parser, keyword: Span) {
    let span = p.with_trailing_space(keyword);
    p.emit(
        Diagnostic::new(
            Code::EN0214,
            "`readonly` before a return type that holds no reference",
            keyword,
            "`readonly` makes a returned reference read-only",
        )
        .with_help(Help::machine("remove `readonly`", vec![Edit::delete(span)])),
    );
}

/// EN0214 at the `readonly` of a field's type that is not a reference.
pub(super) fn readonly_field(p: &mut Parser, keyword: Span) {
    p.emit(
        Diagnostic::new(
            Code::EN0214,
            "`readonly` before a field type that is not a reference",
            keyword,
            "expected `&` after `readonly`",
        )
        .with_help(Help::text(
            "use `readonly &T` for a read-only reference, or write `readonly` before the field's name",
        )),
    );
}

/// EN0214 at a constructor parameter's `readonly` with no visibility, which only
/// a field may have (SPEC 3.1 `CtorParam`).
pub(super) fn readonly_parameter(p: &mut Parser, keyword: Span) {
    p.emit(
        Diagnostic::new(
            Code::EN0214,
            "`readonly` on a parameter needs a visibility",
            keyword,
            "only a field is `readonly`",
        )
        .with_help(Help::suggest(
            "make it a field with `private`",
            vec![Edit::insert(keyword.lo, "private ")],
        )),
    );
}

/// `Promise` as a type name: EN1001.
pub(super) fn promise(p: &mut Parser, name: &Ident) {
    if name.name.as_str() == "Promise" {
        report_deferred(p, Code::EN1001, name.span, "a promise type");
    }
}

/// EN1024 at an intersection type's `&`, after its first operand.
pub(super) fn intersection(p: &mut Parser, amp: Span) {
    report_deferred(p, Code::EN1024, amp, "an intersection type");
}
