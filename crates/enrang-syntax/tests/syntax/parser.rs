//! The parser (SPEC 3): every `ts` block of SPEC parses with no diagnostic, the tour
//! and `Ownership in three lines` among them; the parser fixtures of TESTING 23's M1
//! row with the exact tree SPEC 3.4 gives each; a tree-shape table for each level of
//! SPEC 3.5 against its neighbours, and for its associativity; the disambiguation
//! rules of SPEC 3.4; and the EN1013 forms of TESTING 18, each EN1013 at `...` and
//! nothing else.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use enrang_base::{SourceFile, Span, intern};
use enrang_diag::{Code, DiagCtx, Diagnostic};
use enrang_syntax::ast::*;
use enrang_syntax::{NodeIdGen, ParseMode, erase, parse_file};
use enrang_testkit::{Harness, extract_cases, fenced_blocks};

use crate::support::{backticked, doc, section, source};

/// A file parsed as `check` parses it, with what it reported.
pub struct Parsed {
    pub file: SourceFile,
    pub tree: File,
    pub diags: Vec<Diagnostic>,
}

impl Parsed {
    pub fn new(name: &str, text: &str) -> Parsed {
        let file = source(name, text);
        let mut dcx = DiagCtx::new();
        let tree = parse_file(&file, &mut NodeIdGen::new(), ParseMode::Test, &mut dcx);
        let diags = dcx.take();
        Parsed { file, tree, diags }
    }

    /// The source under `span`.
    pub fn text(&self, span: Span) -> &str {
        let start = self.file.start.0;
        &self.file.text[(span.lo.0 - start) as usize..(span.hi.0 - start) as usize]
    }

    /// Each diagnostic as its code and the source under its primary span.
    pub fn reports(&self) -> Vec<(Code, String)> {
        self.diags
            .iter()
            .map(|diag| (diag.code, self.text(diag.primary.span).to_owned()))
            .collect()
    }

    /// Every diagnostic, one per line, for a failure message.
    pub fn listing(&self) -> String {
        self.diags
            .iter()
            .map(|diag| {
                let at = self.text(diag.primary.span);
                format!("{}: {} at {at:?}\n", diag.code, diag.message)
            })
            .collect()
    }

    /// The expression of the file's only statement, `<expr>;`.
    pub fn expr(&self) -> &Expr {
        match self.tree.stmts.as_slice() {
            [
                Stmt {
                    kind: StmtKind::Expr(expr),
                    ..
                },
            ] => expr,
            other => panic!("expected one expression statement, found {other:#?}"),
        }
    }
}

/// A SPEC block or case file and the name it is parsed under.
pub struct SpecSource {
    pub label: String,
    pub name: String,
    pub text: String,
}

/// The G cases that SPEC 14 gives syntax errors; their stderr is tested byte for
/// byte elsewhere.
pub const SYNTAX_GOLDENS: &[&str] = &["G01", "G02", "G03", "G04"];

/// The `ts` blocks of SPEC that are not Enrang source, or are fragments on purpose,
/// each by a line it holds and the reason. Every other block must parse with no
/// diagnostic. None is needed today: every block outside G01 to G04 is a whole file.
const NOT_SOURCE: &[(&str, &str)] = &[];

/// Every `ts` block of SPEC except G01 to G04: the files of each case under the name
/// its marker gives, and every other block as `spec.en`, or `spec.test.en` when it
/// holds a test item at its top level, as SPEC 12.1 and 12.3 write test files.
pub fn spec_sources() -> &'static [SpecSource] {
    static SOURCES: OnceLock<Vec<SpecSource>> = OnceLock::new();
    SOURCES.get_or_init(|| {
        let spec = doc("SPEC.md");
        let cases = extract_cases(spec).unwrap_or_else(|errors| panic!("{errors}"));
        let case_texts: BTreeSet<&str> = cases
            .iter()
            .flat_map(|case| case.files.iter().map(|file| file.contents.as_str()))
            .collect();
        let mut sources = Vec::new();
        for case in &cases {
            if SYNTAX_GOLDENS.contains(&case.id.as_str()) {
                continue;
            }
            for file in &case.files {
                sources.push(SpecSource {
                    label: format!("case {} {}", case.id, file.name),
                    name: file.name.clone(),
                    text: file.contents.clone(),
                });
            }
        }
        let blocks = fenced_blocks(spec).unwrap_or_else(|errors| panic!("{errors}"));
        for block in blocks {
            if block.lang != "ts" || case_texts.contains(block.contents.as_str()) {
                continue;
            }
            if NOT_SOURCE
                .iter()
                .any(|(line, _)| block.contents.lines().any(|l| l == *line))
            {
                continue;
            }
            let tests = block.contents.lines().any(|line| {
                ["describe(", "test(", "test.", "compileFails(", "compileOk("]
                    .iter()
                    .any(|start| line.starts_with(start))
            });
            let name = if tests { "spec.test.en" } else { "spec.en" };
            sources.push(SpecSource {
                label: format!("line {}", block.line),
                name: name.to_owned(),
                text: block.contents,
            });
        }
        sources
    })
}

// ---------------------------------------------------------------------------------
// Trees, written compactly: an S-expression of each erased node.

/// An expression as an S-expression: `(+ a (* b c))`.
pub fn shape(expr: &Expr) -> String {
    let all = |exprs: &[Expr]| {
        exprs
            .iter()
            .map(shape)
            .map(|s| format!(" {s}"))
            .collect::<String>()
    };
    let types = |tys: &[TypeExpr]| tys.iter().map(ty_shape).collect::<Vec<_>>().join(", ");
    match &expr.kind {
        ExprKind::Int { text, .. } => text.to_string(),
        ExprKind::Float(text) => text.to_string(),
        ExprKind::Str(value) => format!("{:?}", value.as_str()),
        ExprKind::Template(parts) => {
            let parts: String = parts
                .iter()
                .map(|part| match part {
                    TplPart::Str(text) => format!(" {:?}", text.as_str()),
                    TplPart::Expr(e) => format!(" {}", shape(e)),
                })
                .collect();
            format!("(template{parts})")
        }
        ExprKind::RawTemplate(text) => format!("(raw {:?})", text.as_str()),
        ExprKind::Bool(b) => b.to_string(),
        ExprKind::Null => "null".to_owned(),
        ExprKind::Paren(inner) => format!("(paren {})", shape(inner)),
        ExprKind::Ident(name) => name.to_string(),
        ExprKind::This => "this".to_owned(),
        ExprKind::Super => "super".to_owned(),
        ExprKind::Array(elems) => {
            let elems: Vec<String> = elems
                .iter()
                .map(|elem| match elem {
                    ArrayElem::Item(e) => shape(e),
                    ArrayElem::Spread { expr, .. } => format!("...{}", shape(expr)),
                })
                .collect();
            format!("[{}]", elems.join(", "))
        }
        ExprKind::Repeat(value, count) => format!("[{}; {}]", shape(value), shape(count)),
        ExprKind::TypeMember { ty, name } => format!("(member-of {} {})", ty_shape(ty), name.name),
        ExprKind::New { ty, init } => match init {
            NewInit::Args(args) => format!("(new {}{})", ty_shape(ty), all(args)),
            NewInit::Fields(fields) => format!("(new {} {})", ty_shape(ty), fields_shape(fields)),
        },
        ExprKind::CaseLit { path, args, fields } => {
            let path: Vec<&str> = path.iter().map(|i| i.name.as_str()).collect();
            format!(
                "(case {}<{}> {})",
                path.join("."),
                types(args),
                fields_shape(fields)
            )
        }
        ExprKind::ObjectLit(fields) => fields_shape(fields),
        ExprKind::Match { subject, arms } => {
            format!("(match {} {} arms)", shape(subject), arms.len())
        }
        ExprKind::SizeForm(form) => match form {
            SizeForm::SizeOf(ty) => format!("(sizeOf {})", ty_shape(ty)),
            SizeForm::AlignOf(ty) => format!("(alignOf {})", ty_shape(ty)),
            SizeForm::OffsetOf(ty, field) => {
                format!("(offsetOf {} {:?})", ty_shape(ty), field.value.as_str())
            }
        },
        ExprKind::Asm(asm) => format!("(asm {})", shape(&asm.template)),
        ExprKind::Unary(op, e) => format!("({} {})", op.as_str(), shape(e)),
        ExprKind::Borrow(e) => format!("(& {})", shape(e)),
        ExprKind::Deref(e) => format!("(* {})", shape(e)),
        ExprKind::VoidOp(e) => format!("(void {})", shape(e)),
        ExprKind::Binary(op, l, r) => format!("({} {} {})", op.as_str(), shape(l), shape(r)),
        ExprKind::Logical(op, l, r) => format!("({} {} {})", op.as_str(), shape(l), shape(r)),
        ExprKind::Coalesce(l, r) => format!("(?? {} {})", shape(l), shape(r)),
        ExprKind::Ternary(c, t, e) => format!("(? {} {} {})", shape(c), shape(t), shape(e)),
        ExprKind::Cast(e, ty) => format!("(as {} {})", shape(e), ty_shape(ty)),
        ExprKind::Assign { op, target, value } => {
            format!("({} {} {})", op.as_str(), shape(target), shape(value))
        }
        ExprKind::IncDec {
            target,
            inc,
            prefix,
        } => {
            let op = if *inc { "++" } else { "--" };
            if *prefix {
                format!("({op} {})", shape(target))
            } else {
                format!("({} {op})", shape(target))
            }
        }
        ExprKind::Member {
            base,
            name,
            optional,
        } => {
            let dot = if *optional { "?." } else { "." };
            format!("({dot} {} {})", shape(base), name.name)
        }
        ExprKind::Index(base, index) => format!("(index {} {})", shape(base), shape(index)),
        ExprKind::Call {
            callee,
            type_args,
            args,
        } => {
            let type_args = if type_args.is_empty() {
                String::new()
            } else {
                format!(" <{}>", types(type_args))
            };
            format!("(call {}{type_args}{})", shape(callee), all(args))
        }
        ExprKind::Try(e) => format!("(try {})", shape(e)),
        ExprKind::NonNull(e) => format!("(non-null {})", shape(e)),
        ExprKind::Arrow(arrow) => {
            let params: Vec<String> = arrow
                .params
                .iter()
                .map(|param| {
                    let mark = if param.is_let { "let " } else { "" };
                    match &param.ty {
                        Some(ty) => format!("{mark}{}: {}", param.name.name, ty_shape(ty)),
                        None => format!("{mark}{}", param.name.name),
                    }
                })
                .collect();
            let ret = match &arrow.ret {
                Some(ret) => format!(" : {}", ty_shape(&ret.ty)),
                None => String::new(),
            };
            let body = match &arrow.body {
                ArrowBody::Expr(e) => shape(e),
                ArrowBody::Block(block) => format!("{{{} stmts}}", block.stmts.len()),
            };
            format!("(=> ({}){ret} {body})", params.join(", "))
        }
        ExprKind::Error => "ERROR".to_owned(),
    }
}

fn fields_shape(fields: &[FieldInit]) -> String {
    let fields: Vec<String> = fields
        .iter()
        .map(|field| match &field.value {
            Some(value) => format!("{}: {}", field.name.name, shape(value)),
            None => field.name.name.to_string(),
        })
        .collect();
    format!("{{{}}}", fields.join(", "))
}

/// A type as it would be written, every operator in parentheses.
pub fn ty_shape(ty: &TypeExpr) -> String {
    let list = |tys: &[TypeExpr]| tys.iter().map(ty_shape).collect::<Vec<_>>().join(", ");
    match &ty.kind {
        TypeExprKind::Named { path, args } => {
            let path: Vec<&str> = path.iter().map(|i| i.name.as_str()).collect();
            if args.is_empty() {
                path.join(".")
            } else {
                format!("{}<{}>", path.join("."), list(args))
            }
        }
        TypeExprKind::Nullable(inner) => format!("({} | null)", ty_shape(inner)),
        TypeExprKind::Ref(inner) => format!("(&{})", ty_shape(inner)),
        TypeExprKind::Raw(inner) => format!("(*{})", ty_shape(inner)),
        TypeExprKind::ReadonlyRef(inner) => format!("(readonly &{})", ty_shape(inner)),
        TypeExprKind::Array(inner) => format!("({}[])", ty_shape(inner)),
        TypeExprKind::Fixed(inner, len) => format!("({}[{}])", ty_shape(inner), shape(len)),
        TypeExprKind::Tuple(elems) => format!("[{}]", list(elems)),
        TypeExprKind::FnPtr(f) => {
            let params: Vec<String> = f
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name.name, ty_shape(&p.ty)))
                .collect();
            format!("(fn({}) => {})", params.join(", "), ty_shape(&f.ret.ty))
        }
        TypeExprKind::Closure(c) => {
            let params: Vec<String> = c
                .params
                .iter()
                .map(|p| format!("{}: {}", p.name.name, ty_shape(&p.ty)))
                .collect();
            format!("(({}) => {})", params.join(", "), ty_shape(&c.ret))
        }
        TypeExprKind::Object(fields) => {
            let fields: Vec<String> = fields
                .iter()
                .map(|(name, optional, ty)| {
                    let q = if *optional { "?" } else { "" };
                    format!("{}{q}: {}", name.name, ty_shape(ty))
                })
                .collect();
            format!("{{{}}}", fields.join(", "))
        }
        TypeExprKind::StrUnion(members) => {
            let members: Vec<String> = members
                .iter()
                .map(|m| format!("{:?}", m.value.as_str()))
                .collect();
            members.join(" | ")
        }
        TypeExprKind::Union(operands) => {
            format!("(union {})", list(operands).replace(", ", " "))
        }
        TypeExprKind::Paren(inner) => format!("(paren {})", ty_shape(inner)),
        TypeExprKind::Void => "void".to_owned(),
        TypeExprKind::Never => "never".to_owned(),
        TypeExprKind::NullLit => "null".to_owned(),
        TypeExprKind::Error => "ERROR".to_owned(),
    }
}

// ---------------------------------------------------------------------------------
// Erased trees built by hand, for TESTING 23's M1 fixtures.

fn e(kind: ExprKind) -> Expr {
    Expr {
        id: NodeId(0),
        span: Span::DUMMY,
        kind,
    }
}

fn name(text: &str) -> Ident {
    Ident {
        name: intern(text),
        span: Span::DUMMY,
    }
}

fn var(text: &str) -> Expr {
    e(ExprKind::Ident(intern(text)))
}

fn named(text: &str, args: Vec<TypeExpr>) -> TypeExpr {
    TypeExpr {
        id: NodeId(0),
        span: Span::DUMMY,
        kind: TypeExprKind::Named {
            path: vec![name(text)],
            args,
        },
    }
}

fn binary(op: BinOp, l: Expr, r: Expr) -> Expr {
    e(ExprKind::Binary(op, Box::new(l), Box::new(r)))
}

fn paren(inner: Expr) -> Expr {
    e(ExprKind::Paren(Box::new(inner)))
}

fn call(callee: Expr, type_args: Vec<TypeExpr>, args: Vec<Expr>) -> Expr {
    e(ExprKind::Call {
        callee: Box::new(callee),
        type_args,
        args,
    })
}

fn cast(value: Expr, ty: TypeExpr) -> Expr {
    e(ExprKind::Cast(Box::new(value), ty))
}

/// TESTING 23's M1 parser fixtures, read from its M1 row, with the tree SPEC 3.4
/// gives each and the codes it must report. `a < b > (c)` is EN0107 (SPEC 3.4), a
/// code of the hint stage; until then it reports nothing, and the tree is the same.
fn m1_fixtures() -> Vec<(&'static str, Expr, &'static [Code])> {
    vec![
        (
            "a < b > (c)",
            binary(
                BinOp::Gt,
                binary(BinOp::Lt, var("a"), var("b")),
                paren(var("c")),
            ),
            &[Code::EN0107],
        ),
        (
            "a<b>(c)",
            call(var("a"), vec![named("b", vec![])], vec![var("c")]),
            &[],
        ),
        (
            "f(a < b, c > (d))",
            call(
                var("f"),
                vec![],
                vec![
                    binary(BinOp::Lt, var("a"), var("b")),
                    binary(BinOp::Gt, var("c"), paren(var("d"))),
                ],
            ),
            &[],
        ),
        (
            "x as usize < n",
            binary(BinOp::Lt, cast(var("x"), named("usize", vec![])), var("n")),
            &[],
        ),
        (
            "x as Box<i32>",
            cast(var("x"), named("Box", vec![named("i32", vec![])])),
            &[],
        ),
    ]
}

/// The parser fixtures TESTING 23's M1 row names, in its order.
fn m1_row_fixtures() -> Vec<String> {
    let text = section(doc("TESTING.md"), "## 23. Definition of done per milestone");
    let row = text
        .lines()
        .find(|line| line.starts_with("| **M1**"))
        .expect("TESTING 23 has an M1 row");
    let start = row
        .find("parser fixtures for")
        .expect("the parser fixtures");
    let end = row[start..].find(';').map_or(row.len(), |at| start + at);
    backticked(&row[start..end])
}

// ---------------------------------------------------------------------------------
// SPEC 3.5, level against level.

/// `(source, shape)`: the source is one expression statement without its `;`. Each
/// adjacent pair of levels appears in both orders, and each associative level with a
/// chain of its own operators.
const PRECEDENCE: &[(&str, &str)] = &[
    // 1, left: postfix chains.
    ("a.b.c", "(. (. a b) c)"),
    ("a.b(c)[d]", "(index (call (. a b) c) d)"),
    ("a?.b!", "(non-null (?. a b))"),
    ("f()?.g()?", "(try (call (?. (call f) g)))"),
    ("a()()", "(call (call a))"),
    ("x++", "(x ++)"),
    // 1 against 2.
    ("-a.b", "(- (. a b))"),
    ("!f()", "(! (call f))"),
    ("&xs[0]", "(& (index xs 0))"),
    ("*p++", "(* (p ++))"),
    ("-a?", "(- (try a))"),
    ("++a.b", "(++ (. a b))"),
    // 2, right: prefix chains, `**` and `&&` split in prefix position (SPEC 2).
    ("!-~a", "(! (- (~ a)))"),
    ("**pp", "(* (* pp))"),
    ("&&x", "(& (& x))"),
    ("void *p", "(void (* p))"),
    ("--x", "(-- x)"),
    // 2 against 3: prefix binds tighter than `as`.
    ("-x as u8", "(as (- x) u8)"),
    ("*p as i64", "(as (* p) i64)"),
    // 3, left.
    ("x as u8 as i64", "(as (as x u8) i64)"),
    ("p as *u16", "(as p (*u16))"),
    ("x as i64[3]", "(as x (i64[3]))"),
    // 3 against 4: `as` binds tighter than `*`, unlike TypeScript.
    ("a * b as i64", "(* a (as b i64))"),
    ("a as i64 * b", "(* (as a i64) b)"),
    // 4, left.
    ("a / b % c", "(% (/ a b) c)"),
    ("a * b * c", "(* (* a b) c)"),
    // 4 against 5.
    ("a + b * c", "(+ a (* b c))"),
    ("a * b + c", "(+ (* a b) c)"),
    // 5, left.
    ("a - b + c", "(+ (- a b) c)"),
    // 5 against 6.
    ("a << b + c", "(<< a (+ b c))"),
    ("a + b >> c", "(>> (+ a b) c)"),
    // 6, left.
    ("a << b >> c", "(>> (<< a b) c)"),
    // 6 against 7.
    ("a < b << c", "(< a (<< b c))"),
    ("a >> b <= c", "(<= (>> a b) c)"),
    // 7, none: a chain is EN0107, which keeps the left-associative tree.
    ("a < b < c", "(< (< a b) c)"),
    ("a <= b > c", "(> (<= a b) c)"),
    // 7 against 8.
    ("a == b < c", "(== a (< b c))"),
    ("a >= b != c", "(!= (>= a b) c)"),
    // 8, none: the same.
    ("a == b != c", "(!= (== a b) c)"),
    // 8 against 9: as in JS, `a & b == c` is `a & (b == c)` (SPEC 3.5).
    ("a & b == c", "(& a (== b c))"),
    ("a == b & c", "(& (== a b) c)"),
    // 9, left.
    ("a & b & c", "(& (& a b) c)"),
    // 9 against 10.
    ("a ^ b & c", "(^ a (& b c))"),
    ("a & b ^ c", "(^ (& a b) c)"),
    // 10, left.
    ("a ^ b ^ c", "(^ (^ a b) c)"),
    // 10 against 11.
    ("a | b ^ c", "(| a (^ b c))"),
    ("a ^ b | c", "(| (^ a b) c)"),
    // 11, left.
    ("a | b | c", "(| (| a b) c)"),
    // 11 against 12.
    ("a && b | c", "(&& a (| b c))"),
    ("a | b && c", "(&& (| a b) c)"),
    // 12, left.
    ("a && b && c", "(&& (&& a b) c)"),
    // 12 against 13.
    ("a || b && c", "(|| a (&& b c))"),
    ("a && b || c", "(|| (&& a b) c)"),
    // 13, left.
    ("a || b || c", "(|| (|| a b) c)"),
    // 13 against 14: mixing `??` with `||` or `&&` is EN0106, which keeps this tree.
    ("a || b ?? c", "(?? (|| a b) c)"),
    ("a ?? b && c", "(?? a (&& b c))"),
    ("a | b ?? c", "(?? (| a b) c)"),
    ("a ?? b | c", "(?? a (| b c))"),
    ("a ?? (b || c)", "(?? a (paren (|| b c)))"),
    // 14, right: the JS idiom.
    ("a ?? b ?? c", "(?? a (?? b c))"),
    // 14 against 15.
    ("a ?? b ? c : d", "(? (?? a b) c d)"),
    ("a ? b ?? c : d ?? e", "(? a (?? b c) (?? d e))"),
    // 15, right.
    ("a ? b : c ? d : e", "(? a b (? c d e))"),
    ("a ? b ? c : d : e", "(? a (? b c d) e)"),
    ("a\n  ? b\n  : c", "(? a b c)"),
    // 15 against 16: each branch is an `Expr`.
    ("a = b ? c : d", "(= a (? b c d))"),
    ("a ? b : c = d", "(? a b (= c d))"),
    // 16, right.
    ("a = b = c", "(= a (= b c))"),
    ("a += b -= c", "(+= a (-= b c))"),
    ("a >>= b <<= c", "(>>= a (<<= b c))"),
    // 16 against 17.
    ("f = x => x + 1", "(= f (=> (x) (+ x 1)))"),
    ("x => y = 1", "(=> (x) (= y 1))"),
    ("(a, b) => a ?? b", "(=> (a, b) (?? a b))"),
    ("(let x: i64): i64 => x", "(=> (let x: i64) : i64 x)"),
    ("() => ({ x: 1 })", "(=> () (paren {x: 1}))"),
    ("() => { return; }", "(=> () {1 stmts})"),
    // SPEC 3.4, Disambiguation.
    ("a < b > (c)", "(> (< a b) (paren c))"),
    ("a<b>(c)", "(call a <b> c)"),
    ("f(a < b, c > (d))", "(call f (< a b) (> c (paren d)))"),
    ("x as usize < n", "(< (as x usize) n)"),
    ("x as Box<i32>", "(as x Box<i32>)"),
    ("x as Box < i32 > y", "(> (< (as x Box) i32) y)"),
    ("x as Box<Box<i32>> > y", "(> (as x Box<Box<i32>>) y)"),
    ("a<b>c", "(> (< a b) c)"),
    ("a<1>(x)", "(> (< a 1) (paren x))"),
    ("a<{ x: 1 }>(d)", "(> (< a {x: 1}) (paren d))"),
    ("a<b>>c", "(< a (>> b c))"),
    ("a<b>=c", "(>= (< a b) c)"),
    ("x.wrap<u8>()", "(call (. x wrap) <u8>)"),
    (
        "(300 as u16).wrap<u8>()",
        "(call (. (paren (as 300 u16)) wrap) <u8>)",
    ),
    ("Stack<i64>.empty()", "(call (member-of Stack<i64> empty))"),
    (
        "i64[].withCapacity(8)",
        "(call (member-of (i64[]) withCapacity) 8)",
    ),
    (
        "Slice<u32>.fromRaw(base, n)",
        "(call (member-of Slice<u32> fromRaw) base n)",
    ),
    ("E<i64>.V { x: 1 }", "(case E.V<i64> {x: 1})"),
    (
        "Shape.Circle { radius: 2.5 }",
        "(case Shape.Circle<> {radius: 2.5})",
    ),
    ("&Expr.Num { value: n }", "(& (case Expr.Num<> {value: n}))"),
    ("new Point { x: 1 }", "(new Point {x: 1})"),
    ("new vga.Screen { rows }", "(new vga.Screen {rows})"),
    ("new Stack<i64>()", "(new Stack<i64>)"),
    (
        "new Box(new Node { value, next })",
        "(new Box (new Node {value, next}))",
    ),
    ("a ? (b) : c", "(? a (paren b) c)"),
    ("a ? (b) : c => d", "(? a (paren b) (=> (c) d))"),
    ("a ? (x): i64 => x : y", "(? a (=> (x) : i64 x) y)"),
    ("a ? (x): T => b", "(? a (paren x) (=> (T) b))"),
    (
        "a ? (x): T => b ? (y): U => c",
        "(? a (paren x) (=> (T) (? b (paren y) (=> (U) c))))",
    ),
    // The first branch ends at the ternary's `:` along its right edge, so `x : T =>`
    // there is never EN0224's bare arrow: not in an arrow's body, an assignment's
    // value, or a nested ternary's second branch (as TypeScript reads them).
    ("c ? (b, i) => n : a => a", "(? c (=> (b, i) n) (=> (a) a))"),
    ("c ? x => n : a => a", "(? c (=> (x) n) (=> (a) a))"),
    ("c ? x = n : a => a", "(? c (= x n) (=> (a) a))"),
    ("c ? d ? x : n : a => a", "(? c (? d x n) (=> (a) a))"),
    (
        "c ? (x): T => y => n : a => a",
        "(? c (=> (x) : T (=> (y) n)) (=> (a) a))",
    ),
    ("sizeOf<u32>()", "(sizeOf u32)"),
    ("alignOf<[u8, i64]>()", "(alignOf [u8, i64])"),
    ("offsetOf<Regs>(\"ebx\")", "(offsetOf Regs \"ebx\")"),
    ("[1, 2, ...xs]", "[1, 2, ...xs]"),
    ("[0; 10]", "[0; 10]"),
    ("[]", "[]"),
    ("`a${b}c${d}`", "(template \"a\" b \"c\" d \"\")"),
    ("`plain`", "(template \"plain\")"),
    ("raw`x${y}`", "(raw \"x${y}\")"),
    ("super(name)", "(call super name)"),
    ("this.n += 1", "(+= (. this n) 1)"),
    ("node.type", "(. node type)"),
    ("xs.map(x => x * x)", "(call (. xs map) (=> (x) (* x x)))"),
];

/// `(source, type)`: the type of `let x: <source> = y;`. Covers `split_token` and
/// the shapes of SPEC 3.2.
const TYPES: &[(&str, &str)] = &[
    ("Box<Box<Box<i64>>>", "Box<Box<Box<i64>>>"),
    ("**u8", "(*(*u8))"),
    ("&&T", "(&(&T))"),
    ("&T[]", "(&(T[]))"),
    ("&T | null", "((&T) | null)"),
    ("T[3][4]", "((T[3])[4])"),
    ("[int, string]", "[int, string]"),
    ("{ name: string, age?: int }", "{name: string, age?: int}"),
    ("A | B", "(union A B)"),
    ("A | B | null", "((union A B) | null)"),
    ("(i64)", "(paren i64)"),
    (
        "((k: u8) => void) | null",
        "((paren ((k: u8) => void)) | null)",
    ),
    (
        "fn(xs: &Slice<i64>) => &i64",
        "(fn(xs: (&Slice<i64>)) => (&i64))",
    ),
    ("unsafe fn() => void", "(fn() => void)"),
    ("vga.Screen", "vga.Screen"),
    ("Result<void, E>", "Result<void, E>"),
];

/// TESTING 18's spread rows: each source, and the `(code, text)` it must report.
fn spread_rows() -> Vec<(String, Vec<(Code, &'static str)>)> {
    vec![
        ("const r = [...a; 3];".to_owned(), vec![(Code::EN0100, ";")]),
        (
            "const r = [...0..n];".to_owned(),
            vec![(Code::EN0100, "..")],
        ),
        (
            "for (const i of a...b) {}".to_owned(),
            vec![(Code::EN0100, "...")],
        ),
        ("a...b;".to_owned(), vec![(Code::EN0100, "...")]),
        ("const v = i64[].withCapacity(8);".to_owned(), vec![]),
        ("const w = x[...i];".to_owned(), vec![(Code::EN1013, "...")]),
        ("const c = [...a];".to_owned(), vec![]),
    ]
}

/// A whole file for each EN1013 form of TESTING 18's "Deferred forms" row, keyed by
/// the form as the row writes it; "rest parameters" is prose there.
const EN1013_FILES: &[(&str, &str)] = &[
    ("f(...a)", "f(...a);"),
    ("new C(...a)", "new C(...a);"),
    ("console.log(...a)", "console.log(...a);"),
    (
        "rest parameters",
        "private function f(...a: i64[]): void {}",
    ),
    ("(...a) => 1", "const g = (...a) => 1;"),
    ("{...o}", "const x = {...o};"),
    ("new Point { ...p }", "const q = new Point { ...p };"),
    ("const { a, ...r } = p", "const { a, ...r } = p;"),
    ("xs[...i]", "xs[...i];"),
    ("for (const x of ...a)", "for (const x of ...a) {}"),
    ("@d([...a])", "@d([...a]) private function f(): void {}"),
    ("[a, ...r] = xs", "[a, ...r] = xs;"),
    ("const [a, ...r] = xs", "const [a, ...r] = xs;"),
];

/// The forms TESTING 18's "Deferred forms" row lists.
fn en1013_row_forms() -> Vec<String> {
    let text = section(doc("TESTING.md"), "## 18. Traceability meta-tests");
    let row = text
        .lines()
        .find(|line| line.starts_with("| Deferred forms:"))
        .expect("the row of deferred spread forms");
    let forms = row.split('|').nth(1).expect("a first cell");
    let mut found = backticked(forms);
    if forms.contains("rest parameters") {
        found.push("rest parameters".to_owned());
    }
    found
}

/// `(label, file name, source, reports)`: what SPEC 3's grammar itself rejects,
/// each with the code its label names (EN0100 where the grammar has no code of its
/// own) at the token or construct given; and near-misses that report nothing.
type Row = (
    &'static str,
    &'static str,
    &'static str,
    Vec<(Code, &'static str)>,
);

fn grammar_rows() -> Vec<Row> {
    let en0100 = |at: &'static str| vec![(Code::EN0100, at)];
    let en0226 = |at: &'static str| vec![(Code::EN0226, at)];
    vec![
        // `ItemVis` and `Visibility` (SPEC 3.1).
        ("EN0226/a class", "s.en", "class A {}\n", en0226("class")),
        (
            "EN0226/an abstract class",
            "s.en",
            "abstract class A {}\n",
            en0226("abstract"),
        ),
        ("EN0226/an enum", "s.en", "enum E { A }\n", en0226("enum")),
        (
            "EN0226/an interface",
            "s.en",
            "interface I { x: i64; }\n",
            en0226("interface"),
        ),
        (
            "EN0226/a type alias",
            "s.en",
            "type T = i64;\n",
            en0226("type"),
        ),
        (
            "EN0226/a declared function",
            "s.en",
            "declare function f(): void;\n",
            en0226("declare"),
        ),
        (
            "EN0226/an unsafe let",
            "s.en",
            "unsafe let x: i64;\n",
            en0226("unsafe"),
        ),
        (
            "EN0226/a field",
            "s.en",
            "public class A { x: i64; }\n",
            en0226("x"),
        ),
        (
            "EN0226/a method",
            "s.en",
            "public class A { m(): void {} }\n",
            en0226("m"),
        ),
        (
            "EN0226/a constructor",
            "s.en",
            "public class A { constructor() {} }\n",
            en0226("constructor"),
        ),
        (
            "EN0226/a destructor",
            "s.en",
            "public class A { destructor() {} }\n",
            en0226("destructor"),
        ),
        (
            "EN0226/an enum method",
            "s.en",
            "public enum E { A; m(): void {} }\n",
            en0226("m"),
        ),
        (
            "EN0226/an extend member",
            "s.en",
            "extend<T> T[] { push(x: T): void {} }\n",
            en0226("push"),
        ),
        // SPEC 3.1: an unmarked function in a file with no statements, never EN0115.
        (
            "EN0226/an unmarked function after an item",
            "s.en",
            "public class A {}\nfunction helper() {}\n",
            en0226("function"),
        ),
        (
            "EN0226/an unmarked function before an item",
            "s.en",
            "function helper() {}\npublic class A {}\n",
            en0226("function"),
        ),
        (
            "EN0226/an unmarked function alone",
            "s.en",
            "unsafe function f() {}\n",
            en0226("unsafe"),
        ),
        // `File = { Import } { TopStmt } { Item }`.
        (
            "EN0115/a statement after an item",
            "s.en",
            "public class A {}\nconsole.log(1);\n",
            vec![(Code::EN0115, "console.log(1);")],
        ),
        (
            "EN0115/a local function after an item, in a program",
            "s.en",
            "console.log(1);\npublic class A {}\nfunction helper() {}\n",
            vec![(Code::EN0115, "function helper() {}")],
        ),
        (
            "EN0110/an import after a statement",
            "s.en",
            "f();\nimport { x } from \"./x\";\n",
            vec![(Code::EN0110, "import { x } from \"./x\";")],
        ),
        (
            "EN0110/an import after an item",
            "s.en",
            "public class A {}\npublic import { x } from \"./x\";\n",
            vec![(Code::EN0110, "public import { x } from \"./x\";")],
        ),
        // `VarDecl`: a `const` always has a value.
        (
            "EN0116/a const with no value",
            "s.en",
            "const x;\n",
            vec![(Code::EN0116, "x")],
        ),
        (
            "EN0116/a const pattern with no value",
            "s.en",
            "const [a, b];\n",
            vec![(Code::EN0116, "[a, b]")],
        ),
        // Decorators where none is taken.
        (
            "EN0108/before a statement",
            "s.en",
            "@d f();\n",
            vec![(Code::EN0108, "@d")],
        ),
        (
            "EN0108/before an assert",
            "s.en",
            "@d assert(true);\n",
            vec![(Code::EN0108, "@d")],
        ),
        (
            "EN0108/before a test item",
            "s.test.en",
            "@d test(\"a\", () => {});\n",
            vec![(Code::EN0108, "@d")],
        ),
        // The order of member modifiers (SPEC 3.1).
        (
            "modifiers/out of order",
            "s.en",
            "public class A { public override static m(): void {} }\n",
            en0100("static"),
        ),
        (
            "modifiers/two receiver marks",
            "s.en",
            "public class A { public let move m(): void {} }\n",
            en0100("move"),
        ),
        (
            "modifiers/static and abstract",
            "s.en",
            "public class A { public static abstract m(): void; }\n",
            en0100("abstract"),
        ),
        (
            "modifiers/written twice",
            "s.en",
            "public class A { public static static m(): void {} }\n",
            en0100("static"),
        ),
        (
            "modifiers/readonly before override",
            "s.en",
            "public class A { public readonly override x: i64; }\n",
            en0100("override"),
        ),
        (
            "modifiers/let before unsafe in an interface",
            "s.en",
            "private interface I { unsafe let n(): void; }\n",
            en0100("let"),
        ),
        // `TestBody` takes at most one parameter (SPEC 3.6).
        (
            "test body/two parameters",
            "s.test.en",
            "test(\"a\", (a, b) => {});\n",
            en0100("b"),
        ),
        // Near-misses.
        (
            "accepted/a marked function after an item",
            "s.en",
            "public class A {}\nprivate function helper(): void {}\n",
            vec![],
        ),
        (
            "accepted/a program's local functions",
            "s.en",
            "function helper() {}\nconsole.log(1);\nfunction other() {}\npublic class A {}\n",
            vec![],
        ),
        (
            "accepted/imports first",
            "s.en",
            "import { x } from \"./x\";\npublic import { y } from \"./y\";\nf();\n",
            vec![],
        ),
        (
            "accepted/an assert after an item",
            "s.en",
            "public class A {}\nassert(true);\n",
            vec![],
        ),
        (
            "accepted/a let with no value",
            "s.en",
            "let n: i64;\n",
            vec![],
        ),
        (
            "accepted/decorators before declarations",
            "s.en",
            "@e function g(): void {}\ng();\n@d private function f(): void {}\n",
            vec![],
        ),
        (
            "accepted/every modifier in order",
            "s.en",
            "public abstract class A { public abstract override let unsafe m(): void; public static n(): void {} public override readonly x: i64; }\n",
            vec![],
        ),
        (
            "accepted/interface modifiers in order",
            "s.en",
            "private interface I { static make(): I; let unsafe n(): void; move take(): i64; }\n",
            vec![],
        ),
        (
            "accepted/an extend member with a visibility",
            "s.en",
            "extend<T> T[] { public push(x: T): void {} }\n",
            vec![],
        ),
        (
            "accepted/a test body with one parameter",
            "s.test.en",
            "test(\"a\", (t) => {});\n",
            vec![],
        ),
    ]
}

pub fn register(h: &mut Harness) {
    register_spec(h);
    register_fixtures(h);
    register_shapes(h);
    register_spread(h);
    register_structure(h);
    register_grammar(h);
}

fn register_grammar(h: &mut Harness) {
    for (label, file, text, want) in grammar_rows() {
        h.case(format!("parser/grammar/{label}"), move || {
            let parsed = Parsed::new(file, text);
            let want: Vec<(Code, String)> = want
                .iter()
                .map(|&(code, at)| (code, at.to_owned()))
                .collect();
            assert_eq!(parsed.reports(), want, "{}", parsed.listing());
        });
    }
}

fn register_spec(h: &mut Harness) {
    for (index, spec_source) in spec_sources().iter().enumerate() {
        h.case(
            format!("parser/SPEC parses clean/{index:02} {}", spec_source.label),
            move || {
                let parsed = Parsed::new(&spec_source.name, &spec_source.text);
                if !parsed.diags.is_empty() {
                    return Err(format!("{}\n{}", spec_source.text, parsed.listing()));
                }
                Ok(())
            },
        );
    }
    h.case("parser/SPEC has the blocks it should", || {
        let sources = spec_sources();
        let labels: Vec<&str> = sources.iter().map(|s| s.label.as_str()).collect();
        for want in ["case tour tour.en", "case ownership ownership.en"] {
            assert!(labels.contains(&want), "{want} missing from {labels:?}");
        }
        for golden in SYNTAX_GOLDENS {
            let prefix = format!("case {golden} ");
            assert!(!labels.iter().any(|label| label.starts_with(&prefix)));
        }
        // Every `ts` block is parsed, as a case file or on its own, unless it is a
        // file of G01 to G04 or listed in `NOT_SOURCE`, and each entry there names
        // one block.
        let spec = doc("SPEC.md");
        let goldens: BTreeSet<String> = extract_cases(spec)
            .unwrap_or_else(|errors| panic!("{errors}"))
            .into_iter()
            .filter(|case| SYNTAX_GOLDENS.contains(&case.id.as_str()))
            .flat_map(|case| case.files.into_iter().map(|file| file.contents))
            .collect();
        assert_eq!(goldens.len(), SYNTAX_GOLDENS.len());
        let parsed: BTreeSet<&str> = sources.iter().map(|s| s.text.as_str()).collect();
        let blocks: Vec<_> = fenced_blocks(spec)
            .unwrap_or_else(|errors| panic!("{errors}"))
            .into_iter()
            .filter(|block| block.lang == "ts")
            .collect();
        assert!(blocks.len() > 50, "{} `ts` blocks", blocks.len());
        for block in &blocks {
            let listed = NOT_SOURCE
                .iter()
                .any(|(line, _)| block.contents.lines().any(|l| l == *line));
            assert!(
                listed
                    || goldens.contains(&block.contents)
                    || parsed.contains(block.contents.as_str()),
                "the block at line {} is not parsed",
                block.line
            );
        }
        for (line, reason) in NOT_SOURCE {
            let found = blocks
                .iter()
                .filter(|block| block.contents.lines().any(|l| l == *line))
                .count();
            assert_eq!(
                found, 1,
                "NOT_SOURCE {line:?} ({reason}) names {found} blocks"
            );
        }
    });
    h.case("parser/the tour parses to its statements and items", || {
        let tour = spec_sources()
            .iter()
            .find(|s| s.label == "case tour tour.en")
            .expect("the tour");
        let parsed = Parsed::new(&tour.name, &tour.text);
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        assert_eq!(parsed.tree.stmts.len(), 3);
        let names: Vec<String> = parsed
            .tree
            .items
            .iter()
            .map(|item| match &item.kind {
                ItemKind::Enum(decl) => decl.name.name.to_string(),
                ItemKind::Class(decl) => decl.name.name.to_string(),
                ItemKind::Function(decl) => decl.name.name.to_string(),
                other => panic!("unexpected item {other:?}"),
            })
            .collect();
        assert_eq!(names, ["Op", "Stack", "Trace", "pop2", "run"]);
        assert!(
            parsed
                .tree
                .items
                .iter()
                .all(|item| item.visibility == Some(Visibility::Private))
        );
    });
    h.case(
        "parser/Ownership in three lines is a program with local functions",
        || {
            let block = spec_sources()
                .iter()
                .find(|s| s.label == "case ownership ownership.en")
                .expect("the ownership block");
            let parsed = Parsed::new(&block.name, &block.text);
            assert!(parsed.diags.is_empty(), "{}", parsed.listing());
            assert!(parsed.tree.items.is_empty());
            let kinds: Vec<&str> = parsed
                .tree
                .stmts
                .iter()
                .map(|stmt| match stmt.kind {
                    StmtKind::LocalFn { .. } => "fn",
                    StmtKind::VarDecl(_) => "decl",
                    StmtKind::Expr(_) => "expr",
                    _ => "other",
                })
                .collect();
            assert_eq!(kinds, ["fn", "fn", "fn", "decl", "expr", "expr", "decl"]);
        },
    );
}

fn register_fixtures(h: &mut Harness) {
    h.case(
        "parser/TESTING 23's M1 fixtures are the ones tested",
        || {
            let tested: Vec<&str> = m1_fixtures().iter().map(|(source, ..)| *source).collect();
            assert_eq!(m1_row_fixtures(), tested);
        },
    );
    for (source, want, allowed) in m1_fixtures() {
        h.case(format!("parser/M1 fixture/{source}"), move || {
            let parsed = Parsed::new("fixture.en", &format!("{source};\n"));
            for diag in &parsed.diags {
                assert!(allowed.contains(&diag.code), "{}", parsed.listing());
            }
            assert_eq!(erase(parsed.expr()), want);
        });
    }
}

fn register_shapes(h: &mut Harness) {
    for &(source, want) in PRECEDENCE {
        let label = source.replace('\n', "\\n");
        h.case(format!("parser/shape/{label}"), move || {
            let parsed = Parsed::new("shape.en", &format!("{source};\n"));
            let allowed = [Code::EN0107, Code::EN0106];
            for diag in &parsed.diags {
                assert!(allowed.contains(&diag.code), "{}", parsed.listing());
            }
            assert_eq!(shape(parsed.expr()), want);
        });
    }
    for &(source, want) in TYPES {
        h.case(format!("parser/type/{source}"), move || {
            let parsed = Parsed::new("type.en", &format!("let x: {source} = y;\n"));
            assert!(parsed.diags.is_empty(), "{}", parsed.listing());
            let [
                Stmt {
                    kind: StmtKind::VarDecl(decl),
                    ..
                },
            ] = parsed.tree.stmts.as_slice()
            else {
                panic!("expected one declaration: {:#?}", parsed.tree);
            };
            let ty = decl.ty.as_ref().expect("a type");
            assert_eq!(ty_shape(ty), want);
            assert!(decl.init.is_some());
        });
    }
    h.case("parser/split_token/`Box<i32>=` splits `>=`", || {
        let parsed = Parsed::new("split.en", "let x: Box<i32>= v;\n");
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let StmtKind::VarDecl(decl) = &parsed.tree.stmts[0].kind else {
            panic!("a declaration");
        };
        assert_eq!(ty_shape(decl.ty.as_ref().expect("a type")), "Box<i32>");
        assert_eq!(shape(decl.init.as_ref().expect("a value")), "v");
    });
    h.case(
        "parser/split_token/type parameters close inside `>>`",
        || {
            let parsed = Parsed::new(
                "split.en",
                "private function f<T extends Box<U>>(x: Box<Box<T>>): void {}\n",
            );
            assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        },
    );
}

fn register_spread(h: &mut Harness) {
    h.case("parser/EN1013/every form of TESTING 18 is tested", || {
        let tested: Vec<&str> = EN1013_FILES.iter().map(|(form, _)| *form).collect();
        let mut row = en1013_row_forms();
        row.sort();
        let mut tested_sorted: Vec<String> = tested.iter().map(|s| (*s).to_owned()).collect();
        tested_sorted.sort();
        assert_eq!(row, tested_sorted);
    });
    for &(form, text) in EN1013_FILES {
        h.case(format!("parser/EN1013/{form}"), move || {
            let parsed = Parsed::new("spread.en", &format!("{text}\n"));
            assert_eq!(
                parsed.reports(),
                [(Code::EN1013, "...".to_owned())],
                "{}",
                parsed.listing()
            );
        });
    }
    for (text, want) in spread_rows() {
        h.case(format!("parser/spread/{text}"), move || {
            let parsed = Parsed::new("spread.en", &format!("{text}\n"));
            let want: Vec<(Code, String)> = want
                .iter()
                .map(|&(code, at)| (code, at.to_owned()))
                .collect();
            assert_eq!(parsed.reports(), want, "{}", parsed.listing());
        });
    }
    h.case(
        "parser/spread/`a...b` in a range has a fix-it to `..`",
        || {
            let parsed = Parsed::new("spread.en", "for (const i of a...b) {}\n");
            let help = &parsed.diags[0].helps[0];
            assert_eq!(help.edits.len(), 1);
            assert_eq!(help.edits[0].replacement, "..");
            assert_eq!(parsed.text(help.edits[0].span), "...");
            let StmtKind::ForOf(stmt) = &parsed.tree.stmts[0].kind else {
                panic!("a for...of");
            };
            assert!(matches!(stmt.source, ForOfSource::Range(..)));
        },
    );
}

/// SPEC 3.1, 3.3, 3.4 and 3.6: where each form lands in the tree.
fn register_structure(h: &mut Harness) {
    h.case("parser/structure/`{` at statement start is a block", || {
        let parsed = Parsed::new("s.en", "{ f(); }\n");
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        assert!(matches!(parsed.tree.stmts[0].kind, StmtKind::Block(_)));
    });
    h.case(
        "parser/structure/an object literal statement fails at `:`",
        || {
            let parsed = Parsed::new("s.en", "{ name: \"Ada\", age: 36 };\n");
            assert!(!parsed.diags.is_empty());
            assert!(parsed.diags.iter().all(|d| d.code == Code::EN0100));
        },
    );
    h.case("parser/structure/a statement `match` ends at `}`", || {
        let parsed = Parsed::new("s.en", "match (x) { 1 => a, default => b }\nf();\n");
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        assert_eq!(parsed.tree.stmts.len(), 2);
        let StmtKind::Expr(expr) = &parsed.tree.stmts[0].kind else {
            panic!("an expression statement");
        };
        let ExprKind::Match { arms, .. } = &expr.kind else {
            panic!("a match");
        };
        assert_eq!(arms.len(), 2);
        assert!(arms[1].values.is_empty());
    });
    h.case("parser/structure/arm values", || {
        let parsed = Parsed::new(
            "s.en",
            "while (go) {\n  match (x) { null => 0, Ok => 1, Err => 2, Op.Push => 3, -1, 2 => 4, 0..9 => 5, \"s\" => 6, x => 7, a, b if c => return, default => break }\n}\n",
        );
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let StmtKind::While(looped) = &parsed.tree.stmts[0].kind else {
            panic!("a loop");
        };
        let StmtKind::Expr(expr) = &looped.body.stmts[0].kind else {
            panic!("an expression statement");
        };
        let ExprKind::Match { arms, .. } = &erase(expr).kind else {
            panic!("a match");
        };
        let d = Span::DUMMY;
        assert_eq!(arms[0].values, [ArmValue::Null(d)]);
        assert_eq!(arms[1].values, [ArmValue::Ok(d)]);
        assert_eq!(arms[2].values, [ArmValue::Err(d)]);
        assert_eq!(arms[3].values, [ArmValue::Case(vec![name("Op"), name("Push")])]);
        assert!(matches!(arms[4].values.as_slice(), [ArmValue::Value(_), ArmValue::Value(_)]));
        assert!(matches!(arms[5].values.as_slice(), [ArmValue::Range(..)]));
        assert!(matches!(arms[6].values.as_slice(), [ArmValue::Value(_)]));
        assert_eq!(arms[7].values, [ArmValue::Case(vec![name("x")])]);
        assert_eq!(arms[8].values.len(), 2);
        assert!(arms[8].guard.is_some());
        assert_eq!(arms[8].body, ArmBody::Return(None));
        assert_eq!(arms[9].body, ArmBody::Break(None));
    });
    h.case(
        "parser/structure/a named literal's `{` is on the same line",
        || {
            let parsed = Parsed::new("s.en", "const p = Point\n{ x: 1 };\n");
            assert!(!parsed.diags.is_empty());
            let parsed = Parsed::new("s.en", "const p = new Point\n{ x: 1 };\n");
            assert!(!parsed.diags.is_empty());
        },
    );
    h.case("parser/structure/member modifiers need a name after them", || {
        let parsed = Parsed::new(
            "s.en",
            "private class A {\n  public move(): void {}\n  public get(i: isize): &T | null { return null; }\n  public static let: i64 = 1;\n  public static withCapacity(n: isize): A { return new A(); }\n  public override readonly x: readonly &T;\n  public let unsafe m(): void;\n}\n",
        );
        let ItemKind::Class(class) = &parsed.tree.items[0].kind else {
            panic!("a class");
        };
        let method = |index: usize| match &class.members[index].kind {
            ClassMemberKind::Method(m) => m,
            other => panic!("expected a method, found {other:?}"),
        };
        assert_eq!(method(0).name.name.as_str(), "move");
        assert_eq!(method(0).receiver, Receiver::Plain);
        assert_eq!(method(1).name.name.as_str(), "get");
        assert_eq!(method(3).receiver, Receiver::Static);
        let ClassMemberKind::Field(field) = &class.members[4].kind else {
            panic!("a field");
        };
        assert!(field.is_override && field.is_readonly);
        assert!(matches!(field.ty.kind, TypeExprKind::ReadonlyRef(_)));
        assert_eq!(method(5).receiver, Receiver::Let);
        assert!(method(5).is_unsafe && method(5).body.is_none());
        // `static` before a field is EN1021; the field stays.
        assert_eq!(
            parsed.reports().iter().map(|(c, t)| (*c, t.as_str())).collect::<Vec<_>>(),
            [(Code::EN1021, "static")],
            "{}",
            parsed.listing()
        );
    });
    h.case(
        "parser/structure/a file with no statements has no program",
        || {
            let parsed = Parsed::new(
                "s.en",
                "public class A {}\nfunction helper() {}\nassert(true);\n",
            );
            assert!(parsed.tree.stmts.is_empty());
            assert_eq!(parsed.tree.items.len(), 3);
            assert!(matches!(parsed.tree.items[1].kind, ItemKind::Function(_)));
            assert_eq!(parsed.tree.items[1].visibility, None);
            assert!(matches!(
                parsed.tree.items[2].kind,
                ItemKind::StaticAssert { .. }
            ));
        },
    );
    h.case(
        "parser/structure/a program keeps its local functions",
        || {
            let parsed = Parsed::new(
                "s.en",
                "console.log(1);\npublic class A {}\nfunction helper() {}\n",
            );
            assert_eq!(parsed.tree.stmts.len(), 2);
            assert!(matches!(
                parsed.tree.stmts[1].kind,
                StmtKind::LocalFn { .. }
            ));
            assert_eq!(parsed.tree.items.len(), 1);
        },
    );
    h.case("parser/structure/imports", || {
        let parsed = Parsed::new(
            "s.en",
            "import { a, b as c } from \"./x\";\nimport * as ns from \"core\";\npublic import { d } from '../y';\n",
        );
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let imports = &parsed.tree.imports;
        assert_eq!(imports.len(), 3);
        let ImportKind::Named(names) = &imports[0].kind else {
            panic!("named");
        };
        assert_eq!(names[1].alias.map(|i| i.name.as_str()), Some("c"));
        assert!(matches!(imports[1].kind, ImportKind::Namespace(_)));
        assert!(imports[2].public);
        assert_eq!(imports[2].path.value.as_str(), "../y");
    });
    h.case("parser/structure/for...in is a ForOf with its `in`", || {
        let parsed = Parsed::new("s.en", "for (const k in o) {}\n");
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let StmtKind::ForOf(stmt) = &parsed.tree.stmts[0].kind else {
            panic!("a for...of");
        };
        assert_eq!(parsed.text(stmt.in_keyword.expect("the `in`")), "in");
    });
    h.case("parser/structure/expect statements and their matchers", || {
        let parsed = Parsed::new(
            "s.test.en",
            "expect(a).toBe(b);\nexpect(x).toEqual(cfg.limit);\nexpect(s).toMatchPattern(Shape.Circle);\nexpect(t, ).not.toBeNull();\nexpect(1);\n",
        );
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let expect = |index: usize| match &parsed.tree.stmts[index].kind {
            StmtKind::Expect(stmt) => stmt,
            other => panic!("expected an expect statement, found {other:?}"),
        };
        assert!(matches!(expect(0).args.as_slice(), [MatcherArg::Expr(_)]));
        assert!(matches!(expect(1).args.as_slice(), [MatcherArg::Expr(_)]));
        assert!(matches!(
            expect(2).args.as_slice(),
            [MatcherArg::Arm(ArmValue::Case(_))]
        ));
        assert!(expect(3).negated);
        assert!(matches!(parsed.tree.stmts[4].kind, StmtKind::Expr(_)));
    });
    h.case("parser/structure/asm options keep their spans", || {
        let parsed = Parsed::new("s.en", "asm(\"hlt\", { in: {}, clobbers: [] });\n");
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let ExprKind::Asm(asm) = &parsed.expr().kind else {
            panic!("an asm");
        };
        let options = asm.options.as_ref().expect("options");
        let texts: Vec<&str> = options.iter().map(|o| parsed.text(o.span)).collect();
        assert_eq!(texts, ["in: {}", "clobbers: []"]);
        let parsed = Parsed::new("s.en", "asm(\"hlt\");\n");
        let ExprKind::Asm(asm) = &parsed.expr().kind else {
            panic!("an asm");
        };
        assert!(asm.options.is_none());
    });
    h.case("parser/structure/test items at the top level, calls inside", || {
        let parsed = Parsed::new(
            "s.test.en",
            "test(\"a\", () => { test(\"b\"); });\ndescribe(\"d\", () => {\n  test.todo(\"c\");\n  compileOk(\"e\", raw`x`);\n});\nassert(true, \"m\");\n",
        );
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        assert!(parsed.tree.stmts.is_empty());
        let ItemKind::Test(test) = &parsed.tree.items[0].kind else {
            panic!("a test");
        };
        let body = test.body.as_ref().expect("a body");
        let ArrowBody::Block(block) = &body.body else {
            panic!("a block body");
        };
        assert!(matches!(block.stmts[0].kind, StmtKind::Expr(_)));
        let ItemKind::Describe(describe) = &parsed.tree.items[1].kind else {
            panic!("a describe");
        };
        assert_eq!(describe.items.len(), 2);
        assert!(matches!(
            parsed.tree.items[2].kind,
            ItemKind::StaticAssert {
                message: Some(_),
                ..
            }
        ));
    });
    h.case("parser/structure/test arguments in their order", || {
        let parsed = Parsed::new(
            "s.test.en",
            "test.each(\"p\", () => [1, 2], (c: &i64): void => { f(c); }, { fuel: 5 });\ntest.panics(\"q\", \"bounds\", () => { g(); });\n",
        );
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let ItemKind::Test(each) = &parsed.tree.items[0].kind else {
            panic!("a test");
        };
        assert_eq!(each.mode, Some(TestMode::Each));
        assert!(matches!(each.extra, Some(TestExtra::Cases(_))));
        assert!(each.body.as_ref().is_some_and(|body| body.ret.is_some()));
        assert!(each.options.is_some());
        let ItemKind::Test(panics) = &parsed.tree.items[1].kind else {
            panic!("a test");
        };
        assert!(matches!(panics.extra, Some(TestExtra::Message(_))));
    });
    h.case("parser/structure/destructuring nests", || {
        let parsed = Parsed::new(
            "s.en",
            "const { name: who, pos: { x, y } } = &ada;\nfor (const [i, { name }] of &pairs) {}\n[a, b] = [b, a];\n",
        );
        assert!(parsed.diags.is_empty(), "{}", parsed.listing());
        let StmtKind::VarDecl(decl) = &parsed.tree.stmts[0].kind else {
            panic!("a declaration");
        };
        let Binding::Object { fields, .. } = &decl.binding else {
            panic!("an object pattern");
        };
        assert!(matches!(fields[1].1, Some(Binding::Object { .. })));
    });
    h.case(
        "parser/structure/library functions may take any member name",
        || {
            let file = {
                let mut map = enrang_base::SourceMap::new();
                let id = map.add(
                    std::path::PathBuf::from("core/ptr.en"),
                    std::sync::Arc::from("public function null<T>(): *T { return 0 as *T; }\n"),
                    enrang_base::FileOrigin::Library,
                );
                map.file(id).clone()
            };
            let mut dcx = DiagCtx::new();
            let tree = parse_file(&file, &mut NodeIdGen::new(), ParseMode::Build, &mut dcx);
            assert!(!dcx.has_errors());
            let ItemKind::Function(decl) = &tree.items[0].kind else {
                panic!("a function");
            };
            assert_eq!(decl.name.name.as_str(), "null");
            let user = Parsed::new("user.en", "public function null(): void {}\n");
            assert!(!user.diags.is_empty());
        },
    );
    h.case(
        "parser/structure/node ids are unique and spans nest",
        || {
            let tour = spec_sources()
                .iter()
                .find(|s| s.label == "case tour tour.en")
                .expect("the tour");
            let parsed = Parsed::new(&tour.name, &tour.text);
            crate::parser_props::check_tree(&parsed).unwrap_or_else(|why| panic!("{why}"));
        },
    );
}
