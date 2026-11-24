//! The generators of the syntax suite (TESTING 14, plan d.5).
//!
//! `GenSyntax`: random well-formed trees from the grammar of SPEC 3, built with no
//! source, as a tool builds them. Each is printed by `fmt` and parsed back, which
//! must report nothing and give the same tree after `erase`, with its imports in the
//! order of SPEC 12.5's Imports rule; printing the parsed file again must change
//! nothing (TESTING 14: format, reparse, equal AST, and a second format changes
//! nothing). The default run makes `scaled(200)` programs, a tenth of TESTING 23's
//! 2k, as TESTING 14 sets the default scale, and checks that they reach every node
//! kind of the tree.
//!
//! The generator writes every `Paren` node the printed text needs, as the parser
//! records the parentheses an author wrote, and never makes what SPEC rejects: no
//! `break` outside a loop, no assignment as a condition, no chained comparison, no
//! `??` beside an unparenthesised `&&` or `||`, no statement that starts with `{` or
//! with a `match` it does not end at, no `?` right after a postfix `?` (SPEC 2: `??`
//! is one token, and `x? ?` has a spaced postfix). Where SPEC's grammar is
//! ambiguous, it writes the form the parser reads back: a match guard or arm value
//! holds no unparenthesised ternary, assignment or arrow (SPEC 3.4 gives a guard any
//! `Expr`, so a last `x =>` there could be an arrow), and a ternary's first branch
//! holds no unparenthesised ternary (whose own `(x) : T => y` would read as an
//! annotated arrow).
//!
//! `GenBytes`, the half that concerns `fmt`: SPEC's blocks mutated by the parser
//! properties' mutator never make the parser or the printer panic, and each mutant
//! that parses with no diagnostic passes the four tests of TESTING 17, over
//! `scaled(2_000)` files, a tenth of TESTING 23's 20k. Its other half mutates bytes:
//! the bytes of SPEC's blocks and of the compile fixtures, with bits flipped, bytes
//! cut, copied and inserted, invalid UTF-8 and byte order marks among them, go
//! through the driver's path, `decode_source`, EN0001, the parser and the printer,
//! and nothing panics, over another `scaled(2_000)` files.
//!
//! Every choice of `GenSyntax` comes from a tape, drawn from the seeded generator and
//! recorded, or replayed, where a missing entry reads as 0, the simplest choice. A
//! failure shrinks its tape, or a mutant its text, with the testkit's shrinker, and
//! reports `ENRANG_SEED` and the shrunk input. Each shrunk failure stays as a
//! permanent test (TESTING 14) in `corpus/regress/syntax/`: a file in the canonical
//! style that passes the four tests with its source and the round trip with none.

use std::collections::BTreeSet;
use std::fs;

use enrang_base::{Span, Symbol, intern};
use enrang_diag::DiagCtx;
use enrang_syntax::ast::*;
use enrang_syntax::{
    NodeIdGen, ParseMode, decode_source, erase, parse_file, print_file, report_invalid_utf8,
};
use enrang_testkit::{
    Harness, Rng, Xoshiro256, catch_panic, line_diff, rng_for, scaled, seed, shrink_within,
    workspace_root,
};

use crate::fmt::{four_tests_as, try_parse};
use crate::parser::{Parsed, spec_sources};
use crate::parser_props::{mutate, soup_words};
use crate::support::source;

const SPAN: Span = Span::DUMMY;
const ID: NodeId = NodeId(0);

/// How deep statements, expressions and types nest before only leaves are made.
const MAX_DEPTH: u32 = 5;

/// How many nodes past the leaves one program may make, roughly.
const FUEL: u32 = 260;

/// The most predicate calls a failure's shrink may make.
const SHRINK_LIMIT: usize = 3_000;

/// Names of values: plain identifiers, `$` and non-ASCII included, and none of the
/// contextual words or names the parser treats specially (`expect`, `test`,
/// `assert`, `sizeOf`, `require`, `Promise`, `Ok`, `beforeEach` and the like).
const VALUES: &[&str] = &[
    "a", "b", "c", "x", "y", "n", "i", "count", "items", "value", "node", "total", "x_1", "$el",
    "café", "_tmp",
];

/// Names of types and type parameters.
const TYPES: &[&str] = &[
    "T", "U", "K", "Point", "Shape", "Stack", "Node", "i64", "u8", "usize", "string", "bool",
    "f64", "Result", "Box", "Slice",
];

/// Member names: identifiers, and keywords and reserved words, which a member may be
/// named by (SPEC 3.1 `MemberName`).
const MEMBERS: &[&str] = &[
    "x", "y", "len", "push", "pop", "items", "value", "next", "type", "new", "default", "delete",
    "in", "from", "of", "match", "get", "move", "static", "let", "void",
];

/// Labels of loops.
const LABELS: &[&str] = &["outer", "inner", "scan", "rows"];

/// Decorator names.
const DECORATORS: &[&str] = &[
    "entry", "mustUse", "section", "align", "was", "packed", "abi",
];

/// Matchers of `expect`.
const MATCHERS: &[&str] = &["toBe", "toEqual", "toBeNull", "toContain", "toMatchPattern"];

/// Registers.
const REGISTERS: &[&str] = &["eax", "ebx", "dx", "al", "rdi"];

/// Characters a string, template or raw text is made of: plain text, the quotes
/// and the characters that need escapes, control characters and non-ASCII.
const CHARS: &[char] = &[
    'a', 'b', 'z', ' ', '0', '9', '"', '\'', '`', '\\', '$', '{', '}', '\n', '\t', '\r', '\0',
    '\u{1}', '\u{7f}', 'é', '漢', '😀', '/', '*', '<', '&',
];

// ---------------------------------------------------------------------------------
// The tape.

/// Where the generator's choices come from: drawn from `rng` and recorded in
/// `values`, or, with no `rng`, replayed from `values`, where a missing entry is 0.
struct Tape {
    values: Vec<u64>,
    at: usize,
    rng: Option<Xoshiro256>,
}

impl Tape {
    /// A value in `0..n`.
    fn draw(&mut self, n: u64) -> u64 {
        let value = match (self.values.get(self.at), &mut self.rng) {
            (Some(&value), _) => value % n,
            (None, Some(rng)) => {
                let value = rng.below(n);
                self.values.push(value);
                value
            }
            (None, None) => 0,
        };
        self.at += 1;
        value
    }
}

// ---------------------------------------------------------------------------------
// Nodes.

fn mk(kind: ExprKind) -> Expr {
    Expr {
        id: ID,
        span: SPAN,
        kind,
    }
}

fn mk_ty(kind: TypeExprKind) -> TypeExpr {
    TypeExpr {
        id: ID,
        span: SPAN,
        kind,
    }
}

fn mk_stmt(kind: StmtKind) -> Stmt {
    Stmt {
        id: ID,
        kind,
        span: SPAN,
    }
}

fn ident(name: &str) -> Ident {
    Ident {
        name: intern(name),
        span: SPAN,
    }
}

fn paren(expr: Expr) -> Expr {
    mk(ExprKind::Paren(Box::new(expr)))
}

/// The level of SPEC 3.5's table that `expr` binds at: 1 for a primary or postfix
/// form, up to 17 for an arrow.
fn level(expr: &Expr) -> u8 {
    match &expr.kind {
        ExprKind::Unary(..) | ExprKind::Borrow(_) | ExprKind::Deref(_) | ExprKind::VoidOp(_) => 2,
        ExprKind::IncDec { prefix: true, .. } => 2,
        ExprKind::Cast(..) => CAST_PRECEDENCE,
        ExprKind::Binary(op, ..) => op.precedence(),
        ExprKind::Logical(op, ..) => op.precedence(),
        ExprKind::Coalesce(..) => COALESCE_PRECEDENCE,
        ExprKind::Ternary(..) => TERNARY_PRECEDENCE,
        ExprKind::Assign { .. } => ASSIGN_PRECEDENCE,
        ExprKind::Arrow(_) => 17,
        _ => 1,
    }
}

/// `expr`, in parentheses when it binds looser than `max`.
fn fit(expr: Expr, max: u8) -> Expr {
    if level(&expr) > max {
        paren(expr)
    } else {
        expr
    }
}

/// The node whose first token is `expr`'s first token.
fn leftmost(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Binary(_, left, _)
        | ExprKind::Logical(_, left, _)
        | ExprKind::Coalesce(left, _)
        | ExprKind::Ternary(left, ..)
        | ExprKind::Cast(left, _)
        | ExprKind::Member { base: left, .. }
        | ExprKind::Index(left, _)
        | ExprKind::Try(left)
        | ExprKind::NonNull(left) => leftmost(left),
        ExprKind::Assign { target, .. } => leftmost(target),
        ExprKind::IncDec {
            target,
            prefix: false,
            ..
        } => leftmost(target),
        ExprKind::Call { callee, .. } => leftmost(callee),
        _ => expr,
    }
}

/// `expr` as the start of a statement or an arrow's or arm's body, where `{` always
/// starts a block (SPEC 3.4): in parentheses when it starts with an object literal,
/// or, with `statement`, with a `match` it does not end at (SPEC 3.3).
fn at_start(expr: Expr, statement: bool) -> Expr {
    let first = leftmost(&expr);
    let brace = matches!(first.kind, ExprKind::ObjectLit(_));
    let open_match = statement
        && matches!(first.kind, ExprKind::Match { .. })
        && !matches!(expr.kind, ExprKind::Match { .. });
    if brace || open_match {
        paren(expr)
    } else {
        expr
    }
}

/// How a type binds: 0 a postfix or primary type, 1 a prefix type, 2 a type with
/// `|`, 3 a type open on the right, whose last part is a closure or function
/// pointer type, which would take in a `|` or `[]` after it.
fn ty_level(ty: &TypeExpr) -> u8 {
    match &ty.kind {
        TypeExprKind::Ref(inner) | TypeExprKind::Raw(inner) => {
            if ty_level(inner) == 3 {
                3
            } else {
                1
            }
        }
        TypeExprKind::Nullable(_) | TypeExprKind::Union(_) => 2,
        TypeExprKind::Closure(_) | TypeExprKind::FnPtr(_) => 3,
        _ => 0,
    }
}

fn fit_ty(ty: TypeExpr, max: u8) -> TypeExpr {
    if ty_level(&ty) > max {
        mk_ty(TypeExprKind::Paren(Box::new(ty)))
    } else {
        ty
    }
}

/// Whether `ty` may follow `readonly` as a return type (SPEC 3.1 `RetType`).
fn takes_readonly(ty: &TypeExpr) -> bool {
    let inner = match &ty.kind {
        TypeExprKind::Nullable(inner) => inner,
        _ => ty,
    };
    match &inner.kind {
        TypeExprKind::Ref(_) | TypeExprKind::Named { .. } => true,
        TypeExprKind::Tuple(elems) => elems
            .iter()
            .any(|elem| matches!(elem.kind, TypeExprKind::Ref(_))),
        _ => false,
    }
}

// ---------------------------------------------------------------------------------
// The generator.

struct Gen {
    tape: Tape,
    depth: u32,
    fuel: u32,
    /// The loops around the current statement since the nearest function or arrow
    /// body, each with its label.
    loops: Vec<Option<Symbol>>,
    /// Every label in scope, so that none is used twice (EN0113).
    labels: Vec<Symbol>,
    test_file: bool,
}

impl Gen {
    fn new(tape: Tape) -> Gen {
        Gen {
            tape,
            depth: 0,
            fuel: FUEL,
            loops: Vec::new(),
            labels: Vec::new(),
            test_file: false,
        }
    }

    fn draw(&mut self, n: usize) -> usize {
        self.tape.draw(n as u64) as usize
    }

    /// True `percent` times in 100; a replayed 0 is false.
    fn chance(&mut self, percent: usize) -> bool {
        self.draw(100) >= 100 - percent
    }

    fn upto(&mut self, max: usize) -> usize {
        self.draw(max + 1)
    }

    /// Whether only leaves may be made now.
    fn low(&self) -> bool {
        self.depth >= MAX_DEPTH || self.fuel == 0
    }

    /// `make` one level deeper, spending fuel.
    fn nest<R>(&mut self, make: impl FnOnce(&mut Gen) -> R) -> R {
        self.depth += 1;
        self.fuel = self.fuel.saturating_sub(1);
        let made = make(self);
        self.depth -= 1;
        made
    }

    /// A list length up to `max`, short when low.
    fn len(&mut self, max: usize) -> usize {
        if self.low() {
            self.upto(max.min(1))
        } else {
            self.upto(max)
        }
    }

    fn word(&mut self, pool: &[&str]) -> Ident {
        let at = self.draw(pool.len());
        ident(pool[at])
    }

    fn value_name(&mut self) -> Ident {
        self.word(VALUES)
    }

    fn type_name(&mut self) -> Ident {
        self.word(TYPES)
    }

    fn member_name(&mut self) -> Ident {
        if self.chance(25) {
            self.word(MEMBERS)
        } else {
            self.word(VALUES)
        }
    }

    fn text(&mut self, raw: bool) -> String {
        let len = self.upto(6);
        let mut text = String::new();
        for _ in 0..len {
            let c = CHARS[self.draw(CHARS.len())];
            // A raw template holds any character but a backtick (SPEC 2), and a CR
            // there would come back as written, which `fmt` turns into LF.
            if raw && matches!(c, '`' | '\r') {
                continue;
            }
            text.push(c);
        }
        text
    }

    fn str_lit(&mut self) -> StrLit {
        let text = self.text(false);
        StrLit {
            value: intern(&text),
            span: SPAN,
        }
    }

    // -----------------------------------------------------------------------------
    // Literals.

    fn int(&mut self) -> Expr {
        let value: u128 = match self.draw(4) {
            0 => self.draw(10) as u128,
            1 => self.draw(1000) as u128,
            2 => 0xB8000,
            _ => u128::from(u32::MAX),
        };
        let text = match self.draw(6) {
            0 | 1 => value.to_string(),
            2 => format!("0x{value:X}"),
            3 => format!("0x{value:x}"),
            4 => format!("0o{value:o}"),
            _ => format!("0b{value:b}"),
        };
        let text = if self.chance(15) && text.len() > 2 && !text.starts_with('0') {
            format!("{}_{}", &text[..1], &text[1..])
        } else {
            text
        };
        mk(ExprKind::Int {
            value,
            text: intern(&text),
        })
    }

    fn float(&mut self) -> Expr {
        let text = [
            "1.5", "0.25", "1e10", "2.5E-3", "1_000.5", "3.0", "6e+2", "0.0",
        ][self.draw(8)];
        mk(ExprKind::Float(intern(text)))
    }

    fn string(&mut self) -> Expr {
        let text = self.text(false);
        mk(ExprKind::Str(intern(&text)))
    }

    fn template(&mut self) -> Expr {
        let holes = if self.low() { 0 } else { self.upto(2) };
        let mut parts = Vec::new();
        let text = self.text(false);
        parts.push(TplPart::Str(intern(&text)));
        for _ in 0..holes {
            let hole = self.nest(|g| g.expr_or_assign(17));
            parts.push(TplPart::Expr(hole));
            let text = self.text(false);
            parts.push(TplPart::Str(intern(&text)));
        }
        mk(ExprKind::Template(parts))
    }

    fn raw_template(&mut self) -> Expr {
        let text = self.text(true);
        mk(ExprKind::RawTemplate(intern(&text)))
    }

    fn leaf(&mut self) -> Expr {
        match self.draw(12) {
            0..=2 => mk(ExprKind::Ident(self.value_name().name)),
            3 | 4 => self.int(),
            5 => self.float(),
            6 => self.string(),
            7 => mk(ExprKind::Bool(self.chance(50))),
            8 => mk(ExprKind::Null),
            9 => mk(ExprKind::This),
            10 => self.template(),
            _ => self.raw_template(),
        }
    }

    // -----------------------------------------------------------------------------
    // Expressions.

    /// An expression that binds at `max` or tighter, never an assignment at its top.
    fn expr(&mut self, max: u8) -> Expr {
        if self.low() {
            return self.leaf();
        }
        let expr = self.nest(|g| match g.draw(30) {
            0..=4 => g.leaf(),
            5..=7 => g.binary(),
            8 => g.logical(),
            9 => g.coalesce(),
            10 => g.ternary(),
            11 | 12 => g.unary(),
            13 => g.cast(),
            14..=16 => g.postfix(),
            17 | 18 => g.call(),
            19 => g.arrow(),
            20 => g.array(),
            21 => g.object(),
            22 => g.new_expr(),
            23 => g.case_lit(),
            24 => g.match_expr(),
            25 => g.template(),
            26 => g.special(),
            27 => g.type_member(),
            28 => paren(g.expr(17)),
            _ => g.repeat(),
        });
        fit(expr, max)
    }

    /// An expression that may be an assignment, where SPEC allows one: never a
    /// condition or an operand of `&&`, `||` or `!`, which EN0105 forbids even in
    /// parentheses.
    fn expr_or_assign(&mut self, max: u8) -> Expr {
        if !self.low() && self.chance(12) {
            let assign = self.nest(|g| g.assign());
            if self.chance(20) {
                paren(assign)
            } else {
                fit(assign, max)
            }
        } else {
            self.expr(max)
        }
    }

    /// `e`, never an unparenthesised `&&` or `||` (SPEC 3.4: `??` does not mix).
    fn no_logical(expr: Expr) -> Expr {
        if matches!(expr.kind, ExprKind::Logical(..)) {
            paren(expr)
        } else {
            expr
        }
    }

    fn binary(&mut self) -> Expr {
        let op = BinOp::ALL[self.draw(BinOp::ALL.len())];
        let level = op.precedence();
        // Levels 7 and 8 do not associate (EN0107).
        let left_max = if op.is_comparison() { level - 1 } else { level };
        let left = self.expr(left_max);
        let right = self.expr(level - 1);
        mk(ExprKind::Binary(op, Box::new(left), Box::new(right)))
    }

    fn logical(&mut self) -> Expr {
        let op = if self.chance(50) {
            LogOp::Or
        } else {
            LogOp::And
        };
        let level = op.precedence();
        let left = self.expr(level);
        let right = self.expr(level - 1);
        mk(ExprKind::Logical(op, Box::new(left), Box::new(right)))
    }

    fn coalesce(&mut self) -> Expr {
        let left = Gen::no_logical(self.expr(COALESCE_PRECEDENCE - 1));
        let right = Gen::no_logical(self.expr(COALESCE_PRECEDENCE));
        mk(ExprKind::Coalesce(Box::new(left), Box::new(right)))
    }

    /// A ternary. Its first branch holds no unparenthesised ternary, assignment or
    /// arrow with a long body, so no `(x) : T => y` inside it is read as an arrow
    /// in the first branch (SPEC 3.4).
    fn ternary(&mut self) -> Expr {
        let cond = self.expr(COALESCE_PRECEDENCE);
        let then = if self.chance(10) {
            self.arrow_with(true)
        } else {
            self.expr(COALESCE_PRECEDENCE)
        };
        let otherwise = self.expr(17);
        mk(ExprKind::Ternary(
            Box::new(cond),
            Box::new(then),
            Box::new(otherwise),
        ))
    }

    /// A place: what may be assigned or incremented (SPEC 3.4, EN0114), at `max`.
    fn place(&mut self, max: u8) -> Expr {
        let place = if self.low() {
            mk(ExprKind::Ident(self.value_name().name))
        } else {
            self.nest(|g| match g.draw(7) {
                0 | 1 => mk(ExprKind::Ident(g.value_name().name)),
                2 => {
                    let base = g.postfix_base();
                    mk(ExprKind::Member {
                        base: Box::new(base),
                        name: g.member_name(),
                        optional: false,
                    })
                }
                3 => {
                    let base = g.postfix_base();
                    let index = g.expr_or_assign(17);
                    mk(ExprKind::Index(Box::new(base), Box::new(index)))
                }
                4 => mk(ExprKind::Deref(Box::new(g.expr(2)))),
                5 => {
                    let base = g.postfix_base();
                    mk(ExprKind::NonNull(Box::new(base)))
                }
                _ => paren(g.place(17)),
            })
        };
        fit(place, max)
    }

    fn assign(&mut self) -> Expr {
        let op = AssignOp::ALL[self.draw(AssignOp::ALL.len())];
        let target = if op == AssignOp::Assign && self.chance(15) {
            self.pattern_target()
        } else {
            self.place(TERNARY_PRECEDENCE)
        };
        let value = self.expr_or_assign(17);
        mk(ExprKind::Assign {
            op,
            target: Box::new(target),
            value: Box::new(value),
        })
    }

    /// `[a, b]` or `{ a: x }` on the left of `=`: places and patterns, nested.
    fn pattern_target(&mut self) -> Expr {
        let len = self.len(3);
        if self.chance(50) {
            let elems = (0..len)
                .map(|_| {
                    let part = if !self.low() && self.chance(20) {
                        self.nest(|g| g.pattern_target())
                    } else {
                        self.place(17)
                    };
                    ArrayElem::Item(part)
                })
                .collect();
            mk(ExprKind::Array(elems))
        } else {
            let fields = (0..len)
                .map(|_| FieldInit {
                    name: self.member_name(),
                    value: Some(self.place(17)),
                    span: SPAN,
                })
                .collect();
            mk(ExprKind::ObjectLit(fields))
        }
    }

    fn unary(&mut self) -> Expr {
        match self.draw(8) {
            0 => mk(ExprKind::Unary(UnOp::Not, Box::new(self.expr(2)))),
            1 => mk(ExprKind::Unary(UnOp::Neg, Box::new(self.expr(2)))),
            2 => mk(ExprKind::Unary(UnOp::BitNot, Box::new(self.expr(2)))),
            3 => mk(ExprKind::Borrow(Box::new(self.expr(2)))),
            4 => mk(ExprKind::Deref(Box::new(self.expr(2)))),
            5 => mk(ExprKind::VoidOp(Box::new(self.expr(2)))),
            _ => {
                let target = self.place(2);
                mk(ExprKind::IncDec {
                    target: Box::new(target),
                    inc: self.chance(50),
                    prefix: true,
                })
            }
        }
    }

    fn cast(&mut self) -> Expr {
        let value = self.expr(CAST_PRECEDENCE);
        let ty = self.ty();
        mk(ExprKind::Cast(Box::new(value), fit_ty(ty, 1)))
    }

    /// The base of a postfix operation: a primary or postfix form. A member access
    /// after a postfix `?` is `x? .f` in print, since `?.` is one token (SPEC 2).
    fn postfix_base(&mut self) -> Expr {
        self.expr(1)
    }

    /// The operand of a postfix `?`: never another `?`, which no spelling allows
    /// (`x??` is `??`, and `x? ?` has a spaced postfix `?`, EN0103).
    fn try_operand(&mut self) -> Expr {
        let base = self.expr(1);
        if matches!(base.kind, ExprKind::Try(_)) {
            paren(base)
        } else {
            base
        }
    }

    fn postfix(&mut self) -> Expr {
        match self.draw(6) {
            0 | 1 => {
                let base = self.postfix_base();
                mk(ExprKind::Member {
                    base: Box::new(base),
                    name: self.member_name(),
                    optional: self.chance(30),
                })
            }
            2 => {
                let base = self.postfix_base();
                let index = self.expr_or_assign(17);
                mk(ExprKind::Index(Box::new(base), Box::new(index)))
            }
            3 => {
                let base = self.try_operand();
                mk(ExprKind::Try(Box::new(base)))
            }
            4 => {
                let base = self.expr(1);
                mk(ExprKind::NonNull(Box::new(base)))
            }
            _ => {
                let target = self.place(1);
                mk(ExprKind::IncDec {
                    target: Box::new(target),
                    inc: self.chance(50),
                    prefix: false,
                })
            }
        }
    }

    fn args(&mut self) -> Vec<Expr> {
        let len = self.len(3);
        (0..len).map(|_| self.expr_or_assign(17)).collect()
    }

    fn type_args(&mut self) -> Vec<TypeExpr> {
        let len = 1 + self.upto(1);
        (0..len).map(|_| self.ty()).collect()
    }

    /// A call. Type arguments follow only a path or a member access (SPEC 3.4).
    fn call(&mut self) -> Expr {
        let callee = match self.draw(4) {
            0 => mk(ExprKind::Ident(self.value_name().name)),
            1 => {
                let base = self.postfix_base();
                mk(ExprKind::Member {
                    base: Box::new(base),
                    name: self.member_name(),
                    optional: self.chance(20),
                })
            }
            _ => self.postfix_base(),
        };
        let takes_args = matches!(callee.kind, ExprKind::Ident(_) | ExprKind::Member { .. });
        let type_args = if takes_args && self.chance(25) {
            self.type_args()
        } else {
            Vec::new()
        };
        let args = self.args();
        mk(ExprKind::Call {
            callee: Box::new(callee),
            type_args,
            args,
        })
    }

    fn arrow(&mut self) -> Expr {
        self.arrow_with(false)
    }

    /// An arrow; in a ternary's first branch its body is an expression with no
    /// ternary, assignment or arrow at its top.
    fn arrow_with(&mut self, in_then: bool) -> Expr {
        let len = self.upto(2);
        let params: Vec<ArrowParam> = (0..len)
            .map(|_| ArrowParam {
                is_let: self.chance(15),
                name: self.value_name(),
                ty: if self.chance(50) {
                    Some(self.ty())
                } else {
                    None
                },
            })
            .collect();
        let ret = if self.chance(25) {
            Some(self.ret_type())
        } else {
            None
        };
        let body = if !in_then && self.chance(35) {
            ArrowBody::Block(self.body_block())
        } else {
            let saved = self.barrier();
            let body = if in_then {
                self.expr(COALESCE_PRECEDENCE)
            } else {
                self.expr_or_assign(17)
            };
            self.restore(saved);
            ArrowBody::Expr(Box::new(at_start(body, false)))
        };
        mk(ExprKind::Arrow(ArrowFn {
            params,
            ret,
            body,
            span: SPAN,
        }))
    }

    fn array(&mut self) -> Expr {
        let len = self.len(4);
        let elems = (0..len)
            .map(|_| {
                if self.chance(15) {
                    ArrayElem::Spread {
                        dots: SPAN,
                        expr: self.expr(17),
                    }
                } else {
                    ArrayElem::Item(self.expr_or_assign(17))
                }
            })
            .collect();
        mk(ExprKind::Array(elems))
    }

    fn repeat(&mut self) -> Expr {
        let value = self.expr(TERNARY_PRECEDENCE);
        let count = self.expr(TERNARY_PRECEDENCE);
        mk(ExprKind::Repeat(Box::new(value), Box::new(count)))
    }

    fn field_inits(&mut self) -> Vec<FieldInit> {
        let len = self.len(3);
        (0..len)
            .map(|_| {
                if self.chance(20) {
                    // The shorthand names a value, so it is a plain identifier.
                    FieldInit {
                        name: self.value_name(),
                        value: None,
                        span: SPAN,
                    }
                } else {
                    FieldInit {
                        name: self.member_name(),
                        value: Some(self.expr_or_assign(17)),
                        span: SPAN,
                    }
                }
            })
            .collect()
    }

    fn object(&mut self) -> Expr {
        let fields = self.field_inits();
        mk(ExprKind::ObjectLit(fields))
    }

    fn type_path(&mut self) -> Vec<Ident> {
        let mut path = vec![self.type_name()];
        if self.chance(20) {
            path.push(self.type_name());
        }
        path
    }

    fn new_expr(&mut self) -> Expr {
        let args = if self.chance(30) {
            self.type_args()
        } else {
            Vec::new()
        };
        let ty = mk_ty(TypeExprKind::Named {
            path: self.type_path(),
            args,
        });
        let init = if self.chance(50) {
            NewInit::Args(self.args())
        } else {
            NewInit::Fields(self.field_inits())
        };
        mk(ExprKind::New { ty, init })
    }

    fn case_lit(&mut self) -> Expr {
        let mut path = vec![self.type_name()];
        for _ in 0..self.upto(2) {
            path.push(self.type_name());
        }
        let args = if self.chance(20) {
            self.type_args()
        } else {
            Vec::new()
        };
        let fields = self.field_inits();
        mk(ExprKind::CaseLit { path, args, fields })
    }

    fn type_member(&mut self) -> Expr {
        let path = self.type_path();
        let ty = if self.chance(50) {
            // `a<>.b`: an empty list still makes a `TypeMember`.
            let args = if self.chance(10) {
                Vec::new()
            } else {
                self.type_args()
            };
            mk_ty(TypeExprKind::Named { path, args })
        } else {
            let args = if self.chance(30) {
                self.type_args()
            } else {
                Vec::new()
            };
            mk_ty(TypeExprKind::Array(Box::new(mk_ty(TypeExprKind::Named {
                path,
                args,
            }))))
        };
        mk(ExprKind::TypeMember {
            ty,
            name: self.member_name(),
        })
    }

    /// `super`, the size forms and `asm`.
    fn special(&mut self) -> Expr {
        match self.draw(6) {
            0 => {
                let args = self.args();
                mk(ExprKind::Call {
                    callee: Box::new(mk(ExprKind::Super)),
                    type_args: Vec::new(),
                    args,
                })
            }
            1 => mk(ExprKind::Member {
                base: Box::new(mk(ExprKind::Super)),
                name: self.member_name(),
                optional: false,
            }),
            2 => mk(ExprKind::SizeForm(SizeForm::SizeOf(self.ty()))),
            3 => mk(ExprKind::SizeForm(SizeForm::AlignOf(self.ty()))),
            4 => {
                let ty = self.ty();
                mk(ExprKind::SizeForm(SizeForm::OffsetOf(ty, self.str_lit())))
            }
            _ => self.asm(),
        }
    }

    fn asm(&mut self) -> Expr {
        let template = if self.chance(50) {
            self.string()
        } else {
            self.template()
        };
        let options = if self.chance(60) {
            let mut keys = vec![0, 1, 2];
            let mut options = Vec::new();
            for _ in 0..self.upto(3) {
                let key = keys.remove(self.draw(keys.len()));
                let kind = match key {
                    0 | 1 => {
                        let len = self.upto(2);
                        let regs = (0..len)
                            .map(|_| RegBinding {
                                reg: self.word(REGISTERS),
                                value: if self.chance(70) {
                                    Some(self.expr(17))
                                } else {
                                    None
                                },
                            })
                            .collect();
                        if key == 0 {
                            AsmOptionKind::In(regs)
                        } else {
                            AsmOptionKind::Out(regs)
                        }
                    }
                    _ => {
                        let len = self.upto(2);
                        AsmOptionKind::Clobbers((0..len).map(|_| self.str_lit()).collect())
                    }
                };
                options.push(AsmOption { kind, span: SPAN });
            }
            Some(options)
        } else {
            None
        };
        mk(ExprKind::Asm(AsmExpr {
            template: Box::new(template),
            options,
        }))
    }

    fn match_expr(&mut self) -> Expr {
        let subject = self.expr(17);
        let len = self.len(4);
        let arms = (0..len).map(|_| self.arm()).collect();
        mk(ExprKind::Match {
            subject: Box::new(subject),
            arms,
        })
    }

    fn arm(&mut self) -> MatchArm {
        let values = if self.chance(20) {
            Vec::new()
        } else {
            let len = 1 + self.upto(2);
            (0..len).map(|_| self.arm_value()).collect()
        };
        let guard = if self.chance(20) {
            Some(self.expr(COALESCE_PRECEDENCE))
        } else {
            None
        };
        let body = match self.draw(8) {
            0 | 1 => ArmBody::Block(self.block()),
            2 => ArmBody::Return(if self.chance(50) {
                Some(self.expr_or_assign(17))
            } else {
                None
            }),
            3 if !self.loops.is_empty() => ArmBody::Break(self.jump_label()),
            4 if !self.loops.is_empty() => ArmBody::Continue(self.jump_label()),
            _ => ArmBody::Expr(at_start(self.expr_or_assign(17), false)),
        };
        MatchArm {
            values,
            guard,
            body,
            span: SPAN,
        }
    }

    /// An arm value (SPEC 3.4 `ArmValue`): a value is never a path, `null`, `Ok` or
    /// `Err`, which read as their own kinds, and binds at `??` or tighter.
    fn arm_value(&mut self) -> ArmValue {
        match self.draw(9) {
            0 => ArmValue::Null(SPAN),
            1 => ArmValue::Ok(SPAN),
            2 => ArmValue::Err(SPAN),
            3 | 4 => {
                let mut path = vec![self.type_name()];
                if self.chance(60) {
                    path.push(self.type_name());
                }
                ArmValue::Case(path)
            }
            5 => {
                let lo = self.bound();
                let hi = self.bound();
                ArmValue::Range(lo, hi)
            }
            6 => ArmValue::Value(mk(ExprKind::Unary(UnOp::Neg, Box::new(self.int())))),
            7 => {
                let left = mk(ExprKind::Ident(self.value_name().name));
                let right = self.int();
                ArmValue::Value(mk(ExprKind::Binary(
                    BinOp::Gt,
                    Box::new(left),
                    Box::new(right),
                )))
            }
            _ => ArmValue::Value(match self.draw(4) {
                0 => self.int(),
                1 => self.string(),
                2 => self.float(),
                _ => mk(ExprKind::Bool(true)),
            }),
        }
    }

    /// A bound of a range: a value with no ternary, assignment or arrow at its top.
    fn bound(&mut self) -> Expr {
        match self.draw(4) {
            0 => self.int(),
            1 => mk(ExprKind::Unary(UnOp::Neg, Box::new(self.int()))),
            2 => mk(ExprKind::Ident(self.value_name().name)),
            _ => self.expr(COALESCE_PRECEDENCE),
        }
    }

    // -----------------------------------------------------------------------------
    // Types.

    /// A type of any form that a full `Type` position takes.
    fn ty(&mut self) -> TypeExpr {
        if self.low() {
            return self.named_leaf();
        }
        self.nest(|g| match g.draw(20) {
            0..=5 => g.named_type(),
            6 => mk_ty(TypeExprKind::Ref(Box::new(fit_ty(g.ty(), 1)))),
            7 => mk_ty(TypeExprKind::Raw(Box::new(fit_ty(g.ty(), 1)))),
            8 => mk_ty(TypeExprKind::Array(Box::new(fit_ty(g.ty(), 0)))),
            9 => {
                let elem = fit_ty(g.ty(), 0);
                let len = g.bound_len();
                mk_ty(TypeExprKind::Fixed(Box::new(elem), Box::new(len)))
            }
            10 => g.nullable(),
            11 => g.union(),
            12 => {
                let len = g.upto(3);
                mk_ty(TypeExprKind::Tuple((0..len).map(|_| g.ty()).collect()))
            }
            13 => g.object_type(),
            14 => g.closure_type(),
            15 => g.fn_ptr_type(),
            16 => mk_ty(TypeExprKind::Paren(Box::new(g.ty()))),
            17 => mk_ty(TypeExprKind::Void),
            18 => mk_ty(TypeExprKind::Never),
            _ => mk_ty(TypeExprKind::NullLit),
        })
    }

    fn named_leaf(&mut self) -> TypeExpr {
        mk_ty(TypeExprKind::Named {
            path: vec![self.type_name()],
            args: Vec::new(),
        })
    }

    fn named_type(&mut self) -> TypeExpr {
        let path = self.type_path();
        let args = if self.chance(30) {
            self.type_args()
        } else {
            Vec::new()
        };
        mk_ty(TypeExprKind::Named { path, args })
    }

    fn bound_len(&mut self) -> Expr {
        match self.draw(3) {
            0 => self.int(),
            1 => mk(ExprKind::Ident(self.value_name().name)),
            _ => mk(ExprKind::Binary(
                BinOp::Add,
                Box::new(self.int()),
                Box::new(mk(ExprKind::Ident(self.value_name().name))),
            )),
        }
    }

    /// An operand of `|`: a prefix type, never `null` or an object type, so that
    /// the union stays one (a last `null` makes it nullable, all objects EN0215).
    fn union_operand(&mut self) -> TypeExpr {
        loop {
            let ty = fit_ty(self.ty(), 1);
            if !matches!(ty.kind, TypeExprKind::NullLit | TypeExprKind::Object(_)) {
                return ty;
            }
        }
    }

    fn nullable(&mut self) -> TypeExpr {
        let inner = if self.chance(15) {
            self.union()
        } else {
            self.union_operand()
        };
        mk_ty(TypeExprKind::Nullable(Box::new(inner)))
    }

    fn union(&mut self) -> TypeExpr {
        let len = 2 + self.upto(1);
        mk_ty(TypeExprKind::Union(
            (0..len).map(|_| self.union_operand()).collect(),
        ))
    }

    fn object_type(&mut self) -> TypeExpr {
        let len = self.upto(3);
        mk_ty(TypeExprKind::Object(
            (0..len)
                .map(|_| (self.member_name(), self.chance(30), self.ty()))
                .collect(),
        ))
    }

    fn typed_params(&mut self) -> Vec<TypedParam> {
        let len = self.upto(2);
        (0..len)
            .map(|_| TypedParam {
                is_let: self.chance(20),
                name: self.value_name(),
                ty: self.ty(),
            })
            .collect()
    }

    fn closure_type(&mut self) -> TypeExpr {
        let params = self.typed_params();
        let ret = self.ty();
        mk_ty(TypeExprKind::Closure(ClosureType {
            params,
            ret: Box::new(ret),
        }))
    }

    fn fn_ptr_type(&mut self) -> TypeExpr {
        let decorators = if self.chance(20) {
            vec![self.decorator()]
        } else {
            Vec::new()
        };
        let is_unsafe = self.chance(30);
        let params = self.typed_params();
        let ret = self.ret_type();
        mk_ty(TypeExprKind::FnPtr(FnPtrType {
            decorators,
            is_unsafe,
            params,
            ret: Box::new(ret),
        }))
    }

    fn ret_type(&mut self) -> RetType {
        let ty = self.ty();
        let readonly = takes_readonly(&ty) && self.chance(20);
        RetType { readonly, ty }
    }

    /// A field's type (SPEC 3.1 `FieldType`): `readonly &T`, optionally `| null`, at
    /// the top or as a part of a tuple, or any type.
    fn field_type(&mut self) -> TypeExpr {
        match self.draw(8) {
            0 => {
                let referent = fit_ty(self.ty(), 1);
                let readonly = mk_ty(TypeExprKind::ReadonlyRef(Box::new(referent)));
                if self.chance(40) {
                    mk_ty(TypeExprKind::Nullable(Box::new(readonly)))
                } else {
                    readonly
                }
            }
            1 if !self.low() => {
                let len = self.upto(3);
                let elems = (0..len).map(|_| self.nest(|g| g.field_type())).collect();
                let tuple = mk_ty(TypeExprKind::Tuple(elems));
                if self.chance(30) {
                    mk_ty(TypeExprKind::Nullable(Box::new(tuple)))
                } else {
                    tuple
                }
            }
            _ => self.ty(),
        }
    }

    // -----------------------------------------------------------------------------
    // Statements.

    /// Leaves the loops of the enclosing body behind, as a function or arrow body
    /// does (EN0111), and returns them for `restore`.
    fn barrier(&mut self) -> Vec<Option<Symbol>> {
        std::mem::take(&mut self.loops)
    }

    fn restore(&mut self, loops: Vec<Option<Symbol>>) {
        self.loops = loops;
    }

    /// A function's, method's or arrow's body: no loop outside it is reachable.
    fn body_block(&mut self) -> Block {
        let saved = self.barrier();
        let block = self.block();
        self.restore(saved);
        block
    }

    fn block(&mut self) -> Block {
        let len = self.len(4);
        let stmts = (0..len).map(|_| self.stmt()).collect();
        Block { stmts, span: SPAN }
    }

    /// A label for `break` or `continue`: one of an enclosing loop's, or none.
    fn jump_label(&mut self) -> Option<Ident> {
        let labels: Vec<Symbol> = self.loops.iter().flatten().copied().collect();
        if labels.is_empty() || self.chance(50) {
            return None;
        }
        let at = self.draw(labels.len());
        Some(Ident {
            name: labels[at],
            span: SPAN,
        })
    }

    /// A loop's body, inside a loop with `label`.
    fn loop_body(&mut self, label: Option<Symbol>) -> Block {
        self.loops.push(label);
        let block = self.block();
        self.loops.pop();
        block
    }

    fn stmt(&mut self) -> Stmt {
        if self.low() {
            return match self.draw(3) {
                0 => mk_stmt(StmtKind::Expr(at_start(self.expr_or_assign(17), true))),
                1 => mk_stmt(StmtKind::VarDecl(self.var_decl())),
                _ => mk_stmt(StmtKind::Return(None)),
            };
        }
        self.nest(|g| g.stmt_kind(None))
    }

    /// A statement; a loop gets `label`.
    fn stmt_kind(&mut self, label: Option<Symbol>) -> Stmt {
        let kind = match self.draw(22) {
            0..=3 => StmtKind::Expr(at_start(self.expr_or_assign(17), true)),
            4..=6 => StmtKind::VarDecl(self.var_decl()),
            7 | 8 => StmtKind::If(self.if_stmt()),
            9..=12 => self.loop_stmt(label),
            13 => StmtKind::Return(if self.chance(70) {
                Some(self.expr_or_assign(17))
            } else {
                None
            }),
            14 if !self.loops.is_empty() => StmtKind::Break(self.jump_label()),
            15 if !self.loops.is_empty() => StmtKind::Continue(self.jump_label()),
            16 => StmtKind::Block(self.block()),
            17 => StmtKind::Unsafe(self.block()),
            18 => {
                let free: Vec<&str> = LABELS
                    .iter()
                    .copied()
                    .filter(|label| !self.labels.contains(&intern(label)))
                    .collect();
                if free.is_empty() {
                    StmtKind::Block(self.block())
                } else {
                    let name = intern(free[self.draw(free.len())]);
                    self.labels.push(name);
                    let looped = mk_stmt(self.loop_stmt(Some(name)));
                    self.labels.pop();
                    StmtKind::Labeled(Ident { name, span: SPAN }, Box::new(looped))
                }
            }
            19 => StmtKind::Expect(self.expect_stmt()),
            20 => StmtKind::Expr(self.match_expr()),
            _ => StmtKind::Expr(at_start(self.expr_or_assign(17), true)),
        };
        mk_stmt(kind)
    }

    /// A loop (SPEC 3.3 `LabeledStmt` takes these four), with `label`.
    fn loop_stmt(&mut self, label: Option<Symbol>) -> StmtKind {
        match self.draw(4) {
            0 => StmtKind::While(WhileStmt {
                cond: self.expr(17),
                body: self.loop_body(label),
                span: SPAN,
            }),
            1 => StmtKind::DoWhile(WhileStmt {
                body: self.loop_body(label),
                cond: self.expr(17),
                span: SPAN,
            }),
            2 => StmtKind::For(self.for_stmt(label)),
            _ => StmtKind::ForOf(self.for_of(label)),
        }
    }

    fn binding(&mut self) -> Binding {
        if self.low() || self.chance(70) {
            return Binding::Name(self.value_name());
        }
        self.nest(|g| {
            let len = g.upto(3);
            if g.chance(50) {
                let fields = (0..len)
                    .map(|_| {
                        if g.chance(50) {
                            (g.value_name(), None)
                        } else {
                            (g.member_name(), Some(g.binding()))
                        }
                    })
                    .collect();
                Binding::Object { fields, span: SPAN }
            } else {
                let elems = (0..len).map(|_| g.binding()).collect();
                Binding::Tuple { elems, span: SPAN }
            }
        })
    }

    fn var_decl(&mut self) -> VarDecl {
        let mutable = self.chance(50);
        let binding = self.binding();
        let ty = if self.chance(30) {
            Some(self.ty())
        } else {
            None
        };
        // A `const` always has a value (EN0116), and so does a destructuring.
        let needs = !mutable || !matches!(binding, Binding::Name(_));
        let init = if needs || self.chance(70) {
            Some(self.expr_or_assign(17))
        } else {
            None
        };
        VarDecl {
            mutable,
            binding,
            ty,
            init,
            span: SPAN,
        }
    }

    fn if_stmt(&mut self) -> IfStmt {
        let cond = self.expr(17);
        let then_block = self.block();
        let else_branch = match self.draw(4) {
            0 | 1 => None,
            2 => Some(ElseBranch::Block(self.block())),
            _ => Some(ElseBranch::If(Box::new(self.nest(|g| g.if_stmt())))),
        };
        IfStmt {
            cond,
            then_block,
            else_branch,
            span: SPAN,
        }
    }

    fn for_stmt(&mut self, label: Option<Symbol>) -> ForStmt {
        let init = match self.draw(3) {
            0 => None,
            1 => Some(ForInit::VarDecl(self.var_decl())),
            _ => Some(ForInit::Expr(at_start(self.expr_or_assign(17), true))),
        };
        let cond = if self.chance(70) {
            Some(self.expr(17))
        } else {
            None
        };
        let step = if self.chance(70) {
            Some(self.expr_or_assign(17))
        } else {
            None
        };
        ForStmt {
            init,
            cond,
            step,
            body: self.loop_body(label),
            span: SPAN,
        }
    }

    fn for_of(&mut self, label: Option<Symbol>) -> ForOfStmt {
        let source = if self.chance(40) {
            ForOfSource::Range(self.bound(), self.bound())
        } else {
            ForOfSource::Expr(self.expr(TERNARY_PRECEDENCE))
        };
        ForOfStmt {
            mutable: self.chance(30),
            binding: self.binding(),
            in_keyword: None,
            source,
            body: self.loop_body(label),
            span: SPAN,
        }
    }

    fn expect_stmt(&mut self) -> ExpectStmt {
        let actual = self.expr(17);
        let matcher = self.word(MATCHERS);
        let len = self.upto(2);
        let args = (0..len)
            .map(|_| {
                if matcher.name.as_str() == "toMatchPattern" {
                    MatcherArg::Arm(self.arm_value())
                } else {
                    MatcherArg::Expr(self.expr(17))
                }
            })
            .collect();
        ExpectStmt {
            actual,
            negated: self.chance(30),
            matcher,
            args,
            span: SPAN,
        }
    }

    // -----------------------------------------------------------------------------
    // Items.

    fn decorator(&mut self) -> Decorator {
        let args = if self.chance(50) {
            let len = self.upto(2);
            Some((0..len).map(|_| self.decorator_arg()).collect())
        } else {
            None
        };
        Decorator {
            name: self.word(DECORATORS),
            args,
            span: SPAN,
        }
    }

    fn literal(&mut self) -> Expr {
        match self.draw(5) {
            0 => self.int(),
            1 => mk(ExprKind::Unary(UnOp::Neg, Box::new(self.int()))),
            2 => self.string(),
            3 => mk(ExprKind::Bool(self.chance(50))),
            _ => self.float(),
        }
    }

    /// `DecoratorArg = Literal | ObjectLit | Ident`: an object literal of literals
    /// and arrays of literals.
    fn decorator_arg(&mut self) -> Expr {
        match self.draw(4) {
            0 | 1 => self.literal(),
            2 => mk(ExprKind::Ident(self.value_name().name)),
            _ => {
                let len = self.upto(2);
                let fields = (0..len)
                    .map(|_| {
                        let value = if self.chance(30) {
                            let len = self.upto(2);
                            mk(ExprKind::Array(
                                (0..len).map(|_| ArrayElem::Item(self.literal())).collect(),
                            ))
                        } else {
                            self.literal()
                        };
                        FieldInit {
                            name: self.member_name(),
                            value: Some(value),
                            span: SPAN,
                        }
                    })
                    .collect();
                mk(ExprKind::ObjectLit(fields))
            }
        }
    }

    fn decorators(&mut self) -> Vec<Decorator> {
        if self.chance(20) {
            let len = 1 + self.upto(1);
            (0..len).map(|_| self.decorator()).collect()
        } else {
            Vec::new()
        }
    }

    fn type_params(&mut self) -> Vec<TypeParam> {
        if !self.chance(30) {
            return Vec::new();
        }
        let len = 1 + self.upto(1);
        (0..len)
            .map(|_| TypeParam {
                name: self.type_name(),
                bounds: (0..self.upto(2)).map(|_| self.named_type()).collect(),
            })
            .collect()
    }

    /// Parameters; once one has `?` or a default, every later one has one of the
    /// two, and none has both (EN0227, EN0229).
    fn params(&mut self) -> Vec<Param> {
        let len = self.len(3);
        let mut defaulted = false;
        (0..len)
            .map(|_| {
                let mark = [ParamMark::Plain, ParamMark::Let, ParamMark::Const][self.draw(3)];
                let binding = self.binding();
                let simple = matches!(binding, Binding::Name(_));
                let (optional, default) = match self.draw(4) {
                    0 if simple => (true, None),
                    1 => (false, Some(self.expr(17))),
                    _ if defaulted => (false, Some(self.expr(17))),
                    _ => (false, None),
                };
                defaulted |= optional || default.is_some();
                let ty = if self.chance(15) {
                    let closure = mk_ty(TypeExprKind::Paren(Box::new(self.closure_type())));
                    mk_ty(TypeExprKind::Nullable(Box::new(closure)))
                } else {
                    self.ty()
                };
                Param {
                    mark,
                    binding,
                    optional,
                    ty,
                    default,
                    span: SPAN,
                }
            })
            .collect()
    }

    fn ctor_params(&mut self) -> Vec<CtorParam> {
        let len = self.len(3);
        let mut defaulted = false;
        (0..len)
            .map(|_| {
                let property = match self.draw(4) {
                    0 => Some(Visibility::Public),
                    1 => Some(Visibility::Private),
                    2 => Some(Visibility::Protected),
                    _ => None,
                };
                let (optional, default) = match self.draw(4) {
                    0 => (true, None),
                    1 => (false, Some(self.expr(17))),
                    _ if defaulted => (false, Some(self.expr(17))),
                    _ => (false, None),
                };
                defaulted |= optional || default.is_some();
                // Only a parameter that is a field takes `readonly` (SPEC 3.1).
                let ty = if property.is_some() {
                    self.field_type()
                } else {
                    self.ty()
                };
                CtorParam {
                    property,
                    is_readonly: property.is_some() && self.chance(30),
                    mark: [ParamMark::Plain, ParamMark::Let, ParamMark::Const][self.draw(3)],
                    name: self.value_name(),
                    optional,
                    ty,
                    default,
                    span: SPAN,
                }
            })
            .collect()
    }

    fn visibility(&mut self, protected: bool) -> Visibility {
        match self.draw(if protected { 3 } else { 2 }) {
            0 => Visibility::Public,
            1 => Visibility::Private,
            _ => Visibility::Protected,
        }
    }

    fn function_decl(&mut self) -> FunctionDecl {
        FunctionDecl {
            is_unsafe: self.chance(15),
            name: self.value_name(),
            type_params: self.type_params(),
            params: self.params(),
            ret: if self.chance(70) {
                Some(self.ret_type())
            } else {
                None
            },
            body: self.body_block(),
            span: SPAN,
        }
    }

    /// A method of a class, an enum or an `extend`, or of an interface with
    /// `interface` set: no visibility, no body, no `const` receiver (SPEC 3.1).
    fn method(&mut self, interface: bool) -> MethodDecl {
        let receivers: &[Receiver] = if interface {
            &[
                Receiver::Plain,
                Receiver::Let,
                Receiver::Move,
                Receiver::Static,
            ]
        } else {
            &[
                Receiver::Plain,
                Receiver::Let,
                Receiver::Const,
                Receiver::Move,
                Receiver::Static,
            ]
        };
        let receiver = receivers[self.draw(receivers.len())];
        let is_abstract = !interface && receiver != Receiver::Static && self.chance(15);
        let where_clause = if self.chance(15) {
            (0..1 + self.upto(1))
                .map(|_| WherePred {
                    param: self.type_name(),
                    bounds: (0..1 + self.upto(1)).map(|_| self.named_type()).collect(),
                })
                .collect()
        } else {
            Vec::new()
        };
        MethodDecl {
            visibility: if interface {
                None
            } else {
                Some(self.visibility(true))
            },
            is_abstract,
            is_override: !interface && self.chance(15),
            receiver,
            is_unsafe: self.chance(10),
            name: self.member_name(),
            type_params: self.type_params(),
            params: self.params(),
            ret: if self.chance(60) {
                Some(self.ret_type())
            } else {
                None
            },
            where_clause,
            body: if interface || self.chance(15) {
                None
            } else {
                Some(self.body_block())
            },
            span: SPAN,
        }
    }

    fn class_member(&mut self) -> ClassMember {
        let kind = match self.draw(8) {
            0..=2 => {
                let optional = self.chance(20);
                ClassMemberKind::Field(FieldDecl {
                    visibility: Some(self.visibility(true)),
                    is_override: self.chance(10),
                    is_readonly: self.chance(20),
                    name: self.member_name(),
                    optional,
                    ty: self.field_type(),
                    default: if !optional && self.chance(30) {
                        Some(self.expr(17))
                    } else {
                        None
                    },
                })
            }
            3 => ClassMemberKind::Constructor(Constructor {
                visibility: Some(self.visibility(true)),
                params: self.ctor_params(),
                body: self.body_block(),
            }),
            4 => ClassMemberKind::Destructor(Destructor {
                visibility: Some(Visibility::Public),
                body: self.body_block(),
            }),
            _ => ClassMemberKind::Method(self.method(false)),
        };
        ClassMember {
            decorators: self.decorators(),
            kind,
            span: SPAN,
        }
    }

    fn variant(&mut self) -> Variant {
        let payload = match self.draw(4) {
            0 | 1 => VariantPayload::Unit,
            2 => {
                let len = self.upto(2);
                VariantPayload::Fields(
                    (0..len)
                        .map(|_| EnumField {
                            name: self.member_name(),
                            ty: self.ty(),
                        })
                        .collect(),
                )
            }
            _ => VariantPayload::Value(match self.draw(4) {
                0 => self.int(),
                1 => mk(ExprKind::Unary(UnOp::Neg, Box::new(self.int()))),
                2 => self.string(),
                _ => mk(ExprKind::Binary(
                    BinOp::Shl,
                    Box::new(self.int()),
                    Box::new(self.int()),
                )),
            }),
        };
        Variant {
            decorators: self.decorators(),
            name: self.type_name(),
            payload,
            span: SPAN,
        }
    }

    fn iface_member(&mut self) -> IfaceMember {
        if self.chance(40) {
            IfaceMember::Field(IfaceField {
                name: self.member_name(),
                optional: self.chance(30),
                ty: self.ty(),
                span: SPAN,
            })
        } else {
            IfaceMember::Method(self.method(true))
        }
    }

    /// The type an `extend` block extends.
    fn extend_type(&mut self) -> TypeExpr {
        let named = self.named_type();
        match self.draw(4) {
            0 => mk_ty(TypeExprKind::Array(Box::new(named))),
            1 => mk_ty(TypeExprKind::Nullable(Box::new(named))),
            2 => mk_ty(TypeExprKind::Raw(Box::new(named))),
            _ => named,
        }
    }

    /// A declaration with its visibility, or another item a file with no
    /// statements may hold.
    fn item(&mut self) -> Item {
        self.nest(|g| {
            let decorators = g.decorators();
            let pick = if g.test_file { g.draw(14) } else { g.draw(11) };
            let (visibility, kind, decorators) = match pick {
                0 | 1 => (Some(()), ItemKind::Function(g.function_decl()), decorators),
                2 => (
                    Some(()),
                    ItemKind::Class(ClassDecl {
                        modifier: [
                            ClassModifier::Plain,
                            ClassModifier::Abstract,
                            ClassModifier::Final,
                        ][g.draw(3)],
                        name: g.type_name(),
                        type_params: g.type_params(),
                        extends: if g.chance(30) {
                            Some(g.named_type())
                        } else {
                            None
                        },
                        implements: (0..g.upto(2)).map(|_| g.named_type()).collect(),
                        members: (0..g.len(4)).map(|_| g.class_member()).collect(),
                        span: SPAN,
                    }),
                    decorators,
                ),
                3 => {
                    let variants = (0..g.len(4)).map(|_| g.variant()).collect();
                    let methods = if g.chance(30) {
                        (0..1 + g.upto(1)).map(|_| g.method(false)).collect()
                    } else {
                        Vec::new()
                    };
                    (
                        Some(()),
                        ItemKind::Enum(EnumDecl {
                            name: g.type_name(),
                            type_params: g.type_params(),
                            variants,
                            methods,
                            span: SPAN,
                        }),
                        decorators,
                    )
                }
                4 => (
                    Some(()),
                    ItemKind::Interface(InterfaceDecl {
                        name: g.type_name(),
                        type_params: g.type_params(),
                        members: (0..g.len(3)).map(|_| g.iface_member()).collect(),
                        span: SPAN,
                    }),
                    decorators,
                ),
                5 => {
                    let ty = if g.chance(25) {
                        let len = 1 + g.upto(2);
                        mk_ty(TypeExprKind::StrUnion(
                            (0..len).map(|_| g.str_lit()).collect(),
                        ))
                    } else {
                        g.ty()
                    };
                    (
                        Some(()),
                        ItemKind::TypeAlias(TypeAlias {
                            name: g.type_name(),
                            type_params: g.type_params(),
                            ty,
                        }),
                        decorators,
                    )
                }
                6 => (
                    Some(()),
                    ItemKind::TopConst(TopConst {
                        name: g.value_name(),
                        ty: if g.chance(50) { Some(g.ty()) } else { None },
                        value: g.expr(17),
                    }),
                    decorators,
                ),
                7 => (
                    Some(()),
                    ItemKind::UnsafeLet(UnsafeLet {
                        name: g.value_name(),
                        ty: g.ty(),
                        value: if g.chance(50) { Some(g.expr(17)) } else { None },
                    }),
                    decorators,
                ),
                8 => (
                    Some(()),
                    ItemKind::DeclareFn(DeclareFn {
                        name: g.value_name(),
                        type_params: g.type_params(),
                        params: g.params(),
                        ret: if g.chance(60) { Some(g.ty()) } else { None },
                        span: SPAN,
                    }),
                    decorators,
                ),
                9 => (
                    None,
                    ItemKind::Extend(ExtendDecl {
                        type_params: g.type_params(),
                        ty: g.extend_type(),
                        members: (0..g.len(3))
                            .map(|_| ExtendMember {
                                decorators: g.decorators(),
                                method: g.method(false),
                                span: SPAN,
                            })
                            .collect(),
                    }),
                    decorators,
                ),
                10 => (
                    None,
                    ItemKind::StaticAssert {
                        cond: g.expr(17),
                        message: if g.chance(50) {
                            Some(g.str_lit())
                        } else {
                            None
                        },
                    },
                    Vec::new(),
                ),
                _ => (None, g.test_item(), Vec::new()),
            };
            let visibility = visibility.map(|()| g.visibility(false));
            Item {
                id: ID,
                decorators,
                visibility,
                kind,
                span: SPAN,
            }
        })
    }

    /// A test item of SPEC 3.6, in a `.test.en` file.
    fn test_item(&mut self) -> ItemKind {
        match self.draw(5) {
            0 if !self.low() => ItemKind::Describe(DescribeItem {
                name: self.str_lit(),
                items: (0..self.len(3))
                    .map(|_| {
                        let kind = self.nest(|g| g.test_item());
                        Item {
                            id: ID,
                            decorators: Vec::new(),
                            visibility: None,
                            kind,
                            span: SPAN,
                        }
                    })
                    .collect(),
            }),
            1 => ItemKind::CompileCase(CompileCase {
                kind: if self.chance(50) {
                    CompileKind::Ok
                } else {
                    CompileKind::Fails
                },
                name: self.str_lit(),
                source: {
                    let text = self.text(true);
                    StrLit {
                        value: intern(&text),
                        span: SPAN,
                    }
                },
                options: if self.chance(40) {
                    Some(self.object())
                } else {
                    None
                },
            }),
            _ => {
                let mode = [
                    None,
                    Some(TestMode::Only),
                    Some(TestMode::Skip),
                    Some(TestMode::Todo),
                    Some(TestMode::Panics),
                    Some(TestMode::Each),
                ][self.draw(6)];
                let extra = match mode {
                    Some(TestMode::Panics) if self.chance(70) => {
                        Some(TestExtra::Message(self.str_lit()))
                    }
                    Some(TestMode::Each) => {
                        let body = at_start(self.expr(17), false);
                        Some(TestExtra::Cases(ArrowFn {
                            params: Vec::new(),
                            ret: None,
                            body: ArrowBody::Expr(Box::new(body)),
                            span: SPAN,
                        }))
                    }
                    _ => None,
                };
                let body = if mode == Some(TestMode::Todo) && self.chance(50) {
                    None
                } else {
                    let params = if self.chance(30) {
                        vec![ArrowParam {
                            is_let: false,
                            name: self.value_name(),
                            ty: if self.chance(50) {
                                Some(self.ty())
                            } else {
                                None
                            },
                        }]
                    } else {
                        Vec::new()
                    };
                    let ret = if self.chance(20) {
                        Some(RetType {
                            readonly: false,
                            ty: self.ty(),
                        })
                    } else {
                        None
                    };
                    Some(ArrowFn {
                        params,
                        ret,
                        body: ArrowBody::Block(self.body_block()),
                        span: SPAN,
                    })
                };
                ItemKind::Test(TestDecl {
                    mode,
                    name: self.str_lit(),
                    extra,
                    body,
                    options: if self.chance(20) {
                        Some(self.object())
                    } else {
                        None
                    },
                })
            }
        }
    }

    fn import(&mut self) -> Import {
        let kind = if self.chance(25) {
            ImportKind::Namespace(self.value_name())
        } else {
            let len = self.upto(3);
            ImportKind::Named(
                (0..len)
                    .map(|_| ImportName {
                        name: if self.chance(50) {
                            self.type_name()
                        } else {
                            self.value_name()
                        },
                        alias: if self.chance(25) {
                            Some(self.value_name())
                        } else {
                            None
                        },
                    })
                    .collect(),
            )
        };
        let path = [
            "./z",
            "core",
            "os/vga",
            "../lib/util",
            "alloc",
            "./Shapes",
            "a\"b",
        ][self.draw(7)];
        Import {
            public: self.chance(20),
            kind,
            path: StrLit {
                value: intern(path),
                span: SPAN,
            },
            span: SPAN,
        }
    }

    /// A top-level statement of a program: a statement, a local function or an
    /// `assert`.
    fn top_stmt(&mut self) -> Stmt {
        match self.draw(8) {
            0 => mk_stmt(StmtKind::LocalFn {
                decorators: self.decorators(),
                decl: self.function_decl(),
            }),
            1 => mk_stmt(StmtKind::Assert {
                cond: self.expr(17),
                message: if self.chance(50) {
                    Some(self.str_lit())
                } else {
                    None
                },
            }),
            _ => self.stmt(),
        }
    }

    /// A whole file. A program's statements hold one that is neither a local
    /// function nor an `assert` (SPEC 3.1: else it is no program), and its items
    /// state their visibility, as a file with no statements does.
    fn file(&mut self) -> File {
        self.test_file = self.chance(30);
        let imports = (0..self.upto(3)).map(|_| self.import()).collect();
        let mut stmts: Vec<Stmt> = Vec::new();
        if self.chance(50) {
            for _ in 0..self.upto(4) {
                stmts.push(self.top_stmt());
            }
            let program = stmts.iter().any(|stmt| {
                !matches!(
                    stmt.kind,
                    StmtKind::LocalFn { .. } | StmtKind::Assert { .. }
                )
            });
            if !program {
                stmts.push(self.stmt());
            }
        }
        let mut items: Vec<Item> = (0..self.upto(5)).map(|_| self.item()).collect();
        // In a program, an `assert` before the first declaration is a statement
        // (SPEC 3.1 `TopStmt`); only one after it is an item.
        while !stmts.is_empty()
            && let Some(Item {
                kind: ItemKind::StaticAssert { .. },
                ..
            }) = items.first()
        {
            if let ItemKind::StaticAssert { cond, message } = items.remove(0).kind {
                stmts.push(mk_stmt(StmtKind::Assert { cond, message }));
            }
        }
        File {
            imports,
            stmts,
            items,
            span: SPAN,
        }
    }
}

// ---------------------------------------------------------------------------------
// The round trip.

/// A generated program: its file name and tree.
fn generate(tape: Tape) -> (&'static str, File) {
    let mut generator = Gen::new(tape);
    let file = generator.file();
    let name = if generator.test_file {
        "gen.test.en"
    } else {
        "gen.en"
    };
    (name, file)
}

/// `file` with its imports as one group sorted by SPEC 12.5's Imports rule: a tree
/// with no source has no blank lines and no comments.
fn imports_sorted(file: &File) -> File {
    let mut file = file.clone();
    file.imports
        .sort_by(|a, b| a.path.value.as_str().cmp(b.path.value.as_str()));
    for import in &mut file.imports {
        if let ImportKind::Named(names) = &mut import.kind {
            names.sort_by(|a, b| a.name.name.as_str().cmp(b.name.name.as_str()));
        }
    }
    file
}

/// Print `tree`, parse it back, compare, print again. The error names the step.
fn round_trip(name: &str, tree: &File) -> Result<String, String> {
    let blank = source(name, "");
    let text = match catch_panic(|| print_file(&blank, tree)) {
        None => print_file(&blank, tree),
        Some(panic) => return Err(format!("the printer panicked: {panic}")),
    };
    let parsed = catch_panic(|| try_parse(name, &text))
        .map_or_else(|| Ok(try_parse(name, &text)), Err)
        .map_err(|panic| format!("the parser panicked: {panic}\n{text}"))?;
    let (file, back) =
        parsed.map_err(|listing| format!("the printed text does not parse:\n{listing}\n{text}"))?;
    let want = imports_sorted(tree);
    let got = erase(&back);
    if want != got {
        return Err(format!(
            "the tree read back differs (- generated, + parsed):\n{}\nprinted:\n{text}",
            line_diff(&format!("{want:#?}"), &format!("{got:#?}"))
        ));
    }
    let again = print_file(&file, &back);
    if again != text {
        return Err(format!(
            "printing the parsed file changes it:\n{}",
            line_diff(&text, &again)
        ));
    }
    Ok(text)
}

/// The round trip of the program a tape makes.
fn check(values: &[u64]) -> Result<String, String> {
    let (name, tree) = generate(Tape {
        values: values.to_vec(),
        at: 0,
        rng: None,
    });
    round_trip(name, &tree)
}

/// The productions of SPEC 3 the generated programs are checked to reach, as the
/// names their `Debug` text shows.
const REACHED: &[&str] = &[
    "Int {",
    "Float(",
    "Str(",
    "Template(",
    "RawTemplate(",
    "Bool(",
    "kind: Null }",
    "Paren(",
    "Ident(",
    "kind: This }",
    "kind: Super }",
    "Array(",
    "Repeat(",
    "TypeMember {",
    "New {",
    "CaseLit {",
    "ObjectLit(",
    "Match {",
    "SizeOf(",
    "AlignOf(",
    "OffsetOf(",
    "Asm(",
    "Unary(",
    "Borrow(",
    "Deref(",
    "VoidOp(",
    "Binary(",
    "Logical(",
    "Coalesce(",
    "Ternary(",
    "Cast(",
    "Assign {",
    "IncDec {",
    "Member {",
    "Index(",
    "Call {",
    "Try(",
    "NonNull(",
    "Arrow(",
    "Spread {",
    "VarDecl(",
    "If(",
    "While(",
    "DoWhile(",
    "For(",
    "ForOf(",
    "Return(",
    "Break(",
    "Continue(",
    "Block(",
    "Unsafe(",
    "Labeled(",
    "Expect(",
    "LocalFn {",
    "Assert {",
    "Function(",
    "Class(",
    "Constructor(",
    "Destructor(",
    "Method(",
    "Field(",
    "Enum(",
    "Interface(",
    "TypeAlias(",
    "StrUnion(",
    "TopConst(",
    "UnsafeLet(",
    "DeclareFn(",
    "Extend(",
    "StaticAssert {",
    "Describe(",
    "Test(",
    "CompileCase(",
    "Namespace(",
    "Named(",
    "Nullable(",
    "Ref(",
    "Raw(",
    "ReadonlyRef(",
    "Fixed(",
    "Tuple(",
    "FnPtr(",
    "Closure(",
    "Object(",
    "Union(",
    "kind: Void }",
    "kind: Never }",
    "kind: NullLit }",
    "Range(",
    "Ok(",
    "Err(",
    "Case(",
    "Value(",
    "Tuple {",
    "Object {",
    "Decorator {",
    "WherePred {",
    "In(",
    "Out(",
    "Clobbers(",
];

/// `GenBytes`'s check of `fmt` (plan d.5): a mutated file never makes the parser or
/// the printer panic, and one that parses with no diagnostic passes the four tests
/// of TESTING 17. Whether it parsed clean.
fn bytes_check(name: &str, text: &str) -> Result<bool, String> {
    let mut parsed = None;
    if let Some(panic) = catch_panic(|| parsed = Some(Parsed::new(name, text))) {
        return Err(format!("the parser panicked: {panic}"));
    }
    let parsed = parsed.expect("set when the parser returns");
    if let Some(panic) = catch_panic(|| print_file(&parsed.file, &parsed.tree)) {
        return Err(format!("the printer panicked: {panic}"));
    }
    if !parsed.diags.is_empty() {
        return Ok(false);
    }
    four_tests_as(name, text, None)?;
    Ok(true)
}

/// Byte sequences a mutation inserts: invalid UTF-8 of each kind (a lone
/// continuation byte, a cut sequence, an overlong form, a surrogate, a byte that never
/// starts one), a byte order mark, and bytes that open or close tokens.
const INSERTS: &[&[u8]] = &[
    b"\x80",
    b"\xC3",
    b"\xE2\x82",
    b"\xC0\xAF",
    b"\xED\xA0\x80",
    b"\xFF\xFE",
    b"\xEF\xBB\xBF",
    b"\"",
    b"`",
    b"${",
    b"/*",
    b"{",
    b"}",
    b"\r\n",
    b"\0",
];

/// `bytes` with one to four byte mutations: a bit flipped, a byte cut, a slice copied
/// or cut, or one of [`INSERTS`] put anywhere, often at the start, where a byte order
/// mark goes.
fn mutate_bytes(rng: &mut Xoshiro256, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    for _ in 0..=rng.below(4) {
        let at = rng.below(out.len() as u64 + 1) as usize;
        match rng.below(5) {
            0 if at < out.len() => out[at] ^= 1 << rng.below(8),
            1 if at < out.len() => {
                out.remove(at);
            }
            2 if at < out.len() => {
                let end = (at + 1 + rng.below(16) as usize).min(out.len());
                let slice = out[at..end].to_vec();
                let to = rng.below(out.len() as u64 + 1) as usize;
                out.splice(to..to, slice);
            }
            3 if at < out.len() => {
                let end = (at + 1 + rng.below(16) as usize).min(out.len());
                out.drain(at..end);
            }
            _ => {
                let insert = INSERTS[rng.below(INSERTS.len() as u64) as usize];
                let to = if rng.below(4) == 0 { 0 } else { at };
                out.splice(to..to, insert.iter().copied());
            }
        }
    }
    out
}

/// `GenBytes`'s check of raw bytes: decoded as the driver decodes a file, with EN0001
/// at each bad sequence, then parsed and printed, and nothing panics.
fn raw_bytes_check(name: &str, bytes: &[u8]) -> Result<(), String> {
    let decoded = decode_source(bytes);
    let file = source(name, &decoded.text);
    let mut dcx = DiagCtx::new();
    if let Some(panic) = catch_panic(|| report_invalid_utf8(&file, &decoded.invalid, &mut dcx)) {
        return Err(format!("EN0001 panicked: {panic}"));
    }
    let mut tree = None;
    let parse = || {
        tree = Some(parse_file(
            &file,
            &mut NodeIdGen::new(),
            ParseMode::Test,
            &mut dcx,
        ));
    };
    if let Some(panic) = catch_panic(parse) {
        return Err(format!("the parser panicked: {panic}"));
    }
    let tree = tree.expect("set when the parser returns");
    if let Some(panic) = catch_panic(|| print_file(&file, &tree)) {
        return Err(format!("the printer panicked: {panic}"));
    }
    Ok(())
}

/// The compile fixtures as `(label, file name, bytes)`, in path order: the firing
/// fixtures hold the broken forms, and EN0001's are not UTF-8.
fn fixture_bytes() -> Vec<(String, String, Vec<u8>)> {
    let root = workspace_root().join("tests/compile");
    let mut found = Vec::new();
    let mut directories: Vec<_> = fs::read_dir(&root)
        .expect("tests/compile")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    directories.sort();
    for directory in directories {
        let mut files: Vec<_> = fs::read_dir(&directory)
            .expect("a fixture directory")
            .map(|entry| entry.expect("an entry").path())
            .collect();
        files.sort();
        for path in files {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .expect("a UTF-8 file name")
                .to_owned();
            let label = path
                .strip_prefix(workspace_root())
                .expect("under the workspace")
                .display()
                .to_string();
            found.push((label, name, fs::read(&path).expect("a fixture")));
        }
    }
    found
}

/// The shrunk failures of earlier runs, each a permanent test (TESTING 14), as
/// `(file name, text)` in name order: `corpus/regress/syntax/*.en`, each already in
/// the canonical style.
fn regressions() -> Vec<(String, String)> {
    let dir = workspace_root().join("corpus/regress/syntax");
    let entries =
        fs::read_dir(&dir).unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()));
    let mut found: Vec<(String, String)> = entries
        .map(|entry| entry.expect("a directory entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "en"))
        .map(|path| {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .expect("a UTF-8 file name")
                .to_owned();
            let text = fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("cannot read {}: {error}", path.display()));
            (name, text)
        })
        .collect();
    found.sort();
    found
}

pub fn register(h: &mut Harness) {
    // Each shrunk failure passes the four tests of TESTING 17 with its source, and
    // the round trip above as a tree with none.
    for (name, text) in regressions() {
        h.case(format!("gen/regress/{name}"), move || {
            four_tests_as(&name, &text, Some(&text))?;
            let (_, tree) = try_parse(&name, &text)?;
            round_trip(&name, &erase(&tree)).map(|_| ())
        });
    }
    h.case("gen/regress holds the shrunk failures", || {
        assert!(regressions().len() >= 4, "{:?}", regressions());
    });
    // `[A] | B | null` in a field reads as it does in any other type position.
    h.case(
        "gen/regress: a field's tuple-first type with a last `| null` is nullable",
        || {
            let field = |text: &str| {
                let (_, tree) = try_parse("f.en", text).expect("parses");
                match &erase(&tree).items[0].kind {
                    ItemKind::Class(class) => match &class.members[0].kind {
                        ClassMemberKind::Field(field) => field.ty.clone(),
                        other => panic!("{other:?}"),
                    },
                    other => panic!("{other:?}"),
                }
            };
            let alias = |text: &str| {
                let (_, tree) = try_parse("f.en", text).expect("parses");
                match &erase(&tree).items[0].kind {
                    ItemKind::TypeAlias(alias) => alias.ty.clone(),
                    other => panic!("{other:?}"),
                }
            };
            for ty in [
                "[] | T | null",
                "[A, B] | C | D | null",
                "[A] | null",
                "[A] | B",
            ] {
                let in_field = field(&format!("public class C {{\n  public a: {ty};\n}}\n"));
                let elsewhere = alias(&format!("public type A = {ty};\n"));
                assert_eq!(in_field, elsewhere, "{ty}");
            }
        },
    );
    h.case(
        "gen/GenSyntax: generated programs print, parse back to their tree and print the same",
        || {
            let mut rng = rng_for("gen-syntax");
            let mut reached: BTreeSet<&str> = BTreeSet::new();
            let count = scaled(200);
            for index in 0..count {
                let program_seed = rng.next_u64();
                let tape = Tape {
                    values: Vec::new(),
                    at: 0,
                    rng: Some(Xoshiro256::new(program_seed)),
                };
                let (name, tree) = generate(tape);
                let debug = format!("{tree:?}");
                reached.extend(REACHED.iter().copied().filter(|word| debug.contains(word)));
                if let Err(why) = round_trip(name, &tree) {
                    // Record the tape again and shrink it.
                    let mut recorder = Gen::new(Tape {
                        values: Vec::new(),
                        at: 0,
                        rng: Some(Xoshiro256::new(program_seed)),
                    });
                    recorder.file();
                    let values = recorder.tape.values;
                    let small = shrink_within(values, SHRINK_LIMIT, |t| check(t).is_err());
                    let (small_name, small_tree) = generate(Tape {
                        values: small.clone(),
                        at: 0,
                        rng: None,
                    });
                    let small_why = check(&small).err().unwrap_or_default();
                    let small_text = print_file(&source(small_name, ""), &small_tree);
                    return Err(format!(
                        "ENRANG_SEED={:#x}, program {index} of {count} ({name}):\n{why}\n\n\
                         shrunk to ({small_name}):\n{small_text}\n{small_why}",
                        seed()
                    ));
                }
            }
            if count >= 200 {
                let missed: Vec<&&str> = REACHED
                    .iter()
                    .filter(|word| !reached.contains(**word))
                    .collect();
                if !missed.is_empty() {
                    return Err(format!("no generated program has {missed:?}"));
                }
            }
            Ok(())
        },
    );
    h.case(
        "gen/GenBytes: mutated SPEC blocks never make fmt panic, and those that parse \
         pass the four tests",
        || {
            let mut rng = rng_for("gen-bytes");
            let words = soup_words();
            let blocks = spec_sources();
            let count = scaled(2_000);
            let mut clean = 0;
            for _ in 0..count {
                let spec = &blocks[rng.below(blocks.len() as u64) as usize];
                let text = mutate(&mut rng, &spec.text, &words);
                match bytes_check(&spec.name, &text) {
                    Ok(parsed) => clean += usize::from(parsed),
                    Err(why) => {
                        let fails = |t: &String| bytes_check(&spec.name, t).is_err();
                        let small = shrink_within(text, SHRINK_LIMIT, fails);
                        let small_why = bytes_check(&spec.name, &small).err().unwrap_or_default();
                        return Err(format!(
                            "ENRANG_SEED={:#x}, a mutation of {} ({}):\n{why}\n\n\
                             shrunk to:\n{small}\n{small_why}",
                            seed(),
                            spec.label,
                            spec.name
                        ));
                    }
                }
            }
            // Enough of them parse for the four tests to have run.
            assert!(clean * 20 >= count, "only {clean} of {count} parsed clean");
            Ok(())
        },
    );
    h.case(
        "gen/GenBytes: byte mutations of SPEC blocks and fixtures, invalid UTF-8 \
         included, never make the parser or the printer panic",
        || {
            let mut rng = rng_for("gen-raw-bytes");
            let mut inputs: Vec<(String, String, Vec<u8>)> = spec_sources()
                .iter()
                .map(|spec| {
                    (
                        spec.label.clone(),
                        spec.name.clone(),
                        spec.text.as_bytes().to_vec(),
                    )
                })
                .collect();
            inputs.extend(fixture_bytes());
            assert!(inputs.len() > 200, "{} inputs", inputs.len());
            let count = scaled(2_000);
            let mut invalid = 0;
            for _ in 0..count {
                let (label, name, bytes) = &inputs[rng.below(inputs.len() as u64) as usize];
                let mutant = mutate_bytes(&mut rng, bytes);
                invalid += usize::from(std::str::from_utf8(&mutant).is_err());
                if let Err(why) = raw_bytes_check(name, &mutant) {
                    let fails = |b: &Vec<u8>| raw_bytes_check(name, b).is_err();
                    let small = shrink_within(mutant, SHRINK_LIMIT, fails);
                    let small_why = raw_bytes_check(name, &small).err().unwrap_or_default();
                    return Err(format!(
                        "ENRANG_SEED={:#x}, a byte mutation of {label}:\n{why}\n\n\
                         shrunk to:\n{small:?}\n{small_why}",
                        seed()
                    ));
                }
            }
            // Enough of them are not UTF-8 for EN0001's path to have run.
            assert!(
                invalid * 10 >= count,
                "only {invalid} of {count} were not UTF-8"
            );
            Ok(())
        },
    );
    h.case("gen/a replayed tape makes the same program", || {
        let mut recorder = Gen::new(Tape {
            values: Vec::new(),
            at: 0,
            rng: Some(Xoshiro256::new(7)),
        });
        let first = recorder.file();
        let (_, replayed) = generate(Tape {
            values: recorder.tape.values,
            at: 0,
            rng: None,
        });
        assert_eq!(first, replayed);
        // An empty tape makes the simplest program, which round-trips.
        let (name, empty) = generate(Tape {
            values: Vec::new(),
            at: 0,
            rng: None,
        });
        assert_eq!(
            empty.imports.len() + empty.stmts.len() + empty.items.len(),
            0
        );
        round_trip(name, &empty).map(|_| ())
    });
}
