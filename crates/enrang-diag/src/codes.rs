//! The code registry (SPEC 13.2, ARCHITECTURE 2.2).
//!
//! One macro invocation holds one row per line of the SPEC catalog. It generates
//! `enum Code`, `Code::ALL` and [`ROWS`], the table the meta-tests read. Codes are
//! never reused: a retired code leaves the table and its number is never given out
//! again. EN0704, EN0204, EN0212, EN0217, EN0223, EN0306, EN0407, EN0431, EN0505,
//! EN0620, EN0716, EN0719, EN0720, EN0810, EN1008, EN1016, EN1020 and EN1040 are
//! retired and absent; `enrang explain` says why each one went.

use std::fmt;

use crate::diagnostic::Severity;

/// A milestone of ARCHITECTURE 12, in delivery order.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Milestone {
    M0,
    M1,
    M2,
    M3,
    M4,
    M5,
    M6,
    M7,
    M8,
    M9,
    M10,
}

/// The last milestone closed. The commit closing a milestone bumps it, and
/// meta-tests enforce only rows with `since <= CURRENT_MILESTONE`; the milestone
/// after it is the one being built.
pub const CURRENT_MILESTONE: Milestone = Milestone::M3;

impl fmt::Display for Milestone {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Where a code is reported: a phase of SPEC 13.1, the command line or run time.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Phase {
    /// `0`: the command line, before any source is read.
    CommandLine,
    /// `1`: lexical and syntax.
    Syntax,
    /// `2`: resolve and types.
    Types,
    /// `3`: moves and borrows.
    Borrows,
    /// `4`: level and layout.
    Layout,
    /// `5`: reachability.
    Reachability,
    /// `R`: run time or reload.
    Runtime,
}

impl fmt::Display for Phase {
    /// The catalog's spelling of the phase: a digit, or `R`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Phase::CommandLine => "0",
            Phase::Syntax => "1",
            Phase::Types => "2",
            Phase::Borrows => "3",
            Phase::Layout => "4",
            Phase::Reachability => "5",
            Phase::Runtime => "R",
        })
    }
}

/// The crate family that reports a code.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Owner {
    Borrowck,
    Cli,
    Codegen,
    Dev,
    Driver,
    Layout,
    Link,
    Mono,
    Sema,
    Syntax,
    Target,
    Testrun,
    Vm,
}

impl fmt::Display for Owner {
    /// The catalog's spelling of the owner.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Owner::Borrowck => "borrowck",
            Owner::Cli => "cli",
            Owner::Codegen => "codegen",
            Owner::Dev => "dev",
            Owner::Driver => "driver",
            Owner::Layout => "layout",
            Owner::Link => "link",
            Owner::Mono => "mono",
            Owner::Sema => "sema",
            Owner::Syntax => "syntax",
            Owner::Target => "target",
            Owner::Testrun => "testrun",
            Owner::Vm => "vm",
        })
    }
}

/// How a code's firing test runs.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum FixtureKind {
    /// An anchored source.
    Compile,
    /// A command.
    Cli,
    /// A dev scenario.
    Reload,
    /// A test-runner run.
    TestRun,
}

impl fmt::Display for FixtureKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// One row of the catalog.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct CodeRow {
    /// The code as it is written: `EN0601`.
    pub name: &'static str,
    pub severity: Severity,
    pub phase: Phase,
    pub owner: Owner,
    /// The milestone that must make the code fire.
    pub since: Milestone,
    pub fixture: FixtureKind,
    pub title: &'static str,
}

macro_rules! phase_of {
    (0) => {
        $crate::codes::Phase::CommandLine
    };
    (1) => {
        $crate::codes::Phase::Syntax
    };
    (2) => {
        $crate::codes::Phase::Types
    };
    (3) => {
        $crate::codes::Phase::Borrows
    };
    (4) => {
        $crate::codes::Phase::Layout
    };
    (5) => {
        $crate::codes::Phase::Reachability
    };
    (R) => {
        $crate::codes::Phase::Runtime
    };
}

macro_rules! owner_of {
    (borrowck) => {
        $crate::codes::Owner::Borrowck
    };
    (cli) => {
        $crate::codes::Owner::Cli
    };
    (codegen) => {
        $crate::codes::Owner::Codegen
    };
    (dev) => {
        $crate::codes::Owner::Dev
    };
    (driver) => {
        $crate::codes::Owner::Driver
    };
    (layout) => {
        $crate::codes::Owner::Layout
    };
    (link) => {
        $crate::codes::Owner::Link
    };
    (mono) => {
        $crate::codes::Owner::Mono
    };
    (sema) => {
        $crate::codes::Owner::Sema
    };
    (syntax) => {
        $crate::codes::Owner::Syntax
    };
    (target) => {
        $crate::codes::Owner::Target
    };
    (testrun) => {
        $crate::codes::Owner::Testrun
    };
    (vm) => {
        $crate::codes::Owner::Vm
    };
}

macro_rules! define_codes {
    ($(
        $code:ident $severity:ident phase($phase:tt) owner($owner:ident)
        since($since:ident) fixture($fixture:ident) $title:literal,
    )+) => {
        /// A diagnostic code. The order is the catalog's.
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        pub enum Code {
            $($code,)+
        }

        /// The catalog, in the order of `Code::ALL`.
        pub const ROWS: &[$crate::codes::CodeRow] = &[$(
            $crate::codes::CodeRow {
                name: stringify!($code),
                severity: $crate::diagnostic::Severity::$severity,
                phase: phase_of!($phase),
                owner: owner_of!($owner),
                since: $crate::codes::Milestone::$since,
                fixture: $crate::codes::FixtureKind::$fixture,
                title: $title,
            },
        )+];

        impl Code {
            /// Every code, in catalog order.
            pub const ALL: &'static [Code] = &[$(Code::$code,)+];

            pub fn row(self) -> &'static $crate::codes::CodeRow {
                &ROWS[self as usize]
            }

            /// The code as it is written: `EN0601`.
            pub fn name(self) -> &'static str {
                self.row().name
            }

            pub fn severity(self) -> $crate::diagnostic::Severity {
                self.row().severity
            }

            pub fn phase(self) -> $crate::codes::Phase {
                self.row().phase
            }

            pub fn owner(self) -> $crate::codes::Owner {
                self.row().owner
            }

            pub fn since(self) -> $crate::codes::Milestone {
                self.row().since
            }

            pub fn fixture(self) -> $crate::codes::FixtureKind {
                self.row().fixture
            }

            pub fn title(self) -> &'static str {
                self.row().title
            }

            /// Whether the milestone that must make this code fire has arrived.
            pub fn reached(self) -> bool {
                self.since() <= $crate::codes::CURRENT_MILESTONE
            }

            /// The code written `name`, exactly. Retired codes have none.
            pub fn from_name(name: &str) -> Option<Code> {
                Code::ALL.iter().copied().find(|code| code.name() == name)
            }
        }

        impl std::fmt::Display for Code {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str(self.name())
            }
        }
    };
}

define_codes! {
    EN0001 Error phase(1) owner(syntax) since(M1) fixture(Compile) "source is not valid UTF-8",
    EN0002 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unterminated block comment",
    EN0003 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unknown escape sequence",
    EN0004 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unterminated string or template",
    EN0005 Error phase(1) owner(syntax) since(M1) fixture(Compile) "leading-zero integer literal (TS legacy octal)",
    EN0006 Error phase(1) owner(syntax) since(M1) fixture(Compile) "malformed float literal, `.5` or `5.`",
    EN0007 Error phase(1) owner(syntax) since(M1) fixture(Compile) "numeric literal suffix",
    EN0008 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unexpected character",

    EN0100 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unexpected token",
    EN0101 Error phase(1) owner(syntax) since(M1) fixture(Compile) "missing `;`",
    EN0102 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unclosed delimiter",
    EN0103 Error phase(1) owner(syntax) since(M1) fixture(Compile) "wrong spacing around `?` or postfix `!`",
    EN0104 Error phase(1) owner(syntax) since(M1) fixture(Compile) "braces required after `if`, `else`, `while`, `for`",
    EN0105 Error phase(1) owner(syntax) since(M1) fixture(Compile) "assignment used as a condition or as an operand of `&&`, `||` or `!`",
    EN0106 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`??` mixed with `||` or `&&` without parentheses",
    EN0107 Error phase(1) owner(syntax) since(M1) fixture(Compile) "chained comparison",
    EN0108 Error phase(1) owner(syntax) since(M1) fixture(Compile) "decorator cannot appear here",
    EN0109 Error phase(1) owner(syntax) since(M1) fixture(Compile) "item not allowed at this position",
    EN0110 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`import` after an item",
    EN0111 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`break` or `continue` outside a loop, or crossing an arrow",
    EN0112 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unknown label",
    EN0113 Error phase(1) owner(syntax) since(M1) fixture(Compile) "duplicate label",
    EN0114 Error phase(1) owner(syntax) since(M1) fixture(Compile) "invalid assignment target",
    EN0115 Error phase(1) owner(syntax) since(M1) fixture(Compile) "top-level statement after a class or other declaration",
    EN0116 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`const` without a value",

    EN0201 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`===` or `!==`: use `==` and `!=`",
    EN0202 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`var`: use `let` or `const`",
    EN0203 Error phase(2) owner(sema) since(M2) fixture(Compile) "no truthiness: a condition must be `bool`",
    EN0205 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`any`: use a generic or enum",
    EN0206 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`undefined`: use `null`",
    EN0207 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`throw`, `try`, `catch`: use `Result`, `?`, `panic`",
    EN0208 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`>>>`: `>>` is logical on unsigned types",
    EN0209 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`switch`: use `match`",
    EN0210 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`unknown`: use a generic",
    EN0211 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`typeof`, `instanceof`: use an enum and `match`",
    EN0213 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`using`: every binding already drops; write a `destructor`",
    EN0214 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`readonly T` as a type other than a returned reference or a reference field: use `&T` (also phase 2)",
    EN0215 Error phase(1) owner(syntax) since(M1) fixture(Compile) "union of object types: declare a class or enum",
    EN0216 Error phase(1) owner(syntax) since(M1) fixture(Compile) "string-literal union outside a type alias, or mixed with other types",
    EN0218 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`function` expression: use an arrow",
    EN0219 Error phase(2) owner(sema) since(M2) fixture(Compile) "`this` or `super` out of place",
    EN0220 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`interface ... extends`: list bounds with `&`",
    EN0221 Error phase(2) owner(sema) since(M2) fixture(Compile) "`new` on a non-class",
    EN0222 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`namespace`, `delete`: not in Enrang",
    EN0224 Error phase(1) owner(syntax) since(M1) fixture(Compile) "return type after a bare arrow parameter",
    EN0225 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`number`: use `f64`, or `int` for whole numbers",
    EN0226 Error phase(1) owner(syntax) since(M1) fixture(Compile) "missing `public`, `private` or `protected`",
    EN0227 Error phase(1) owner(syntax) since(M1) fixture(Compile) "both `?` and a default on a parameter or field",
    EN0228 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`move` before an expression: a value moves when there is no `&`",
    EN0229 Error phase(1) owner(syntax) since(M1) fixture(Compile) "parameter with no default after one with a default or `?`",

    EN0301 Error phase(2) owner(sema) since(M2) fixture(Compile) "unresolved name",
    EN0302 Error phase(2) owner(sema) since(M2) fixture(Compile) "unresolved type",
    EN0303 Error phase(2) owner(sema) since(M2) fixture(Compile) "no such member",
    EN0304 Error phase(2) owner(sema) since(M2) fixture(Compile) "import cycle",
    EN0305 Error phase(2) owner(sema) since(M2) fixture(Compile) "import path not found",
    EN0307 Error phase(2) owner(sema) since(M2) fixture(Compile) "duplicate definition",
    EN0308 Error phase(2) owner(sema) since(M2) fixture(Compile) "private or protected member",
    EN0309 Error phase(2) owner(sema) since(M2) fixture(Compile) "wrong number of type arguments",
    EN0310 Error phase(5) owner(driver) since(M4) fixture(Cli) "no top-level statements or `main` on a hosted target",
    EN0311 Error phase(2) owner(sema) since(M2) fixture(Compile) "importing a `private` item",
    EN0312 Error phase(2) owner(sema) since(M2) fixture(Compile) "imported file has top-level statements",
    EN0313 Error phase(2) owner(sema) since(M2) fixture(Compile) "top-level variable not visible here",
    EN0314 Warning phase(2) owner(sema) since(M2) fixture(Compile) "`main` beside top-level statements is not the entry point",
    EN0315 Error phase(2) owner(driver) since(M4) fixture(Cli) "module has a stale interface file and no source",
    EN0316 Error phase(3) owner(driver) since(M4) fixture(Cli) "interface file's stored code fails the check on load",

    EN0401 Error phase(2) owner(sema) since(M2) fixture(Compile) "mismatched types",
    EN0402 Error phase(2) owner(sema) since(M2) fixture(Compile) "mixed numeric types",
    EN0403 Error phase(2) owner(sema) since(M2) fixture(Compile) "operator needs integer types",
    EN0404 Error phase(2) owner(sema) since(M2) fixture(Compile) "invalid `as`",
    EN0405 Error phase(2) owner(sema) since(M2) fixture(Compile) "index must be an integer",
    EN0406 Error phase(2) owner(sema) since(M2) fixture(Compile) "union other than `T | null`",
    EN0408 Error phase(2) owner(sema) since(M2) fixture(Compile) "recursive type needs `Box`",
    EN0409 Error phase(2) owner(sema) since(M2) fixture(Compile) "missing annotation on a parameter or field",
    EN0410 Error phase(2) owner(sema) since(M2) fixture(Compile) "cannot infer type",
    EN0411 Error phase(2) owner(sema) since(M2) fixture(Compile) "literal does not fit",
    EN0412 Error phase(2) owner(sema) since(M2) fixture(Compile) "constant evaluation failed, or constant cycle",
    EN0413 Error phase(2) owner(sema) since(M2) fixture(Compile) "`?.` on an owned rvalue",
    EN0414 Error phase(5) owner(mono) since(M4) fixture(Compile) "monomorphisation depth above 64",
    EN0415 Error phase(2) owner(sema) since(M2) fixture(Compile) "compile-time assert failed",
    EN0416 Error phase(2) owner(sema) since(M2) fixture(Compile) "class does not satisfy `implements`",
    EN0417 Error phase(2) owner(sema) since(M2) fixture(Compile) "interface mixes fields and methods",
    EN0418 Error phase(2) owner(sema) since(M2) fixture(Compile) "invalid `implements Copy` (also phase 3)",
    EN0419 Error phase(2) owner(sema) since(M2) fixture(Compile) "type argument does not satisfy a bound, or sealed bound implemented",
    EN0420 Error phase(2) owner(sema) since(M2) fixture(Compile) "operator not applicable to these types",
    EN0421 Error phase(2) owner(sema) since(M2) fixture(Compile) "`==` needs `Eq`",
    EN0422 Error phase(2) owner(sema) since(M2) fixture(Compile) "assigning a value to a reference variable",
    EN0423 Error phase(2) owner(sema) since(M2) fixture(Compile) "wrong argument count",
    EN0424 Error phase(2) owner(sema) since(M2) fixture(Compile) "`?` in a function that does not return `Result` or nullable",
    EN0425 Error phase(2) owner(sema) since(M2) fixture(Compile) "`?` error type differs",
    EN0426 Error phase(2) owner(sema) since(M2) fixture(Compile) "unused `Result`",
    EN0427 Error phase(2) owner(sema) since(M2) fixture(Compile) "missing return",
    EN0428 Error phase(2) owner(sema) since(M2) fixture(Compile) "not callable",
    EN0429 Error phase(2) owner(sema) since(M2) fixture(Compile) "`?` on a type other than `Result` or nullable",
    EN0430 Warning phase(2) owner(sema) since(M2) fixture(Compile) "integer division truncates",
    EN0432 Error phase(2) owner(sema) since(M2) fixture(Compile) "ternary or arm types differ",
    EN0433 Error phase(2) owner(sema) since(M2) fixture(Compile) "field with no default left unset",
    EN0434 Error phase(2) owner(sema) since(M2) fixture(Compile) "unknown field in a literal",
    EN0435 Error phase(4) owner(layout) since(M2) fixture(Compile) "type, frame or static too large for the target (also phase 5 and link)",
    EN0436 Error phase(2) owner(sema) since(M2) fixture(Compile) "invalid `main` signature",
    EN0437 Error phase(2) owner(sema) since(M2) fixture(Compile) "recursive type alias",
    EN0438 Error phase(2) owner(sema) since(M2) fixture(Compile) "spread source is not an array of cloneable elements",
    EN0439 Error phase(2) owner(sema) since(M2) fixture(Compile) "`extend` on an anonymous object type or tuple",
    EN0440 Error phase(2) owner(sema) since(M2) fixture(Compile) "extra fields where the declared type fixes the storage",
    EN0441 Error phase(2) owner(sema) since(M2) fixture(Compile) "`length` read as a property: call `length()`",
    EN0442 Error phase(2) owner(sema) since(M2) fixture(Compile) "class extends a `final` class",
    EN0443 Error phase(2) owner(sema) since(M2) fixture(Compile) "`override` on a member that replaces nothing",
    EN0444 Error phase(2) owner(sema) since(M2) fixture(Compile) "member replaces a base member without `override`",
    EN0445 Error phase(2) owner(sema) since(M2) fixture(Compile) "`new` on an abstract class",
    EN0446 Error phase(2) owner(sema) since(M2) fixture(Compile) "class does not implement an abstract method",
    EN0447 Error phase(2) owner(sema) since(M2) fixture(Compile) "named form on a class with a constructor",
    EN0448 Error phase(2) owner(sema) since(M2) fixture(Compile) "class needs a constructor: a field has no default",
    EN0449 Error phase(2) owner(sema) since(M2) fixture(Compile) "arguments to `new` or `super` for a class with no constructor",
    EN0450 Error phase(2) owner(sema) since(M2) fixture(Compile) "overloads one call cannot tell apart",
    EN0451 Error phase(2) owner(sema) since(M2) fixture(Compile) "no overload, or more than one, matches the call",
    EN0452 Error phase(2) owner(sema) since(M2) fixture(Compile) "tuple index out of range or not a constant",
    EN0453 Warning phase(2) owner(sema) since(M2) fixture(Compile) "result of a must-use call is not used",
    EN0454 Error phase(2) owner(sema) since(M2) fixture(Compile) "`Result` error argument is not an error type",
    EN0455 Error phase(2) owner(sema) since(M2) fixture(Compile) "plain value that could be a success or an error",
    EN0456 Error phase(2) owner(sema) since(M2) fixture(Compile) "enum `=` values mix numbers and texts",
    EN0457 Error phase(2) owner(sema) since(M2) fixture(Compile) "`super` call to an abstract method",
    EN0458 Error phase(2) owner(sema) since(M2) fixture(Compile) "`move` method not declared in the receiver's class",
    EN0459 Warning phase(2) owner(sema) since(M2) fixture(Compile) "`move` method of an abstract class can never run",
    EN0460 Error phase(2) owner(sema) since(M2) fixture(Compile) "override of a method compiled once per type, or an abstract one",

    EN0501 Error phase(2) owner(sema) since(M2) fixture(Compile) "non-exhaustive `match`",
    EN0502 Error phase(2) owner(sema) since(M2) fixture(Compile) "unqualified enum case in a `match` arm",
    EN0503 Warning phase(2) owner(sema) since(M2) fixture(Compile) "unreachable arm",
    EN0504 Error phase(2) owner(sema) since(M2) fixture(Compile) "arm value does not match the subject's type",
    EN0506 Error phase(2) owner(sema) since(M2) fixture(Compile) "refutable pattern in a destructuring",

    EN0601 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "use after move",
    EN0602 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "use before assignment of a type with no default",
    EN0603 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "move through a reference",
    EN0604 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "move out of an array element",
    EN0605 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "move out of `*box`",
    EN0606 Error phase(2) owner(sema) since(M2) fixture(Compile) "a `destructor` called by name, or declared in an interface",
    EN0607 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "partial move from a class with a destructor",
    EN0608 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "mutating through `const`",
    EN0609 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "writing a `readonly` field",
    EN0610 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "`this` used before all fields are assigned",
    EN0611 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "moved in a previous loop iteration",
    EN0612 Error phase(2) owner(sema) since(M2) fixture(Compile) "missing `&` where a reference is expected",
    EN0613 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "assignment to a `const` or to a parameter not marked `let`",
    EN0614 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "changing method called on a `const` value or through a read-only reference",
    EN0615 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "body does more with its references than its declaration allows",
    EN0616 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "writing through a read-only reference, rebinding or storing through a capture, or storing into a `readonly &` field from a field written through",
    EN0617 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "closure moves a capture",
    EN0618 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "call reads a top-level variable before its declaration",
    EN0619 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "`super(...)` not run exactly once on every path",
    EN0621 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "an assignment's value can't be kept",

    EN0701 Error phase(2) owner(sema) since(M2) fixture(Compile) "reference, or a class holding one, in an element, payload, generic argument or interface value, or in a non-`private` field",
    EN0702 Error phase(2) owner(sema) since(M2) fixture(Compile) "reference to a reference",
    EN0703 Error phase(2) owner(sema) since(M2) fixture(Compile) "type parameter bound to a reference",
    EN0705 Error phase(2) owner(sema) since(M2) fixture(Compile) "closure type outside a parameter, or nested closure type",
    EN0706 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "mutated while shared-borrowed",
    EN0707 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "second exclusive borrow",
    EN0708 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "read while exclusively borrowed",
    EN0709 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "moved while borrowed",
    EN0710 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "returning a reference to local data",
    EN0711 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "dropped while borrowed",
    EN0712 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "temporary dropped while borrowed",
    EN0714 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "returned reference from a parameter outside the allowed sources",
    EN0715 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "closure capture conflicts with a live borrow",
    EN0718 Error phase(3) owner(borrowck) since(M3) fixture(Compile) "closure used re-entrantly: called, forwarded or captured twice",

    EN0801 Error phase(2) owner(sema) since(M2) fixture(Compile) "operation needs `unsafe`",
    EN0802 Error phase(2) owner(sema) since(M2) fixture(Compile) "invalid type for an `unsafe let`",
    EN0803 Error phase(2) owner(sema) since(M2) fixture(Compile) "function with preconditions used as a safe `fn` or closure",
    EN0804 Error phase(4) owner(borrowck) since(M3) fixture(Compile) "reference to a misaligned packed field",
    EN0805 Error phase(2) owner(sema) since(M2) fixture(Compile) "volatile access on a type outside `VolatileValue`",
    EN0806 Error phase(2) owner(sema) since(M2) fixture(Compile) "unknown or misapplied decorator, or library-only form in user code",
    EN0807 Error phase(2) owner(sema) since(M2) fixture(Compile) "calling an interrupt handler",
    EN0808 Error phase(2) owner(sema) since(M2) fixture(Compile) "invalid interrupt signature",
    EN0809 Error phase(5) owner(driver) since(M9) fixture(Compile) "missing or invalid `@entry`",
    EN0811 Error phase(2) owner(sema) since(M9) fixture(Compile) "second `@panicHandler`",
    EN0812 Error phase(5) owner(mono) since(M9) fixture(Compile) "missing `@panicHandler`",
    EN0813 Error phase(5) owner(link) since(M9) fixture(Compile) "`@at` overlap",
    EN0814 Error phase(2) owner(sema) since(M2) fixture(Compile) "section not allowed on this target, or reserved",
    EN0815 Error phase(2) owner(sema) since(M2) fixture(Compile) "`declare function` without `@dll`",
    EN0816 Error phase(2) owner(sema) since(M2) fixture(Compile) "`string`, `T[]` or a reference in FFI",
    EN0817 Error phase(2) owner(sema) since(M2) fixture(Compile) "conflicting layout attributes",
    EN0819 Error phase(2) owner(sema) since(M2) fixture(Compile) "unknown `@abi`",
    EN0820 Error phase(5) owner(mono) since(M9) fixture(Compile) "allocation with no global allocator",
    EN0821 Error phase(2) owner(sema) since(M4) fixture(Compile) "second `@globalAllocator`",
    EN0822 Error phase(2) owner(sema) since(M4) fixture(Compile) "allocator type lacks `GlobalAllocator`",
    EN0823 Error phase(5) owner(mono) since(M9) fixture(Compile) "`os` hosted API on a freestanding target",
    EN0824 Error phase(5) owner(mono) since(M9) fixture(Compile) "allocation reachable from an interrupt handler, panic handler or the allocator",
    EN0825 Error phase(2) owner(sema) since(M4) fixture(Compile) "`@globalAllocator` on something other than an `unsafe let`",
    EN0826 Error phase(2) owner(sema) since(M2) fixture(Compile) "`@packed` field must be Copy and non-generic",
    EN0827 Error phase(2) owner(sema) since(M2) fixture(Compile) "layout decorator on a class that is not `final`, has a base, or holds a hidden pointer",
    EN0828 Warning phase(2) owner(sema) since(M2) fixture(Compile) "function that is not `unsafe` reads or writes through a raw-pointer parameter",

    EN0901 Error phase(4) owner(codegen) since(M5) fixture(Compile) "instruction above the target CPU level",
    EN0902 Error phase(4) owner(codegen) since(M5) fixture(Compile) "unknown mnemonic",
    EN0903 Error phase(4) owner(codegen) since(M5) fixture(Compile) "invalid operands",
    EN0904 Error phase(4) owner(codegen) since(M5) fixture(Compile) "unknown register",
    EN0905 Error phase(4) owner(codegen) since(M5) fixture(Compile) "cannot bind stack or frame register",
    EN0907 Error phase(2) owner(sema) since(M2) fixture(Compile) "`@requires` function called outside `unsafe`",
    EN0908 Error phase(2) owner(sema) since(M2) fixture(Compile) "unknown feature name",
    EN0909 Error phase(0) owner(target) since(M1) fixture(Cli) "unknown or rejected `--cpu`",
    EN0910 Error phase(4) owner(sema) since(M5) fixture(Compile) "atomic operation or `Atomic64` above the level",
    EN0911 Error phase(0) owner(target) since(M1) fixture(Cli) "float strategy not available at this level or on this target",
    EN0912 Error phase(0) owner(target) since(M1) fixture(Cli) "level does not apply to this target",
    EN0913 Error phase(4) owner(codegen) since(M5) fixture(Compile) "`@bits` misuse",
    EN0914 Warning phase(4) owner(codegen) since(M5) fixture(Compile) "`popa` erratum at `i386`",
    EN0915 Error phase(4) owner(codegen) since(M5) fixture(Compile) "interpolation in `asm`",
    EN0916 Error phase(4) owner(codegen) since(M5) fixture(Compile) "MMX, 3DNow! or packed SSE form",
    EN0917 Error phase(4) owner(codegen) since(M5) fixture(Compile) "register not valid in this mode",

    EN1001 Error phase(1) owner(syntax) since(M1) fixture(Compile) "async functions",
    EN1002 Error phase(1) owner(syntax) since(M1) fixture(Compile) "generators",
    EN1003 Error phase(2) owner(sema) since(M2) fixture(Compile) "threads",
    EN1004 Error phase(2) owner(sema) since(M2) fixture(Compile) "shared ownership types",
    EN1005 Error phase(1) owner(syntax) since(M1) fixture(Compile) "named lifetimes",
    EN1006 Error phase(2) owner(sema) since(M2) fixture(Compile) "interface type by value outside a parameter",
    EN1007 Error phase(2) owner(sema) since(M2) fixture(Compile) "capturing arrow as a function pointer",
    EN1009 Error phase(1) owner(syntax) since(M1) fixture(Compile) "unsupported module form",
    EN1010 Error phase(1) owner(syntax) since(M1) fixture(Compile) "default in a destructuring pattern",
    EN1011 Error phase(2) owner(sema) since(M2) fixture(Compile) "range indexing, `str`",
    EN1012 Error phase(2) owner(sema) since(M2) fixture(Compile) "`Map` and `Set`",
    EN1013 Error phase(1) owner(syntax) since(M1) fixture(Compile) "spread outside an array literal, and rest",
    EN1014 Error phase(2) owner(sema) since(M2) fixture(Compile) "unsupported generic feature",
    EN1015 Error phase(2) owner(sema) since(M2) fixture(Compile) "unsupported `for...of` source",
    EN1017 Error phase(1) owner(syntax) since(M1) fixture(Compile) "setters",
    EN1018 Error phase(1) owner(syntax) since(M1) fixture(Compile) "operator overloading",
    EN1019 Error phase(2) owner(sema) since(M2) fixture(Compile) "character type",
    EN1021 Error phase(1) owner(syntax) since(M1) fixture(Compile) "static fields",
    EN1022 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`**` operator",
    EN1023 Error phase(1) owner(syntax) since(M1) fixture(Compile) "type-level computation",
    EN1024 Error phase(1) owner(syntax) since(M1) fixture(Compile) "intersection types",
    EN1025 Error phase(1) owner(syntax) since(M1) fixture(Compile) "regular expressions",
    EN1026 Error phase(2) owner(sema) since(M2) fixture(Compile) "`Math`",
    EN1027 Error phase(2) owner(sema) since(M2) fixture(Compile) "`JSON`",
    EN1028 Error phase(2) owner(sema) since(M2) fixture(Compile) "network APIs",
    EN1029 Error phase(2) owner(sema) since(M2) fixture(Compile) "reflection",
    EN1030 Error phase(2) owner(sema) since(M2) fixture(Compile) "foreign ABI, or class by value in FFI",
    EN1031 Error phase(0) owner(target) since(M1) fixture(Cli) "32-bit Windows output",
    EN1032 Error phase(2) owner(sema) since(M2) fixture(Compile) "compile-time function calls",
    EN1033 Error phase(2) owner(sema) since(M2) fixture(Compile) "unchecked reinterpretation",
    EN1034 Error phase(0) owner(cli) since(M1) fixture(Cli) "DWARF output",
    EN1035 Error phase(1) owner(syntax) since(M1) fixture(Compile) "nested functions",
    EN1036 Error phase(1) owner(syntax) since(M1) fixture(Compile) "generic arrows",
    EN1037 Error phase(1) owner(syntax) since(M1) fixture(Compile) "class expressions",
    EN1038 Error phase(1) owner(syntax) since(M1) fixture(Compile) "labelled blocks",
    EN1039 Error phase(1) owner(syntax) since(M1) fixture(Compile) "`as const`",
    EN1041 Error phase(0) owner(cli) since(M1) fixture(Cli) "`--multiboot`, `--coverage`",
    EN1042 Error phase(2) owner(sema) since(M2) fixture(Compile) "destructuring a `T[]` or `T[N]`",

    EN1101 Error phase(2) owner(sema) since(M4) fixture(Compile) "`expect` outside a test",
    EN1102 Error phase(1) owner(syntax) since(M4) fixture(Compile) "non-test content in `describe`",
    EN1103 Error phase(2) owner(sema) since(M4) fixture(Compile) "`expect` as a value",
    EN1104 Error phase(2) owner(sema) since(M4) fixture(Compile) "Jest matcher hint",
    EN1105 Error phase(1) owner(syntax) since(M4) fixture(Compile) "lifecycle hook hint",
    EN1106 Error phase(0) owner(testrun) since(M4) fixture(TestRun) "`test.only` under `--ci`",
    EN1107 Error phase(0) owner(testrun) since(M4) fixture(TestRun) "compile-test anchor mismatch",
    EN1108 Error phase(2) owner(sema) since(M4) fixture(Compile) "unknown matcher",
    EN1109 Error phase(2) owner(sema) since(M4) fixture(Compile) "duplicate test ID",
    EN1110 Error phase(2) owner(sema) since(M4) fixture(Compile) "test declared inside a function",
    EN1111 Error phase(0) owner(testrun) since(M4) fixture(TestRun) "`allow` names a path outside the project root",
    EN1112 Error phase(1) owner(syntax) since(M4) fixture(Compile) "test outside a `*.test.en` file",

    EN1201 Error phase(5) owner(mono) since(M4) fixture(Cli) "program cannot run in the VM: `asm` reachable",
    EN1202 Error phase(5) owner(mono) since(M4) fixture(Cli) "raw `syscall` reachable in the VM",
    EN1203 Error phase(5) owner(mono) since(M4) fixture(Cli) "port I/O reachable in the VM",
    EN1204 Error phase(R) owner(vm) since(M4) fixture(Cli) "integer-derived pointer with no provenance, \"this touches physical memory\"",
    EN1205 Error phase(5) owner(mono) since(M4) fixture(Cli) "interrupt handler reachable in the VM",
    EN1210 Error phase(R) owner(dev) since(M6) fixture(Reload) "reload refused: migration impossible, with path",
    EN1211 Error phase(2) owner(sema) since(M6) fixture(Compile) "`@devMigrate` hook called from code",
    EN1212 Warning phase(R) owner(dev) since(M6) fixture(Reload) "stale migration hook",
    EN1213 Error phase(R) owner(dev) since(M6) fixture(Reload) "reload blocked by a live reference",
    EN1214 Error phase(R) owner(dev) since(M6) fixture(Reload) "reload refused: raw pointer into a rewritten allocation",
    EN1215 Error phase(R) owner(dev) since(M6) fixture(Reload) "census failure",
    EN1216 Error phase(R) owner(dev) since(M6) fixture(Reload) "narrowing retype failed on a value",
    EN1217 Error phase(R) owner(dev) since(M6) fixture(Reload) "migration hook reaches user `unsafe`, an `unsafe let` or a host call",

    EN1301 Error phase(0) owner(cli) since(M0) fixture(Cli) "deferred command",
    EN1302 Error phase(0) owner(cli) since(M0) fixture(Cli) "unknown command",
    EN1303 Error phase(0) owner(target) since(M1) fixture(Cli) "unknown target",
    EN1304 Error phase(0) owner(target) since(M1) fixture(Cli) "invalid flag value or combination, or `--base` overlapping the boot stages",
    EN1305 Error phase(0) owner(cli) since(M1) fixture(Cli) "file not found",
    EN1306 Error phase(0) owner(cli) since(M5) fixture(Cli) "output path not writable",
    EN1307 Error phase(0) owner(cli) since(M1) fixture(Cli) "`init` would overwrite",

    T0001 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "value matcher found different values",
    T0002 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "test panicked unexpectedly",
    T0003 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "test passed but leaked",
    T0004 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "test exceeded its fuel budget",
    T0005 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "`test.panics` body did not panic as expected",
    T0006 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "snapshot mismatch, or missing under `--ci`",
    T0007 Fail phase(R) owner(testrun) since(M4) fixture(TestRun) "test returned `Err`",
    T0008 Fail phase(R) owner(testrun) since(M5) fixture(TestRun) "native watchdog timeout",
}

#[cfg(test)]
mod tests {
    use enrang_testkit::{FixtureStatus, GateRow, gate};

    use super::{CURRENT_MILESTONE, Milestone};

    /// The macro over a small registry, so that gating can be tested on rows whose
    /// milestones and fixtures are chosen rather than read from the real catalog.
    mod fake {
        define_codes! {
            FAKE1 Error phase(1) owner(syntax) since(M0) fixture(Compile) "reached, passing",
            FAKE2 Warning phase(R) owner(dev) since(M0) fixture(Reload) "reached, no fixture",
            FAKE3 Fail phase(0) owner(testrun) since(M4) fixture(TestRun) "not reached, passing",
            FAKE4 Error phase(5) owner(mono) since(M4) fixture(Cli) "not reached, no fixture",
        }
    }

    use fake::Code;

    fn status(code: Code) -> FixtureStatus {
        match code {
            Code::FAKE1 | Code::FAKE3 => FixtureStatus::Passing,
            Code::FAKE2 | Code::FAKE4 => FixtureStatus::Missing,
        }
    }

    fn gate_rows() -> Vec<GateRow<'static, Milestone>> {
        Code::ALL
            .iter()
            .map(|&code| GateRow {
                id: code.name(),
                since: code.since(),
                fixture: status(code),
            })
            .collect()
    }

    #[test]
    fn fake_registry_generates_its_tables_in_order() {
        let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
        assert_eq!(names, ["FAKE1", "FAKE2", "FAKE3", "FAKE4"]);
        assert_eq!(fake::ROWS.len(), 4);
        assert_eq!(Code::FAKE3.title(), "not reached, passing");
        assert_eq!(Code::FAKE2.severity(), crate::Severity::Warning);
        assert_eq!(Code::FAKE3.severity(), crate::Severity::Fail);
        assert!(Code::FAKE1.reached(), "since M0 at {CURRENT_MILESTONE}");
        assert!(!Code::FAKE3.reached(), "since M4 at {CURRENT_MILESTONE}");
        assert_eq!(Code::FAKE2.phase().to_string(), "R");
        assert_eq!(Code::FAKE3.phase().to_string(), "0");
        assert_eq!(Code::FAKE4.owner().to_string(), "mono");
        assert_eq!(Code::FAKE2.fixture().to_string(), "Reload");
        assert_eq!(Code::from_name("FAKE4"), Some(Code::FAKE4));
        assert_eq!(Code::from_name("FAKE5"), None);
    }

    #[test]
    fn gate_at_m0_finds_the_gap_and_the_stale_row() {
        let report = gate(&gate_rows(), &Milestone::M0);
        assert_eq!(report.enforced, 2);
        assert_eq!(report.deferred, 2);
        let gaps: Vec<&str> = report.gaps.iter().map(|row| row.id.as_str()).collect();
        let stale: Vec<&str> = report.stale.iter().map(|row| row.id.as_str()).collect();
        assert_eq!(gaps, ["FAKE2"]);
        assert_eq!(stale, ["FAKE3"]);
    }

    #[test]
    fn gate_moves_with_the_milestone() {
        for (current, gaps, stale) in [
            (Milestone::M0, vec!["FAKE2"], vec!["FAKE3"]),
            (Milestone::M1, vec!["FAKE2"], vec!["FAKE3"]),
            (Milestone::M2, vec!["FAKE2"], vec!["FAKE3"]),
            (Milestone::M3, vec!["FAKE2"], vec!["FAKE3"]),
            (Milestone::M4, vec!["FAKE2", "FAKE4"], vec![]),
            (Milestone::M10, vec!["FAKE2", "FAKE4"], vec![]),
        ] {
            let report = gate(&gate_rows(), &current);
            let got: Vec<&str> = report.gaps.iter().map(|row| row.id.as_str()).collect();
            let old: Vec<&str> = report.stale.iter().map(|row| row.id.as_str()).collect();
            assert_eq!(got, gaps, "gaps at {current}");
            assert_eq!(old, stale, "stale at {current}");
        }
    }

    #[test]
    fn milestones_order_numerically_not_textually() {
        assert!(Milestone::M9 < Milestone::M10);
        assert!(Milestone::M0 < Milestone::M1);
        assert_eq!(Milestone::M10.to_string(), "M10");
    }
}
