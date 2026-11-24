//! Recovery and the structural codes of SPEC 2 and 3: G01 to G04 rendered byte for
//! byte as SPEC 14 prints them; EN0100 to EN0116 and EN0214, EN0226 to EN0229,
//! each firing at its primary span with its message, and a near miss that reports
//! nothing; the missing `;` fold and the unclosed `{` pass with their fix-its
//! applied; and malformed files that report exactly their mistakes and nothing that
//! cascades from them. The TypeScript habits and deferred features are `hints.rs`;
//! a coverage case checks that the two tables between them name every syntax code
//! of phase 1.

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::{Arc, OnceLock};

use enrang_base::{FileOrigin, SourceMap};
use enrang_diag::{
    Applicability, Code, DiagCtx, Diagnostic, Owner, Phase, RenderOpts, apply_fixes, render_text,
};
use enrang_syntax::{NodeIdGen, ParseMode, parse_file};
use enrang_testkit::{Case, Harness, extract_cases, line_diff};

use crate::parser::{Parsed, shape};
use crate::support::doc;
use enrang_syntax::ast::{ItemKind, StmtKind};

/// A firing row: `(label, file name, source, reports)`, each report the code, the
/// source under its primary span and its message. The file must report exactly
/// these, in source order, so nothing cascades.
pub type Fires = (
    &'static str,
    &'static str,
    &'static str,
    &'static [(Code, &'static str, &'static str)],
);

/// A near miss: `(code, label, file name, source)`, close to what fires `code`,
/// that must report nothing at all.
pub type NearMiss = (Code, &'static str, &'static str, &'static str);

/// Checks a firing row.
pub fn check_fires(file: &str, text: &str, want: &[(Code, &str, &str)]) -> Result<(), String> {
    let parsed = Parsed::new(file, text);
    let got: Vec<(Code, String, String)> = parsed
        .diags
        .iter()
        .map(|diag| {
            (
                diag.code,
                parsed.text(diag.primary.span).to_owned(),
                diag.message.clone(),
            )
        })
        .collect();
    let want: Vec<(Code, String, String)> = want
        .iter()
        .map(|&(code, at, message)| (code, at.to_owned(), message.to_owned()))
        .collect();
    if got != want {
        return Err(format!(
            "{text}\nexpected {want:#?}\nfound {got:#?}\n{}",
            parsed.listing()
        ));
    }
    Ok(())
}

/// Checks a near miss.
pub fn check_near_miss(file: &str, text: &str) -> Result<(), String> {
    let parsed = Parsed::new(file, text);
    if parsed.diags.is_empty() {
        Ok(())
    } else {
        Err(format!("{text}\n{}", parsed.listing()))
    }
}

/// The cases of SPEC 14, read once.
fn cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| extract_cases(doc("SPEC.md")).unwrap_or_else(|errors| panic!("{errors}")))
}

/// What `enrang check` prints for one file, in process: phase 1, rendered with the
/// plain options, the `aborting` line included.
pub fn check_output(name: &str, text: &str) -> String {
    let mut map = SourceMap::new();
    let id = map.add(PathBuf::from(name), Arc::from(text), FileOrigin::User);
    let file = map.file(id).clone();
    let mut dcx = DiagCtx::new();
    parse_file(&file, &mut NodeIdGen::new(), ParseMode::Test, &mut dcx);
    let diags = dcx.take();
    render_text(&diags, &map, &RenderOpts::default())
}

/// The diagnostics of `text` and the text with every edit of each machine help
/// applied, help by help in order.
fn parse_and_fix(name: &str, text: &str, code: Code) -> (Vec<Diagnostic>, String) {
    let parsed = Parsed::new(name, text);
    let mut fixed = text.to_owned();
    for diag in parsed.diags.iter().filter(|diag| diag.code == code) {
        for help in &diag.helps {
            if help.edits.is_empty() {
                continue;
            }
            let reparsed = Parsed::new(name, &fixed);
            fixed = apply_fixes(&fixed, reparsed.file.start, &help.edits)
                .unwrap_or_else(|conflict| panic!("{conflict}"));
        }
    }
    (parsed.diags, fixed)
}

/// G01 to G04: the syntax errors of SPEC 14, which `check` prints byte for byte.
const GOLDENS: &[&str] = &["G01", "G02", "G03", "G04"];

fn register_goldens(h: &mut Harness) {
    for &id in GOLDENS {
        h.case(
            format!("recovery/golden/{id} is SPEC 14 byte for byte"),
            move || {
                let case = cases()
                    .iter()
                    .find(|case| case.id == id)
                    .unwrap_or_else(|| panic!("SPEC has no case {id}"));
                assert_eq!(case.files.len(), 1, "{id} has one file");
                assert_eq!(case.exit, 1, "{id} fails");
                let file = &case.files[0];
                let rendered = check_output(&file.name, &file.contents);
                if rendered != case.stderr.text {
                    return Err(format!(
                        "{id} differs (- SPEC, + parser):\n{}",
                        line_diff(&case.stderr.text, &rendered)
                    ));
                }
                Ok(())
            },
        );
        h.case(
            format!("recovery/golden/{id}'s fix-its leave it clean"),
            move || {
                let case = cases().iter().find(|case| case.id == id).expect("the case");
                let file = &case.files[0];
                let parsed = Parsed::new(&file.name, &file.contents);
                let mut edits = Vec::new();
                for diag in &parsed.diags {
                    for help in &diag.helps {
                        edits.extend(help.edits.iter().cloned());
                    }
                }
                let fixed = apply_fixes(&file.contents, parsed.file.start, &edits)
                    .unwrap_or_else(|conflict| panic!("{conflict}"));
                let again = Parsed::new(&file.name, &fixed);
                assert!(again.diags.is_empty(), "{fixed}\n{}", again.listing());
            },
        );
    }
}

const FIRES: &[Fires] = &[
    // EN0100: what the grammar rejects with no code of its own.
    (
        "EN0100/a ternary with no `:`",
        "s.en",
        "const x = a ? b;\n",
        &[(Code::EN0100, ";", "expected `:` to finish the choice")],
    ),
    (
        "EN0100/a `;` on the same line is expected",
        "s.en",
        "const x = 1 2;\nf();\n",
        &[(Code::EN0100, "2", "expected `;`, found `2`")],
    ),
    (
        "EN0100/a getter",
        "s.en",
        "public class A {\n  public get value(): i64 { return 1; }\n}\n",
        &[(Code::EN0100, "get value", "getters do not exist in Enrang")],
    ),
    (
        "EN0100/a stray `}` at the top level",
        "s.en",
        "f();\n}\ng();\n",
        &[(Code::EN0100, "}", "expected an expression, found `}`")],
    ),
    // EN0101: the missing `;` fold (SPEC 2, G01).
    (
        "EN0101/one missing `;`",
        "s.en",
        "const x = 1\nconsole.log(x);\n",
        &[(Code::EN0101, "", "missing `;` after this statement")],
    ),
    (
        "EN0101/a file with no `;` gets one diagnostic",
        "s.en",
        "const x = 1\nconst y = 2\nconsole.log(x + y)\n",
        &[(Code::EN0101, "", "missing `;` after this statement")],
    ),
    (
        "EN0101/before a `}`",
        "s.en",
        "public function f(): void { g() }\n",
        &[(Code::EN0101, "", "missing `;` after this statement")],
    ),
    (
        "EN0101/a field and an import",
        "s.en",
        "import { a } from \"./a\"\nprivate class A {\n  public x: i64\n}\n",
        &[(Code::EN0101, "", "missing `;` after this statement")],
    ),
    // EN0102: SPEC 2's indentation comparison (G02).
    (
        "EN0102/a mismatched `}`",
        "s.en",
        "function greet(): void {\n  if (true) {\n    console.log(\"hi\");\n}\ngreet();\n",
        &[(Code::EN0102, "{", "the file ended with `{` still open")],
    ),
    (
        "EN0102/no mismatch closes at the end",
        "s.en",
        "public function f(): void {\n  g();\n",
        &[(Code::EN0102, "{", "the file ended with `{` still open")],
    ),
    (
        "EN0102/two unclosed blocks",
        "s.en",
        "public function f(): void {\n  if (x) {\n    g();\n",
        &[
            (Code::EN0102, "{", "the file ended with `{` still open"),
            (Code::EN0102, "{", "the file ended with `{` still open"),
        ],
    ),
    (
        "EN0102/an unclosed `(` closes before the next line",
        "s.en",
        "foo(a, b\nbar();\n",
        &[(Code::EN0102, "(", "the file ended with `(` still open")],
    ),
    (
        "EN0102/an unclosed `(` before its `;`",
        "s.en",
        "foo(a;\nbar();\n",
        &[(Code::EN0102, "(", "the file ended with `(` still open")],
    ),
    (
        "EN0102/an unclosed `(` inside a block",
        "s.en",
        "public function f(): void {\n  g(a\n}\n",
        &[(Code::EN0102, "(", "the file ended with `(` still open")],
    ),
    (
        "EN0102/an unclosed `[`",
        "s.en",
        "const xs = [1, 2\nf();\n",
        &[(Code::EN0102, "[", "the file ended with `[` still open")],
    ),
    // EN0103: postfix `?` and `!` against the ternary (SPEC 2).
    (
        "EN0103/a ternary `?` with no space",
        "s.en",
        "const x = a? b : c;\n",
        &[(Code::EN0103, "?", "a ternary `?` needs a space before it")],
    ),
    (
        "EN0103/a postfix `?` with a space",
        "s.en",
        "const x = f() ?;\n",
        &[(Code::EN0103, "?", "a postfix `?` takes no space before it")],
    ),
    (
        "EN0103/a postfix `!` with a space",
        "s.en",
        "x ! = y;\n",
        &[(Code::EN0103, "!", "a postfix `!` takes no space before it")],
    ),
    // EN0104: braces after `if`, `else`, `while`, `for` (SPEC 3.3).
    (
        "EN0104/if",
        "s.en",
        "if (x) y();\n",
        &[(Code::EN0104, "y();", "`if` needs braces around its body")],
    ),
    (
        "EN0104/else",
        "s.en",
        "if (x) {\n  y();\n} else z();\n",
        &[(Code::EN0104, "z();", "`else` needs braces around its body")],
    ),
    (
        "EN0104/while",
        "s.en",
        "while (x)\n  y();\n",
        &[(Code::EN0104, "y();", "`while` needs braces around its body")],
    ),
    (
        "EN0104/for",
        "s.en",
        "for (const x of xs) f(x);\n",
        &[(Code::EN0104, "f(x);", "`for` needs braces around its body")],
    ),
    (
        "EN0104/do",
        "s.en",
        "do f(); while (x);\n",
        &[(Code::EN0104, "f();", "`do` needs braces around its body")],
    ),
    (
        "EN0104/a line indented as if inside",
        "s.en",
        "if (x)\n  y();\n  z();\nw();\n",
        &[(Code::EN0104, "y();", "`if` needs braces around its body")],
    ),
    // EN0105: an assignment as a condition or an operand (SPEC 3.4).
    (
        "EN0105/an if condition",
        "s.en",
        "if (x = 1) {}\n",
        &[(Code::EN0105, "x = 1", "assignment used as a condition")],
    ),
    (
        "EN0105/in parentheses",
        "s.en",
        "while ((x = next())) {}\n",
        &[(Code::EN0105, "x = next()", "assignment used as a condition")],
    ),
    (
        "EN0105/a do condition",
        "s.en",
        "do {} while (x += 1);\n",
        &[(Code::EN0105, "x += 1", "assignment used as a condition")],
    ),
    (
        "EN0105/a for condition",
        "s.en",
        "for (let i = 0; i = 3; i++) {}\n",
        &[(Code::EN0105, "i = 3", "assignment used as a condition")],
    ),
    (
        "EN0105/a ternary's condition",
        "s.en",
        "const y = (x = 1) ? 2 : 3;\n",
        &[(Code::EN0105, "x = 1", "assignment used as a condition")],
    ),
    (
        "EN0105/an operand of `&&`",
        "s.en",
        "const y = a && (b = c);\n",
        &[(
            Code::EN0105,
            "b = c",
            "assignment used as an operand of `&&`",
        )],
    ),
    (
        "EN0105/an operand of `!`",
        "s.en",
        "const y = !(b = c);\n",
        &[(
            Code::EN0105,
            "b = c",
            "assignment used as an operand of `!`",
        )],
    ),
    // EN0106: `??` with `||` or `&&` (SPEC 3.4).
    (
        "EN0106/`||` on the right",
        "s.en",
        "const y = a ?? b || c;\n",
        &[(
            Code::EN0106,
            "??",
            "`??` and `||` cannot mix without parentheses",
        )],
    ),
    (
        "EN0106/`&&` on the left",
        "s.en",
        "const y = a && b ?? c;\n",
        &[(
            Code::EN0106,
            "??",
            "`??` and `&&` cannot mix without parentheses",
        )],
    ),
    // EN0107: comparisons do not associate (SPEC 3.4, 3.5).
    (
        "EN0107/a < b < c",
        "s.en",
        "const y = a < b < c;\n",
        &[(Code::EN0107, "<", "comparisons cannot be chained")],
    ),
    (
        "EN0107/a == b != c",
        "s.en",
        "const y = a == b != c;\n",
        &[(Code::EN0107, "!=", "comparisons cannot be chained")],
    ),
    (
        "EN0107/a < b > (c)",
        "s.en",
        "a < b > (c);\n",
        &[(Code::EN0107, ">", "comparisons cannot be chained")],
    ),
    // EN0108: decorators before what takes none.
    (
        "EN0108/a statement",
        "s.en",
        "@d f();\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before a statement",
        )],
    ),
    (
        "EN0108/a statement in a block",
        "s.en",
        "public function f(): void {\n  @d g();\n}\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before a statement",
        )],
    ),
    (
        "EN0108/a parameter",
        "s.en",
        "public function f(@d x: i64): void {}\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before a parameter",
        )],
    ),
    (
        "EN0108/an expression",
        "s.en",
        "const x = @d f();\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before an expression",
        )],
    ),
    (
        "EN0108/an interface member",
        "s.en",
        "public interface I {\n  @d m(): void;\n}\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before an interface member",
        )],
    ),
    (
        "EN0108/an enum method",
        "s.en",
        "public enum E {\n  A;\n  @d public m(): void {}\n}\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before an enum method",
        )],
    ),
    (
        "EN0108/a test item",
        "s.test.en",
        "@d test(\"a\", () => {});\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before a test item",
        )],
    ),
    (
        "EN0108/an assert",
        "s.en",
        "@d assert(true);\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before an `assert`",
        )],
    ),
    // EN0109: declarations inside a block.
    (
        "EN0109/a class in a function",
        "s.en",
        "public function f(): void {\n  class A {}\n  g();\n}\n",
        &[(
            Code::EN0109,
            "class",
            "a declaration cannot go inside a block",
        )],
    ),
    (
        "EN0109/a public type in a block",
        "s.en",
        "if (x) {\n  public type T = i64;\n}\n",
        &[(
            Code::EN0109,
            "public",
            "a declaration cannot go inside a block",
        )],
    ),
    (
        "EN0109/an import in a block",
        "s.en",
        "if (x) {\n  import { a } from \"./a\";\n}\n",
        &[(
            Code::EN0109,
            "import",
            "a declaration cannot go inside a block",
        )],
    ),
    // EN0110: imports come first.
    (
        "EN0110/after a statement",
        "s.en",
        "f();\nimport { x } from \"./x\";\n",
        &[(
            Code::EN0110,
            "import { x } from \"./x\";",
            "`import` after a statement",
        )],
    ),
    (
        "EN0110/after a declaration",
        "s.en",
        "public class A {}\nimport { x } from \"./x\";\n",
        &[(
            Code::EN0110,
            "import { x } from \"./x\";",
            "`import` after a declaration",
        )],
    ),
    // EN0111 to EN0113: `break`, `continue` and labels (SPEC 3.3).
    (
        "EN0111/break outside a loop",
        "s.en",
        "break;\n",
        &[(Code::EN0111, "break", "`break` outside a loop")],
    ),
    (
        "EN0111/continue in a function",
        "s.en",
        "while (x) {\n  f(() => {});\n}\npublic function g(): void {\n  continue;\n}\n",
        &[(Code::EN0111, "continue", "`continue` outside a loop")],
    ),
    (
        "EN0111/break crossing an arrow",
        "s.en",
        "for (const x of xs) {\n  ys.forEach(y => {\n    break;\n  });\n}\n",
        &[(
            Code::EN0111,
            "break",
            "`break` cannot leave an arrow's body",
        )],
    ),
    (
        "EN0111/a labelled break crossing an arrow",
        "s.en",
        "outer: while (x) {\n  f(() => {\n    break outer;\n  });\n}\n",
        &[(
            Code::EN0111,
            "break",
            "`break` cannot leave an arrow's body",
        )],
    ),
    (
        "EN0111/a nested function's break cannot reach the loop around it",
        "s.en",
        "while (x) {\n  function g(): void {\n    break;\n  }\n}\n",
        &[
            (
                Code::EN1035,
                "function",
                "nested functions are not supported yet",
            ),
            (Code::EN0111, "break", "`break` outside a loop"),
        ],
    ),
    (
        "EN0111/a match arm's break outside a loop",
        "s.en",
        "match (x) { 1 => break, default => 0 }\n",
        &[(Code::EN0111, "break", "`break` outside a loop")],
    ),
    (
        "EN0112/an unknown label",
        "s.en",
        "outer: while (x) {\n  break otuer;\n}\n",
        &[(
            Code::EN0112,
            "otuer",
            "no enclosing loop is labelled `otuer`",
        )],
    ),
    (
        "EN0113/a duplicate label",
        "s.en",
        "outer: while (x) {\n  outer: for (const y of ys) {}\n}\n",
        &[(Code::EN0113, "outer", "the label `outer` is already in use")],
    ),
    // EN0114: assignment targets.
    (
        "EN0114/a call",
        "s.en",
        "f() = 1;\n",
        &[(Code::EN0114, "f()", "cannot assign to a call's result")],
    ),
    (
        "EN0114/a literal",
        "s.en",
        "1 += x;\n",
        &[(Code::EN0114, "1", "cannot assign to a literal")],
    ),
    (
        "EN0114/this",
        "s.en",
        "this = x;\n",
        &[(Code::EN0114, "this", "cannot assign to `this`")],
    ),
    (
        "EN0114/an increment of a call",
        "s.en",
        "f()++;\n",
        &[(Code::EN0114, "f()", "cannot increment a call's result")],
    ),
    (
        "EN0114/a decrement of a literal",
        "s.en",
        "--1;\n",
        &[(Code::EN0114, "1", "cannot decrement a literal")],
    ),
    (
        "EN0114/a part of a pattern",
        "s.en",
        "[a, f()] = t;\n",
        &[(Code::EN0114, "f()", "cannot assign to a call's result")],
    ),
    (
        "EN0114/a compound assignment to a pattern",
        "s.en",
        "[a, b] += t;\n",
        &[(Code::EN0114, "[a, b]", "cannot assign to this expression")],
    ),
    // EN0115: statements before declarations.
    (
        "EN0115/a statement after a class",
        "s.en",
        "public class A {}\nconsole.log(1);\n",
        &[(
            Code::EN0115,
            "console.log(1);",
            "top-level statement after a declaration",
        )],
    ),
    // EN0116: a `const` always has a value.
    (
        "EN0116/a local const",
        "s.en",
        "const x: i64;\n",
        &[(Code::EN0116, "x", "a `const` needs a value")],
    ),
    (
        "EN0116/a top-level const",
        "s.en",
        "private const X: i64;\n",
        &[(Code::EN0116, "X", "a `const` needs a value")],
    ),
    // EN0214: `readonly` where no reference is (SPEC 3.1, 3.2).
    (
        "EN0214/a return type",
        "s.en",
        "public function f(): readonly i64[] { return []; }\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` before a return type that holds no reference",
        )],
    ),
    (
        "EN0214/a field type",
        "s.en",
        "private class A {\n  private xs: readonly i64[];\n}\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` before a field type that is not a reference",
        )],
    ),
    (
        "EN0214/a whole tuple",
        "s.en",
        "private class A {\n  private t: readonly [&i64, i32];\n}\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` before a field type that is not a reference",
        )],
    ),
    (
        "EN0214/a parameter",
        "s.en",
        "public function f(x: readonly &i64): void {}\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` is not part of a type here",
        )],
    ),
    (
        "EN0214/a local",
        "s.en",
        "let x: readonly &i64 = y;\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` is not part of a type here",
        )],
    ),
    (
        "EN0214/a constructor parameter that is no field",
        "s.en",
        "private class A {\n  public constructor(readonly x: &i64) {}\n}\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` on a parameter needs a visibility",
        )],
    ),
    (
        "EN0214/a constructor parameter's type",
        "s.en",
        "private class A {\n  public constructor(x: readonly &i64) {}\n}\n",
        &[(
            Code::EN0214,
            "readonly",
            "`readonly` is not part of a type here",
        )],
    ),
    // EN0226: visibility.
    (
        "EN0226/a class",
        "s.en",
        "class A {}\n",
        &[(
            Code::EN0226,
            "class",
            "this declaration needs `public` or `private`",
        )],
    ),
    (
        "EN0226/an unsafe let",
        "s.en",
        "@globalAllocator unsafe let heap: FreeListHeap;\n",
        &[(
            Code::EN0226,
            "unsafe",
            "this declaration needs `public` or `private`",
        )],
    ),
    (
        "EN0226/a method",
        "s.en",
        "public class A {\n  m(): void {}\n}\n",
        &[(
            Code::EN0226,
            "m",
            "this member needs `public`, `private` or `protected`",
        )],
    ),
    (
        "EN0226/a function in a file with no statements",
        "s.en",
        "function helper(): void {}\n",
        &[(
            Code::EN0226,
            "function",
            "this declaration needs `public` or `private`",
        )],
    ),
    // EN0227 and EN0229: defaults (SPEC 3.1, 4.14).
    (
        "EN0227/a parameter",
        "s.en",
        "public function f(x?: i64 = 3): void {}\n",
        &[(
            Code::EN0227,
            "=",
            "a parameter with `?` cannot also have a default",
        )],
    ),
    (
        "EN0227/a field",
        "s.en",
        "public class Opts {\n  public width?: i64 | null = 3;\n}\n",
        &[(
            Code::EN0227,
            "=",
            "a field with `?` cannot also have a default",
        )],
    ),
    (
        "EN0227/a constructor parameter",
        "s.en",
        "public class A {\n  public constructor(x?: i64 = 1) {}\n}\n",
        &[(
            Code::EN0227,
            "=",
            "a parameter with `?` cannot also have a default",
        )],
    ),
    (
        "EN0229/SPEC's span",
        "s.en",
        "public function span(start?: i64, end: i64): void {}\n",
        &[(
            Code::EN0229,
            "end: i64",
            "`end` has no default, so it can't follow `start`, which has one",
        )],
    ),
    (
        "EN0229/after a default",
        "s.en",
        "public class A {\n  public constructor(a: i64 = 1, private b: i64) {}\n}\n",
        &[(
            Code::EN0229,
            "private b: i64",
            "`b` has no default, so it can't follow `a`, which has one",
        )],
    ),
    // Review of the parser stage: each mistake reports once, and what follows it
    // parses as written.
    (
        "EN0100/a keyword as a function's name stays its name",
        "s.en",
        "public function match(s: string, re: string): bool {\n  return s.indexOf(re) >= 0;\n}\npublic class B {}\n",
        &[(
            Code::EN0100,
            "match",
            "expected an identifier, found `match`",
        )],
    ),
    (
        "EN0100/`move` as a function's name after a declaration",
        "s.en",
        "public class A {}\npublic function move(x: i64): void {}\n",
        &[(Code::EN0100, "move", "expected an identifier, found `move`")],
    ),
    (
        "EN0100/a keyword as a binding's name stays its name",
        "s.en",
        "const type = 1;\nfor (const match of xs) {}\npublic function f(delete: i64): void {}\n",
        &[
            (
                Code::EN0100,
                "type",
                "expected a name or a pattern, found `type`",
            ),
            (
                Code::EN0100,
                "match",
                "expected a name or a pattern, found `match`",
            ),
            (
                Code::EN0100,
                "delete",
                "expected a name or a pattern, found `delete`",
            ),
        ],
    ),
    (
        "EN0100/a reserved word as a function's name",
        "s.en",
        "public function delete(x: i64): void {}\n",
        &[(
            Code::EN0100,
            "delete",
            "expected an identifier, found `delete`",
        )],
    ),
    (
        "EN0100/a `where` clause after a function's result is one error, not three",
        "s.en",
        "console.log(1);\nprivate interface Labeled { label(): &string; }\nprivate function largest<T>(xs: &T[]): &T where T extends Ord & Labeled { return &xs[0]; }\n",
        &[(Code::EN0100, "where", "expected `{`, found `where`")],
    ),
    (
        "EN0100/a function header with no `(` goes with its body",
        "s.en",
        "public function f x: i64): void {}\npublic class B {}\n",
        &[(Code::EN0100, "x", "expected `(`, found `x`")],
    ),
    (
        "EN0100/a member named by a keyword starts no named literal",
        "s.en",
        "const v = a.type { x: 1 };\n",
        &[(Code::EN0100, "{", "expected `;`, found `{`")],
    ),
    (
        "EN0100/`default` as a member starts no named literal",
        "s.en",
        "const v = a.default { x: 1 };\n",
        &[(Code::EN0100, "{", "expected `;`, found `{`")],
    ),
    (
        "EN0100/a skipped braced statement ends at its `;`",
        "s.en",
        "const v = E[].V { x: 1 };\n",
        &[(Code::EN0100, "{", "expected `;`, found `{`")],
    ),
    (
        "EN0100/SPEC 3.4's object literal where a statement starts",
        "s.en",
        "{ name: \"Ada\", age: 36 };\n",
        &[(
            Code::EN0100,
            ":",
            "this `{` starts a block, not an object literal",
        )],
    ),
    (
        "EN0100/an object literal as an arrow's body",
        "s.en",
        "const k = () => { x: 1 };\n",
        &[(
            Code::EN0100,
            ":",
            "this `{` starts a block, not an object literal",
        )],
    ),
    (
        "EN0100/an object literal as an arm's body",
        "s.en",
        "const v = match (x) { 1 => { a: 1 }, default => b };\n",
        &[(
            Code::EN0100,
            ":",
            "this `{` starts a block, not an object literal",
        )],
    ),
    (
        "EN0100/a label before no loop goes with its statement",
        "s.en",
        "f();\nx: a b;\ng();\n",
        &[(
            Code::EN0100,
            "a",
            "expected a loop after the label `x`, found `a`",
        )],
    ),
    (
        "EN0100/`for (x of xs)` declares no variable",
        "s.en",
        "for (x of xs) {}\n",
        &[(Code::EN0100, "of", "expected `;`, found `of`")],
    ),
    (
        "EN0100/a stray `;` leaves the imports' place open",
        "s.en",
        ";\nimport { a } from \"./a\";\n",
        &[(Code::EN0100, ";", "expected an expression, found `;`")],
    ),
    (
        "EN0100/a `;` inside an arrow's parameters",
        "s.en",
        "(a; b) => 1;\n",
        &[(Code::EN0100, ";", "expected `,` or `)`, found `;`")],
    ),
    (
        "EN0100/a bad `expect(...)` skips to its `)`",
        "s.test.en",
        "expect(a; b).toBe(c);\n",
        &[(Code::EN0100, ";", "expected `)`, found `;`")],
    ),
    (
        "EN0004/a template open at the end of the file needs no `;`",
        "s.en",
        "const s = `abc${x",
        &[(Code::EN0004, "`", "unterminated template")],
    ),
    (
        "EN0108/a decorator before an import",
        "s.en",
        "@d import { a } from \"./a\";\npublic class B {}\n",
        &[(
            Code::EN0108,
            "@d",
            "a decorator cannot go before an `import`",
        )],
    ),
    (
        "EN0103/a spaceless `?` with a long first branch",
        "s.en",
        "const v = a? b + c + d : e;\n",
        &[(Code::EN0103, "?", "a ternary `?` needs a space before it")],
    ),
    (
        "EN0107/a `{` on the next line starts no named literal",
        "s.en",
        "const v = Name<T>\n{ x: 1 };\n",
        &[(Code::EN0107, ">", "comparisons cannot be chained")],
    ),
    (
        "EN0229/names the nearest default before it",
        "s.en",
        "public function f(a: i64 = 1, b: i64 = 2, c: i64): void {}\n",
        &[(
            Code::EN0229,
            "c: i64",
            "`c` has no default, so it can't follow `b`, which has one",
        )],
    ),
];

const NEAR_MISSES: &[NearMiss] = &[
    (
        Code::EN0100,
        "a ternary with its `:`",
        "s.en",
        "const x = a ? b : c;\n",
    ),
    (
        Code::EN0101,
        "every `;` written",
        "s.en",
        "const x = 1;\nconsole.log(x);\n",
    ),
    (
        Code::EN0101,
        "statements that end in a block",
        "s.en",
        "if (x) {\n  f();\n}\nwhile (y) {}\nmatch (z) { default => 1 }\n",
    ),
    (
        Code::EN0102,
        "every `{` closed",
        "s.en",
        "function greet(): void {\n  if (true) {\n    console.log(\"hi\");\n  }\n}\ngreet();\n",
    ),
    (
        Code::EN0102,
        "a call over several lines",
        "s.en",
        "foo(\n  a,\n  b,\n);\nbar(() => {\n  x;\n});\n",
    ),
    (
        Code::EN0103,
        "both spellings right",
        "s.en",
        "const x = a ? b : c;\nconst y = f()?;\nconst z = w!;\nconst t = flag ? [1] : [];\n",
    ),
    (
        Code::EN0103,
        "a postfix `?` before a binary operator, in a ternary",
        "s.en",
        "const y = c ? f()? - 1 : 2;\n",
    ),
    (
        Code::EN0103,
        "a ternary broken before `?`",
        "s.en",
        "const x = cond\n  ? a\n  : b;\n",
    ),
    (
        Code::EN0104,
        "braced bodies and `else if`",
        "s.en",
        "if (x) { y(); } else if (z) { w(); } else { v(); }\nwhile (a) { b(); }\n",
    ),
    (
        Code::EN0105,
        "an assignment compared",
        "s.en",
        "while ((line = readLine()) != null) {}\n",
    ),
    (
        Code::EN0106,
        "`??` with parentheses",
        "s.en",
        "const y = a ?? (b || c);\nconst z = (a && b) ?? c;\nconst w = a ?? b ?? c;\n",
    ),
    (
        Code::EN0107,
        "comparisons joined by `&&`",
        "s.en",
        "const y = a < b && b < c;\nconst z = (a == b) == c;\n",
    ),
    (
        Code::EN0108,
        "decorators on declarations",
        "s.en",
        "@entry public function main(): void {}\n@packed private final class P {}\n",
    ),
    (
        Code::EN0109,
        "declarations at the top level, a block's statements inside",
        "s.en",
        "public class A {}\npublic function f(): void {\n  const t = 1;\n  let u: i64;\n}\n",
    ),
    (
        Code::EN0110,
        "imports first",
        "s.en",
        "import { x } from \"./x\";\npublic import { y } from \"./y\";\nf();\n",
    ),
    (
        Code::EN0111,
        "break and continue inside loops",
        "s.en",
        "while (x) {\n  if (y) { break; }\n  continue;\n}\nfor (const a of b) {\n  match (a) { 1 => break, default => continue }\n}\n",
    ),
    (
        Code::EN0111,
        "a loop inside an arrow",
        "s.en",
        "xs.forEach(x => {\n  while (x) { break; }\n});\n",
    ),
    (
        Code::EN0112,
        "a known label",
        "s.en",
        "outer: while (x) {\n  for (const y of ys) {\n    break outer;\n  }\n}\n",
    ),
    (
        Code::EN0113,
        "two labels in turn",
        "s.en",
        "a: while (x) {}\na: while (y) {}\n",
    ),
    (
        Code::EN0114,
        "places",
        "s.en",
        "x = 1;\nthis.n += 1;\nxs[0] = 2;\n*p = 3;\nq! = 4;\n(r) = 5;\n[a, b] = [b, a];\n({ x, y: z } = o);\ni++;\n--j;\n",
    ),
    (
        Code::EN0115,
        "statements before declarations",
        "s.en",
        "console.log(1);\nfunction helper(): void {}\npublic class A {}\nassert(true);\n",
    ),
    (
        Code::EN0116,
        "a const with a value, a let without one",
        "s.en",
        "const x: i64 = 1;\nlet y: i64;\nprivate const Z: i64 = 2;\n",
    ),
    (
        Code::EN0214,
        "readonly where it belongs",
        "s.en",
        "public interface Maker {\n  make(): readonly Two;\n}\nprivate class L {\n  private readonly src: readonly &Slice<u8>;\n  private t: [readonly &i64[], i32];\n  public constructor(private readonly s: readonly &Slice<u8>) {}\n  public first(): readonly &u8 { return &this.s[0]; }\n}\n",
    ),
    (
        Code::EN0226,
        "every visibility stated",
        "s.en",
        "public class A {\n  private x: i64;\n  public m(): void {}\n}\nprivate enum E { A }\n@globalAllocator private unsafe let heap: FreeListHeap;\n",
    ),
    (
        Code::EN0226,
        "a program's local function",
        "s.en",
        "function helper(): void {}\nhelper();\n",
    ),
    (
        Code::EN0227,
        "`?` or a default",
        "s.en",
        "public function f(x?: i64, y: i64 = 3): void {}\n",
    ),
    (
        Code::EN0229,
        "defaults last",
        "s.en",
        "public function greet(name: &string, greeting: &string = \"hello\", end: &string = \"!\"): void {}\n",
    ),
    // Review of the parser stage.
    (
        Code::EN0109,
        "`extend` with type arguments is a call",
        "s.en",
        "public function f(a: i64, b: i64): void { extend<i64>(a, b); }\n",
    ),
    (
        Code::EN0109,
        "`extend * y` is an expression",
        "s.en",
        "public function f(): void { const y = 1; extend * y; }\n",
    ),
    (
        Code::EN0115,
        "`extend<i64>(a, b);` at the top level is a statement",
        "s.en",
        "extend<i64>(a, b);\nextend(a, b);\nextend = 1;\n",
    ),
    (
        Code::EN0113,
        "a label used again beyond an arrow",
        "s.en",
        "a: while (x) { const f = () => { a: while (y) {} }; }\n",
    ),
    (
        Code::EN0100,
        "a labelled loop first in a block",
        "s.en",
        "public function f(): void {\n  { inner: for (;;) {} }\n}\n",
    ),
    (
        Code::EN0214,
        "a returned tuple with a nullable reference",
        "s.en",
        "public function f(x: &i64): readonly [&i64 | null, i32] { return [x, 1]; }\n",
    ),
];

/// The phase 1 syntax codes the parser reports: every one but the lexer's.
fn parser_codes() -> Vec<Code> {
    Code::ALL
        .iter()
        .copied()
        .filter(|code| code.owner() == Owner::Syntax && code.phase() == Phase::Syntax)
        .filter(|code| !code.name().starts_with("EN000"))
        .collect()
}

fn register_rows(h: &mut Harness) {
    for &(label, file, text, want) in FIRES {
        h.case(format!("recovery/fires/{label}"), move || {
            check_fires(file, text, want)
        });
    }
    for &(code, label, file, text) in NEAR_MISSES {
        h.case(format!("recovery/near miss/{code}/{label}"), move || {
            check_near_miss(file, text)
        });
    }
    h.case(
        "recovery/every parser code has a firing row and a near miss",
        || {
            let fired: BTreeSet<Code> = FIRES
                .iter()
                .chain(crate::hints::FIRES)
                .flat_map(|(_, _, _, want)| want.iter().map(|&(code, ..)| code))
                .collect();
            let near: BTreeSet<Code> = NEAR_MISSES
                .iter()
                .chain(crate::hints::NEAR_MISSES)
                .map(|&(code, ..)| code)
                .collect();
            let mut missing = Vec::new();
            for code in parser_codes() {
                if !fired.contains(&code) {
                    missing.push(format!("{code} fires nowhere"));
                }
                if !near.contains(&code) {
                    missing.push(format!("{code} has no near miss"));
                }
            }
            assert_eq!(missing, Vec::<String>::new());
        },
    );
}

/// Fix-its applied: the fixed file no longer reports the code.
fn register_fixes(h: &mut Harness) {
    let rows: &[(&str, &str, Code)] = &[
        (
            "no `;` at all",
            "const x = 1\nconst y = 2\nf(x)\ng(y)\n",
            Code::EN0101,
        ),
        (
            "a field with no `;`",
            "private class A {\n  public x: i64\n}\n",
            Code::EN0101,
        ),
        (
            "G02's shape",
            "function greet(): void {\n  if (true) {\n    console.log(\"hi\");\n}\ngreet();\n",
            Code::EN0102,
        ),
        (
            "an unclosed block at the end",
            "public function f(): void {\n  g();",
            Code::EN0102,
        ),
        ("a ternary `?`", "const x = a? b : c;\n", Code::EN0103),
        ("a postfix `?`", "const x = f() ?;\n", Code::EN0103),
        ("a same-line body", "if (x) y();\n", Code::EN0104),
        (
            "a body on the next line",
            "while (x)\n  y();\nz();\n",
            Code::EN0104,
        ),
        (
            "indented lines",
            "public function f(): void {\n  if (x)\n    a();\n    b();\n  c();\n}\n",
            Code::EN0104,
        ),
        ("an assignment condition", "if (x = 1) {}\n", Code::EN0105),
        ("`??` and `||`", "const y = a ?? b || c;\n", Code::EN0106),
        (
            "a chained comparison",
            "const y = a < b < c;\n",
            Code::EN0107,
        ),
        ("a missing visibility", "class A {}\n", Code::EN0226),
        (
            "a member's visibility",
            "public class A {\n  x: i64;\n}\n",
            Code::EN0226,
        ),
        (
            "`?` and a default",
            "public function f(x?: i64 = 3): void {}\n",
            Code::EN0227,
        ),
        (
            "a readonly return",
            "public function f(): readonly i64[] { return []; }\n",
            Code::EN0214,
        ),
    ];
    for &(label, text, code) in rows {
        h.case(format!("recovery/fix-it/{code}/{label}"), move || {
            let (diags, fixed) = parse_and_fix("fix.en", text, code);
            assert!(diags.iter().any(|diag| diag.code == code), "{code} fires");
            let again = Parsed::new("fix.en", &fixed);
            assert!(
                again.diags.iter().all(|diag| diag.code != code),
                "{fixed}\n{}",
                again.listing()
            );
        });
    }
    h.case("recovery/fix-it/EN0101 folds every site", || {
        let text = "const a = 1\nconst b = 2\nconst c = 3\nf(a, b, c)\n";
        let parsed = Parsed::new("fold.en", text);
        assert_eq!(parsed.diags.len(), 1, "{}", parsed.listing());
        let diag = &parsed.diags[0];
        assert_eq!(diag.code, Code::EN0101);
        assert_eq!(diag.helps.len(), 1);
        assert_eq!(diag.helps[0].edits.len(), 4);
        assert_eq!(
            diag.helps[0].applicability,
            Applicability::MachineApplicable
        );
        let notes: Vec<&str> = diag.entries.iter().map(|e| e.text.as_str()).collect();
        assert_eq!(
            notes,
            [
                "3 more statements in this file are missing `;`",
                "Enrang has no automatic semicolon insertion."
            ]
        );
        let fixed = apply_fixes(text, parsed.file.start, &diag.helps[0].edits).expect("fixes");
        assert_eq!(
            fixed,
            "const a = 1;\nconst b = 2;\nconst c = 3;\nf(a, b, c);\n"
        );
    });
    h.case("recovery/fix-it/EN0226 makes a member public", || {
        let text = "public class A {\n  x: i64;\n}\n";
        let (_, fixed) = parse_and_fix("vis.en", text, Code::EN0226);
        assert_eq!(fixed, "public class A {\n  public x: i64;\n}\n");
        let (_, fixed) = parse_and_fix("vis.en", "class A {}\n", Code::EN0226);
        assert_eq!(fixed, "private class A {}\n");
    });
    h.case(
        "recovery/EN0102/a `(` around an unclosed block closes after it",
        || {
            let parsed = Parsed::new("p.en", "f(() => {\n  x;\n");
            let got: Vec<(Code, &str)> = parsed
                .diags
                .iter()
                .map(|diag| (diag.code, parsed.text(diag.primary.span)))
                .collect();
            assert_eq!(got, [(Code::EN0102, "("), (Code::EN0102, "{")]);
            // The `}` comes first, so the `(` has no place to close before it.
            assert!(parsed.diags[0].helps[0].edits.is_empty());
            let StmtKind::Expr(call) = &parsed.tree.stmts[0].kind else {
                panic!("a call statement");
            };
            assert_eq!(shape(call), "(call f (=> () {1 stmts}))");
        },
    );
    h.case("recovery/fix-it/EN0101 counts one more as one", || {
        let parsed = Parsed::new("fold.en", "const a = 1\nf(a)\n");
        let notes: Vec<&str> = parsed.diags[0]
            .entries
            .iter()
            .map(|e| e.text.as_str())
            .collect();
        assert_eq!(notes[0], "1 more statement in this file is missing `;`");
    });
    h.case("recovery/fix-it/EN0104 wraps the indented lines", || {
        let text = "public function f(): void {\n  if (x)\n    a();\n    b();\n  c();\n}\n";
        let (diags, fixed) = parse_and_fix("wrap.en", text, Code::EN0104);
        assert_eq!(diags[0].secondary.len(), 1);
        assert_eq!(
            diags[0].secondary[0].text,
            "indented as if it were inside the `if`"
        );
        assert_eq!(
            fixed,
            "public function f(): void {\n  if (x) {\n    a();\n    b();\n  }\n  c();\n}\n"
        );
    });
    h.case(
        "recovery/fix-it/EN0104 closes after a trailing comment",
        || {
            let text = "while (x)\n  y(); // go\nz();\n";
            let (_, fixed) = parse_and_fix("wrap.en", text, Code::EN0104);
            assert_eq!(fixed, "while (x) {\n  y(); // go\n}\nz();\n");
        },
    );
    h.case(
        "recovery/fix-it/EN0102 closes at the end of the file",
        || {
            let (_, fixed) = parse_and_fix(
                "end.en",
                "public function f(): void {\n  g();",
                Code::EN0102,
            );
            assert_eq!(fixed, "public function f(): void {\n  g();\n}\n");
        },
    );
}

/// Recovery: what follows a mistake parses as it would without it, so each file
/// reports its mistakes and nothing that cascades from them.
fn register_recovery(h: &mut Harness) {
    let rows: &[(&str, &str, &[Code])] = &[
        (
            "a bad statement skips to its `;`",
            "const x = 1 2 3;\nconst y = ;\nf(x);\n",
            &[Code::EN0100, Code::EN0100],
        ),
        (
            "a bad statement in a block skips to its `}`",
            "public function f(): void {\n  g(1 2\n}\npublic function h(): void {}\n",
            &[Code::EN0102, Code::EN0100],
        ),
        (
            "a bad item skips to the next item",
            "public class A { public x: i64; }\nprivate garbage here;\npublic class B {}\n",
            &[Code::EN0100],
        ),
        (
            "a TS file with no `;` and a habit",
            "var x = 1\nif (x === 1) {\n  console.log(x)\n}\n",
            &[Code::EN0202, Code::EN0101, Code::EN0201],
        ),
        (
            "an unclosed block keeps what follows",
            "function a(): void {\n  if (x) {\n    f();\n}\nfunction b(): void {\n  g();\n}\na();\n",
            &[Code::EN0102],
        ),
        (
            "an unclosed call keeps the next statement",
            "foo(a, b\nbar();\nbaz();\n",
            &[Code::EN0102],
        ),
        (
            "habits in a row",
            "var a: any = undefined;\nvar b: number = a === 1 ? 2 : 3;\n",
            &[
                Code::EN0202,
                Code::EN0205,
                Code::EN0206,
                Code::EN0202,
                Code::EN0225,
                Code::EN0201,
            ],
        ),
        (
            "a try with its handlers",
            "try {\n  f();\n} catch (e) {\n  g();\n} finally {\n  h();\n}\nk();\n",
            &[Code::EN0207],
        ),
        (
            "a switch is skipped whole",
            "switch (x) {\n  case 1: f(); break;\n  default: g();\n}\nh();\n",
            &[Code::EN0209],
        ),
        (
            "a name on the next line is no label",
            "while (x) {\n  if (y) { continue }\n  continue\n  console.log(i)\n}\n",
            &[Code::EN0101],
        ),
        (
            "a postfix `++` stays on its operand's line",
            "let x = 1\nx++\n++x\n",
            &[Code::EN0101],
        ),
        (
            "a labelled block's own break",
            "public function f(): void {\n  done: {\n    break done;\n  }\n}\n",
            &[Code::EN1038],
        ),
        (
            "a bad statement ends at the next line's statement",
            "var x = 1 2\nconst y = 3\nf(x, y);\n",
            &[Code::EN0202, Code::EN0100, Code::EN0101],
        ),
        (
            "an unsupported import ends at its line",
            "import type { A } from \"./a\"\nimport { b } from \"./b\";\nf();\n",
            &[Code::EN1009],
        ),
        (
            "brackets left open at one place get one diagnostic",
            "f(a, [1, 2\nbar();\n",
            &[Code::EN0102],
        ),
        (
            "a `(` left open in a block closes before its `}`",
            "public function f(): void {\n  if (x) {\n    foo(a\n}\n",
            &[Code::EN0102, Code::EN0102],
        ),
        (
            "a getter is a method",
            "public class A {\n  public get value(): i64 { return 1; }\n  public m(): void {}\n}\n",
            &[Code::EN0100],
        ),
        (
            "a bad statement goes on at a line that starts with `as`",
            "const x = 1 2\n  as i64;\nf();\n",
            &[Code::EN0100],
        ),
        (
            "a stray `;` before an import",
            ";\nimport { a } from \"./a\";\nf();\n",
            &[Code::EN0100],
        ),
        (
            "a TypeScript cast is no chained comparison",
            "const n = <i64>value;\nf(n);\n",
            &[Code::EN0100],
        ),
        (
            "a `for await` loop goes on as a `for`",
            "for await (const x of xs) {\n  f(x);\n}\ng();\n",
            &[Code::EN1001],
        ),
        (
            "a `for` with no `(` is skipped whole",
            "for const x of xs {\n  f(x);\n}\ng();\n",
            &[Code::EN0100],
        ),
        (
            "a `const` with no name needs no value too",
            "const enum E { A }\nf();\n",
            &[Code::EN0100],
        ),
        (
            "a type parameter's default skips to its `>`",
            "public function f<T = string>(x: T): void {}\npublic function g<T = Map<K, V>, U>(x: T): U {}\n",
            &[Code::EN0100, Code::EN0100],
        ),
        (
            "a type parameter list cut short keeps its `(`",
            "public function f<T(x: T): void {}\npublic function g(): void {}\n",
            &[Code::EN0100],
        ),
        (
            "a logical assignment is no assignment to an operator",
            "x ||= y;\nz ??= w;\n",
            &[Code::EN0100, Code::EN0100],
        ),
        (
            "a declared module is one bad item",
            "public declare module \"x\" {}\npublic function f(): void {}\n",
            &[Code::EN0100],
        ),
    ];
    for &(label, text, want) in rows {
        h.case(format!("recovery/no cascade/{label}"), move || {
            let parsed = Parsed::new("r.en", text);
            let got: Vec<Code> = parsed.diags.iter().map(|diag| diag.code).collect();
            assert_eq!(got, want, "{text}\n{}", parsed.listing());
        });
    }
}

/// What the review of the parser stage pinned beyond the rows: labels, the words
/// of EN0102, a kept import, and fix-its applied.
fn register_review(h: &mut Harness) {
    h.case(
        "recovery/review/a `where` clause on a function moves its bounds onto the parameters (SPEC 3.1)",
        || {
            let text = "private function f<T, U>(a: &T, b: &U): void where T extends Ord, U extends Labeled & Clone {\n  g();\n}\n";
            let parsed = Parsed::new("w.en", text);
            assert_eq!(parsed.reports(), [(Code::EN0100, "where".to_owned())]);
            let helps: Vec<&str> = parsed.diags[0]
                .helps
                .iter()
                .map(|help| help.message.as_str())
                .collect();
            assert_eq!(
                helps,
                ["move the bounds onto the type parameters: `<T extends Ord, U extends Labeled & Clone>`"]
            );
            // The body after the clause is the function's.
            let ItemKind::Function(f) = &parsed.tree.items[0].kind else {
                panic!("a function");
            };
            assert_eq!(f.body.stmts.len(), 1);
            // A method keeps its `where` clause, with nothing reported.
            let method = Parsed::new(
                "m.en",
                "public class B<T> {\n  public m(): void where T extends Ord {}\n}\n",
            );
            assert!(method.diags.is_empty(), "{}", method.listing());
        },
    );
    h.case("recovery/review/a name alone on the line after `break` is its label", || {
        let parsed = Parsed::new(
            "r.en",
            "outer: while (x) {\n  break\n  outer\n  f();\n}\n",
        );
        assert_eq!(parsed.reports(), [(Code::EN0101, String::new())]);
        let StmtKind::Labeled(_, body) = &parsed.tree.stmts[0].kind else {
            panic!("a labelled loop");
        };
        let StmtKind::While(loop_) = &body.kind else {
            panic!("a while loop");
        };
        assert!(
            matches!(loop_.body.stmts[0].kind, StmtKind::Break(Some(label)) if label.name.as_str() == "outer"),
            "{:?}",
            loop_.body.stmts[0].kind
        );
        assert_eq!(loop_.body.stmts.len(), 2);
    });
    h.case(
        "recovery/review/EN0112 offers no label beyond an arrow",
        || {
            let parsed = Parsed::new(
                "r.en",
                "outer: while (x) { const f = () => { inner: while (y) { break outr; } }; }\n",
            );
            assert_eq!(parsed.reports(), [(Code::EN0112, "outr".to_owned())]);
            assert!(
                parsed.diags[0].helps.is_empty(),
                "{:?}",
                parsed.diags[0].helps
            );
        },
    );
    h.case(
        "recovery/review/EN0102's `}` lines up with the innermost `{` of its width",
        || {
            let parsed = Parsed::new("r.en", "if (a) {\nif (b) {\n  if (c) {\n    x();\n}\n");
            let diag = parsed
                .diags
                .iter()
                .find(|diag| !diag.secondary.is_empty())
                .unwrap_or_else(|| panic!("{}", parsed.listing()));
            assert_eq!(
                diag.secondary[0].text,
                "this `}` lines up with `if` on line 2, so it probably closes that instead"
            );
            assert_eq!(diag.helps[0].message, "close the `if` block before line 5");
        },
    );
    let words: &[(&str, &str)] = &[
        (
            "public function f(): void {\n  g();\n",
            "close the `function` block at the end of the file",
        ),
        (
            "public class A {\n  public static m(): void {\n",
            "close the `m` block at the end of the file",
        ),
        (
            "if (a) {\n  x();\n} else if (b) {\n  y();\n",
            "close the `if` block at the end of the file",
        ),
        (
            "unsafe {\n  f();\n",
            "close the `unsafe` block at the end of the file",
        ),
    ];
    for &(text, help) in words {
        h.case(format!("recovery/review/EN0102 says {help:?}"), move || {
            let parsed = Parsed::new("r.en", text);
            let helps: Vec<&str> = parsed
                .diags
                .iter()
                .filter(|diag| diag.code == Code::EN0102)
                .map(|diag| diag.helps[0].message.as_str())
                .collect();
            assert!(helps.contains(&help), "{helps:?}");
        });
    }
    h.case(
        "recovery/review/a keyword names its function all the same",
        || {
            let parsed = Parsed::new(
                "r.en",
                "public function match(s: string, re: string): bool {\n  return true;\n}\n",
            );
            assert_eq!(parsed.diags.len(), 1, "{}", parsed.listing());
            let [item] = parsed.tree.items.as_slice() else {
                panic!("one item: {:#?}", parsed.tree);
            };
            let ItemKind::Function(decl) = &item.kind else {
                panic!("a function");
            };
            assert_eq!(decl.name.name.as_str(), "match");
            assert_eq!(decl.params.len(), 2);
            assert_eq!(decl.body.stmts.len(), 1);
        },
    );
    h.case("recovery/review/a decorated import is kept", || {
        let parsed = Parsed::new("r.en", "@d import { a } from \"./a\";\npublic class B {}\n");
        assert_eq!(parsed.tree.imports.len(), 1);
        assert_eq!(parsed.tree.items.len(), 1);
    });
    h.case(
        "recovery/review/`extend` with type arguments is a call",
        || {
            let parsed = Parsed::new("r.en", "extend<i64>(a, b);\n");
            assert_eq!(shape(parsed.expr()), "(call extend <i64> a b)");
        },
    );
    h.case(
        "recovery/review/`for (x of xs)` is told to declare `x`",
        || {
            let text = "for (x of xs) {}\n";
            let parsed = Parsed::new("r.en", text);
            let fixed = apply_fixes(text, parsed.file.start, &parsed.diags[0].helps[0].edits)
                .expect("the fix-it applies");
            assert_eq!(fixed, "for (const x of xs) {}\n");
            assert!(Parsed::new("r.en", &fixed).diags.is_empty());
        },
    );
}

/// SPEC 13.1: a message starts lower-case unless with a code span, and has no
/// final period; every primary label says something.
fn register_style(h: &mut Harness) {
    h.case("recovery/every message is in SPEC 13.1's style", || {
        let mut bad = Vec::new();
        for &(label, file, text, _) in FIRES.iter().chain(crate::hints::FIRES) {
            for diag in Parsed::new(file, text).diags {
                let first = diag.message.chars().next().unwrap_or(' ');
                if !(first.is_lowercase() || first == '`') || diag.message.ends_with('.') {
                    bad.push(format!("{label}: {:?}", diag.message));
                }
                if diag.primary.text.is_empty() {
                    bad.push(format!("{label}: {} has no label", diag.code));
                }
            }
        }
        assert_eq!(bad, Vec::<String>::new());
    });
}

pub fn register(h: &mut Harness) {
    register_style(h);
    register_goldens(h);
    register_rows(h);
    register_fixes(h);
    register_recovery(h);
    register_review(h);
}
