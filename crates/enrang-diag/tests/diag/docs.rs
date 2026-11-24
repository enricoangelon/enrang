//! The renderer against the other diagnostics the documents show: the shape of
//! SPEC 13.1, the test verdict of TESTING 9 and the VM refusal of DEV_RUNTIME 3.
//! These carry no case markers, so the expected text is cut out of the document.

use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_testkit::Harness;

use crate::support::{Src, doc, same};

/// The first `text` block after the line `heading`.
fn block_after(document: &str, heading: &str) -> String {
    let mut lines = document.lines();
    lines
        .find(|line| *line == heading)
        .unwrap_or_else(|| panic!("no line `{heading}`"));
    lines.find(|line| *line == "```text").expect("a text block");
    let mut block = String::new();
    for line in lines {
        if line == "```" {
            return block;
        }
        block.push_str(line);
        block.push('\n');
    }
    panic!("the block after `{heading}` never closes");
}

/// The lines of the `text` block holding `first`, from it through `last`.
fn lines_between(document: &str, first: &str, last: &str) -> String {
    let start = document
        .find(&format!("\n{first}"))
        .unwrap_or_else(|| panic!("no line starting `{first}`"))
        + 1;
    let rest = &document[start..];
    let end = rest
        .find(last)
        .unwrap_or_else(|| panic!("no `{last}` after `{first}`"))
        + last.len();
    let line_end = rest[end..].find('\n').map_or(rest.len(), |at| end + at + 1);
    rest[..line_end].to_owned()
}

/// A source block of `document`, by the line naming its file.
fn ts_block_after(document: &str, naming_line: &str) -> String {
    let mut lines = document.lines();
    lines
        .find(|line| *line == naming_line)
        .unwrap_or_else(|| panic!("no line `{naming_line}`"));
    lines.find(|line| *line == "```ts").expect("a ts block");
    let mut block = String::new();
    for line in lines {
        if line == "```" {
            return block;
        }
        block.push_str(line);
        block.push('\n');
    }
    panic!("the block after `{naming_line}` never closes");
}

pub fn register(h: &mut Harness) {
    h.case("docs/the shape block of SPEC 13.1", || {
        let source =
            "\n\n\n  const u = new User(\"Ada\");\n  archive(u);\n  console.log(u.name);\n";
        let src = Src::new("moved.en", source);
        let diag = Diagnostic::new(
            Code::EN0601,
            "`u` was moved into `archive`",
            src.on_line(6, "u"),
            "used here, after the move",
        )
        .with_secondary(
            src.on_line(4, "u"),
            "`u` owns this `User`, which is not Copy",
        )
        .with_secondary(
            src.on_line(5, "u"),
            "`u` moves here, because `archive` takes `User`, not `&User`",
        )
        .note("<free text; continuation lines indented to align after \"note: \">")
        .with_help(Help::suggest(
            "<one line>",
            vec![Edit::insert(src.on_line(5, "u").hi, ".clone()")],
        ));
        let shape = block_after(doc("SPEC.md"), "### 13.1 Rendered format");
        // The block shows one diagnostic; the final line comes after all of them.
        let expected = format!("{shape}\nerror: aborting due to 1 previous error\n");
        same(&src.one(diag), &expected);
    });
    h.case("docs/the abort line of SPEC 13.1's bullet", || {
        let bullet = doc("SPEC.md")
            .lines()
            .find(|line| line.starts_with("- After all diagnostics: "))
            .expect("the bullet exists");
        let spans: Vec<&str> = bullet.split('`').skip(1).step_by(2).collect();
        assert_eq!(spans.len(), 3, "{bullet}");
        let src = Src::new("a.en", "");
        let error = |message: &str| Diagnostic::spanless(Code::EN1301, message);
        let warning = |message: &str| Diagnostic::spanless(Code::EN0430, message);
        let last_line = |diags: &[Diagnostic]| {
            let text = src.render(diags);
            text.lines().last().expect("a final line").to_owned()
        };
        assert_eq!(
            last_line(&[error("a"), error("b")]),
            spans[0].replace('N', "2"),
        );
        assert_eq!(last_line(&[error("a")]), spans[1]);
        assert_eq!(
            last_line(&[error("a"), error("b"), warning("c"), warning("d")]),
            format!(
                "{}{}",
                spans[0].replace('N', "2"),
                spans[2].replace('M', "2")
            ),
        );
    });
    h.case("docs/the failing test of TESTING 9", || {
        let source = ts_block_after(doc("TESTING.md"), "`src/stack.test.en`:");
        let src = Src::new("src/stack.test.en", &source);
        let diag = Diagnostic::new(
            Code::T0001,
            "`toBe` found different values",
            src.on_line(11, "s.pop()"),
            "actual",
        )
        .with_secondary(
            src.on_line(11, "new User { name: \"Grace\", age: 86 }"),
            "expected",
        )
        .note(
            "difference at `.age`:\n  User {\n    name: 'Grace',\n-   age: 86,   expected\n+   age: 85,   actual\n  }",
        )
        .note("`s.pop()` has type `User | null`; the non-null payload was compared.")
        .note("ran on vm64, used 1204 of 200000000 fuel")
        .with_help(Help::suggest(
            "rerun only this test",
            vec![Edit::command(
                "enrang test src/stack.test.en -t \"Stack > pop is LIFO\"",
            )],
        ));
        let expected = lines_between(
            doc("TESTING.md"),
            "fail[T0001]:",
            "= explain: run `enrang explain T0001`",
        );
        same(&src.one(diag), &expected);
    });
    h.case("docs/the VM refusal of DEV_RUNTIME 3", || {
        let mut source = "\n".repeat(13);
        source.push_str("    unsafe { asm(`out dx, al`, { in: { dx: port, al: value } }); }\n");
        let src = Src::new("vga.en", &source);
        let diag = Diagnostic::new(
            Code::EN1201,
            "this program cannot run in the VM: inline assembly is reachable",
            src.find("asm(`out dx, al`"),
            "inline assembly cannot be interpreted",
        )
        .note("reached through main -> console.write -> vga.putc")
        .with_help(Help::text(
            "build it natively: enrang build --target=i386-none",
        ));
        let expected = lines_between(
            doc("DEV_RUNTIME.md"),
            "error[EN1201]:",
            "= explain: run `enrang explain EN1201`",
        );
        let rendered = src.one(diag);
        let (body, summary) = rendered
            .split_once("\n\n")
            .expect("a diagnostic and a final line");
        same(&format!("{body}\n"), &expected);
        same(summary, "error: aborting due to 1 previous error\n");
    });
}
