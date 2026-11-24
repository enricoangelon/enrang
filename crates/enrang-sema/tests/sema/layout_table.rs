//! SPEC 11's worked sizes from source (owner 4F; plan g.1; S:1654-1663): each row of
//! the table, read from `docs/SPEC.md`, written as an Enrang declaration or type,
//! `sizeOf` and `alignOf` evaluated by const eval on `i386-linux` (`P == 4`) and
//! `x86_64-linux` (`P == 8`), and compared with the row's two columns. Also SPEC
//! 7.6's compile-time `assert(sizeOf<GdtPointer>() == 6);` over its example block,
//! and SPEC 11's prose offsets, the subclass and the anonymous object, through
//! `offsetOf`.

use std::fs;
use std::sync::OnceLock;

use enrang_testkit::{Harness, workspace_root};

use crate::consteval::from_source::{diag, diags, int, src_on};
use crate::support::Run;

const TARGETS: [&str; 2] = ["i386-linux", "x86_64-linux"];

const HEADER: &str = "| Type | `P == 4` | `P == 8` |";

/// `docs/SPEC.md`, read once.
fn spec() -> &'static str {
    static SPEC: OnceLock<String> = OnceLock::new();
    SPEC.get_or_init(|| {
        fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("docs/SPEC.md")
    })
}

/// The cells of a table line, split at each `|` that is not escaped, trimmed, with
/// `\|` read back as `|`.
fn cells(line: &str) -> Vec<String> {
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

/// The text between backticks in `text`, in order.
fn backticked(text: &str) -> Vec<String> {
    text.split('`')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

/// The worked sizes: each row's declaration or type with its size on `P == 4` and
/// on `P == 8`. "same with `level: i32` added" is the row above with that field
/// appended.
fn worked_rows() -> Vec<(String, u64, u64)> {
    let mut lines = spec().lines().skip_while(|line| line.trim() != HEADER);
    assert!(
        lines.next().is_some(),
        "SPEC has no table headed {HEADER:?}"
    );
    let separator = lines.next().expect("a separator line");
    assert!(separator.starts_with("|---"), "{separator:?}");
    let mut rows: Vec<(String, u64, u64)> = Vec::new();
    for line in lines.take_while(|line| line.starts_with('|')) {
        let row = cells(line);
        let text = if row[0].starts_with("same with ") {
            let field = &backticked(&row[0])[0];
            let previous = &rows.last().expect("a row above").0;
            let close = previous.rfind('}').expect("a declaration");
            format!("{}public {field}; }}", &previous[..close])
        } else {
            backticked(&row[0]).into_iter().next().expect("a type")
        };
        let size = |cell: &str| cell.parse::<u64>().expect("a size");
        rows.push((text, size(&row[1]), size(&row[2])));
    }
    rows
}

/// The program that measures `text`, a declaration or a type: the declaration
/// itself, then `SIZE` and `ALIGN` as constants.
fn measuring(text: &str) -> String {
    let (decl, ty) = match declared_name(text) {
        Some(name) => (format!("{text}\n"), name),
        None => (String::new(), text.to_owned()),
    };
    format!(
        "{decl}private const SIZE: usize = sizeOf<{ty}>();\nprivate const ALIGN: usize = alignOf<{ty}>();\n"
    )
}

/// The name a declaration declares, after `class` or `enum`; `None` for a type.
fn declared_name(text: &str) -> Option<String> {
    let words: Vec<&str> = text.split_whitespace().collect();
    let at = words.iter().position(|w| *w == "class" || *w == "enum")?;
    let name = words.get(at + 1)?;
    Some(name.trim_end_matches('{').to_owned())
}

/// The value of the `usize` constant `name`, which must have one.
fn usize_of(r: &Run, name: &str) -> u64 {
    let def = r.def(&format!("src/main::{name}"));
    let tree = r
        .tcx
        .const_value(def)
        .unwrap_or_else(|| panic!("`{name}` has no value\n{}", r.rendered()));
    let (value, ty) = int(&r.tcx, tree);
    assert_eq!(ty, "usize");
    u64::try_from(value).expect("a size")
}

/// SPEC 7.6's example block: the declarations after its heading.
fn layout_control_block() -> String {
    let section = spec()
        .split("### 7.6 Layout control")
        .nth(1)
        .expect("SPEC 7.6");
    section
        .split("```ts\n")
        .nth(1)
        .expect("its example")
        .split("```")
        .next()
        .expect("its end")
        .to_owned()
}

/// A sentence of SPEC that this file quotes, which must be there word for word.
fn spec_says(text: &str) {
    assert!(spec().contains(text), "SPEC no longer says {text:?}");
}

const STATIC_ASSERT: &str =
    "`assert(sizeOf<GdtPointer>() == 6);` at top level is evaluated at compile time.";

const SUBCLASS: &str = "A subclass never reuses its base's tail padding: with `public class A { public a: i64; public b: u8; }` and `public class D extends A { public c: u8; }` on `x86_64`, `A` has its table pointer at 0, `a` at 8 and `b` at 16, size 24, and `D` places `c` at 24, size 32; on `i386`, `A` is size 16, and `D` places `c` at 16, size 20.";

const OBJECT: &str = "`{ found: bool, index: i32, last: bool }` places `index` at 0, `found` at 4 and `last` at 5, size 8 on both `P == 4` and `P == 8`";

pub fn register(h: &mut Harness) {
    h.case(
        "layout_table/SPEC 11's worked sizes have eight rows",
        || {
            assert_eq!(worked_rows().len(), 8);
        },
    );
    for (text, p4, p8) in worked_rows() {
        for target in TARGETS {
            let text = text.clone();
            h.case(format!("layout_table/{text} on {target}"), move || {
                let r = src_on(target, &measuring(&text));
                r.clean();
                let size = usize_of(&r, "SIZE");
                let align = usize_of(&r, "ALIGN");
                let want = if target.starts_with("i386") { p4 } else { p8 };
                assert_eq!(size, want, "sizeOf<{text}>() on {target}");
                assert!(align.is_power_of_two(), "alignOf {align}");
                assert_eq!(size % align, 0, "size {size}, align {align}");
            });
        }
    }
    for target in TARGETS {
        h.case(
            format!("layout_table/SPEC 7.6's compile-time assert holds on {target}"),
            move || {
                spec_says(STATIC_ASSERT);
                let block = layout_control_block();
                let assert = &backticked(STATIC_ASSERT)[0];
                let r = src_on(target, &format!("{block}\n{assert}\n"));
                r.clean();
                // One byte off, the same assert is EN0415 at its condition.
                let wrong = assert.replace("== 6", "== 8");
                let r = src_on(target, &format!("{wrong}\n{block}"));
                assert_eq!(
                    diags(&r),
                    [diag(
                        "EN0415",
                        "1:8",
                        "compile-time assert failed",
                        "this is `false`",
                    )],
                    "{}",
                    r.rendered()
                );
                let r = src_on(
                    target,
                    &format!(
                        "{block}\nprivate const PAGE: usize = alignOf<PageTable>();\nprivate const REGS: usize = offsetOf<Regs>(\"ebx\");\n"
                    ),
                );
                r.clean();
                assert_eq!(usize_of(&r, "PAGE"), 4096);
                assert_eq!(usize_of(&r, "REGS"), 4);
            },
        );
        h.case(
            format!("layout_table/SPEC 11's subclass and object offsets on {target}"),
            move || {
                spec_says(SUBCLASS);
                spec_says(OBJECT);
                let declarations = backticked(SUBCLASS);
                let object = &backticked(OBJECT)[0];
                let text = format!(
                    "{}\n{}\nprivate const A_SIZE: usize = sizeOf<A>();
private const D_SIZE: usize = sizeOf<D>();
private const D_C: usize = offsetOf<D>(\"c\");
private const A_B: usize = offsetOf<A>(\"b\");
private const INDEX: usize = offsetOf<{object}>(\"index\");
private const FOUND: usize = offsetOf<{object}>(\"found\");
private const LAST: usize = offsetOf<{object}>(\"last\");
",
                    declarations[0], declarations[1]
                );
                let r = src_on(target, &text);
                r.clean();
                let got: Vec<u64> = ["A_SIZE", "D_SIZE", "D_C", "A_B", "INDEX", "FOUND", "LAST"]
                    .iter()
                    .map(|name| usize_of(&r, name))
                    .collect();
                if target.starts_with("x86_64") {
                    assert_eq!(got, [24, 32, 24, 16, 0, 4, 5]);
                } else {
                    assert_eq!(&got[..3], [16, 20, 16]);
                    assert_eq!(&got[4..], [0, 4, 5]);
                }
            },
        );
    }
}
