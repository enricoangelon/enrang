//! SPEC 14 is the acceptance test of the renderer.
//!
//! The source and the expected stderr of each case come out of `docs/SPEC.md`
//! through the testkit extractor and nothing here repeats the expected text. No
//! compiler exists yet, so each diagnostic is built by hand, with its spans found
//! in the extracted source, and has to render to the document's bytes.

use std::sync::OnceLock;

use enrang_diag::{Code, Diagnostic, Edit, Help, Milestone, Severity, apply_fixes};
use enrang_testkit::{Case, Harness, extract_cases, headings_without_cases};

use crate::support::{Src, doc, same, strip_ansi};

fn cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        extract_cases(doc("SPEC.md"))
            .unwrap_or_else(|errors| panic!("docs/SPEC.md does not extract:\n{errors}"))
    })
}

fn case(id: &str) -> &'static Case {
    cases()
        .iter()
        .find(|case| case.id == id)
        .unwrap_or_else(|| panic!("docs/SPEC.md has no case {id}"))
}

/// The case's source, in the source map the way the driver would load it.
fn source(id: &str) -> Src {
    let case = case(id);
    assert_eq!(case.files.len(), 1, "{id} has one source file");
    let file = &case.files[0];
    Src::new(&file.name, &file.contents)
}

pub type Builder = fn(&Src) -> Vec<Diagnostic>;

/// Every builder. `register` fails the suite if this and the document disagree.
pub const BUILDERS: [(&str, Builder); 24] = [
    ("G01", g01),
    ("G02", g02),
    ("G03", g03),
    ("G04", g04),
    ("G05", g05),
    ("G06", g06),
    ("G07", g07),
    ("G08", g08),
    ("G09", g09),
    ("G10", g10),
    ("G11", g11),
    ("G12", g12),
    ("G13", g13),
    ("G14", g14),
    ("G15", g15),
    ("G16", g16),
    ("G17", g17),
    ("G18", g18),
    ("G19", g19),
    ("G20", g20),
    ("G21", g21),
    ("G22", g22),
    ("G23", g23),
    ("G24", g24),
];

/// The samples of SPEC 15 whose stderr is a diagnostic. The renderer owes them the
/// same bytes, and a meta-test below finds any it has no builder for. None has one
/// now: S11's loop warning went with EN0719.
pub const SAMPLE_BUILDERS: [(&str, Builder); 0] = [];

/// Every case with a diagnostic to render.
fn all_builders() -> impl Iterator<Item = (&'static str, Builder)> {
    BUILDERS.into_iter().chain(SAMPLE_BUILDERS)
}

fn g01(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0101,
            "missing `;` after this statement",
            s.eol(1),
            "expected `;` here",
        )
        .from_typescript("Enrang has no automatic semicolon insertion.")
        .with_help(Help::machine(
            "add the semicolon",
            vec![Edit::insert(s.line_end(1), ";")],
        )),
    ]
}

fn g02(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0102,
            "the file ended with `{` still open",
            s.on_line(2, "{"),
            "this block has no matching `}`",
        )
        .with_secondary(
            s.on_line(4, "}"),
            "this `}` lines up with `function` on line 1, so it probably closes that instead",
        )
        .with_help(Help::machine(
            "close the `if` block before line 4",
            vec![Edit::insert(s.line_start(4), "  }\n")],
        )),
    ]
}

fn g03(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0201,
            "`===` does not exist in Enrang",
            s.find("==="),
            "use `==` here",
        )
        .from_typescript("`==` never coerces in Enrang, so the strict form is the only form.")
        .with_help(Help::machine(
            "replace `===` with `==`",
            vec![Edit::replace(s.find("==="), "==")],
        )),
    ]
}

fn g04(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0205,
            "`any` does not exist in Enrang",
            s.find("any"),
            "every value has one known type",
        )
        .with_help(Help::suggest(
            "accept every value type with a generic",
            vec![
                Edit::insert(s.find("show").hi, "<T>"),
                Edit::replace(s.find("any"), "&T"),
            ],
        )),
        Diagnostic::new(
            Code::EN0202,
            "`var` does not exist in Enrang",
            s.find("var"),
            "use `let` for a binding that changes, `const` otherwise",
        )
        .with_help(Help::machine(
            "replace `var` with `let`",
            vec![Edit::replace(s.find("var"), "let")],
        )),
        Diagnostic::new(
            Code::EN0206,
            "`undefined` does not exist in Enrang",
            s.find("undefined"),
            "absence has one spelling",
        )
        .with_help(Help::suggest(
            "replace `undefined` with `null`, which needs a nullable type",
            vec![
                Edit::insert(s.on_line(2, "y").hi, ": i64 | null"),
                Edit::replace(s.find("undefined"), "null"),
            ],
        )),
    ]
}

fn g05(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0401,
            "mismatched types: expected `string`, found `i64`",
            s.find("area(2, 3)"),
            "this is `i64`",
        )
        .with_secondary(s.find("string"), "`string` is required by this annotation")
        .note("Enrang never converts between numbers and strings implicitly.")
        .with_help(Help::suggest(
            "convert it explicitly",
            vec![Edit::insert(s.find("area(2, 3)").hi, ".toString()")],
        )),
    ]
}

fn g06(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0301,
            "cannot find `totl` in this scope",
            s.find("totl"),
            "not found",
        )
        .with_secondary(
            s.find("total"),
            "a local with a similar name is declared here",
        )
        .with_help(Help::machine(
            "did you mean `total`?",
            vec![Edit::replace(s.find("totl"), "total")],
        )),
    ]
}

fn g07(s: &Src) -> Vec<Diagnostic> {
    let moved = s.on_line(4, "u");
    vec![
        Diagnostic::new(
            Code::EN0601,
            "`u` was moved into `archive`",
            s.on_line(5, "u"),
            "used here, after the move",
        )
        .with_secondary(
            s.on_line(3, "u"),
            "`u` owns this `User`, which is not Copy because it has a `string` field",
        )
        .with_secondary(
            moved,
            "`u` moves here, because `archive` takes `User`, not `&User`",
        )
        .from_typescript(
            "both names would share one object. In Enrang a value has one owner, so passing `u` hands it over.",
        )
        .with_help(Help::suggest(
            "if `archive` only needs to look at it, change the parameter to `u: &User`",
            vec![
                Edit::insert(s.on_line(1, "User").lo, "&"),
                Edit::insert(moved.lo, "&"),
            ],
        ))
        .with_help(Help::suggest(
            "to keep your own, pass a copy: `archive(u.clone())`",
            vec![Edit::insert(moved.hi, ".clone()")],
        )),
    ]
}

fn g08(s: &Src) -> Vec<Diagnostic> {
    let source = s.on_line(2, "&queue");
    vec![
        Diagnostic::new(
            Code::EN0706,
            "cannot mutate `queue` while iterating over it",
            s.find("queue.push(\"retry\")"),
            "conflicting mutable access",
        )
        .with_secondary(source, "immutable borrow begins here")
        .note("structural mutations may invalidate the iterator")
        .with_help(Help::suggest(
            "collect new jobs separately, or loop over a copy",
            vec![
                Edit::replace(s.on_line(2, "&"), "[..."),
                Edit::insert(source.hi, "]"),
            ],
        )),
    ]
}

fn g09(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0707,
            "cannot borrow `xs` as exclusive twice at the same time",
            s.nth_on_line(8, "&xs", 1),
            "second exclusive borrow",
        )
        .with_secondary(
            s.nth_on_line(8, "&xs", 0),
            "first exclusive borrow, still live until the call returns",
        )
        .rule("a value has many shared borrows or one exclusive borrow, never both.")
        .with_help(Help::text(
            "to exchange two elements of one array, use `xs.swap(i, j)`",
        )),
    ]
}

fn g10(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0710,
            "cannot return a reference to local `s`",
            s.on_line(3, "&s"),
            "this reference would point at freed memory",
        )
        .with_secondary(
            s.nth_on_line(2, "s", 1),
            "`s` is dropped when `longest` returns",
        )
        .rule("a returned reference must borrow from a parameter, and `longest` has no reference parameters.")
        .with_help(Help::suggest(
            "return the owned value instead",
            vec![
                Edit::replace(s.find("&string"), "string"),
                Edit::replace(s.on_line(3, "&s"), "s"),
            ],
        )),
    ]
}

fn g11(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0711,
            "`s` is dropped while `r` still borrows it",
            s.on_line(6, "}"),
            "`s` is dropped here",
        )
        .with_secondary(
            s.nth_on_line(4, "s", 1),
            "`s` lives until the end of this block",
        )
        .with_secondary(
            s.on_line(5, "&s"),
            "shared borrow of `s` starts here, held by `r`",
        )
        .with_secondary(s.on_line(7, "r"), "the borrow is still in use here")
        .with_help(Help::text(
            "declare `s` outside the block so it lives as long as `r`",
        )),
    ]
}

fn g12(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0501,
            "`match` doesn't handle `Shape.Empty`",
            s.nth_on_line(8, "s", 0),
            "missing `Shape.Empty`",
        )
        .with_secondary(s.on_line(4, "Empty"), "`Shape.Empty` is declared here")
        .with_help(Help::suggest(
            "add `Shape.Empty => ...`, or a `default` arm",
            vec![Edit::insert(
                s.line_start(11),
                "    Shape.Empty => panic(\"unhandled\"),\n",
            )],
        )),
    ]
}

fn g13(s: &Src) -> Vec<Diagnostic> {
    let call = s.find("VGA.writeVolatile(0x0741);");
    vec![
        Diagnostic::new(
            Code::EN0801,
            "writing through a raw pointer needs `unsafe`",
            s.find("VGA.writeVolatile(0x0741)"),
            "`writeVolatile` dereferences `VGA`, a `*u16`",
        )
        .rule(
            "`unsafe` grants exactly five powers; this one is \"dereference a raw pointer\". Nothing checks the address for you.",
        )
        .with_help(Help::suggest(
            "state that you have checked the address",
            vec![Edit::insert(call.lo, "unsafe { "), Edit::insert(call.hi, " }")],
        )),
    ]
}

fn g14(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0820,
            "`string[]` needs a heap, and this program has no global allocator",
            s.find("string[]"),
            "first allocating type reached from `@entry`",
        )
        .note(
            "target `i386-none` has no operating system to get memory from, so `alloc` works only after a program registers an allocator.",
        )
        .with_help(Help::suggest(
            "register an allocator and give it memory with `heap.addBootRegions(boot)` in `kmain`",
            vec![Edit::insert(
                s.line_start(1),
                "@globalAllocator private unsafe let heap: FreeListHeap;\n",
            )],
        ))
        .with_help(Help::text(
            "or stay allocation-free: fixed arrays `T[N]` and `&string` parameters need no allocator",
        )),
    ]
}

fn g15(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0901,
            "`bswap` needs CPU feature `bswap`, which target level `i386` does not have",
            s.find("bswap eax"),
            "`bswap r32` needs level `i486` or higher",
        )
        .note(
            "`i386` output must run on every listed CPU, and an 80386 does not decode this instruction.",
        )
        .with_help(Help::text(
            "`x.swapBytes()` in `core` does the same at every level, with no `asm`",
        ))
        .with_help(Help::text("or build for a higher level: `--cpu=i486`"))
        .with_help(Help::text(
            "or mark a separate function `@requires(\"bswap\")` and guard the call with `cpu.has(\"bswap\")`",
        )),
    ]
}

fn g16(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0614,
            "`xs` is `const`, so `push` cannot change it",
            s.find("xs.push(1)"),
            "`push` changes `xs`",
        )
        .with_secondary(
            s.on_line(1, "xs"),
            "declared `const` here: immutable all the way down",
        )
        .from_typescript(
            "a TS `const` only freezes the binding. In Enrang values have no shared identity, so `const` freezes the value.",
        )
        .with_help(Help::machine(
            "make the binding mutable",
            vec![Edit::replace(s.on_line(1, "const"), "let")],
        )),
    ]
}

fn g17(s: &Src) -> Vec<Diagnostic> {
    let argument = s.on_line(4, "a");
    vec![
        Diagnostic::new(
            Code::EN0612,
            "missing `&`: `bump` takes a reference",
            argument,
            "expected `&i64[]`, found `i64[]`",
        )
        .note(
            "a reference is only ever made by writing `&`; with no `&`, a value is moved or copied.",
        )
        .with_help(Help::machine(
            "write `&a`",
            vec![Edit::insert(argument.lo, "&")],
        )),
    ]
}

fn g18(s: &Src) -> Vec<Diagnostic> {
    let declared = s.on_line(2, "inc");
    vec![
        Diagnostic::new(
            Code::EN0615,
            "`inc` changes the object, but `Counter` declares that it doesn't",
            s.find("this.n += 1"),
            "this write needs exclusive access to `this`",
        )
        .with_secondary(declared, "declared here without `let`")
        .with_help(Help::suggest(
            "if implementations may change the object, write `let inc(): void;` in `Counter`",
            vec![Edit::insert(declared.lo, "let ")],
        )),
    ]
}

fn g19(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0701,
            "an array can't hold a `Lexer`, because `Lexer` holds a reference",
            s.find("Lexer[]"),
            "`Lexer` borrows through its field `src`",
        )
        .rule(
            "a class that holds a reference lives only where a reference can: in locals, parameters, return values and fields of another such class.",
        )
        .with_help(Help::text("own the data: `private src: string;`")),
    ]
}

fn g20(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0426,
            "this `Result` is not used, so an error would be lost silently",
            s.find("save(\"a\")"),
            "returns `Result<void>`",
        )
        .from_typescript("a thrown exception cannot be ignored by accident, and neither can this.")
        .with_help(Help::machine(
            "discard it deliberately",
            vec![Edit::insert(s.find("save(\"a\")").lo, "void ")],
        )),
    ]
}

fn g21(s: &Src) -> Vec<Diagnostic> {
    let source = s.on_line(2, "&q");
    vec![
        Diagnostic::new(
            Code::EN0706,
            "cannot reassign `q` during iteration",
            s.on_line(4, "q = []"),
            "cannot reassign while borrowed",
        )
        .with_secondary(source, "`q` is borrowed here")
        .with_help(Help::suggest(
            "iterate over `q.clone()` if reassignment is intentional",
            vec![Edit::replace(source, "q.clone()")],
        )),
    ]
}

fn g22(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0438,
            "`...` clones each element, and `T` has no `Clone` bound",
            s.find("...xs"),
            "each element of `xs` would be cloned here",
        )
        .with_secondary(s.on_line(1, "T"), "`T` is declared here")
        .from_typescript(
            "JS spread copies references to the same objects. In Enrang a value has one owner, so `...` copies the elements too.",
        )
        .with_help(Help::machine(
            "require `Clone`",
            vec![Edit::insert(s.on_line(1, "T").hi, " extends Clone")],
        )),
    ]
}

fn g23(s: &Src) -> Vec<Diagnostic> {
    let call = s.find("name.trim()");
    vec![
        Diagnostic::new(
            Code::EN0453,
            "the result of `trim` is not used",
            call,
            "`trim` returns a new string and leaves `name` as it was",
        )
        .with_help(Help::machine(
            "keep it",
            vec![Edit::insert(call.lo, "name = ")],
        )),
        Diagnostic::new(
            Code::EN0706,
            "`queue` cannot change while `first` still points into it",
            s.find("queue.clear()"),
            "`clear` changes `queue`, so it needs exclusive access to it",
        )
        .with_secondary(
            s.find("&queue[0]"),
            "shared borrow of `queue` starts here, held by `first`",
        )
        .with_secondary(s.on_line(8, "first"), "`first` is used again here")
        .rule("a value has many shared borrows or one exclusive borrow, never both.")
        .with_help(Help::suggest(
            "keep a copy instead of a reference",
            vec![Edit::replace(s.find("&queue[0]"), "queue[0].clone()")],
        )),
    ]
}

fn g24(s: &Src) -> Vec<Diagnostic> {
    let call = s.find("super(name)");
    let set = s.find("this.owner = owner;");
    let both = s.span(
        s.text.find("super(name);").expect("the call"),
        s.text.find("this.owner = owner;").expect("the assignment") + "this.owner = owner;".len(),
    );
    vec![
        Diagnostic::new(
            Code::EN0610,
            "`this.owner` is not set when `super(name)` runs",
            call,
            "`Animal`'s constructor runs here, before `this.owner` is set",
        )
        .with_secondary(set, "`this.owner` is set only here")
        .from_typescript(
            "TypeScript requires `super(...)` before any use of `this` (TS17009). Enrang sets a subclass's own fields first, so a base constructor that calls an override finds them set.",
        )
        .with_help(Help::machine(
            "set `this.owner` before `super(name)`, because `Animal`'s constructor may call `Dog`'s methods",
            vec![Edit::replace(both, "this.owner = owner;\n    super(name);")],
        )),
    ]
}

fn build(id: &str, source: &Src) -> Vec<Diagnostic> {
    let (_, builder) = all_builders()
        .find(|(known, _)| *known == id)
        .unwrap_or_else(|| panic!("{id} has no builder"));
    builder(source)
}

/// A case's source and its hand-built diagnostics.
pub fn built(id: &str) -> (Src, Vec<Diagnostic>) {
    let source = source(id);
    let diags = build(id, &source);
    (source, diags)
}

/// The acceptance test itself.
fn renders_the_document(id: &str) {
    let source = source(id);
    let rendered = source.render(&build(id, &source));
    same(&rendered, &case(id).stderr.text);
}

/// Every line a help shows must be what applying its edits to the source produces,
/// or a reader following the snippet would get a different program than a machine.
fn shown_fixes_are_the_applied_fixes(id: &str) {
    let source = source(id);
    let mut checked = 0;
    for diag in build(id, &source) {
        for help in &diag.helps {
            if help.edits.is_empty() {
                continue;
            }
            let fixed = apply_fixes(&source.text, source.base(), &help.edits)
                .unwrap_or_else(|conflict| panic!("{id}: {conflict}"));
            assert_ne!(fixed, *source.text, "{id}: the fix changes nothing");
            let mut alone = diag.clone();
            alone.helps = vec![help.clone()];
            alone.entries.clear();
            let rendered = source.one(alone);
            let after_help = rendered
                .split_once(&format!("help: {}\n", help.message))
                .expect("the help is rendered")
                .1;
            for line in after_help.lines() {
                let Some(shown) = snippet_text(line) else {
                    continue;
                };
                assert!(
                    fixed.lines().any(|fixed_line| fixed_line == shown),
                    "{id}: `{shown}` is shown but is not a line of the fixed source:\n{fixed}"
                );
                checked += 1;
            }
        }
    }
    let has_code = build(id, &source)
        .iter()
        .any(|diag| diag.helps.iter().any(|help| !help.edits.is_empty()));
    assert_eq!(checked > 0, has_code, "{id}: lines checked: {checked}");
}

/// The source text of a numbered snippet line such as `3 + text`, if it is one.
fn snippet_text(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    let digits = trimmed.len()
        - trimmed
            .trim_start_matches(|c: char| c.is_ascii_digit())
            .len();
    if digits == 0 {
        return None;
    }
    let rest = trimmed[digits..].strip_prefix(' ')?;
    let mut chars = rest.chars();
    matches!(chars.next(), Some('|' | '+' | '~')).then_some(())?;
    Some(chars.as_str().strip_prefix(' ').unwrap_or(""))
}

/// The G cases `text` names, with a range such as `G07-G11` expanded.
fn g_ids(text: &str) -> Vec<String> {
    let number = |token: &str| -> Option<u32> {
        let digits = token.strip_prefix('G')?;
        let all_digits = digits.len() == 2 && digits.bytes().all(|b| b.is_ascii_digit());
        all_digits.then(|| digits.parse().expect("two digits"))
    };
    let mut found = Vec::new();
    for token in text.split(|c: char| !(c.is_ascii_alphanumeric() || c == '-')) {
        if let Some(n) = number(token) {
            found.push(format!("G{n:02}"));
        } else if let Some((first, last)) = token.split_once('-')
            && let (Some(first), Some(last)) = (number(first), number(last))
        {
            assert!(first < last, "`{token}` is no range");
            found.extend((first..=last).map(|n| format!("G{n:02}")));
        }
    }
    found
}

/// Each G case a row of TESTING 23 promises byte-exact, with the row's milestone.
/// TESTING 18 takes a case's milestone from this table.
fn byte_exact_milestones() -> Vec<(String, Milestone)> {
    let section = doc("TESTING.md")
        .split_once("## 23. Definition of done per milestone")
        .expect("TESTING has section 23")
        .1;
    let section = section.split("\n## ").next().expect("the section");
    let mut named = Vec::new();
    for line in section.lines() {
        let Some(rest) = line.strip_prefix("| **") else {
            continue;
        };
        let written = rest.split("**").next().expect("a milestone");
        let milestone = MILESTONES
            .into_iter()
            .find(|milestone| milestone.to_string() == written)
            .unwrap_or_else(|| panic!("`{written}` is no milestone"));
        // Only a clause that promises the bytes: M0's "hand-built G01 shape" does not.
        for clause in line.split([';', '|']) {
            if clause.trim_end().ends_with("byte-exact") {
                named.extend(g_ids(clause).into_iter().map(|id| (id, milestone)));
            }
        }
    }
    assert!(
        !named.is_empty(),
        "TESTING 23 promises no G case byte-exact"
    );
    named
}

const MILESTONES: [Milestone; 11] = [
    Milestone::M0,
    Milestone::M1,
    Milestone::M2,
    Milestone::M3,
    Milestone::M4,
    Milestone::M5,
    Milestone::M6,
    Milestone::M7,
    Milestone::M8,
    Milestone::M9,
    Milestone::M10,
];

fn register_meta(h: &mut Harness) {
    h.case("golden/every G heading has a marker", || {
        let missing = headings_without_cases(doc("SPEC.md")).expect("the document scans");
        assert_eq!(missing, Vec::<String>::new());
    });
    h.case(
        "golden/the document and the builders list the same cases",
        || {
            let in_doc: Vec<&str> = cases()
                .iter()
                .map(|case| case.id.as_str())
                .filter(|id| id.starts_with('G'))
                .collect();
            let built: Vec<&str> = BUILDERS.iter().map(|(id, _)| *id).collect();
            assert_eq!(in_doc, built);
        },
    );
    h.case(
        "golden/every diagnostic in the document has a builder",
        || {
            let with_diagnostics: Vec<&str> = cases()
                .iter()
                .filter(|case| {
                    let text = &case.stderr.text;
                    text.starts_with("error[") || text.starts_with("warning[")
                })
                .map(|case| case.id.as_str())
                .collect();
            let built: Vec<&str> = all_builders().map(|(id, _)| id).collect();
            assert_eq!(with_diagnostics, built);
        },
    );
    h.case("golden/the G reader expands ranges", || {
        assert_eq!(
            g_ids("G07-G11, G16 byte-exact"),
            ["G07", "G08", "G09", "G10", "G11", "G16"]
        );
        assert_eq!(g_ids("G01-G04 byte-exact"), ["G01", "G02", "G03", "G04"]);
        assert_eq!(g_ids("G15 byte-exact; GenExpr, G2, G123"), ["G15"]);
    });
    h.case(
        "golden/TESTING 23 names each G case once, no earlier than its codes",
        || {
            let named = byte_exact_milestones();
            for (id, _) in BUILDERS {
                let rows: Vec<Milestone> = named
                    .iter()
                    .filter(|(named, _)| named == id)
                    .map(|(_, milestone)| *milestone)
                    .collect();
                assert_eq!(rows.len(), 1, "{id} is byte-exact at {rows:?}");
                let (_, diags) = built(id);
                for diag in &diags {
                    assert!(
                        diag.code.since() <= rows[0],
                        "{id} is byte-exact at {}, before {} fires at {}",
                        rows[0],
                        diag.code,
                        diag.code.since()
                    );
                }
            }
            for (id, milestone) in &named {
                let known = BUILDERS.iter().any(|(case, _)| case == id);
                assert!(
                    known,
                    "TESTING 23 names {id} at {milestone}, a case SPEC 14 lacks"
                );
            }
        },
    );
    h.case("golden/the comparison can fail", || {
        let id = "G01";
        let source = source(id);
        let mut diags = build(id, &source);
        diags[0].message.push('!');
        assert_ne!(source.render(&diags), case(id).stderr.text);
    });
}

/// The final line SPEC 13.1 gives these counts, written apart from the renderer.
fn final_line(errors: usize, warnings: usize) -> Option<String> {
    if errors == 0 {
        return None;
    }
    let plural =
        |count: usize, noun: &str| format!("{count} {noun}{}", if count == 1 { "" } else { "s" });
    let errors = plural(errors, "previous error");
    Some(match warnings {
        0 => format!("error: aborting due to {errors}"),
        _ => format!(
            "error: aborting due to {errors}; {} emitted",
            plural(warnings, "warning")
        ),
    })
}

pub fn register(h: &mut Harness) {
    register_meta(h);
    for (id, _) in all_builders() {
        h.case(format!("golden/{id}/bytes"), move || {
            renders_the_document(id)
        });
        h.case(format!("golden/{id}/marker"), move || {
            let case = case(id);
            let source = source(id);
            let diags = build(id, &source);
            let errors = diags.iter().any(|diag| diag.severity == Severity::Error);
            assert_eq!(
                case.exit,
                i32::from(errors),
                "SPEC 14: 1 for an error, 0 for warnings alone"
            );
            assert!(
                errors || !case.stderr.text.contains("= explain:"),
                "SPEC 13.1: warnings do not print the explain line"
            );
            assert!(
                diags
                    .iter()
                    .all(|diag| diag.severity == diag.code.severity())
            );
        });
        h.case(format!("golden/{id}/fixes"), move || {
            shown_fixes_are_the_applied_fixes(id);
        });
        h.case(format!("golden/{id}/headers follow SPEC 13.1"), move || {
            // Lower-case first letter unless a code span, and no final period.
            let (_, diags) = built(id);
            for diag in &diags {
                let first = diag.message.chars().next().expect("a message");
                assert!(first.is_lowercase() || first == '`', "{}", diag.message);
                assert!(!diag.message.ends_with('.'), "{}", diag.message);
            }
        });
        h.case(
            format!("golden/{id}/the document ends with the final line"),
            move || {
                let text = &case(id).stderr.text;
                let (_, diags) = built(id);
                let count = |severity| diags.iter().filter(|d| d.severity == severity).count();
                match final_line(count(Severity::Error), count(Severity::Warning)) {
                    Some(line) => {
                        assert!(text.ends_with(&format!("\n\n{line}\n")), "{text}");
                    }
                    None => assert!(!text.contains("aborting"), "{text}"),
                }
            },
        );
        h.case(format!("golden/{id}/color"), move || {
            let source = source(id);
            let colored = source.render_colored(&build(id, &source));
            assert!(colored.contains('\x1b'), "asked for colour, got none");
            same(&strip_ansi(&colored), &case(id).stderr.text);
        });
    }
}
