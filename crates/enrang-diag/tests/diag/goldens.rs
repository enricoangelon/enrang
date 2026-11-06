//! SPEC 14 is the acceptance test of the renderer.
//!
//! The source and the expected stderr of each case come out of `docs/SPEC.md`
//! through the testkit extractor and nothing here repeats the expected text. No
//! compiler exists yet, so each diagnostic is built by hand, with its spans found
//! in the extracted source, and has to render to the document's bytes.

use std::sync::OnceLock;

use enrang_base::Span;
use enrang_diag::{Code, Diagnostic, Edit, Help, Severity, apply_fixes};
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
pub const BUILDERS: [(&str, Builder); 23] = [
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
];

/// The samples of SPEC 15 whose stderr is a diagnostic. The renderer owes them the
/// same bytes, and a meta-test below finds any it has no builder for.
pub const SAMPLE_BUILDERS: [(&str, Builder); 1] = [("S11", s11)];

/// Every case with a diagnostic to render.
fn all_builders() -> impl Iterator<Item = (&'static str, Builder)> {
    BUILDERS.into_iter().chain(SAMPLE_BUILDERS)
}

fn g01(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0101,
            "missing `;` after this statement",
            s.eol(2),
            "expected `;` here",
        )
        .from_typescript("Enrang has no automatic semicolon insertion.")
        .with_help(Help::machine(
            "add the semicolon",
            vec![Edit::insert(s.line_end(2), ";")],
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
            "accept every type with a generic",
            vec![
                Edit::insert(s.find("show").hi, "<T extends Display>"),
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
    vec![
        Diagnostic::new(
            Code::EN0601,
            "`u` is used after it was moved",
            s.on_line(12, "u"),
            "used here, after the move",
        )
        .with_secondary(
            s.on_line(10, "u"),
            "`u` owns this `User`, which is not Copy because it has a `string` field",
        )
        .with_secondary(
            s.nth_on_line(11, "u", 0),
            "moved here: `archive` takes `u: User` by value",
        )
        .from_typescript(
            "both names would share one object. In Enrang a value has one owner, so passing `u` hands it over.",
        )
        .with_help(Help::suggest(
            "`archive` only reads `u`, so borrow it instead",
            vec![Edit::insert(s.on_line(5, "User").lo, "&")],
        ))
        .with_help(Help::suggest(
            "or pass a copy",
            vec![Edit::insert(s.on_line(11, "u").hi, ".clone()")],
        )),
    ]
}

fn g08(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0706,
            "`queue` cannot change while `job` still points into it",
            s.find("queue.push(\"retry\")"),
            "`push` is a `mut` method, so it needs exclusive access to `queue`",
        )
        .with_secondary(
            s.on_line(3, "job"),
            "`job` points into `queue` for this turn",
        )
        .with_secondary(s.on_line(7, "job"), "`job` is used again here")
        .why(
            "`push` may move the array to a bigger block of memory, leaving `job` pointing at freed memory.",
        )
        .rule("a value has many shared borrows or one exclusive borrow, never both.")
        .with_help(spread_help(s.on_line(3, "queue")))
        .with_help(Help::suggest(
            "or keep a clone of `job` from before the change",
            vec![
                Edit::insert(s.line_start(4), "    const saved = job.clone();\n"),
                Edit::replace(s.on_line(7, "job"), "saved"),
            ],
        )),
    ]
}

/// The edit that turns a `for...of` over a path into one over a copy (SPEC 4.13).
fn spread_help(source: Span) -> Help {
    Help::suggest(
        "to loop over the items as they are now, iterate over a copy",
        vec![
            Edit::insert(source.lo, "[..."),
            Edit::insert(source.hi, "]"),
        ],
    )
}

/// The warning of a loop that can change its own source (SPEC 5.6), with `access`
/// the first statement that counts.
fn en0719(name: &str, source: Span, access: Span) -> Diagnostic {
    Diagnostic::new(
        Code::EN0719,
        format!("`{name}` can change inside this loop, so the loop may never stop"),
        source,
        "read again at the start of every turn",
    )
    .with_secondary(
        access,
        format!("`push` is a `mut` method, so it can change `{name}`"),
    )
    .note(
        "a `for...of` loop over a path sees changes to its source: added items get turns and removed items do not.",
    )
}

fn g21(s: &Src) -> Vec<Diagnostic> {
    let source = s.on_line(3, "queue");
    vec![
        en0719("queue", source, s.find("queue.push(\"retry\")"))
            .with_help(spread_help(source))
            .with_help(Help::text(
                "or, to keep the new items and lose this warning, use an index loop: `for (let i = 0; i < queue.length; i++)`",
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
    let source = s.on_line(3, "queue");
    vec![
        en0719("queue", source, s.find("queue.push(\"retry\")"))
            .with_help(spread_help(source))
            .with_help(Help::text(
                "or, to keep the new items and lose this warning, use an index loop: `for (let i = 0; i < queue.length; i++)`",
            )),
        Diagnostic::new(
            Code::EN0706,
            "`queue` cannot change while `first` still points into it",
            s.find("queue.clear()"),
            "`clear` is a `mut` method, so it needs exclusive access to `queue`",
        )
        .with_secondary(
            s.find("&queue[0]"),
            "shared borrow of `queue` starts here, held by `first`",
        )
        .with_secondary(s.on_line(10, "first"), "`first` is used again here")
        .rule("a value has many shared borrows or one exclusive borrow, never both.")
        .with_help(Help::suggest(
            "keep a copy instead of a reference",
            vec![Edit::replace(s.find("&queue[0]"), "queue[0].clone()")],
        )),
    ]
}

fn s11(s: &Src) -> Vec<Diagnostic> {
    vec![
        en0719("work", s.on_line(22, "work"), s.find("work.push(v - 1)")).with_help(Help::text(
            "to keep the new items and lose this warning, use an index loop: `for (let i = 0; i < work.length; i++)`",
        )),
    ]
}

fn g09(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0707,
            "cannot borrow `xs` as exclusive twice at the same time",
            s.nth_on_line(9, "&mut xs", 1),
            "second exclusive borrow",
        )
        .with_secondary(
            s.nth_on_line(9, "&mut xs", 0),
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
            s.on_line(7, "}"),
            "`s` is dropped here",
        )
        .with_secondary(
            s.nth_on_line(5, "s", 1),
            "`s` lives until the end of this block",
        )
        .with_secondary(
            s.on_line(6, "&s"),
            "shared borrow of `s` starts here, held by `r`",
        )
        .with_secondary(s.on_line(8, "r"), "the borrow is still in use here")
        .with_help(Help::text(
            "declare `s` outside the block so it lives as long as `r`",
        )),
    ]
}

fn g12(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0501,
            "this `match` does not handle every `Shape`",
            s.nth_on_line(8, "s", 0),
            "missing `Shape.Empty`",
        )
        .with_secondary(s.on_line(4, "Empty"), "`Shape.Empty` is declared here")
        .with_help(Help::suggest(
            "add the missing arm",
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
            "`writeVolatile` dereferences `VGA`, a `*mut u16`",
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
                "@globalAllocator unsafe let heap: FreeListHeap;\n",
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
            "`push` is a `mut` method",
        )
        .with_secondary(
            s.on_line(2, "xs"),
            "declared `const` here: immutable all the way down",
        )
        .from_typescript(
            "a TS `const` only freezes the binding. In Enrang values have no shared identity, so `const` freezes the value.",
        )
        .with_help(Help::machine(
            "make the binding mutable",
            vec![Edit::replace(s.on_line(2, "const"), "let")],
        )),
    ]
}

fn g17(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0612,
            "`bump` changes its argument, so the call must say `&mut`",
            s.on_line(7, "a"),
            "expected `&mut i64[]`, found `i64[]`",
        )
        .note(
            "shared borrows are implicit because they cannot change anything; mutation is always visible at the call.",
        )
        .with_help(Help::machine(
            "lend it exclusively",
            vec![Edit::insert(s.on_line(7, "a").lo, "&mut ")],
        )),
    ]
}

fn g18(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0615,
            "`inc` changes `this` but is not marked `mut`",
            s.find("this.n += 1"),
            "this write needs exclusive access to `this`",
        )
        .with_help(Help::machine(
            "mark the method `mut`",
            vec![Edit::insert(s.find("inc").lo, "mut ")],
        )),
    ]
}

fn g19(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0701,
            "a class field cannot hold a reference",
            s.find("&string"),
            "references live only in locals, parameters and return values",
        )
        .with_help(Help::suggest(
            "own the data",
            vec![Edit::replace(s.find("&string"), "string")],
        ))
        .with_help(Help::text(
            "or keep only `pos` in the class and pass `src: &string` to each method",
        )),
    ]
}

fn g20(s: &Src) -> Vec<Diagnostic> {
    vec![
        Diagnostic::new(
            Code::EN0426,
            "this `Result` is not used, so an error would be lost silently",
            s.find("save(\"a\")"),
            "returns `Result<void, string>`",
        )
        .from_typescript("a thrown exception cannot be ignored by accident, and neither can this.")
        .with_help(Help::machine(
            "discard it deliberately",
            vec![Edit::insert(s.find("save(\"a\")").lo, "void ")],
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
