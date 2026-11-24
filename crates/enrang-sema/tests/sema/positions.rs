//! R1/R2 position checks (plan d.15; owner 4E): EN0701 for a reference or a
//! borrowing value in an element, a payload, an object-type field, a written type
//! argument, a non-`private` reference field or a class bound; EN0401 for a view by
//! value; EN1006 for an interface by value outside a parameter; EN0702 and EN0705 in
//! a body's written types; EN0440 for a by-value object parameter moved whole. Every
//! check runs on resolved types, looks at written types and unannotated locals only,
//! and gives one diagnostic per mistake (G19 byte for byte). The helpers here are
//! shared with `views.rs`, `unsafety.rs` and `deferred.rs`.

use enrang_sema::LibSource;
use enrang_testkit::{Case, Harness, extract_cases, line_diff, workspace_root};

use crate::support::{Run, run_with};

/// G19's borrowing class.
pub const LEXER: &str = "private class Lexer {
  private src: &string;
  private pos: isize = 0;
  public constructor(src: &string) { this.src = src; }
}
";

/// Checks `src` as the entry `main.en` with the embedded library on `x86_64-linux`.
pub fn check(src: &str) -> Run {
    check_on(src, "x86_64-linux")
}

/// Checks `src` as the entry `main.en` with the embedded library on `target`.
pub fn check_on(src: &str, target: &str) -> Run {
    run_with(&[("main.en", src)], LibSource::Embedded, target)
}

/// Each diagnostic as `CODE `text under the primary span` message [label]`.
pub fn shown(r: &Run) -> Vec<String> {
    r.diags
        .iter()
        .map(|d| {
            let text = if d.primary.span.is_dummy() {
                String::new()
            } else {
                r.map.text(d.primary.span).to_owned()
            };
            format!(
                "{} `{text}` {} [{}]",
                d.code.name(),
                d.message,
                d.primary.text
            )
        })
        .collect()
}

/// Asserts that `src` reports exactly `expected`, in `shown`'s form.
pub fn reports(src: &str, expected: &[&str]) {
    let r = check(src);
    assert_eq!(shown(&r), expected, "{}", r.rendered());
}

/// Asserts that `src` checks with no diagnostic.
pub fn compiles(src: &str) {
    let r = check(src);
    r.clean();
}

/// Asserts that `src` renders exactly `expected`, as `enrang check` prints it.
pub fn renders(src: &str, expected: &str) {
    let r = check(src);
    let actual = r.rendered();
    assert!(actual == expected, "{}", line_diff(expected, &actual));
}

/// The SPEC case `id`.
pub fn spec_case(id: &str) -> Case {
    let spec = std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
    extract_cases(&spec)
        .expect("SPEC's cases extract")
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("no case {id}"))
}

/// Runs the SPEC case `id` as `enrang check <file>` would on the host target and
/// compares stderr byte for byte, and the exit code.
pub fn golden(id: &str) {
    let case = spec_case(id);
    assert_eq!(case.files.len(), 1, "{id}: one file");
    let file = &case.files[0];
    let r = run_with(
        &[(file.name.as_str(), file.contents.as_str())],
        LibSource::Embedded,
        enrang_target::host_target(),
    );
    let actual = r.rendered();
    assert!(
        actual == case.stderr.text,
        "{id}: {}",
        line_diff(&case.stderr.text, &actual)
    );
    let exit = i32::from(r.diags.iter().any(|d| d.severity.fails()));
    assert_eq!(exit, case.exit, "{id}: exit code");
}

pub fn register(h: &mut Harness) {
    g19(h);
    held(h);
    fields(h);
    bounds(h);
    views(h);
    interfaces(h);
    written_in_bodies(h);
    shapes(h);
    conversions(h);
    near_misses(h);
    review(h);
}

fn g19(h: &mut Harness) {
    h.case("positions/G19 byte-exact through load and analyze", || {
        golden("G19");
    });
    h.case(
        "positions/G19: the array literal `[lx]` is not checked, its annotation is",
        || {
            let src = format!(
                "private function f(lx: Lexer): void {{ let all: Lexer[] = [lx]; }}\n{LEXER}"
            );
            reports(
                &src,
                &["EN0701 `Lexer[]` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
            );
        },
    );
}

/// EN0701 for what a value position holds.
fn held(h: &mut Harness) {
    h.case("positions/EN0701 through an alias, at the alias's use", || {
        let src = format!(
            "private function f(lx: Lexer): void {{ let all: Lexers = [lx]; }}\nprivate type Lexers = Lexer[];\n{LEXER}"
        );
        reports(
            &src,
            &["EN0701 `Lexers` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
        );
    });
    h.case(
        "positions/EN0701 once for `Lexer[][]`, at the constructor holding the offender",
        || {
            let src = format!("private function f(all: &Lexer[][]): void {{}}\n{LEXER}");
            reports(
                &src,
                &["EN0701 `Lexer[]` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
            );
        },
    );
    h.case("positions/EN0701 for a fixed array of a borrowing class", || {
        let src = format!("private function f(all: &Lexer[4]): void {{}}\n{LEXER}");
        reports(
            &src,
            &["EN0701 `Lexer[4]` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
        );
    });
    h.case("positions/EN0701 for an array of references", || {
        renders(
            "private function f(xs: &(&i64)[]): void {}\n",
            "error[EN0701]: an array can't hold a `&i64`, because `&i64` is a reference
 --> main.en:1:25
  |
1 | private function f(xs: &(&i64)[]): void {}
  |                         ^^^^^^^^ a reference
  |
  = rule: a reference lives only in locals, parameters, return values, tuple parts and `private` fields of a class that holds references.
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
",
        );
    });
    h.case("positions/EN0701 for a nullable reference element", || {
        reports(
            "private function f(xs: &(&i64 | null)[]): void {}\n",
            &["EN0701 `(&i64 | null)[]` an array can't hold a `&i64 | null`, because `&i64 | null` is a reference [a reference]"],
        );
    });
    h.case("positions/EN0701 for a borrowing tuple element", || {
        reports(
            "private function f(xs: &[&i64, i32][]): void {}\n",
            &["EN0701 `[&i64, i32][]` an array can't hold a `[&i64, int]`, because `[&i64, int]` holds a reference [a tuple with a reference part]"],
        );
    });
    h.case("positions/EN0701 for a `Box` of a borrowing class", || {
        let src = format!("private function f(b: &Box<Lexer>): void {{}}\n{LEXER}");
        reports(
            &src,
            &["EN0701 `Box<Lexer>` a `Box` can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
        );
    });
    h.case("positions/EN0701 for a written type argument of a class", || {
        let src = format!(
            "private class Keeper<T> {{ private x: T | null = null; }}\nprivate function f(k: &Keeper<Lexer>): void {{}}\n{LEXER}"
        );
        reports(
            &src,
            &["EN0701 `Keeper<Lexer>` a `Keeper` can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
        );
    });
    h.case("positions/EN0701 for a reference as a written type argument", || {
        reports(
            "private class Keeper<T> { private x: T | null = null; }\nprivate function f(k: &Keeper<&i64>): void {}\n",
            &["EN0701 `Keeper<&i64>` a `Keeper` can't hold a `&i64`, because `&i64` is a reference [a reference]"],
        );
    });
    h.case("positions/EN0701 for an enum case's reference field", || {
        renders(
            "private enum Tok { Word { text: &string }, End }\n",
            "error[EN0701]: an enum case can't hold a `&string`, because `&string` is a reference
 --> main.en:1:33
  |
1 | private enum Tok { Word { text: &string }, End }
  |                                 ^^^^^^^ a reference
  |
  = rule: a reference lives only in locals, parameters, return values, tuple parts and `private` fields of a class that holds references.
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
",
        );
    });
    h.case("positions/EN0701 for an enum case's borrowing class field", || {
        let src = format!("private enum Tok {{ Lex {{ lx: Lexer }}, End }}\n{LEXER}");
        reports(
            &src,
            &["EN0701 `Lexer` an enum case can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
        );
    });
    h.case("positions/EN0701 for an object type's reference field", || {
        reports(
            "private function f(o: &{ name: &string }): void {}\n",
            &["EN0701 `{ name: &string }` an object type can't hold a `&string`, because `&string` is a reference [a reference]"],
        );
    });
    h.case(
        "positions/EF-08: `Result<i64, &AgeError>` is EN0701 once, with no EN0454",
        || {
            reports(
                "private function f(): Result<i64, &AgeError> { unreachable(); }\nprivate enum AgeError { Negative = \"negative age\" }\n",
                &["EN0701 `Result<i64, &AgeError>` a `Result` can't hold a `&AgeError`, because `&AgeError` is a reference [a reference]"],
            );
        },
    );
    h.case(
        "positions/EF-08: `Result<i64, Lexer>` is EN0701 once, with no EN0454",
        || {
            let src = format!("private function f(): Result<i64, Lexer> {{ unreachable(); }}\n{LEXER}");
            reports(
                &src,
                &["EN0701 `Result<i64, Lexer>` a `Result` can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
            );
        },
    );
    h.case(
        "positions/EN0701 for an unannotated local's inferred type, at its name",
        || {
            let src = format!("private function f(lx: Lexer): void {{ let all = [lx]; }}\n{LEXER}");
            reports(
                &src,
                &["EN0701 `all` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
            );
        },
    );
    h.case(
        "positions/the help owns the data: an array for a view, a `Box` for an interface",
        || {
            let src = "private interface Speaker { speak(): string; }
private class Cut { private part: &Slice<u8>; public constructor(p: &Slice<u8>) { this.part = p; } }
private class Talk { private s: &Speaker | null = null; }
private function f(a: &Cut[], b: &Talk[]): void {}
";
            let r = check(src);
            let helps: Vec<String> = r
                .diags
                .iter()
                .flat_map(|d| d.helps.iter().map(|h| h.message.clone()))
                .collect();
            assert_eq!(
                helps,
                [
                    "own the data: `private part: u8[];`",
                    "own the data: `private s: Box<Speaker> | null;`",
                ],
                "{}",
                r.rendered()
            );
        },
    );
}

/// EN0701 for a reference field that is not `private`.
fn fields(h: &mut Harness) {
    h.case("positions/S2-15-field: `public t: [&i64[], i32]` is EN0701", || {
        renders(
            "private class Pad {
  public t: [&i64[], i32];
  public constructor(v: &i64[]) { this.t = [v, 0]; }
}
",
            "error[EN0701]: `t` holds a reference, so it must be `private`
 --> main.en:2:13
  |
2 |   public t: [&i64[], i32];
  |             ^^^^^^^^^^^^^ a reference in a `public` field
  |
  = rule: a reference field is seen only inside its class, so the class can keep track of what it borrows.
help: make it `private`: `private t: [&i64[], i32];`
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
",
        );
    });
    h.case(
        "positions/a `protected` reference field and a `readonly &` one are EN0701",
        || {
            let r = check(
                "private class C {\n  public readonly src: readonly &string;\n  protected p: &i64 | null = null;\n}\n",
            );
            assert_eq!(
                shown(&r),
                [
                    "EN0701 `readonly &string` `src` holds a reference, so it must be `private` [a reference in a `public` field]",
                    "EN0701 `&i64 | null` `p` holds a reference, so it must be `private` [a reference in a `protected` field]",
                ],
                "{}",
                r.rendered()
            );
            let helps: Vec<&str> = r
                .diags
                .iter()
                .map(|d| d.helps[0].message.as_str())
                .collect();
            assert_eq!(
                helps,
                [
                    "make it `private`: `private readonly src: readonly &string;`",
                    "make it `private`: `private p: &i64 | null;`",
                ]
            );
        },
    );
    h.case("positions/a public parameter property holding a reference is EN0701", || {
        reports(
            "private class C { public constructor(public r: &i64) {} }\n",
            &["EN0701 `&i64` `r` holds a reference, so it must be `private` [a reference in a `public` field]"],
        );
    });
    h.case(
        "positions/a public field of a borrowing class type is no reference field",
        || {
            let src = format!(
                "private class Parser {{ public lx: Lexer; public constructor(lx: Lexer) {{ this.lx = lx; }} }}\n{LEXER}"
            );
            compiles(&src);
        },
    );
}

/// EN0701 for a class bound naming a borrowing class (S:764).
fn bounds(h: &mut Harness) {
    h.case("positions/D8-bound: `<T extends Lexer>` is EN0701 at the bound", || {
        let src = format!("private function f<T extends Lexer>(x: &T): void {{}}\n{LEXER}");
        renders(
            &src,
            "error[EN0701]: `T` can't stand for a `Lexer`, because `Lexer` holds a reference
 --> main.en:1:30
  |
1 | private function f<T extends Lexer>(x: &T): void {}
  |                              ^^^^^ `Lexer` borrows through its field `src`
  |
  = rule: a class that holds a reference lives only where a reference can: in locals, parameters, return values and fields of another such class.
help: own the data: `private src: string;`
  = explain: run `enrang explain EN0701`

error: aborting due to 1 previous error
",
        );
    });
    h.case("positions/a class's and a method's borrowing bounds are EN0701", || {
        let src = format!(
            "private class Box2<T extends Lexer> {{ public show<U extends Lexer>(x: &U): void {{}} }}\n{LEXER}"
        );
        reports(
            &src,
            &[
                "EN0701 `Lexer` `T` can't stand for a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]",
                "EN0701 `Lexer` `U` can't stand for a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]",
            ],
        );
    });
    h.case("positions/a bound naming a class that owns its data compiles", || {
        compiles(
            "private class Animal { public name: string = \"\"; }\nprivate function f<T extends Animal>(x: &T): void {}\n",
        );
    });
}

/// EN0401 for a view by value (S:606).
fn views(h: &mut Harness) {
    h.case(
        "positions/a `Slice<u8>` local is EN0401, with the help of S:606",
        || {
            renders(
                "private function f(): void { let v: Slice<u8>; }\n",
                "error[EN0401]: `Slice<u8>` is a view, so it exists only behind `&`
 --> main.en:1:37
  |
1 | private function f(): void { let v: Slice<u8>; }
  |                                     ^^^^^^^^^ a view by value
  |
help: write `&Slice<u8>`, or `u8[]` for an array of its own
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case("positions/OQ13-slice: a field `public s: Slice<u8>;` is EN0401", || {
        reports(
            "private class C { public s: Slice<u8>; }\n",
            &["EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]"],
        );
    });
    h.case(
        "positions/a view as an element, a result, a parameter, a tuple part, behind `*`",
        || {
            reports(
                "private function f(a: &Slice<u8>[], p: Slice<i64>, q: *Slice<u8>, t: &[Slice<u8>, i32]): Slice<u8> | null { unreachable(); }\n",
                &[
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0401 `Slice<i64>` `Slice<i64>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                ],
            );
        },
    );
    h.case(
        "positions/a view written for a type parameter without `views_ok` is EN0401",
        || {
            reports(
                "private class Keeper<T> { private x: T | null = null; }\nprivate function f(k: &Keeper<Slice<u8>>): void {}\n",
                &["EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]"],
            );
        },
    );
    h.case(
        "positions/a view written for a type parameter used only behind `&` compiles",
        || {
            compiles(
                "private class Shower<T> { public show(x: &T): void {} }\nprivate function f(k: &Shower<Slice<u8>>): void {}\n",
            );
        },
    );
    h.case("positions/`Result<Slice<u8>>` is EN0401 at the view", || {
        reports(
            "private function f(): Result<Slice<u8>> { unreachable(); }\n",
            &["EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]"],
        );
    });
}

/// EN1006 for an interface by value outside a parameter (S:631, S:3458).
fn interfaces(h: &mut Harness) {
    const SPEAKER: &str = "private interface Speaker { speak(): string; }\n";
    h.case(
        "positions/an interface local is EN1006 with SPEC 16's head, note and help",
        || {
            renders(
                &format!("private function f(): void {{ let s: Speaker; }}\n{SPEAKER}"),
                "error[EN1006]: an interface type by value outside a parameter is not supported yet
 --> main.en:1:37
  |
1 | private function f(): void { let s: Speaker; }
  |                                     ^^^^^^^ `Speaker` by value in a variable
  |
  = note: `Speaker` is an interface, so the size of a `Speaker` in a variable isn't known
help: `&Speaker` to refer to one, `Box<Speaker>` to own one
  = explain: run `enrang explain EN1006`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case(
        "positions/F7: a local inferred as an interface by value is EN1006 at its name (T:862)",
        || {
            let r = check(&format!(
                "private function un(b: Box<Speaker>): void {{ const s = b.unbox(); const r = &*b; }}\n{SPEAKER}"
            ));
            assert_eq!(
                shown(&r),
                ["EN1006 `s` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a variable]"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`Speaker` is an interface, so the size of a `Speaker` in a variable isn't known"
            );
        },
    );
    h.case(
        "positions/an interface result, field, element, tuple part and type argument",
        || {
            let src = format!(
                "private class Keeper<T> {{ private x: T | null = null; }}
private class C {{ private s: Speaker | null = null; }}
private function f(a: &Speaker[], t: &[Speaker, i32], k: &Keeper<Speaker>): Speaker {{ unreachable(); }}
{SPEAKER}"
            );
            reports(
                &src,
                &[
                    "EN1006 `Speaker` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a field]",
                    "EN1006 `Speaker` an interface type by value outside a parameter is not supported yet [`Speaker` by value in an array]",
                    "EN1006 `Speaker` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a tuple part]",
                    "EN1006 `Speaker` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a type argument]",
                    "EN1006 `Speaker` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a result]",
                ],
            );
        },
    );
    h.case(
        "positions/T:1000, T:1007: a `Box<I>` or a two-word `&I` of an interface no table serves is EN1006",
        || {
            let r = check(&format!(
                "private function first(a: &Clone, b: &Clone): &Clone {{ return a; }}
private class Holder {{ private c: &Clone; public constructor(c: &Clone) {{ this.c = c; }} }}
private function boxed(b: Box<Clone>, d: Box<Dumper>, f: fn(c: &Clone) => void): void {{}}
private function look(x: &Clone, s: &Speaker, b: Box<Speaker>): &Speaker {{ return s; }}
private interface Dumper {{ dump<T>(x: &T): void; }}
{SPEAKER}"
            ));
            let head = "an interface type by value outside a parameter is not supported yet";
            assert_eq!(
                shown(&r),
                [
                    format!("EN1006 `&Clone` {head} [this `&Clone` needs its class's table]"),
                    format!("EN1006 `&Clone` {head} [this `&Clone` needs its class's table]"),
                    format!("EN1006 `Box<Clone>` {head} [this `Box<Clone>` needs its class's table]"),
                    format!("EN1006 `Box<Dumper>` {head} [this `Box<Dumper>` needs its class's table]"),
                    format!(
                        "EN1006 `fn(c: &Clone) => void` {head} [this `&Clone` needs its class's table]"
                    ),
                ],
                "{}",
                r.rendered()
            );
            let notes: Vec<&str> = r.diags.iter().map(|d| d.entries[0].text.as_str()).collect();
            let clone = "`Clone.clone` takes or returns `Self` by value, which can't run where the class is unknown";
            let dump = "`Dumper.dump` is compiled once per type, so no table can hold it where the class is unknown";
            assert_eq!(notes, [clone, clone, clone, dump, clone]);
            assert_eq!(r.diags[0].helps[0].message, "use a type parameter `T extends Clone`");
            assert_eq!(r.diags[3].helps[0].message, "use a type parameter `T extends Dumper`");
        },
    );
    h.case(
        "positions/`Result<T, Error>` is EN1006 with the help for errors",
        || {
            let r = check("private function f(): Result<i64, Error> { unreachable(); }\n");
            assert_eq!(
                shown(&r),
                ["EN1006 `Error` an interface type by value outside a parameter is not supported yet [`Error` by value in a type argument]"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "for errors, `Result<i64>`, because `Error` is a family of types, not a type"
            );
        },
    );
    h.case(
        "positions/a nullable by-value interface parameter is EN1006 in a nullable",
        || {
            reports(
                &format!("private function f(s: Speaker | null): void {{}}\n{SPEAKER}"),
                &["EN1006 `Speaker` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a nullable]"],
            );
        },
    );
    h.case(
        "positions/an interface parameter, `&I`, `&I | null` and `Box<I>[]` compile",
        || {
            compiles(&format!(
                "private class C {{ private s: Box<Speaker>[] = []; private r: &Speaker | null = null; }}
private function f(s: Speaker, r: &Speaker, b: Box<Speaker>): &Speaker {{ unreachable(); }}
{SPEAKER}"
            ));
        },
    );
}

/// EN0702 and EN0705 wherever a body writes a type (lowering reports them as it
/// lowers each annotation; a written type gets one diagnostic).
fn written_in_bodies(h: &mut Harness) {
    h.case("positions/`&(&i64 | null)` as a local's annotation is EN0702", || {
        reports(
            "private function f(): void { let r: &(&i64 | null); }\n",
            &["EN0702 `&(&i64 | null)` a reference can't point to a reference [this points to `&i64 | null`]"],
        );
    });
    h.case("positions/`&&i64` in a cast and an arrow's parameter is EN0702", || {
        reports(
            "private function f(x: &i64): void { const p = x as &&i64; const g = (y: &&i64): void => {}; }\n",
            &[
                "EN0702 `&&i64` a reference can't point to a reference [this points to `&i64`]",
                "EN0702 `&&i64` a reference can't point to a reference [this points to `&i64`]",
            ],
        );
    });
    h.case("positions/`&&T` in a signature is EN0702 (T:640)", || {
        reports(
            "private function f(x: &&i64): void {}\n",
            &["EN0702 `&&i64` a reference can't point to a reference [this points to `&i64`]"],
        );
    });
    h.case(
        "positions/a closure type as a local's annotation is EN0705",
        || {
            renders(
                "private function f(): void { let g: (k: u8) => void; }\n",
                "error[EN0705]: a closure type can be written only as a parameter's type
 --> main.en:1:37
  |
1 | private function f(): void { let g: (k: u8) => void; }
  |                                     ^^^^^^^^^^^^^^^ not a parameter's type
  |
  = explain: run `enrang explain EN0705`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case(
        "positions/T:597: a closure-typed parameter of a closure type is EN0705",
        || {
            reports(
                "private function f(run: (g: (k: u8) => void) => void): void {}\n",
                &["EN0705 `(k: u8) => void` a closure type can be written only as a parameter's type [inside another closure type]"],
            );
        },
    );
    h.case(
        "positions/OQ24-nested: `| null` at a closure parameter's top is no nesting",
        || {
            compiles(
                "private function a(handler?: (k: u8) => void): void {}\nprivate function b(handler: ((k: u8) => void) | null): void {}\n",
            );
            reports(
                "private function c(f: (g: ((k: u8) => void) | null) => void): void {}\n",
                &["EN0705 `(k: u8) => void` a closure type can be written only as a parameter's type [inside another closure type]"],
            );
        },
    );
}

/// EN0440 for a by-value object parameter moved whole into storage its declared
/// type fixes (A:892, T:861).
fn shapes(h: &mut Harness) {
    h.case("positions/F5: `return x;` of a by-value object parameter is EN0440", || {
        renders(
            "private function keepName(x: { name: string }): { name: string } { return x; }\n",
            "error[EN0440]: `x` may have more fields than `{ name: string }`
 --> main.en:1:75
  |
1 | private function keepName(x: { name: string }): { name: string } { return x; }
  |                                                                           ^ `x` stands for any value with these fields
  |
help: build the smaller object: `{ name: x.name }`
  = explain: run `enrang explain EN0440`

error: aborting due to 1 previous error
",
        );
    });
    h.case(
        "positions/EN0440 into an annotated local and an array element",
        || {
            reports(
                "private function f(x: { name: string }): void { const y: { name: string } = x; const ys: { name: string }[] = [x]; }\n",
                &[
                    "EN0440 `x` `x` may have more fields than `{ name: string }` [`x` stands for any value with these fields]",
                    "EN0440 `x` `x` may have more fields than `{ name: string }` [`x` stands for any value with these fields]",
                ],
            );
        },
    );
    h.case(
        "positions/F5: `dispose(x)` of a by-value object parameter compiles",
        || {
            compiles("private function keepName(x: { name: string }): void { dispose(x); }\n");
        },
    );
}

/// A borrowing class never becomes an interface value nor a type argument (A:892,
/// S:631): the C22 conversion and the inferred type argument are checked where they
/// happen (4C's and 4A's), each EN0701 once (`D20E-01`, `F1`, `RR-06`, `EP-07`).
fn conversions(h: &mut Harness) {
    const ECHO: &str = "private interface Speaker { speak(): string; }
private class Echo implements Speaker {
  private t: &string;
  public constructor(t: &string) { this.t = t; }
  public speak(): string { return \"\"; }
}
private class Plain implements Speaker { public speak(): string { return \"\"; } }
";
    h.case(
        "positions/D20E-01: `wrap(new View(&tmp))` is EN0701 at the argument, as A:892 words it",
        || {
            let r = check(
                "private interface Shower { show(): void; }
private class View implements Shower {
  private s: &string;
  public constructor(s: &string) { this.s = s; }
  public show(): void {}
}
private function wrap(s: Shower): Box<Shower> { return new Box(s); }
private function make(): Box<Shower> { const tmp = \"x\".toString(); return wrap(new View(&tmp)); }
",
            );
            let at: Vec<(String, &str, &str)> = r
                .diags
                .iter()
                .map(|d| {
                    (
                        d.code.name().to_owned(),
                        r.map.text(d.primary.span),
                        d.message.as_str(),
                    )
                })
                .collect();
            assert_eq!(
                at,
                [(
                    "EN0701".to_owned(),
                    "new View(&tmp)",
                    "a `Shower` can't hold a `View`, because `View` holds a reference"
                )],
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "positions/F1: a borrowing class at a by-value and an `&` interface parameter is EN0701",
        || {
            let r = check(&format!(
                "private function keep(s: Speaker): Box<Speaker> {{ return new Box(s); }}
private function introduce(s: &Speaker): void {{}}
private function f(): void {{
  const text = \"hi\".toString();
  const k = keep(new Echo(&text));
  const echo = new Echo(&text);
  introduce(&echo);
}}
{ECHO}"
            ));
            let at: Vec<(String, &str)> = r
                .diags
                .iter()
                .map(|d| (d.code.name().to_owned(), r.map.text(d.primary.span)))
                .collect();
            assert_eq!(
                at,
                [
                    ("EN0701".to_owned(), "new Echo(&text)"),
                    ("EN0701".to_owned(), "&echo"),
                ],
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "positions/F1: the same with a class that holds no reference compiles",
        || {
            compiles(&format!(
                "private function keep(s: Speaker): Box<Speaker> {{ return new Box(s); }}
private function introduce(s: &Speaker): void {{}}
private function f(): void {{
  const k = keep(new Plain {{}});
  const p = new Plain {{}};
  introduce(&p);
}}
{ECHO}"
            ));
        },
    );
    h.case(
        "positions/RR-06: a borrowing reader at `&TokenReader` and at `T` is EN0701 at `&v`",
        || {
            let r = check(
                "private interface TokenReader { next(): string; }
private class View implements TokenReader {
  private text: &string;
  public constructor(t: &string) { this.text = t; }
  public next(): string { return \"\"; }
}
private function firstTwo(t: &TokenReader): void {}
private function firstTwoT<T extends TokenReader>(t: &T): void {}
private function f(): void { const s = \"a b\".toString(); const v = new View(&s); firstTwo(&v); firstTwoT(&v); }
",
            );
            let at: Vec<(String, &str)> = r
                .diags
                .iter()
                .map(|d| (d.code.name().to_owned(), r.map.text(d.primary.span)))
                .collect();
            assert_eq!(
                at,
                [("EN0701".to_owned(), "&v"), ("EN0701".to_owned(), "&v")],
                "{}",
                r.rendered()
            );
        },
    );
    h.case(
        "positions/EP-07: `show(&lx)` with G04's `show<T>(x: &T)` is EN0701 at `&lx`",
        || {
            let r = check(&format!(
                "const source = \"let x\";
let lx = new Lexer(&source);
show(&lx);
public function show<T>(x: &T): void {{ console.log(x); }}
{LEXER}"
            ));
            let at: Vec<(String, &str)> = r
                .diags
                .iter()
                .map(|d| (d.code.name().to_owned(), r.map.text(d.primary.span)))
                .collect();
            assert_eq!(at, [("EN0701".to_owned(), "&lx")], "{}", r.rendered());
        },
    );
}

/// What the checks leave alone.
fn near_misses(h: &mut Harness) {
    h.case(
        "positions/a borrowing class in locals, parameters, results and tuple parts compiles",
        || {
            compiles(&format!(
                "private function f(lx: Lexer, r: &Lexer): Lexer {{ const t: [&Lexer, i32] = [r, 1]; let m: Lexer | null = null; return lx; }}\n{LEXER}"
            ));
        },
    );
    h.case(
        "positions/a private reference field, a private borrowing tuple and an `fn` field compile",
        || {
            compiles(
                "private class C {
  private r: &i64 | null = null;
  private t: [&i64[], i32] | null = null;
  public cb: (fn(s: &string) => void) | null = null;
}
",
            );
        },
    );
    h.case(
        "positions/library declarations are trusted: the embedded library reports nothing",
        || {
            compiles("");
        },
    );
    h.case(
        "positions/SPEC 1's tour and `Ownership in three lines` report none of 4E's codes",
        || {
            const MINE: &[&str] = &["EN0701", "EN0702", "EN0705", "EN1006", "EN0440"];
            let spec =
                std::fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
            for c in extract_cases(&spec).expect("cases") {
                if c.id != "tour" && c.id != "ownership" {
                    continue;
                }
                let files: Vec<(&str, &str)> = c
                    .files
                    .iter()
                    .map(|f| (f.name.as_str(), f.contents.as_str()))
                    .collect();
                let r = run_with(&files, LibSource::Embedded, "x86_64-linux");
                let mine: Vec<String> = r
                    .codes()
                    .into_iter()
                    .filter(|code| MINE.contains(&code.as_str()))
                    .collect();
                assert!(mine.is_empty(), "{}: {}", c.id, r.rendered());
            }
        },
    );
    h.case(
        "positions/every M1 near-miss reports none of 4E's codes",
        || {
            const MINE: &[&str] = &[
                "EN0701", "EN0702", "EN0705", "EN1006", "EN0440", "EN0801", "EN0807", "EN0828",
                "EN0907", "EN1003", "EN1026", "EN1027", "EN1028", "EN1029", "EN1033",
            ];
            let root = workspace_root().join("tests/compile");
            let mut files = Vec::new();
            for dir in std::fs::read_dir(&root).expect("tests/compile") {
                let dir = dir.expect("entry").path();
                for f in std::fs::read_dir(&dir).expect("a code's directory") {
                    let f = f.expect("entry").path();
                    if f.to_string_lossy().ends_with(".pass.en") {
                        files.push(f);
                    }
                }
            }
            files.sort();
            assert!(!files.is_empty());
            for f in files {
                let text = std::fs::read_to_string(&f).expect("a near-miss");
                let name = f
                    .file_name()
                    .expect("a name")
                    .to_string_lossy()
                    .into_owned();
                let r = run_with(
                    &[(name.as_str(), text.as_str())],
                    LibSource::Embedded,
                    "x86_64-linux",
                );
                let mine: Vec<String> = r
                    .codes()
                    .into_iter()
                    .filter(|code| MINE.contains(&code.as_str()))
                    .collect();
                assert!(mine.is_empty(), "{name}: {}", r.rendered());
            }
        },
    );
}

/// Stage 6's review fixes of the position checks, and the cases the mutation gate
/// found unpinned.
fn review(h: &mut Harness) {
    h.case(
        "positions/plan d.15: a field initialiser's casts and arrow annotations are checked",
        || {
            reports(
                "public class C { public n: usize = (0 as *Slice<u8>) as usize; }
public class D { public f: fn(x: i64) => i64 = (x: i64): i64 => { const s: Slice<u8>[] = []; return x; }; }
",
                &[
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                ],
            );
        },
    );
    h.case(
        "positions/A:1159: a local that copies a written type is not reported again",
        || {
            reports(
                &format!(
                    "public function g(): Slice<u8> {{ unreachable(); }}
public function f(): void {{ const s = g(); }}
public function k(): Lexer[] {{ unreachable(); }}
public function h(): void {{ const a = k(); }}
public class H {{ public xs: Lexer[] = []; }}
public function m(h: &H): void {{ const a = &h.xs; }}
public function c(x: usize): void {{ const p = x as *Slice<u8>; const q = p; }}
{LEXER}"
                ),
                &[
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                    "EN0701 `Lexer[]` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]",
                    "EN0701 `Lexer[]` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]",
                    "EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]",
                ],
            );
        },
    );
    h.case(
        "positions/a `for...of` binding's inferred type is checked (mutant M06)",
        || {
            reports(
                "public interface Speaker { speak(): string; }
public function f(b: Box<Speaker>): void { for (const s of [b.unbox()]) { } }
",
                &["EN1006 `s` an interface type by value outside a parameter is not supported yet [`Speaker` by value in a variable]"],
            );
        },
    );
    h.case(
        "positions/S:764: a `where` clause naming a borrowing class is EN0701",
        || {
            reports(
                &format!(
                    "public class K<T> {{ public m(x: &T): void where T extends Lexer {{ }} }}\n{LEXER}"
                ),
                &["EN0701 `Lexer` `T` can't stand for a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"],
            );
        },
    );
    h.case(
        "positions/a nested offender is reported where it is held: `&Lexer[][]` at the inner `Lexer[]`",
        || {
            let r = check(&format!("public function f(xs: &Lexer[][]): void {{ }}\n{LEXER}"));
            assert_eq!(
                shown(&r),
                ["EN0701 `Lexer[]` an array can't hold a `Lexer`, because `Lexer` holds a reference [`Lexer` borrows through its field `src`]"]
            );
            let loc = r.map.loc(r.diags[0].primary.span.lo);
            assert_eq!((loc.line, loc.col), (1, 24));
        },
    );
    h.case(
        "positions/A:892: moving a by-value object parameter into `T | null` storage is EN0440",
        || {
            reports(
                "public function keep8(x: { name: string }): { name: string } | null { return x; }\n",
                &["EN0440 `x` `x` may have more fields than `{ name: string }` [`x` stands for any value with these fields]"],
            );
        },
    );
    h.case(
        "positions/SPEC 16: the help for `Result<T, Error>` is the row's, the note's article right",
        || {
            let r = check("public function g(): Result<i64, Error> { unreachable(); }\n");
            assert_eq!(r.diags.len(), 1, "{}", r.rendered());
            assert_eq!(
                r.diags[0].helps[0].message,
                "for errors, `Result<i64>`, because `Error` is a family of types, not a type"
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`Error` is an interface, so the size of an `Error` in a type argument isn't known"
            );
        },
    );
}
