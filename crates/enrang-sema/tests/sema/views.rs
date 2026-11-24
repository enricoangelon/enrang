//! The view and string facts (plan d.9; A:892, SPEC 4.3 S:606, 4.10 S:766; owner
//! 4E): once every body is typed, each type parameter gets `views_ok` and
//! `strings_ok`, lost at a by-value use (a local, a parameter, a result, an element,
//! a field, a cast, `*T`, `sizeOf`), at a C22 conversion, along calls and instances
//! that pass it on to a parameter lacking it, and missing from bodyless declarations
//! (an interface member keeps `strings_ok`); then each binding of a view or of
//! `string` to a parameter without the fact is EN0401, with the label at the use that
//! lost it or the note for a bodyless declaration, and the help adding an overload
//! (TESTING `SL-10-helps`, `Q44-show`, `VI-02-*`, `VI-05-dumper`).
//!
//! The cases of calls and conversions need the generic calls of 4A and the C22
//! conversions of 4C, which bind the type arguments these checks read.

use enrang_testkit::Harness;

use crate::positions::{check, compiles, renders, reports, shown};
use crate::support::Run;

/// `(views_ok, strings_ok)` of each type parameter of the definition at `path`.
fn facts(r: &Run, path: &str) -> (Vec<bool>, Vec<bool>) {
    let def = r.def(path);
    let f = r
        .tcx
        .facts(def)
        .unwrap_or_else(|| panic!("no facts for {path}: {}", r.rendered()));
    (f.views_ok.clone(), f.strings_ok.clone())
}

/// Asserts the facts of `path` in `src`, which must check cleanly.
fn has_facts(src: &str, path: &str, views: &[bool], strings: &[bool]) {
    let r = check(src);
    r.clean();
    assert_eq!(
        facts(&r, path),
        (views.to_vec(), strings.to_vec()),
        "{path}"
    );
}

const MEASURED: &str = "public interface Measured { length(): isize; }\n";

/// The text under diagnostic `i`'s satisfaction-site label, its last secondary
/// label, with the label.
fn site(r: &Run, i: usize) -> (&str, &str) {
    let label = r.diags[i].secondary.last().expect("a site label");
    (r.map.text(label.span), label.text.as_str())
}

pub fn register(h: &mut Harness) {
    computed(h);
    passed_on(h);
    bodyless(h);
    written(h);
    calls(h);
    strings(h);
    arrays(h);
    review(h);
    satisfactions(h);
}

/// The facts of a declaration's own uses.
fn computed(h: &mut Harness) {
    h.case(
        "views/a `T` used only behind `&` has both facts (G04's `show`)",
        || {
            has_facts(
                "public function show<T>(x: &T): void { console.log(x); }\n",
                "main::show",
                &[true],
                &[true],
            );
        },
    );
    h.case("views/`&T | null` keeps `views_ok`", || {
        has_facts(
            "private function opt<T>(x: &T | null): void {}\n",
            "main::opt",
            &[true],
            &[true],
        );
    });
    h.case(
        "views/a by-value parameter, a result, an element lose `views_ok`",
        || {
            let src = "private function own<T>(x: T): void {}
private function res<T>(x: &T): &T[] { unreachable(); }
private function arr<T>(x: &T[]): void {}
private function raw<T>(p: *T): void {}
";
            let r = check(src);
            r.clean();
            for f in ["main::own", "main::res", "main::arr", "main::raw"] {
                assert_eq!(facts(&r, f), (vec![false], vec![true]), "{f}");
            }
        },
    );
    h.case(
        "views/a local holding `T` by value loses `views_ok`, `&T` keeps it",
        || {
            let src = "private function byValue<T>(x: &T): void { let y: T | null = null; }
private function behind<T>(x: &T): void { let y: &T = x; }
";
            let r = check(src);
            r.clean();
            assert_eq!(facts(&r, "main::byValue"), (vec![false], vec![true]));
            assert_eq!(facts(&r, "main::behind"), (vec![true], vec![true]));
        },
    );
    h.case("views/VI-02-cast's body: `x as *T` loses `views_ok`", || {
        has_facts(
            "public function after<T>(x: &T): usize { const p = x as *T; return p as usize; }\n",
            "main::after",
            &[false],
            &[true],
        );
    });
    h.case("views/a local in a nested arrow counts for its body (VI-02-arrow)", || {
        has_facts(
            "private function f<T>(x: &T): void { const g = (): void => { let y: T | null = null; }; }\n",
            "main::f",
            &[false],
            &[true],
        );
    });
    h.case("views/a `T` bounded by a class never has `views_ok` (A:892)", || {
        has_facts(
            "private class Animal { public name: string = \"\"; }\nprivate function f<T extends Animal>(x: &T): void {}\n",
            "main::f",
            &[false],
            &[true],
        );
    });
    h.case(
        "views/each parameter of a list has its own facts, in order",
        || {
            has_facts(
                "private function two<A, B, C>(a: &A, b: B, c: &C[]): void {}\n",
                "main::two",
                &[true, false, false],
                &[true, true, true],
            );
        },
    );
    h.case(
        "views/a class's parameter, over its fields and all its bodies",
        || {
            let src = "private class Keeper<T> { private x: T | null = null; }
private class Shower<T> { public show(x: &T): void {} public static make(): void {} }
private class Local<T> { public f(x: &T): void { let y: T | null = null; } }
";
            let r = check(src);
            r.clean();
            assert_eq!(facts(&r, "main::Keeper"), (vec![false], vec![true]));
            assert_eq!(facts(&r, "main::Shower"), (vec![true], vec![true]));
            assert_eq!(facts(&r, "main::Local"), (vec![false], vec![true]));
        },
    );
}

/// The greatest fixed point along parameters passed on.
fn passed_on(h: &mut Harness) {
    h.case(
        "views/a `T` passed on as a class's type argument takes that parameter's facts",
        || {
            let src = "private class Keeper<T> { private x: T | null = null; }
private class Shower<T> { public show(x: &T): void {} }
private function k<T>(x: &Keeper<T>): void {}
private function s<T>(x: &Shower<T>): void {}
";
            let r = check(src);
            r.clean();
            assert_eq!(facts(&r, "main::k"), (vec![false], vec![true]));
            assert_eq!(facts(&r, "main::s"), (vec![true], vec![true]));
        },
    );
    h.case("views/a chain of classes reaches the fixed point", || {
        let src = "private class A<T> { private b: B<T> | null = null; }
private class B<T> { private c: C<T> | null = null; }
private class C<T> { private x: T | null = null; }
private class D<T> { private e: E<T> | null = null; }
private class E<T> { public show(x: &T): void {} }
";
        let r = check(src);
        r.clean();
        for c in ["main::A", "main::B", "main::C"] {
            assert_eq!(facts(&r, c), (vec![false], vec![true]), "{c}");
        }
        for c in ["main::D", "main::E"] {
            assert_eq!(facts(&r, c), (vec![true], vec![true]), "{c}");
        }
    });
    h.case("views/a cycle of classes keeps the facts no use loses", || {
        let src = "private class P<T> { private q: Box<Q<T>> | null = null; public show(x: &T): void {} }
private class Q<T> { private p: Box<P<T>> | null = null; }
";
        let r = check(src);
        r.clean();
        assert_eq!(facts(&r, "main::P"), (vec![true], vec![true]));
        assert_eq!(facts(&r, "main::Q"), (vec![true], vec![true]));
    });
    h.case(
        "views/calls pass a `T` on: `outer` loses what `inner` lacks",
        || {
            let src = "private function outer<T>(x: &T): void { inner(x); }
private function inner<T>(x: &T): void { const p = x as *T; }
";
            let r = check(src);
            r.clean();
            assert_eq!(facts(&r, "main::inner"), (vec![false], vec![true]));
            assert_eq!(facts(&r, "main::outer"), (vec![false], vec![true]));
        },
    );
}

/// Declarations with no body.
fn bodyless(h: &mut Harness) {
    h.case(
        "views/an interface member lacks `views_ok` and has `strings_ok` (VI-05-dumper)",
        || {
            has_facts(
                "public interface Dumper { dump<T>(x: &T): void; }\n",
                "main::Dumper::dump",
                &[false],
                &[true],
            );
        },
    );
    h.case("views/an abstract method lacks both facts", || {
        // An abstract method with type parameters of its own is also 4D's EN0460
        // (VI-06-tables); its facts are computed all the same.
        let r = check("public abstract class Shape { public abstract show<T>(x: &T): void; }\n");
        assert_eq!(r.codes(), ["EN0460"], "{}", r.rendered());
        assert_eq!(facts(&r, "main::Shape::show"), (vec![false], vec![false]));
    });
}

/// A view or `string` written as a type argument.
fn written(h: &mut Harness) {
    h.case(
        "views/a view written for a class's parameter that lacks `views_ok` is S:606's EN0401",
        || {
            reports(
                "private class Keeper<T> { private x: T | null = null; }\nprivate function f(): void { let k: Keeper<Slice<u8>> | null = null; }\n",
                &["EN0401 `Slice<u8>` `Slice<u8>` is a view, so it exists only behind `&` [a view by value]"],
            );
        },
    );
    h.case("views/`string` written for a parameter that keeps `strings_ok` compiles", || {
        compiles(
            "private class Keeper<T> { private x: T | null = null; }\nprivate function f(k: &Keeper<string>): void {}\n",
        );
    });
}

/// A view bound at a call (4A's bindings, A:892).
fn calls(h: &mut Harness) {
    h.case("views/SL-10-helps: `show(sector.slice(0, 2))` binds a view and compiles", || {
        compiles(
            "let sector: u8[8] = [0; 8];\nshow(sector.slice(0, 2));\npublic function show<T>(x: &T): void { console.log(x); }\n",
        );
    });
    h.case(
        "views/Q44-show: `pair` needs `T` by value at `sizeOf<T>()`: EN0401 with the help",
        || {
            renders(
                "let sector: u8[4] = [7; 4];
pair(sector.slice(0, 2));
private function pair<T>(x: &T): void { console.log(sizeOf<T>(), x); }
",
                "error[EN0401]: `T` can't stand for the view `Slice<u8>`
 --> main.en:2:1
  |
2 | pair(sector.slice(0, 2));
  | ^^^^^^^^^^^^^^^^^^^^^^^^ this binds `T` to `Slice<u8>`
3 | private function pair<T>(x: &T): void { console.log(sizeOf<T>(), x); }
  |                                                     ----------- this needs `T` to be a value type
  |
help: add `pair<T>(x: &Slice<T>)`
  = explain: run `enrang explain EN0401`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case("views/VI-02-cast: the label is at `x as *T`", || {
        let r = check(
            "const sector: u8[4] = [7, 7, 7, 7];
after(sector.slice(0, 2));
public function after<T>(x: &T): usize { const p = x as *T; return p.add(1) as usize - p as usize; }
",
        );
        assert_eq!(
            shown(&r),
            ["EN0401 `after(sector.slice(0, 2))` `T` can't stand for the view `Slice<u8>` [this binds `T` to `Slice<u8>`]"],
            "{}",
            r.rendered()
        );
        let d = &r.diags[0];
        assert_eq!(r.map.text(d.secondary[0].span), "x as *T");
        assert_eq!(d.helps[0].message, "add `after<T>(x: &Slice<T>)`");
    });
    h.case(
        "views/VI-02-measured: a C22 conversion of `&T` loses `views_ok`, labelled at its statement",
        || {
            let r = check(&format!(
                "const sector: u8[4] = [7, 7, 7, 7];
show(sector.slice(0, 2));
private function show<T extends Measured>(x: &T): void {{ const m: &Measured = x; console.log(m.length()); }}
{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                ["EN0401 `show(sector.slice(0, 2))` `T` can't stand for the view `Slice<u8>` [this binds `T` to `Slice<u8>`]"],
                "{}",
                r.rendered()
            );
            let d = &r.diags[0];
            assert_eq!(r.map.text(d.secondary[0].span), "const m: &Measured = x;");
            assert_eq!(
                d.secondary[0].text,
                "this converts `T` to an interface, which needs a value type"
            );
        },
    );
    h.case(
        "views/VI-05-dumper: a call through an interface member binds no view, with the note",
        || {
            let r = check(
                "public interface Dumper { dump<T>(x: &T): void; }
private function dumpWith(d: &Dumper, v: &Slice<u8>): void { d.dump(v); }
",
            );
            assert_eq!(
                shown(&r),
                ["EN0401 `d.dump(v)` `T` can't stand for the view `Slice<u8>` [this binds `T` to `Slice<u8>`]"],
                "{}",
                r.rendered()
            );
            let d = &r.diags[0];
            assert!(d.secondary.is_empty());
            assert_eq!(
                d.entries[0].text,
                "`Dumper.dump` has no body, so its `T` may be used by value"
            );
            assert_eq!(d.helps[0].message, "add `dump<T>(x: &Slice<T>)`");
        },
    );
    h.case(
        "views/a view bound through a chain of calls is labelled at the call that passes it on",
        || {
            let r = check(
                "const sector: u8[4] = [7, 7, 7, 7];
outer(sector.slice(0, 2));
private function outer<T>(x: &T): void { inner(x); }
private function inner<T>(x: &T): void { const p = x as *T; }
",
            );
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
            let d = &r.diags[0];
            assert_eq!(r.map.text(d.primary.span), "outer(sector.slice(0, 2))");
            assert_eq!(r.map.text(d.secondary[0].span), "inner(x)");
            assert_eq!(
                d.secondary[0].text,
                "this passes `T` on to `inner`, which needs a value type"
            );
        },
    );
}

/// `string` bound to a parameter without `strings_ok` (S:631, A:892).
fn strings(h: &mut Harness) {
    const SHOW: &str = "private function show<T extends Measured>(x: &T): void { const m: &Measured = x; console.log(m.length()); }\n";
    h.case(
        "views/VI-02-measured: `show(s.slice(1, 3))` and `show(&s)` are each EN0401",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();\nshow(s.slice(1, 3));\nshow(&s);\n{SHOW}{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                [
                    "EN0401 `show(s.slice(1, 3))` a `&string` can't become a `&Measured`, because it may be a part of a string [this binds `T` to `string`]",
                    "EN0401 `show(&s)` a `&string` can't become a `&Measured`, because it may be a part of a string [this binds `T` to `string`]",
                ],
                "{}",
                r.rendered()
            );
            for d in &r.diags {
                assert_eq!(r.map.text(d.secondary[0].span), "const m: &Measured = x;");
                assert_eq!(d.secondary[0].text, "here a `&T` becomes a `&Measured`");
                assert_eq!(d.helps[0].message, "add `show(x: &string)`");
            }
        },
    );
    h.case(
        "views/VI-02-measured: the facts of `show` after its conversion",
        || {
            let r = check(&format!("{SHOW}{MEASURED}"));
            r.clean();
            assert_eq!(facts(&r, "main::show"), (vec![false], vec![false]));
        },
    );
    h.case(
        "views/VI-02-measured: `LenSizer.size` must keep `strings_ok` for `Sizer.size`",
        || {
            let r = check(&format!(
                "public interface Sizer {{ size<T extends Measured>(x: &T): isize; }}
public class LenSizer implements Sizer {{
  public size<T extends Measured>(x: &T): isize {{ const m: &Measured = x; return m.length(); }}
}}
{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                ["EN0401 `const m: &Measured = x;` a `&string` can't become a `&Measured`, because it may be a part of a string [here a `&T` becomes a `&Measured`]"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`Sizer.size` lets `T` stand for `string`"
            );
            assert_eq!(site(&r, 0), ("Sizer", "`LenSizer` is used as a `Sizer` here"));
        },
    );
    h.case("views/VI-02-class: `new Keeper<string> {}` is EN0401 at `Keeper<string>`", || {
        let r = check(&format!(
            "let s = \"hello\".toString();
const k = new Keeper<string> {{}};
k.show(s.slice(1, 3));
public class Keeper<T extends Measured> {{ public show(x: &T): void {{ const m: &Measured = x; console.log(m.length()); }} }}
{MEASURED}"
        ));
        assert_eq!(
            shown(&r),
            ["EN0401 `Keeper<string>` a `&string` can't become a `&Measured`, because it may be a part of a string [this binds `T` to `string`]"],
            "{}",
            r.rendered()
        );
        assert_eq!(
            r.map.text(r.diags[0].secondary[0].span),
            "const m: &Measured = x;"
        );
    });
    h.case(
        "views/VI-02-arrow: a conversion inside a nested arrow is labelled there",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
show(s.slice(1, 3));
private function show<T extends Measured>(x: &T): void {{ each(() => {{ const m: &Measured = x; console.log(m.length()); }}); }}
private function each(f: () => void): void {{ f(); }}
{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                ["EN0401 `show(s.slice(1, 3))` a `&string` can't become a `&Measured`, because it may be a part of a string [this binds `T` to `string`]"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                r.map.text(r.diags[0].secondary[0].span),
                "const m: &Measured = x;"
            );
        },
    );
}

/// The EN0401 heads and helps of the view rows that pass an array where `&T[]` is
/// expected (`MR-2`, `OQ13-slice`, `SL-10-helps`; S:606, T:874-875, T:1044).
fn arrays(h: &mut Harness) {
    const ADD_ONE: &str = "private function addOne(xs: &u8[]): void { xs.push(1); }\n";
    h.case("views/MR-2: `fill(&buf)` compiles; `addOne(&buf)` and `reset(&buf)` can't grow", || {
        let r = check(&format!(
            "let buf: u8[4] = [0; 4];
fill(&buf);
addOne(&buf);
reset(&buf);
private function fill(xs: &Slice<u8>): void {{ xs[0] = 1; }}
private function reset(xs: &u8[]): void {{ mem.replace(xs, [9]); }}
{ADD_ONE}"
        ));
        assert_eq!(
            shown(&r),
            [
                "EN0401 `&buf` a fixed array can't grow [expected `&u8[]`, found `&u8[4]`]",
                "EN0401 `&buf` a fixed array can't grow [expected `&u8[]`, found `&u8[4]`]",
            ],
            "{}",
            r.rendered()
        );
        let helps: Vec<&str> = r.diags.iter().map(|d| d.helps[0].message.as_str()).collect();
        assert_eq!(
            helps,
            [
                "if `addOne` only reads or sets elements, take `xs: &Slice<u8>`; to let it grow, make `buf` a `u8[]`",
                "if `reset` only reads or sets elements, take `xs: &Slice<u8>`; to let it grow, make `buf` a `u8[]`",
            ]
        );
    });
    h.case(
        "views/OQ13-slice: a part from `slice` can't grow, and a `Slice` has no `push`",
        || {
            let r = check(&format!(
                "let sector: u8[8] = [0; 8];
let list: u8[] = [1, 2, 3];
fill(sector.slice(4, 8), 7);
fill(&list, 5);
addOne(&list);
addOne(list.slice(0, 2));
sector.slice(0, 4).push(1);
private function fill(xs: &Slice<u8>, v: u8): void {{ xs[0] = v; }}
{ADD_ONE}"
            ));
            assert_eq!(
                shown(&r),
                [
                    "EN0401 `list.slice(0, 2)` a part of an array can't grow [`addOne` takes `xs: &u8[]`, a whole array it may grow]",
                    "EN0303 `push` `Slice<u8>` has no member `push` [no such member]",
                ],
                "{}",
                r.rendered()
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "pass the whole array: addOne(&list)"
            );
        },
    );
    h.case(
        "views/SL-10-helps: a part that is a parameter names both parameter types",
        || {
            let r = check(&format!(
                "private function g(part: &Slice<u8>): void {{ addOne(part); }}\n{ADD_ONE}"
            ));
            assert_eq!(
                shown(&r),
                ["EN0401 `part` a part of an array can't grow [`addOne` takes `xs: &u8[]`, a whole array it may grow]"],
                "{}",
                r.rendered()
            );
            assert_eq!(
                r.diags[0].helps[0].message,
                "`addOne` takes `xs: &u8[]`, so take `part: &u8[]` in place of `&Slice<u8>`"
            );
        },
    );
}

/// Stage 6's review: a class bound refuses a view by itself; field initialisers
/// and library generics; the mutation gate's chain of passed-on strings facts.
fn review(h: &mut Harness) {
    h.case(
        "views/A:892: a class parameter used by value in a field initialiser loses `views_ok`",
        || {
            reports(
                "public class K<T> {
  public n: usize = sizeOf<T>();
  public show(x: &T): void { console.log(x); }
}
public class L<T> {
  public p: usize = ptr.null<T>() as usize;
  public show(x: &T): void { console.log(x); }
}
public function f(s: &Slice<u8>): void { const k = new K<Slice<u8>> {}; k.show(s); const l = new L<Slice<u8>> {}; }
",
                &[
                    "EN0401 `K<Slice<u8>>` `T` can't stand for the view `Slice<u8>` [this binds `T` to `Slice<u8>`]",
                    "EN0401 `L<Slice<u8>>` `T` can't stand for the view `Slice<u8>` [this binds `T` to `Slice<u8>`]",
                ],
            );
        },
    );
    h.case(
        "views/A:894: a library generic stands for a value type: `mem.swap` of two views is EN0401",
        || {
            let r = check(
                "public function f(): void {
  let a: u8[4] = [1, 2, 3, 4];
  let b: u8[2] = [5, 6];
  mem.swap(a.slice(0, 4), b.slice(0, 2));
}
",
            );
            assert_eq!(
                shown(&r),
                ["EN0401 `mem.swap(a.slice(0, 4), b.slice(0, 2))` `T` can't stand for the view `Slice<u8>` [this binds `T` to `Slice<u8>`]"]
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`swap` is the library's, whose body may use `T` by value"
            );
            assert!(r.diags[0].helps.is_empty());
        },
    );
    h.case(
        "views/S:766: `strings_ok` is lost along passed-on edges (mutant M14)",
        || {
            reports(
                "public interface Measured { length(): isize; }
private function inner<T extends Measured>(x: &T): isize { const m: &Measured = x; return m.length(); }
private function outer<T extends Measured>(x: &T): isize { return inner(x); }
public function f(): void { let s = \"hello\".toString(); console.log(outer(s.slice(1, 3))); }
",
                &["EN0401 `outer(s.slice(1, 3))` a `&string` can't become a `&Measured`, because it may be a part of a string [this binds `T` to `string`]"],
            );
        },
    );
    h.case(
        "views/S:764: a view bound to a class-bounded `T` is EN0419 alone",
        || {
            reports(
                "public class Animal { public age: i64 = 0; }
public function f<T extends Animal>(x: &T): void { }
public function g(): void {
  const sector: u8[4] = [7, 7, 7, 7];
  f(sector.slice(0, 2));
}
",
                &["EN0419 `sector.slice(0, 2)` `Slice<u8>` does not satisfy `Animal` [`T` must satisfy `Animal`]"],
            );
        },
    );
}

/// `Measured`, `Sizer` and the `Keeper` of TESTING `VI-02-structural`, with no
/// `implements`, whose `size` converts its `&T` to a `&Measured`.
const SIZER: &str = "public interface Sizer { size<T extends Measured>(x: &T): isize; }
public class Keeper {
  public size<T extends Measured>(x: &T): isize { const m: &Measured = x; return m.length(); }
}
public interface Measured { length(): isize; }
";

/// `f` of TESTING `VI-02-structural`, through a non-null `&Sizer` parameter.
const F: &str = "private function f(z: &Sizer, v: &string): void { console.log(z.size(v)); }\n";

/// The message of the string clause's EN0401 for a `&Measured`.
const PART: &str = "a `&string` can't become a `&Measured`, because it may be a part of a string";

/// The string clause of satisfaction (SPEC 4.4, A:899, XC-04): it runs at every site
/// that uses a class as an interface, over the member lookup finds.
fn satisfactions(h: &mut Harness) {
    h.case(
        "views/VI-02-structural: an argument to a `&Sizer` parameter runs the string clause",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
const k = new Keeper();
f(&k, s.slice(1, 3));
{F}{SIZER}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            assert_eq!(
                site(&r, 0),
                ("f(&k, s.slice(1, 3))", "`Keeper` is used as a `Sizer` here")
            );
            assert_eq!(
                r.diags[0].entries[0].text,
                "`Sizer.size` lets `T` stand for `string`"
            );
        },
    );
    h.case(
        "views/VI-02-inherited: the member checked is the inherited one lookup finds",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
const k = new Keeper();
f(&k, s.slice(1, 3));
{F}public interface Sizer {{ size<T extends Measured>(x: &T): isize; }}
public class Base {{
  public size<T extends Measured>(x: &T): isize {{ const m: &Measured = x; return m.length(); }}
}}
public class Keeper extends Base implements Sizer {{}}
{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            // The `implements` entry is recorded first, so the note is there.
            assert_eq!(site(&r, 0), ("Sizer", "`Keeper` is used as a `Sizer` here"));
            assert_eq!(
                r.map.loc(r.diags[0].primary.span.lo).line,
                7,
                "in `Base.size`"
            );
        },
    );
    h.case(
        "views/VI-02-bound: an inferred type argument that meets `Z extends Sizer`",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
const k = new Keeper();
g(&k, s.slice(1, 3));
private function g<Z extends Sizer>(z: &Z, v: &string): void {{ console.log(z.size(v)); }}
{SIZER}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            assert_eq!(
                site(&r, 0),
                ("g(&k, s.slice(1, 3))", "`Keeper` is used as a `Sizer` here")
            );
        },
    );
    h.case(
        "views/VI-02-bound: a written type argument, at a `new` and in a signature",
        || {
            let r = check(&format!(
                "const w = new Holder<Keeper> {{ k: new Keeper() }};
console.log(w.k.size(&new Bag()));
public class Holder<Z extends Sizer> {{ public k: Z; }}
public class Bag {{ public length(): isize {{ return 1; }} }}
{SIZER}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            assert_eq!(
                site(&r, 0).1,
                "`Keeper` is used as a `Sizer` here",
                "{}",
                r.rendered()
            );
            let r = check(&format!(
                "private function take(w: &Holder<Keeper>): isize {{ return w.k.size(&new Bag()); }}
public class Holder<Z extends Sizer> {{ public k: Z; }}
public class Bag {{ public length(): isize {{ return 1; }} }}
{SIZER}"
            ));
            // A declaration's written type is checked at its parameter, as EN0419 is.
            assert_eq!(
                site(&r, 0),
                ("w: &Holder<Keeper>", "`Keeper` is used as a `Sizer` here")
            );
        },
    );
    h.case(
        "views/S:619: an argument to a by-value `Sizer` parameter runs the string clause",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
h(new Keeper(), s.slice(1, 3));
private function h(z: Sizer, v: &string): void {{ console.log(z.size(v)); }}
{SIZER}"
            ));
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
            assert_eq!(
                site(&r, 0),
                (
                    "h(new Keeper(), s.slice(1, 3))",
                    "`Keeper` is used as a `Sizer` here"
                )
            );
        },
    );
    h.case(
        "views/S:619: one report per member and interface, at the first site",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
const k = new Keeper();
f(&k, s.slice(1, 3));
f(&k, &s);
g(&k);
private function g<Z extends Sizer>(z: &Z): void {{ console.log(z.size(&\"ab\".toString())); }}
{F}{SIZER}"
            ));
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
            assert_eq!(site(&r, 0).0, "f(&k, s.slice(1, 3))");
            // Two subclasses that inherit one member are one member.
            let r = check(&format!(
                "f(&new A(), &\"ab\".toString());
f(&new B(), &\"ab\".toString());
{F}public interface Sizer {{ size<T extends Measured>(x: &T): isize; }}
public class Base {{
  public size<T extends Measured>(x: &T): isize {{ const m: &Measured = x; return m.length(); }}
}}
public class A extends Base {{}}
public class B extends Base {{}}
{MEASURED}"
            ));
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
            assert_eq!(
                site(&r, 0),
                (
                    "f(&new A(), &\"ab\".toString())",
                    "`A` is used as a `Sizer` here"
                )
            );
        },
    );
    h.case(
        "views/S:619: a member that passes `T` on is labelled at that call in its body",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
f(&new Keeper(), s.slice(1, 3));
{F}public interface Sizer {{ size<T extends Measured>(x: &T): isize; }}
public class Keeper {{
  public size<T extends Measured>(x: &T): isize {{ return measure(x); }}
}}
private function measure<T extends Measured>(x: &T): isize {{ const m: &Measured = x; return m.length(); }}
{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `measure(x)` {PART} [this passes `T` on to `measure`, which converts it]"
                )],
                "{}",
                r.rendered()
            );
            assert_eq!(
                site(&r, 0),
                (
                    "f(&new Keeper(), s.slice(1, 3))",
                    "`Keeper` is used as a `Sizer` here"
                )
            );
        },
    );
    h.case(
        "views/S:619: a parameter bounded by a class, passed to a `&Sizer` or `Sizer` parameter",
        || {
            // `Q` meets `Sizer` through its class bound's `Keeper.size`, so the call
            // uses that member as `Sizer.size`, as `g<Z extends Sizer>` would.
            for (amp, param) in [("&", "&Sizer"), ("", "Sizer")] {
                let r = check(&format!(
                    "let s = \"hello\".toString();
h({amp}new Keeper(), s.slice(1, 3));
private function h<Q extends Keeper>(q: {amp}Q, v: &string): void {{ f(q, v); }}
private function f(z: {param}, v: &string): void {{ console.log(z.size(v)); }}
{SIZER}"
                ));
                assert_eq!(
                    shown(&r),
                    [format!(
                        "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                    )],
                    "{param}: {}",
                    r.rendered()
                );
                assert_eq!(
                    site(&r, 0),
                    ("f(q, v)", "`Q` is used as a `Sizer` here"),
                    "{param}"
                );
                let keeps =
                    SIZER.replace("const m: &Measured = x; return m.length();", "return 0;");
                compiles(&format!(
                    "let s = \"hello\".toString();
h({amp}new Keeper(), s.slice(1, 3));
private function h<Q extends Keeper>(q: {amp}Q, v: &string): void {{ f(q, v); }}
private function f(z: {param}, v: &string): void {{ console.log(z.size(v)); }}
{keeps}"
                ));
            }
        },
    );
    h.case(
        "views/S:619: a `where` clause met at a call runs the string clause",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
const h = new Holder<Keeper> {{ z: new Keeper() }};
console.log(h.run(s.slice(1, 3)));
public class Holder<Z> {{
  public z: Z;
  public run(v: &string): isize where Z extends Sizer {{ return this.z.size(v); }}
}}
{SIZER}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            assert_eq!(
                site(&r, 0),
                ("h.run(s.slice(1, 3))", "`Keeper` is used as a `Sizer` here")
            );
        },
    );
    h.case(
        "views/VI-02-bound: a written instance's bound naming a class parameter, at its arguments",
        || {
            let r = check(&format!(
                "private function take(w: &Holder<i32, Keeper2>): isize {{ return w.z.size(&new Bag(), 1); }}
public class Holder<U, Z extends Sizer2<U>> {{ public z: Z; }}
public interface Sizer2<U> {{ size<T extends Measured>(x: &T, u: U): isize; }}
public class Keeper2 {{
  public size<T extends Measured>(x: &T, u: i32): isize {{ const m: &Measured = x; return m.length(); }}
}}
public class Bag {{ public length(): isize {{ return 1; }} }}
{MEASURED}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            // `Sizer2<U>` is read at `U := i32`, which `Keeper2.size` meets.
            assert_eq!(
                site(&r, 0),
                (
                    "w: &Holder<i32, Keeper2>",
                    "`Keeper2` is used as a `Sizer2<int>` here"
                )
            );
        },
    );
    h.case(
        "views/S:619: a C22 conversion is a site, behind `&`, in a `Box` and by value",
        || {
            // `&Keeper` to `&Sizer`, then wrapped as `&Sizer | null`.
            let r = check(&format!(
                "let s = \"hello\".toString();
f(&new Keeper(), s.slice(1, 3));
private function f(z: &Sizer | null, v: &string): void {{ if (z != null) {{ console.log(z.size(v)); }} }}
{SIZER}"
            ));
            assert_eq!(r.codes(), ["EN1006", "EN0401"], "{}", r.rendered());
            assert_eq!(
                site(&r, 1),
                ("&new Keeper()", "`Keeper` is used as a `Sizer` here")
            );
            // `Box<Keeper>` to `Box<Sizer>`.
            let r = check(&format!(
                "let s = \"hello\".toString();
const k: Box<Keeper> = new Box(new Keeper());
take(k, s.slice(1, 3));
private function take(b: Box<Sizer>, v: &string): void {{ console.log(b.size(v)); }}
{SIZER}"
            ));
            assert_eq!(r.codes(), ["EN1006", "EN0401"], "{}", r.rendered());
            assert_eq!(site(&r, 1), ("k", "`Keeper` is used as a `Sizer` here"));
            // `Keeper` to the `Sizer` that `new Box<Sizer>(..)` takes by value.
            let r = check(&format!(
                "let s = \"hello\".toString();
take(new Box<Sizer>(new Keeper()), s.slice(1, 3));
private function take(b: Box<Sizer>, v: &string): void {{ console.log(b.size(v)); }}
{SIZER}"
            ));
            assert_eq!(r.codes(), ["EN1006", "EN0401"], "{}", r.rendered());
            assert_eq!(
                site(&r, 1),
                ("new Keeper()", "`Keeper` is used as a `Sizer` here")
            );
        },
    );
    h.case(
        "views/S:619: a member that satisfies two interfaces is reported for each, at one conversion",
        || {
            let r = check(&format!(
                "let s = \"hello\".toString();
const k = new Keeper();
f(&k, s.slice(1, 3));
f2(&k, s.slice(1, 3));
private function f2(z: &SizerB, v: &string): void {{ console.log(z.size(v)); }}
public interface SizerB {{ size<T extends Measured>(x: &T): isize; }}
{F}{SIZER}"
            ));
            assert_eq!(
                shown(&r),
                [format!(
                    "EN0401 `const m: &Measured = x;` {PART} [here a `&T` becomes a `&Measured`]"
                )],
                "{}",
                r.rendered()
            );
            let d = &r.diags[0];
            let sites: Vec<(&str, &str)> = d
                .secondary
                .iter()
                .map(|l| (r.map.text(l.span), l.text.as_str()))
                .collect();
            assert_eq!(
                sites,
                [
                    ("f(&k, s.slice(1, 3))", "`Keeper` is used as a `Sizer` here"),
                    ("f2(&k, s.slice(1, 3))", "`Keeper` is used as a `SizerB` here")
                ],
                "{}",
                r.rendered()
            );
            let notes: Vec<&str> = d.entries.iter().map(|e| e.text.as_str()).collect();
            assert_eq!(
                notes,
                [
                    "`Sizer.size` lets `T` stand for `string`",
                    "`SizerB.size` lets `T` stand for `string`"
                ]
            );
        },
    );
    h.case(
        "views/S:619 near miss: an overload probe that rejects a candidate keeps no record",
        || {
            // The arrow typed against the first `run` uses `Keeper` as a `Sizer` at
            // `g(z)`, but the call runs the second, whose `Keeper2.size` keeps the
            // fact; given a `string`, the call runs the first and is reported.
            let program = |n: &str| {
                format!(
                    "run((z) => {{ g(z); }}, {n});
private function run(f: (z: &Keeper) => void, n: string): void {{ f(&new Keeper()); }}
private function run(f: (z: &Keeper2) => void, n: i32): void {{ f(&new Keeper2()); }}
private function g<Z extends Sizer>(z: &Z): void {{ console.log(z.size(&new Bag())); }}
public class Keeper2 {{ public size<T extends Measured>(x: &T): isize {{ return 0; }} }}
public class Bag {{ public length(): isize {{ return 1; }} }}
{SIZER}"
                )
            };
            compiles(&program("1"));
            let r = check(&program("\"a\""));
            assert_eq!(r.codes(), ["EN0401"], "{}", r.rendered());
            assert_eq!(site(&r, 0), ("g(z)", "`Keeper` is used as a `Sizer` here"));
        },
    );
    h.case(
        "views/VI-02-structural near miss: a `size` that keeps the fact, in every form",
        || {
            let keeps = SIZER.replace("const m: &Measured = x; return m.length();", "return 0;");
            compiles(&format!(
                "let s = \"hello\".toString();
const k = new Keeper();
f(&k, s.slice(1, 3));
g(&k, s.slice(1, 3));
h(new Keeper(), s.slice(1, 3));
private function g<Z extends Sizer>(z: &Z, v: &string): void {{ console.log(z.size(v)); }}
private function h(z: Sizer, v: &string): void {{ console.log(z.size(v)); }}
{F}{keeps}"
            ));
            // A class that is never used as a `Sizer` keeps its own member's
            // business: no satisfaction, no clause.
            compiles(&format!(
                "const k = new Keeper();
console.log(k.size(&new Bag()));
public class Bag {{ public length(): isize {{ return 1; }} }}
{SIZER}"
            ));
        },
    );
}
