//! `for...of` (owner 4B; plan d.10, g.2 "Narrowing and `for...of`"; SPEC 4.8, 5.6,
//! 16; A:429-438, A:902-910; TESTING T:619-620, T:707, T:720-732): the source typed
//! once under the facts at the loop and classified by ARCHITECTURE 2.4's rules 1-6,
//! the binding's type, EN1015, the body's prescan sparing the source facts, and the
//! state after the loop joined over its `break`s.

use enrang_hir::{Body, ExprKind, Fact, ForSource, Pat, RecordKind, StmtKind, VariantIdx};
use enrang_testkit::Harness;

use crate::narrow::{
    accepts, accepts_lib, body, check, d, expect, for_sources, local_ty, no_member, rec, records,
    rejects, stmts,
};
use crate::support::{MINI_LIB, Run, fake_lib, run_with};

/// Each loop of `b`: its source as `Range`, `Path <place kind> `text`` or
/// `Once <mode> `text``, and its binding's type.
fn loops(r: &Run, b: &Body) -> Vec<(String, String)> {
    stmts(&b.root)
        .into_iter()
        .filter_map(|s| match s {
            StmtKind::ForOf { pat, source, .. } => {
                let source = match source {
                    ForSource::Range { .. } => "Range".to_owned(),
                    ForSource::Path { place } => {
                        let kind = match place.kind {
                            ExprKind::Local(_) => "Local",
                            ExprKind::Field(..) => "Field",
                            ExprKind::Deref(_) => "Deref",
                            ExprKind::NarrowedPayload(..) => "NarrowedPayload",
                            _ => "other",
                        };
                        format!("Path {kind} `{}`", r.map.text(place.span))
                    }
                    ForSource::Once { value, mode } => {
                        format!("Once {mode:?} `{}`", r.map.text(value.span))
                    }
                };
                let binding = match pat {
                    Pat::Bind(local) => r.tcx.ty_string(b.locals[*local].ty),
                    _ => "pattern".to_owned(),
                };
                Some((source, binding))
            }
            _ => None,
        })
        .collect()
}

fn l(source: &str, binding: &str) -> (String, String) {
    (source.to_owned(), binding.to_owned())
}

/// The message of EN1015 (SPEC 16).
const UNSUPPORTED: &str = "this `for...of` source is not supported yet";

pub fn register(h: &mut Harness) {
    classification(h);
    unsupported(h);
    ranges(h);
    patterns(h);
    narrowed(h);
    after(h);
}

// ---------------------------------------------------------------------------------
// Classification (A:429-438, S:1002-1010).

fn classification(h: &mut Harness) {
    h.case("forof/each source takes the first of rules 1-6 that fits, and its binding", || {
        let r = accepts(
            "public class C { public items: i64[] = []; public view(): &i64[] { unreachable(); } }
private const TABLE: i64[3] = [1, 2, 3];
public function make(): i64[] { return []; }
public function first(q: &i64[][]): &i64[] { unreachable(); }
public function f(q: i64[], r: &i64[], s: &Slice<i64>, c: C, grid: i64[][], n: i64, k: bool, rn: &i64[] | null): void {
  for (const i of 0..n) { }
  for (const x of &q) { }
  for (const x of &c.items) { }
  for (const x of &grid[0]) { }
  for (const x of &make()) { }
  for (const x of &TABLE) { }
  for (const x of r) { }
  for (const x of s) { }
  for (const x of c.view()) { }
  for (const x of first(&grid)) { }
  for (const x of k ? r : r) { }
  for (const x of rn!) { }
  for (const x of [...q]) { }
  for (const x of make()) { }
  for (const x of q) { }
}
",
        );
        assert_eq!(
            loops(&r, &body(&r, "f")),
            [
                // 1: a range.
                l("Range", "i64"),
                // 2: a leading `&` of a path, of another place, of an rvalue.
                l("Path Local `q`", "&i64"),
                l("Path Field `c.items`", "&i64"),
                l("Once Ref `&grid[0]`", "&i64"),
                l("Once Ref `&make()`", "&i64"),
                l("Once Ref `&TABLE`", "&i64"),
                // 3: a path of reference type.
                l("Path Deref `r`", "&i64"),
                l("Path Deref `s`", "&i64"),
                // 5: a reference rvalue.
                l("Once Ref `c.view()`", "&i64"),
                l("Once Ref `first(&grid)`", "&i64"),
                l("Once Ref `k ? r : r`", "&i64"),
                l("Once Ref `rn!`", "&i64"),
                // 6 and 4: an owned rvalue, an owned path.
                l("Once Owned `[...q]`", "i64"),
                l("Once Owned `make()`", "i64"),
                l("Once Owned `q`", "i64"),
            ]
        );
    });
    h.case(
        "forof/a tuple part is no path, so `&t[0]` is evaluated once (S:739)",
        || {
            let r = accepts(
                "public function f(t: [i64[], i64]): void {
  for (const x of &t[0]) { }
}
",
            );
            assert_eq!(loops(&r, &body(&r, "f")), [l("Once Ref `&t[0]`", "&i64")]);
        },
    );
    h.case("forof/a field through `this` and a `Box` is a path", || {
        let r = accepts(
            "public class C {
  public items: i64[] = [];
  public sum(): void { for (const x of &this.items) { } }
}
public function f(b: Box<C>): void {
  for (const x of &b.items) { }
}
",
        );
        assert_eq!(
            loops(&r, &body(&r, "f")),
            [l("Path Field `b.items`", "&i64")]
        );
        let sum = body(&r, "C::sum");
        assert_eq!(loops(&r, &sum), [l("Path Field `this.items`", "&i64")]);
    });
    h.case(
        "forof/a reference element binds the element itself (O7)",
        || {
            // An array of references is EN0701 in user code (R1, A:892), so the
            // sources come from library declarations, which are trusted.
            let lib: Vec<(&str, String)> = MINI_LIB
                .iter()
                .map(|&(key, text)| match key {
                    "core/prelude" => (
                        key,
                        format!(
                            "{text}public final class Refs {{\n  public items: (&i64)[];\n}}\npublic function refs(): &(&i64)[] {{ unreachable(); }}\n"
                        ),
                    ),
                    _ => (key, text.to_owned()),
                })
                .collect();
            let lib: Vec<(&str, &str)> = lib.iter().map(|(k, t)| (*k, t.as_str())).collect();
            let r = run_with(
                &[(
                    "src/main.en",
                    "public function f(h: &Refs): void {
  for (const x of &h.items) { }
  for (const x of refs()) { }
}
",
                )],
                fake_lib(&lib),
                "x86_64-linux",
            );
            r.clean();
            assert_eq!(
                loops(&r, &body(&r, "f")),
                [l("Path Field `h.items`", "&i64"), l("Once Ref `refs()`", "&i64")]
            );
        },
    );
    h.case(
        "forof/a fixed array of Copy elements is copied by an owned loop (T:619)",
        || {
            let r = accepts(
                "public function f(a: i32[3]): void {
  for (const x of a) { }
  for (const x of &a) { }
}
",
            );
            assert_eq!(
                loops(&r, &body(&r, "f")),
                [l("Once Owned `a`", "int"), l("Path Local `a`", "&int")]
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// EN1015 (SPEC 16, S:1009, S:1138, S:3466; T:619-620, T:707).

fn unsupported(h: &mut Harness) {
    h.case("forof/EN1015 at the `in` of `for...in`, with a fix-it to `of`", || {
        let r = rejects(
            "public function f(xs: i64[]): void {
  for (const k in xs) { }
}
",
            &[d("EN1015", "2:16", "in", UNSUPPORTED)],
        );
        let diag = &r.diags[0];
        assert_eq!(diag.primary.text, "`for...in` walks an object's keys");
        assert_eq!(
            diag.entries[0].text,
            "an Enrang object has no keys to walk; `for...of` goes over the elements of an array"
        );
        assert_eq!(diag.helps.len(), 1);
        assert_eq!(diag.helps[0].message, "to loop over an array's elements, write `of`");
        assert_eq!(diag.helps[0].edits[0].replacement, "of");
    });
    h.case(
        "forof/EN1015 for a `Box<T[]>`, with a `&*b` help (T:707)",
        || {
            let r = rejects(
                "public function f(b: Box<i64[]>): void {
  for (const x of b) { }
  for (const x of &b) { }
}
",
                &[
                    d("EN1015", "2:19", "b", UNSUPPORTED),
                    d("EN1015", "3:19", "&b", UNSUPPORTED),
                ],
            );
            // The label names the source as written, its `&` included.
            assert_eq!(r.diags[0].primary.text, "this is `Box<i64[]>`");
            assert_eq!(r.diags[1].primary.text, "this is `&Box<i64[]>`");
            for diag in &r.diags {
                assert_eq!(diag.helps.len(), 1);
                assert_eq!(
                    diag.helps[0].message,
                    "loop over the array in the box: `&*b`"
                );
                assert_eq!(diag.helps[0].edits[0].replacement, "&*b");
            }
        },
    );
    h.case("forof/EN1015 for a string, owned or borrowed, with SPEC 16's help (T:620)", || {
        let r = rejects(
            "public function f(s: string): void {
  for (const c of \"abc\") { }
  for (const c of &s) { }
}
",
            &[
                d("EN1015", "2:19", "\"abc\"", UNSUPPORTED),
                d("EN1015", "3:19", "&s", UNSUPPORTED),
            ],
        );
        assert_eq!(r.diags[0].primary.text, "this is `string`");
        assert_eq!(r.diags[1].primary.text, "this is `&string`");
        for diag in &r.diags {
            assert_eq!(
                diag.entries[0].text,
                "a string is UTF-8 bytes, and a loop over it would have to choose bytes or code points"
            );
        }
        // SPEC 16's `byteAt` for `string`, as a sentence naming the call
        // (review 5A: not a capitalised fragment).
        assert_eq!(
            r.diags[0].helps[0].message,
            "loop over its indexes and read each byte with `\"abc\".byteAt(i)`"
        );
        assert_eq!(
            r.diags[1].helps[0].message,
            "loop over its indexes and read each byte with `s.byteAt(i)`"
        );
    });
    h.case("forof/EN1015 for a user type and a number", || {
        let r = rejects(
            "public class U { public n: i64 = 0; }
public function f(u: U, r: &U): void {
  for (const x of u) { }
  for (const x of r) { }
  for (const x of 5) { }
}
",
            &[
                d("EN1015", "3:19", "u", UNSUPPORTED),
                d("EN1015", "4:19", "r", UNSUPPORTED),
                d("EN1015", "5:19", "5", UNSUPPORTED),
            ],
        );
        assert_eq!(r.diags[0].primary.text, "this is `U`");
        assert_eq!(r.diags[1].primary.text, "this is `&U`");
        assert_eq!(
            r.diags[0].helps[0].message,
            "Expose an array, or a `get(i)` and `length()`"
        );
    });
    h.case(
        "forof/EN1015 for an owned `T[N]` of non-Copy elements, with a `T[]` help (T:619)",
        || {
            let r = rejects(
                "public class D { public n: i64 = 0; }
public function f(a: D[3]): void {
  for (const x of a) { }
  for (const x of &a) { }
}
",
                &[d("EN1015", "3:19", "a", UNSUPPORTED)],
            );
            let diag = &r.diags[0];
            assert_eq!(diag.primary.text, "this is `D[3]`");
            assert_eq!(
                diag.entries[0].text,
                "a loop takes a fixed array by copying each element, and `D` is not Copy"
            );
            assert_eq!(
                diag.helps[0].message,
                "use a `D[]` for owned non-Copy elements, or borrow it: `&a`"
            );
        },
    );
    h.case(
        "forof/the binding of an unsupported source is an error, and nothing cascades",
        || {
            let r = check(
                "public function f(s: string): void {
  for (const c of s) { const n: i64 = c; c.foo(); }
}
",
            );
            assert_eq!(r.codes(), ["EN1015"], "{}", r.rendered());
        },
    );
}

// ---------------------------------------------------------------------------------
// Ranges (S:1010).

fn ranges(h: &mut Harness) {
    h.case(
        "forof/a range binds its bounds' integer type, and `let` may reassign it",
        || {
            let r = accepts(
                "public function f(n: u8): void {
  for (let i of 0..n) { i = 5; }
  for (const j of 0..10) { }
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "i"), "u8");
            assert_eq!(local_ty(&r, &b, "j"), "int");
        },
    );
    h.case("forof/a range's bounds are one integer type", || {
        rejects(
            "public function f(a: i64, b: u8): void {
  for (const i of a..b) { }
  for (const x of 0.5..2.5) { }
}
",
            &[
                d(
                    "EN0401",
                    "2:22",
                    "b",
                    "mismatched types: expected `i64`, found `u8`",
                ),
                d("EN0403", "3:19", "0.5", "`..` needs integers, found `f64`"),
            ],
        );
    });
}

// ---------------------------------------------------------------------------------
// Patterns as bindings (S:996).

fn patterns(h: &mut Harness) {
    h.case(
        "forof/a pattern over a borrowed source binds references (S:996, T:757)",
        || {
            let r = accepts(
                "public class P { public name: string = \"\"; public age: i64 = 0; }
public function f(pairs: [i64, P][], people: P[]): void {
  for (const [i, { name }] of &pairs) { }
  for (const { name: who, age } of &people) { }
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "i"), "&i64");
            assert_eq!(local_ty(&r, &b, "name"), "&string");
            assert_eq!(local_ty(&r, &b, "who"), "&string");
            assert_eq!(local_ty(&r, &b, "age"), "&i64");
        },
    );
    h.case(
        "forof/a pattern over an owned source binds the parts",
        || {
            let r = accepts(
                "public function f(pairs: [i64, bool][]): void {
  for (const [n, ok] of pairs) { }
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "n"), "i64");
            assert_eq!(local_ty(&r, &b, "ok"), "bool");
        },
    );
    h.case(
        "forof/a tuple pattern over array elements is EN1042",
        || {
            rejects(
                "public function f(rows: i64[][]): void {
  for (const [a, b] of &rows) { }
}
",
                &[d(
                    "EN1042",
                    "2:14",
                    "[a, b]",
                    "array destructuring is not supported yet",
                )],
            );
        },
    );
}

// ---------------------------------------------------------------------------------
// Narrowed sources and the loop's facts (S:745, A:902-910, T:724-732).

const UNDER_P: &str = "public function f(p: string[] | null, c: bool): void {
  if (p != null) {
";

/// `f` with `body` under `p != null`.
fn under_p(body: &str) -> String {
    format!("{UNDER_P}{body}  }}\n}}\n")
}

fn narrowed(h: &mut Harness) {
    h.case(
        "forof/a narrowed source is typed once, and its fact survives the body's prescan",
        || {
            let r = accepts(&under_p(
                "    for (const x of &p) { console.log(p.length()); p = null; break; }\n",
            ));
            let b = body(&r, "f");
            let sources = for_sources(&b);
            let [ForSource::Path { place }] = sources.as_slice() else {
                panic!("{sources:?}");
            };
            let ExprKind::NarrowedPayload(inner, VariantIdx(1), fact) = &place.kind else {
                panic!("{place:?}");
            };
            assert!(matches!(inner.kind, ExprKind::Local(_)));
            assert_eq!(r.map.text(b.facts[*fact].span), "p != null");
            assert_eq!(b.facts[*fact].fact, Fact::NonNull);
            assert_eq!(local_ty(&r, &b, "x"), "&string");
        },
    );
    h.case(
        "forof/the body's prescan kills every other fact it changes",
        || {
            rejects(
                "public function f(p: string[] | null, q: string | null): void {
  if (p != null && q != null) { for (const x of &p) { q.length(); q = null; } }
}
",
                &[d(
                    "EN0303",
                    "2:57",
                    "length",
                    &no_member("string | null", "length"),
                )],
            );
        },
    );
    h.case("forof/a change of a held source passes typing, for phase 3 (S:745)", || {
        accepts(&under_p(
            "    for (const x of &p) { p = null; }\n    for (const x of &p) { p = null; break; }\n",
        ));
    });
    h.case(
        "forof/a move, an arrow's write, a write before `continue` and a push pass typing (T:723, T:731)",
        || {
            accepts(
                "public function take(xs: string[]): void { }
public function run(f: () => void): void { }
public function f(p: string[] | null, c: bool): void {
  if (p != null) { for (const x of &p) { take(p); } }
  if (p != null) { for (const x of &p) { run(() => { p = null; }); } }
  if (p != null) { for (const x of &p) { if (c) { p = null; continue; } } }
  if (p != null) { for (const x of &p) { p.push(\"a\"); } }
}
",
            );
        },
    );
    h.case(
        "forof/a reference to a prefix of the source in the body is recorded (T:720)",
        || {
            let r = accepts(
                "public class H { public items: string[] | null = null; }
public function wipe(h: &H): void { }
public function f(h: &H): void {
  if (h.items != null) { for (const s of &h.items) { wipe(h); } }
}
",
            );
            assert_eq!(
                records(&r, &body(&r, "f")),
                [rec(RecordKind::CallArg, "h", "h.items != null")]
            );
        },
    );
    h.case(
        "forof/an evaluate-once source uses its fact before any kill (T:729, T:730)",
        || {
            accepts(
                "public function f(p: i64[] | null): void {
  if (p != null) { for (const x of [...p]) { p = null; } }
}
public function g(): void {
  let p: i64[] | null = [1, 2, 3];
  if (p != null) { for (const x of &p) { *x = 1; } }
}
public class T { public kids(): &i64[] { unreachable(); } }
public function h(o: T | null): void {
  if (o != null) { for (const x of o.kids()) { o = null; } }
}
",
            );
        },
    );
    h.case(
        "forof/an owned path source moves it, which kills its facts",
        || {
            rejects(
                "public class H { public items: i64[] | null = null; }
public function f(h: H): void {
  if (h.items != null) { for (const x of h.items) { } h.items.length(); }
}
",
                &[d(
                    "EN0303",
                    "3:63",
                    "length",
                    &no_member("i64[] | null", "length"),
                )],
            );
        },
    );
    h.case("forof/`S2-24-narrowed`'s three programs pass typing (T:732)", || {
        accepts_lib(
            "public class Bag { public items: i64[] | null = null; }
public function bump(xs?: &Slice<i64>): void { if (xs != null) { for (const x of xs) { *x += 1; } } }
public function f(b: Bag): void {
  b.items = [1, 5, 3, 7];
  let keep: &i64 | null = null;
  if (b.items != null) { for (const x of &b.items) { if (*x > 2) { keep = x; } } }
  if (keep != null) { *keep = 0; }
  console.log(b.items);
  let p: i64[] | null = [1, 2, 3];
  if (p != null) { for (const x of &p) { *x += 1; } }
  console.log(p);
  let v: i64[] = [1, 2, 3];
  bump(v.slice(0, 3));
  console.log(v);
}
",
        );
    });
    h.case("forof/a narrowed reference source is a path through its `Deref`", || {
        let r = accepts_lib(
            "public function bump(xs?: &Slice<i64>): void { if (xs != null) { for (const x of xs) { *x += 1; } } }
",
        );
        assert_eq!(
            loops(&r, &body(&r, "bump")),
            [l("Path Deref `xs`", "&i64")]
        );
    });
}

// ---------------------------------------------------------------------------------
// The state after the loop (A:908, T:724-728).

fn after(h: &mut Harness) {
    let len = no_member("string[] | null", "length");
    let mismatch = "mismatched types: expected `&string[]`, found `&(string[] | null)`";
    let (l1, l2) = (len.clone(), len.clone());
    h.case(
        "forof/a `break` without the fact loses it after the loop (T:724)",
        move || {
            rejects(
                &under_p(
                    "    for (const x of &p) { p = null; break; }\n    console.log(p.length());\n",
                ),
                &[d("EN0303", "4:19", "length", &l1)],
            );
            let r = rejects(
                &under_p(
                    "    for (const x of &p) { p = null; break; }\n    const r: &string[] = &p;\n",
                ),
                &[d("EN0401", "4:26", "&p", mismatch)],
            );
            assert_eq!(r.diags[0].primary.text, "this is `&(string[] | null)`");
        },
    );
    h.case("forof/a `break outer` records its state for `outer` (T:725)", move || {
        rejects(
            &under_p(
                "    outer: for (const a of &p) { for (const x of &p) { p = null; break outer; } }\n    console.log(p.length());\n",
            ),
            &[d("EN0303", "4:19", "length", &l2)],
        );
        rejects(
            &under_p(
                "    outer: for (const a of &p) { for (const x of &p) { p = null; break outer; } }\n    const r: &string[] = &p;\n",
            ),
            &[d("EN0401", "4:26", "&p", mismatch)],
        );
    });
    h.case("forof/one `break` without the fact is enough (T:726)", move || {
        rejects(
            &under_p(
                "    for (const x of &p) { if (c) { p = null; break; } }\n    console.log(p.length());\n",
            ),
            &[d("EN0303", "4:19", "length", &len)],
        );
        rejects(
            &under_p(
                "    for (const x of &p) { p = null; if (p == null) { break; } }\n    console.log(p.length());\n",
            ),
            &[d("EN0303", "4:19", "length", &len)],
        );
    });
    h.case(
        "forof/a source fact is not checked at the back edges (T:727)",
        || {
            accepts(&under_p(
                "    outer: for (const a of &p) { while (c) { p = null; break outer; } }\n",
            ));
        },
    );
    h.case(
        "forof/every `break` holding the fact, a `return`, an inner `break` keep it (T:728)",
        || {
            accepts(&under_p(
                "    for (const x of &p) { if (c) { break; } }
    console.log(p.length());
    for (const x of &p) { if (c) { p = null; return; } }
    console.log(p.length());
    outer: for (const a of &p) { for (const x of &p) { if (c) { p = null; break outer; } } console.log(p.length()); }
",
            ));
        },
    );
    h.case(
        "forof/the state after an unbroken loop is its head's",
        || {
            let r = check(&under_p(
                "    for (const x of &p) { console.log(x); }\n    console.log(p.length());\n",
            ));
            expect(&r, &[]);
        },
    );
}
