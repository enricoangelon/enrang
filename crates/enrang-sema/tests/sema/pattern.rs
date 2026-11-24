//! Destructuring (owner 4B; plan d.11, g.2 "Patterns"; SPEC 3.3, 4.7 item 7, 5.6;
//! A:355, A:882; TESTING T:753-758): object and tuple patterns at any depth, the
//! binding mode the source sets (a reference gives `&F`, an owned value `F`), the
//! expected tuple type a tuple pattern gives its right side, EN1042 for a tuple
//! pattern over an array, EN0506 for a value that may not match, fields found by
//! name, and the moves and records a pattern makes.

use enrang_hir::{BindingMode, RecordKind, StmtKind};
use enrang_testkit::Harness;

use crate::narrow::{accepts, body, check, d, local_ty, no_member, rec, records, rejects, stmts};
use crate::support::Run;

/// The message of EN1042 (SPEC 16).
const ARRAYS: &str = "array destructuring is not supported yet";

/// The mode of each `Destructure` of function `f`, in order.
fn modes(r: &Run, f: &str) -> Vec<BindingMode> {
    let b = body(r, f);
    stmts(&b.root)
        .into_iter()
        .filter_map(|s| match s {
            StmtKind::Destructure { mode, .. } => Some(*mode),
            _ => None,
        })
        .collect()
}

const PERSON: &str = "public class Pos { public x: i64 = 0; public y: i64 = 0; }
public class Person { public name: string = \"\"; public age: i64 = 0; public pos: Pos; public scores: [i64, i64] = [10, 20]; }
";

pub fn register(h: &mut Harness) {
    tuples(h);
    objects(h);
    arrays(h);
    refutable(h);
    fields(h);
    flow(h);
    review(h);
}

// ---------------------------------------------------------------------------------
// Tuple patterns (S:735 item 7).

fn tuples(h: &mut Harness) {
    h.case(
        "pattern/a tuple pattern takes a returned tuple apart",
        || {
            let r = accepts(
                "public function minMax(xs: &i64[]): [i64, i64] { return [0, 1]; }
public function f(xs: i64[]): i64 {
  const [lo, hi] = minMax(&xs);
  return hi - lo;
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "lo"), "i64");
            assert_eq!(local_ty(&r, &b, "hi"), "i64");
            assert_eq!(modes(&r, "f"), [BindingMode::Owned]);
        },
    );
    h.case(
        "pattern/a tuple pattern gives its right side an expected tuple type (WD-5)",
        || {
            let r = accepts(
                "public function f(): void {
  let a = \"x\" + \"\";
  let b = \"y\" + \"\";
  [a, b] = [b, a];
  const [p, q] = [1, 2];
  let m = 1;
  let n = 2;
  [m, n] = [n, m];
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "a"), "string");
            assert_eq!(local_ty(&r, &b, "p"), local_ty(&r, &b, "m"));
            assert_eq!(local_ty(&r, &b, "q"), local_ty(&r, &b, "n"));
        },
    );
    h.case(
        "pattern/a tuple pattern needs a tuple of as many parts",
        || {
            let r = rejects(
                "public function f(t: [i64, i64, i64]): void {
  const [u, v] = t;
  const [m, n] = 5;
}
",
                &[
                    d(
                        "EN0401",
                        "2:9",
                        "[u, v]",
                        "mismatched types: expected a tuple of 2 parts, found `[i64, i64, i64]`",
                    ),
                    d(
                        "EN0401",
                        "3:9",
                        "[m, n]",
                        "mismatched types: expected a tuple, found `int`",
                    ),
                ],
            );
            assert_eq!(r.diags[0].primary.text, "this pattern has 2 parts");
        },
    );
    h.case(
        "pattern/a tuple pattern of a parameter binds its parts",
        || {
            let r = accepts(
                "public function f([a, b]: [i64, bool]): i64 { if (b) { return a; } return 0; }
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "a"), "i64");
            assert_eq!(local_ty(&r, &b, "b"), "bool");
        },
    );
    h.case("pattern/a `let` pattern declares `let` bindings", || {
        let r = accepts(
            "public function f(): void {
  let [a, b] = [1, 2];
  const [c, d] = [3, 4];
}
",
        );
        let b = body(&r, "f");
        let mutable: Vec<(String, bool)> = b
            .locals
            .iter()
            .filter_map(|l| Some((l.name?.as_str().to_owned(), l.mutable)))
            .collect();
        assert_eq!(
            mutable,
            [
                ("a".to_owned(), true),
                ("b".to_owned(), true),
                ("c".to_owned(), false),
                ("d".to_owned(), false),
            ]
        );
    });
}

// ---------------------------------------------------------------------------------
// Object patterns and the binding mode (S:989-996).

fn objects(h: &mut Harness) {
    h.case(
        "pattern/a reference source binds a reference to each field",
        || {
            let r = accepts(&format!(
                "{PERSON}public function f(ada: Person, p: &Person): void {{
  const {{ name: who, age }} = &ada;
  const {{ name }} = p;
}}
"
            ));
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "who"), "&string");
            assert_eq!(local_ty(&r, &b, "age"), "&i64");
            assert_eq!(local_ty(&r, &b, "name"), "&string");
            assert_eq!(modes(&r, "f"), [BindingMode::Ref, BindingMode::Ref]);
        },
    );
    h.case(
        "pattern/an owned place or rvalue binds each field's value",
        || {
            let r = accepts(&format!(
                "{PERSON}public function make(): Person {{ unreachable(); }}
public function f(ada: Person): void {{
  const {{ age }} = ada;
  const {{ name }} = make();
}}
"
            ));
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "age"), "i64");
            assert_eq!(local_ty(&r, &b, "name"), "string");
            assert_eq!(modes(&r, "f"), [BindingMode::Owned, BindingMode::Owned]);
        },
    );
    h.case(
        "pattern/patterns nest, with the mode at every level (S:996, T:757)",
        || {
            let r = accepts(&format!(
                "{PERSON}public function f(ada: Person): void {{
  const {{ name: who, pos: {{ x, y }} }} = &ada;
  const {{ scores: [first, second] }} = ada;
}}
"
            ));
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "who"), "&string");
            assert_eq!(local_ty(&r, &b, "x"), "&i64");
            assert_eq!(local_ty(&r, &b, "y"), "&i64");
            assert_eq!(local_ty(&r, &b, "first"), "i64");
            assert_eq!(local_ty(&r, &b, "second"), "i64");
        },
    );
    h.case(
        "pattern/a part that is a reference binds that reference (O7)",
        || {
            let r = accepts(
                "public function f(t: [&i64, i64]): void {
  const [a, b] = &t;
  const [c, e] = t;
}
",
            );
            let b = body(&r, "f");
            assert_eq!(local_ty(&r, &b, "a"), "&i64");
            assert_eq!(local_ty(&r, &b, "b"), "&i64");
            assert_eq!(local_ty(&r, &b, "c"), "&i64");
            assert_eq!(local_ty(&r, &b, "e"), "i64");
        },
    );
    h.case("pattern/a field is found through a `Box`", || {
        let r = accepts(&format!(
            "{PERSON}public function f(b: Box<Person>): void {{
  const {{ age }} = &b;
}}
"
        ));
        assert_eq!(local_ty(&r, &body(&r, "f"), "age"), "&i64");
    });
}

// ---------------------------------------------------------------------------------
// EN1042 (S:390, S:735, S:996; T:753-758).

fn arrays(h: &mut Harness) {
    h.case("pattern/a tuple pattern over `T[]` or `T[N]` is EN1042 (T:753)", || {
        let r = rejects(
            "public function f(xs: i64[], ys: i64[3]): void {
  const [a, r] = xs;
  const [b, s] = ys;
  let c = 0;
  let e = 0;
  [c, e] = xs;
  [c, e] = ys;
}
",
            &[
                d("EN1042", "2:9", "[a, r]", ARRAYS),
                d("EN1042", "3:9", "[b, s]", ARRAYS),
                d("EN1042", "6:3", "[c, e]", ARRAYS),
                d("EN1042", "7:3", "[c, e]", ARRAYS),
            ],
        );
        let diag = &r.diags[0];
        assert_eq!(diag.primary.text, "the value is `i64[]`, an array");
        assert_eq!(
            diag.entries[0].text,
            "an array's length is known only when the program runs, so a pattern can't name its elements"
        );
        assert_eq!(diag.helps[0].message, "Index the array, or return a tuple");
        assert_eq!(r.diags[1].primary.text, "the value is `i64[3]`, an array");
    });
    h.case(
        "pattern/EF-09: EN1042 at `[c, d]` and EN0401 at `5`; `pair` compiles (T:754)",
        || {
            rejects(
                "public class H { public pair: [i64, i64] = [0, 0]; public list: i64[] = []; }
public function f(h: H): void {
  const { pair: [a, b] } = h;
  const { list: [c, d] } = h;
  const bad: string = 5;
}
",
                &[
                    d("EN1042", "4:17", "[c, d]", ARRAYS),
                    d(
                        "EN0401",
                        "5:23",
                        "5",
                        "mismatched types: expected `string`, found `int`",
                    ),
                ],
            );
        },
    );
    h.case(
        "pattern/EN1042 at any depth and through a reference (T:758)",
        || {
            rejects(
                "public class H { public list: i64[] = []; }
public function f(h: H, xs: i64[], t: [i64[], i64]): void {
  const { list: [a, b] } = h;
  const [c, e] = &xs;
  const [[g, k], m] = t;
  let u = 0;
  let v = 0;
  let w = 0;
  [[u, v], w] = t;
}
",
                &[
                    d("EN1042", "3:17", "[a, b]", ARRAYS),
                    d("EN1042", "4:9", "[c, e]", ARRAYS),
                    d("EN1042", "5:10", "[g, k]", ARRAYS),
                    d("EN1042", "9:4", "[u, v]", ARRAYS),
                ],
            );
        },
    );
    h.case("pattern/a tuple pattern over a view is EN1042", || {
        rejects(
            "public function f(s: &Slice<i64>): void {
  const [a, b] = s;
}
",
            &[d("EN1042", "2:9", "[a, b]", ARRAYS)],
        );
    });
}

// ---------------------------------------------------------------------------------
// EN0506 (plan d.11, choice).

fn refutable(h: &mut Harness) {
    h.case("pattern/a nullable source is EN0506, test it first", || {
        let r = rejects(
            "public class P { public x: i64 = 0; }
public function f(p: P | null, t: [i64, i64] | null): void {
  const { x } = p;
  const [a, b] = t;
}
",
            &[
                d(
                    "EN0506",
                    "3:9",
                    "{ x }",
                    "this pattern can't destructure a `P | null`: test it first",
                ),
                d(
                    "EN0506",
                    "4:9",
                    "[a, b]",
                    "this pattern can't destructure a `[i64, i64] | null`: test it first",
                ),
            ],
        );
        assert_eq!(r.diags[0].primary.text, "it may be `null`");
    });
    h.case(
        "pattern/an enum or `Result` source is EN0506, match it first",
        || {
            let r = rejects(
                "public enum Shape { Circle { r: f64 }, Empty }
public function f(s: Shape, r: Result<i64>): void {
  const { r: radius } = s;
  const { value } = r;
}
",
                &[
                    d(
                        "EN0506",
                        "3:9",
                        "{ r: radius }",
                        "this pattern can't destructure a `Shape`: match it first",
                    ),
                    d(
                        "EN0506",
                        "4:9",
                        "{ value }",
                        "this pattern can't destructure a `Result<i64>`: match it first",
                    ),
                ],
            );
            assert_eq!(r.diags[0].primary.text, "it may hold another case");
        },
    );
    h.case(
        "pattern/a narrowed nullable destructures as its payload",
        || {
            let r = accepts(
                "public class P { public x: i64 = 0; }
public function f(p: P | null): i64 {
  if (p != null) { const { x } = &p; return *x; }
  return 0;
}
",
            );
            assert_eq!(local_ty(&r, &body(&r, "f"), "x"), "&i64");
        },
    );
}

// ---------------------------------------------------------------------------------
// Fields by name (plan d.11).

fn fields(h: &mut Harness) {
    h.case(
        "pattern/an unknown field is EN0303, a hidden one EN0308, a method EN0303",
        || {
            rejects(
            "public class H { public n: i64 = 0; private secret: i64 = 0; public m(): void { } }
public function f(h: H): void {
  const { nope } = h;
  const { secret } = h;
  const { m } = h;
}
",
            &[
                d("EN0303", "3:11", "nope", &no_member("H", "nope")),
                d("EN0308", "4:11", "secret", "`secret` is private to `H`"),
                d("EN0303", "5:11", "m", "`H` has no field `m`"),
            ],
        );
        },
    );
    h.case(
        "pattern/the names of a rejected pattern are declared, and nothing cascades",
        || {
            let r = check(
                "public function f(xs: i64[]): void {
  const [a, b] = xs;
  const n: string = a;
  b.foo();
}
",
            );
            assert_eq!(r.codes(), ["EN1042"], "{}", r.rendered());
        },
    );
}

// ---------------------------------------------------------------------------------
// Moves and records (S:742).

fn flow(h: &mut Harness) {
    h.case(
        "pattern/a part moved out of a path kills the facts on it",
        || {
            rejects(
            "public class H { public items: string | null = null; public n: i64 | null = null; }
public function f(h: H): void {
  if (h.n != null) { const { n } = h; h.n + 1; }
  if (h.items != null) { const { items } = h; h.items.length(); }
}
",
            &[d(
                "EN0303",
                "4:55",
                "length",
                &no_member("string | null", "length"),
            )],
        );
        },
    );
    h.case(
        "pattern/a reference source is a `Binding` record against the facts below it",
        || {
            let r = accepts(
                "public class H { public items: string | null = null; }
public function f(h: &H): void {
  if (h.items != null) { const { items } = h; h.items.length(); }
}
",
            );
            assert_eq!(
                records(&r, &body(&r, "f")),
                [rec(RecordKind::Binding, "h", "h.items != null")]
            );
        },
    );
}

/// Stage 6's review: the arity message counts parts in the singular too.
fn review(h: &mut Harness) {
    h.case(
        "pattern/a one-part pattern over a pair: `a tuple of 1 part`",
        || {
            rejects(
                "public function g(t: [i64, string]): void { const [m2] = t; }\n",
                &[d(
                    "EN0401",
                    "1:51",
                    "[m2]",
                    "mismatched types: expected a tuple of 1 part, found `[i64, string]`",
                )],
            );
        },
    );
}
