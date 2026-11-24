//! The sema suite's cases for phase 4's size check (owner 4F; plan d.17, g.2; SPEC
//! 11 S:1628, TESTING T:615-616): EN0435 for a type or static larger than the
//! target's `isize.MAX`, a `T[N]` with `N` above it, and a frame, counted as the sum
//! of its locals, above `2^31 - 1` bytes.

use enrang_diag::{DiagCtx, Severity};
use enrang_sema::check_sizes;
use enrang_testkit::Harness;

use crate::consteval::from_source::{diag, diags, src_on};
use crate::support::Run;

/// The program of `text` on `target` through phases 2 and 4: phase 2 must pass,
/// and the run's diagnostics are phase 4's.
fn phase4(target: &str, text: &str) -> Run {
    let r = src_on(target, text);
    r.clean();
    let mut dcx = DiagCtx::new();
    let passed = check_sizes(r.program.as_ref().expect("checked"), &r.tcx, &mut dcx).is_ok();
    let diags = dcx.take();
    assert_eq!(
        passed,
        diags.iter().all(|d| d.severity != Severity::Error),
        "{diags:?}"
    );
    Run { diags, ..r }
}

/// Asserts that `text` on `target` gives exactly `want` in phase 4.
fn sizes(target: &str, text: &str, want: &[[String; 4]]) {
    let r = phase4(target, text);
    assert_eq!(diags(&r), want, "{target}: {text}\n{}", r.rendered());
}

const I386: &str = "i386-linux";
const X86_64: &str = "x86_64-linux";

/// EN0435's message and label for a type too large on `i386` (plan e's head): its
/// bytes above `isize.MAX`.
fn big_on_i386(at: &str, ty: &str) -> [String; 4] {
    diag(
        "EN0435",
        at,
        &format!("`{ty}` is too large for `i386-linux`"),
        "it takes more than `isize.MAX` bytes (2147483647)",
    )
}

/// The same for a `T[N]` whose `N` itself is above `isize.MAX` on `i386`.
fn many_on_i386(at: &str, ty: &str, n: &str) -> [String; 4] {
    diag(
        "EN0435",
        at,
        &format!("`{ty}` is too large for `i386-linux`"),
        &format!("it has {n} elements, more than `isize.MAX` (2147483647)"),
    )
}

pub fn register(h: &mut Harness) {
    h.case(
        "sizes/`u8[3000000000]` is too large on `i386` and fits on `x86_64` (S:1628)",
        || {
            let text = "private unsafe let big: u8[3000000000];\n";
            let r = phase4(I386, text);
            assert_eq!(
                r.rendered(),
                "error[EN0435]: `u8[3000000000]` is too large for `i386-linux`
 --> src/main.en:1:20
  |
1 | private unsafe let big: u8[3000000000];
  |                    ^^^ it has 3000000000 elements, more than `isize.MAX` (2147483647)
  |
  = explain: run `enrang explain EN0435`

error: aborting due to 1 previous error
"
            );
            sizes(X86_64, text, &[]);
        },
    );
    h.case(
        "sizes/`u64[536870912]` on `i386`, whose size would wrap to 0 (T:615)",
        || {
            sizes(
                I386,
                "private unsafe let wraps: u64[536870912];\n",
                &[big_on_i386("1:20", "u64[536870912]")],
            );
        },
    );
    h.case(
        "sizes/WD-4's static rows: `u64[268435455]` compiles on `i386`, `u64[268435456]` is EN0435 (T:616)",
        || {
            sizes(I386, "private unsafe let fits: u64[268435455];\n", &[]);
            sizes(
                I386,
                "private unsafe let over: u64[268435456];\n",
                &[big_on_i386("1:20", "u64[268435456]")],
            );
        },
    );
    h.case(
        "sizes/a `T[N]` with `N` above `isize.MAX` is EN0435 whatever `T` is",
        || {
            sizes(
                X86_64,
                "private unsafe let many: bool[9223372036854775808];\n",
                &[diag(
                    "EN0435",
                    "1:20",
                    "`bool[9223372036854775808]` is too large for `x86_64-linux`",
                    "it has 9223372036854775808 elements, more than `isize.MAX` (9223372036854775807)",
                )],
            );
            sizes(
                I386,
                "private unsafe let many: bool[2147483648];\n",
                &[diag(
                    "EN0435",
                    "1:20",
                    "`bool[2147483648]` is too large for `i386-linux`",
                    "it has 2147483648 elements, more than `isize.MAX` (2147483647)",
                )],
            );
        },
    );
    h.case(
        "sizes/a field, a parameter, a result, a constant and a class as a whole",
        || {
            sizes(
                I386,
                "public class Big {
  public a: u8[2000000000];
  public b: u8[2000000000];
}
public class Holder {
  public c: u8[3000000000];
}
public function take(x: &u8[3000000000][]): void { }
public function give(): u8[3000000000][] { return []; }
private const N: usize = 3000000000;
private const E: u8[N][0] = [];
",
                &[
                    big_on_i386("1:14", "Big"),
                    many_on_i386("6:3", "u8[3000000000]", "3000000000"),
                    many_on_i386("8:22", "u8[3000000000]", "3000000000"),
                    many_on_i386("9:17", "u8[3000000000]", "3000000000"),
                    many_on_i386("11:15", "u8[3000000000]", "3000000000"),
                ],
            );
        },
    );
    h.case(
        "sizes/a class too large is reported where it is declared, not at each use",
        || {
            sizes(
                I386,
                "public class Huge { public a: u8[3000000000]; }
public function f(h: &Huge, hs: Huge[]): &Huge { return h; }
public class User { public h: Huge | null = null; }
",
                &[many_on_i386("1:21", "u8[3000000000]", "3000000000")],
            );
        },
    );
    h.case("sizes/a tuple or an enum too large as a whole", || {
        sizes(
            I386,
            "public function f(pair: &[u8[2000000000], u8[2000000000]]): void { }
public enum Message { Small, Bulk { a: u8[2000000000], b: u8[2000000000] } }
",
            &[
                big_on_i386("1:19", "[u8[2000000000], u8[2000000000]]"),
                big_on_i386("2:13", "Message"),
            ],
        );
    });
    h.case(
        "sizes/a 3 GB local on `x86_64` passes its type and not the frame (S:1628)",
        || {
            let r = phase4(
                X86_64,
                "public function f(): void {\n  const big: u8[3000000000] = [0; 3000000000];\n}\n",
            );
            assert_eq!(
                r.rendered(),
                "error[EN0435]: the stack frame of `f` is too large for `x86_64-linux`
 --> src/main.en:2:9
  |
2 |   const big: u8[3000000000] = [0; 3000000000];
  |         ^^^ `big` takes it past 2147483647 bytes
  |
  = explain: run `enrang explain EN0435`

error: aborting due to 1 previous error
"
            );
            // On `i386` the type itself is too large, reported once.
            sizes(
                I386,
                "public function f(): void {\n  const big: u8[3000000000] = [0; 3000000000];\n}\n",
                &[many_on_i386("2:9", "u8[3000000000]", "3000000000")],
            );
        },
    );
    for target in [I386, X86_64] {
        h.case(
            format!("sizes/locals of exactly `2^31 - 1` bytes fit, one more is EN0435, on {target}"),
            move || {
                sizes(
                    target,
                    "public function f(): void {\n  const a: u8[2147483646] = [0; 2147483646];\n  const b: u8[1] = [0];\n}\n",
                    &[],
                );
                sizes(
                    target,
                    "public function f(): void {\n  const a: u8[2147483646] = [0; 2147483646];\n  const b: u8[2] = [0, 0];\n}\n",
                    &[diag(
                        "EN0435",
                        "3:9",
                        &format!("the stack frame of `f` is too large for `{target}`"),
                        "`b` takes it past 2147483647 bytes",
                    )],
                );
                // The statements' frame holds `args` first (S:1143).
                sizes(
                    target,
                    "console.log(1);\nconst big: u8[2147483647] = [0; 2147483647];\n",
                    &[diag(
                        "EN0435",
                        "2:7",
                        &format!("the stack frame of the top-level statements is too large for `{target}`"),
                        "`big` takes it past 2147483647 bytes",
                    )],
                );
            },
        );
    }
    h.case(
        "sizes/parameters are no part of the frame, and each local is placed at its alignment",
        || {
            sizes(
                X86_64,
                "public function f(a: u8[2147483647]): void { }\n",
                &[],
            );
            sizes(
                X86_64,
                "public function f(): void {\n  const a: u8[2147483639] = [0; 2147483639];\n  const b: i64 = 1;\n}\n",
                &[diag(
                    "EN0435",
                    "3:9",
                    "the stack frame of `f` is too large for `x86_64-linux`",
                    "`b` takes it past 2147483647 bytes",
                )],
            );
        },
    );
    h.case(
        "sizes/generic classes and bodies are mono's (S:1628's `A<T>`)",
        || {
            sizes(
                I386,
                "public class A<T> { public a: T[65536]; public b: T[65536]; }
public function f<T>(xs: &T[2000000000][2]): void { const ys: T[2000000000][] = []; }
",
                &[],
            );
        },
    );
    h.case(
        "sizes/every declaration that is too large is reported",
        || {
            sizes(
                I386,
                "private unsafe let a: u8[3000000000];\nprivate unsafe let b: u16[1500000000];\n",
                &[
                    many_on_i386("1:20", "u8[3000000000]", "3000000000"),
                    big_on_i386("2:20", "u16[1500000000]"),
                ],
            );
        },
    );
}

/// Stage 6's review: arrow frames, and the cases the mutation gate found unpinned.
pub fn review(h: &mut Harness) {
    h.case(
        "sizes/an arrow's locals are in its own frame, not its caller's",
        || {
            sizes(
                X86_64,
                "public function f(): void {
  const g = (): void => { let a: u8[2000000000] = [0; 2000000000]; };
  let b: u8[2000000000] = [0; 2000000000];
}
",
                &[],
            );
            sizes(
                X86_64,
                "public function f(): void {
  const g = (): void => { let a: u8[2000000000] = [0; 2000000000]; let c: u8[2000000000] = [0; 2000000000]; };
}
",
                &[diag(
                    "EN0435",
                    "2:72",
                    "the stack frame of an arrow in `f` is too large for `x86_64-linux`",
                    "`c` takes it past 2147483647 bytes",
                )],
            );
        },
    );
    h.case(
        "sizes/an arrow's parameters and a generic body's locals count for nothing (mutants M40, M42)",
        || {
            sizes(
                X86_64,
                "public function f(): void {
  const g = (a: &u8[1500000000], c: u8[1500000000]): void => { };
  let b: u8[1500000000] = [0; 1500000000];
}
public function h<T>(x: &T): void { let a: u8[3000000000] = [0; 3000000000]; }
",
                &[],
            );
        },
    );
    h.case(
        "sizes/`isize.MAX` elements of two bytes are too many bytes, not too many elements (mutant M39)",
        || {
            sizes(
                I386,
                "private unsafe let x: u16[2147483647];\n",
                &[big_on_i386("1:20", "u16[2147483647]")],
            );
        },
    );
}
