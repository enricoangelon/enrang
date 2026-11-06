# Enrang testing

Part I is the user-facing `enrang test` runner. Part II is the compiler's own test strategy. Language behaviour is in `SPEC.md` section 12; this document adds execution mechanics and everything the toolchain tests about itself.

**Status: M0's tests exist and pass, and later layers do not exist yet.** Items marked [measured] were run on the development host on 2026-11-05 (i5-12400F, WSL2, `as` 2.42, rustc 1.97.1). All other numbers are targets, and the counts in section 11 are for M10. The compiler and `enrang dev` run only on a modern x86-64 machine; only their output runs on old chips.

# Part I: `enrang test`

## 1. API

SPEC 12 is normative. A test file:

```ts
// src/stack.test.en: an extra part of module src/stack.en, so private members are visible
function twoUsers(): Stack<User> {            // a fixture is a function; teardown is Drop
  let s = new Stack<User>();
  s.push(User { name: "Ada", age: 36 });
  s.push(User { name: "Grace", age: 85 });
  return s;
}

describe("Stack", () => {
  test("pop is LIFO", () => {
    let s = twoUsers();
    expect(s.pop()).toBe(User { name: "Grace", age: 85 });
  });

  test.panics("bad index", "out of bounds", () => {
    const xs: i64[] = [];
    console.log(xs[0]);
  });

  test("heavy", () => { sortMillion(); }, { fuel: 2000000000, memory: "64MB" });
  test.todo("handles unicode");
});
```

Forms: `describe`, `test`, `test.only`, `test.skip`, `test.todo`, `test.panics(name, substring, body)`, `test.each(name, cases, body)`, `compileFails`, `compileOk`, and `expect(a).matcher(b);` as a statement. Options are a literal `{ fuel, memory, allow }`. `beforeEach` and friends get EN1105 with a helper-function fix-it. A `test` declared inside a function is EN1110. A test arrow returns `void` unless annotated `(): Result<void, E> => ...`, and `?` and `return` act on the arrow.

## 2. Why compiler forms, and how they lower

An ordinary library `expect` cannot exist: by-value it would move its operand, R1 forbids a matcher object holding `&T`, and there are no top-level statements to register tests at run time.

- **`test` and `describe` are items.** Names are string literals, so IDs (`A > B > c`) are stable and filtering happens before anything runs. Duplicates are EN1109. In `ParseMode::Build` the parser discards them; a file with tests appended builds byte-identical to the file without them (meta-test).
- **A test body** becomes an ordinary function; `mirbuild` lowers it like any other. The driver adds a generated `__test_table` static of `{ id, body, flags, fuel, memory, panic_substring, cases: Option<FnRef> }`.
- **`test.each`** sets `cases` to its generator. The case count is known only at run time, so case IDs such as `parses[2]`, zero-based, are emitted at run time. `-t` filters on the row ID first and on the case index when the generator has run. Fuel and leak balance are per case. Natively the generator is charged and balanced once per process start, and in the VM each case gets a fresh heap and regenerates. The generator must be deterministic. The final `Tests` line counts cases.
- **`expect(a).toBe(b);`** lowers to `t1 = &a; t2 = &b; r = EqGlue<T>(t1, t2); if (!r) __fail(site, ShowGlue(t1), ShowGlue(t2));`. These are real shared borrows for one statement, so a live `&mut` still gets EN0708. Rvalues become temporaries dropped at statement end.
- **`__eq<T>` (`EqGlue`)** is compiler-derived deep structural equality. A user's `Eq` is never consulted, so code under test does not grade itself. Floats follow `Object.is`: `+0` differs from `-0`, and `NaN` equals `NaN`.
- **`__show<T>` (`ShowGlue`)** is generated MIR that emits tagged records on the channel of section 5. It neither allocates nor formats floats. Ownership plus R1 make values a tree, so the walk terminates without cycle detection. Raw pointers print as addresses and are never followed.
- **Peeling.** Matchers peel one `&` and one `| null` from the actual type; R2 caps the depth. Literals adapt to the inner type.
- **Test-only code.** `__eq` and `__show` exist only in test builds.

With no unwinding, a failed `expect` ends the test and no drops run. The VM discards the heap; a native process dies and is resumed at the next test by the parent. A panic cannot be caught inside a test, so `test.panics` is a test-level verdict and `toThrow` does not exist.

## 3. Matchers

All accept `.not`. Unknown matcher is EN1108.

| Group | Matchers |
|---|---|
| Equality | `toBe(v)` |
| Bool | `toBeTrue()`, `toBeFalse()` |
| Null, Result | `toBeNull()`, `toBeOk(v?)`, `toBeErr(v?)` |
| Enums | `toMatchPattern(Pattern)`, lowered to `match` |
| Order | `toBeGreaterThan`, `toBeGreaterThanOrEqual`, `toBeLessThan`, `toBeLessThanOrEqual` |
| Floats | `toBeCloseTo(v, eps)`, `toBeNaN()`, `toHaveBits(bits)` |
| Containers, strings | `toHaveLength(n)`, `toContain(x)`, `toStartWith(s)`, `toEndWith(s)` |
| Snapshots | `toMatchSnapshot()`, `toMatchInlineSnapshot(raw`...`)` |

Jest arrivals get EN1104: `toEqual` and `toStrictEqual` get a rename fix-it to `toBe`; `toBeTruthy` explains there is no truthiness; `toThrow` points to `test.panics`; `toHaveBeenCalled` suggests injecting through `T extends Clock`.

## 4. Execution model

```text
enrang test [paths]
  -t "Stack > pop"           substring plus `*`, on test IDs
  --only-failed  --bail      failures recorded in out/.last-failed
  --target=<t> --cpu=<l> --float=<f>   run natively
  --matrix                   every runnable cell for the host
  --layout=vm64|vm32  --oracle  --fuel=<n>   VM options
  --isolate=test             respawn per test (native)
  --shuffle=<seed>           order, for flushing out mutable statics
  --strict                   native-only tests fail in the VM (EN1201)
  --reporter=pretty|dots|json|junit
  -u                         update snapshots
  --ci                       refuse test.only (EN1106), never create snapshots, no timings, print effective grants
  --allow-read=<paths>  --allow-write=<paths>   command-line grants; the only way to grant outside the project root
  --watch                    mtime poller shared with enrang dev; reruns tests whose reachable MIR changed
  --jobs=<n>
```

`--coverage` is deferred (EN1041). The VM's block counters stay, for the meta-tests of section 18.

**VM, the default.** One process, one worker thread per core. The front end runs once per file and MIR is shared by `Arc`. Each test gets a fresh heap and globals image. A panic returns to the worker and the heap is discarded. VM frames live on the heap, so stack overflow is a panic.

**Native, on request.** Each test file becomes one binary with a static test table. The parent runs one binary per core, starting it with `--enrang-test-start=N:K`, row `N`, case `K` (0 for an ordinary test); the binary continues until it exits. A panic or timeout kills only that process, and the parent resumes at the next test or case, re-running the generator for a `test.each` row. Per-test spawn is affordable on Linux at 0.51 ms [measured] but not through WSL interop at 178 ms [measured], so this one mechanism serves all targets. `--isolate=test` forces a respawn per test. Mutable statics need `unsafe`, so a shared process only endangers `unsafe` tests, and `--shuffle` exposes those.

**Timeouts.** One fuel unit is one MIR statement or terminator. Default 200 million per test; running out is T0004. There is no wall clock in the VM, so timeouts never flake. Native uses a 10 s wall-clock watchdog in the parent (T0008).

**Isolation.** VM tests get no capabilities, a virtual clock and a per-test temp directory; `{ allow: ["read:fixtures/"] }` grants more, but only inside the project root, after canonicalisation and with `..` rejected (EN1111). So running `enrang test` on an untrusted checkout cannot read `~/.ssh` through a test's own options; anything wider needs a command-line grant. Under `--ci` the runner prints the effective grants. Natively nothing is enforced, and the runner says so once. Tests reaching `asm` or port I/O through the mono call graph are `native-only`: the VM reports the site and counts them separately.

**Verdict codes** are SPEC 12.4's T0001-T0008. Exit status 1 if anything failed, 0 otherwise.

## 5. The framed channel

Test binaries report to the parent on fd 3 on Linux, on stderr on Windows (interop gives no spare handle), on COM1 when freestanding, and through a host call in the VM. The Rust parent parses, renders and diffs, so reporting cannot disturb allocation counts, and test kernels need no formatter.

```text
frame:   1E 'E' 'N' kind(u8) len(u32 LE) payload
kinds:   1 TestStart(id, case)   2 TestPass(live_blocks, live_bytes)   3 Fail(code, site)
         4 Value(role, records)   5 PanicSeen(substring match)   6 FileEnd
```

`__show` records are tag-length-value: `B` bool, `I` width and value, `F` width and bits, `S` bytes, `R` class ID with fields, `E` enum ID and variant with fields, `A` count, `N` null, `P` raw address, `C` close. Class, field and variant names come from IDs into the parent's compile data, so the binary carries no name strings beyond its trace table. On Windows the parent demultiplexes frames out of stderr by the 3-byte prefix and passes the rest through as the test's stderr.

## 6. Leak detection

There is no libc and so no sanitizer; the allocator counts instead.

- **VM:** every allocation is tracked with its site.
- **Native:** test builds of `alloc` keep `live_blocks` and `live_bytes`. The runner compares them around each test through `TestPass`.
- **Rule:** a passing test must balance, or it fails with T0003, naming the allocation site in the VM. Failed tests are exempt, since no drops ran.
- **Blame:** a leak in a test reaching no user `unsafe` is labelled a compiler bug.
- `mem.forget` is safe, so a test leaking through it deliberately fails T0003 and must free or use `test.skip`.

## 7. Compile-error tests

```ts
compileFails("use after move", raw`
  class U { name: string; }
  function take(u: U): void {}
  function main(): void {
    const u = U { name: "Ada" };
    take(u);
    console.log(u.name); //~ EN0601
  }
`);

compileFails("bswap above the floor", raw`
  //! target: i386-none, cpu: i386
  function f(): void { unsafe { asm("bswap eax"); } } //~ EN0901
`);

compileOk("borrow ends at last use", raw`...`);
```

The embedded compiler runs these in the runner at discovery, identically for any test target.

- The set of (line, code) pairs must match exactly, so a snippet cannot pass because of an unrelated typo. The set includes warnings. `compileFails` needs at least one anchor on an `E` code. `compileOk` may carry anchors, only for `W` codes, which is how EN0430, EN0431, EN0503 and EN0719 fire in a program that compiles. Any mismatch is EN1107.
- `//~ EN0601 "substring"` also checks the message.
- `//!` sets `target`, `cpu`, `float`.
- `{ snapshot: true }` stores the rendered diagnostic. `{ fixes: true }` applies machine-applicable fix-its and requires the result to compile; warnings in the fixed program are accepted.
- Spans map back to the outer file through `FileOrigin::Snippet`.
- Snippets containing backticks live in `name.fail.en` beside the test file with the same anchors, and are discovered automatically.

## 8. Snapshots and reporters

**Snapshots.** The parent writes them to `__snapshots__/` beside the test file, keyed by test ID and ordinal. Mismatch is T0006. `-u` updates; `--ci` never creates them.

**Streams.** All reporter output, including `fail[...]` blocks, goes to stdout. Compile diagnostics go to stderr.

| Reporter | Format |
|---|---|
| `pretty` | Section 9. `PASS file` or `FAIL file`, indented IDs, final `Tests` line. SPEC S10 is a golden |
| `dots` | One character per test, failures after |
| `json` | Versioned NDJSON, one object per line |
| `junit` | `<testsuite>` per file, `<failure type="T0001">` with the rendered text |

NDJSON:

```json
{"v":1,"event":"run_start","target":"vm64","files":1}
{"v":1,"event":"test","id":"Stack > pop is LIFO","file":"src/stack.test.en","status":"fail","code":"T0001","fuel":1204,"cell":"vm64"}
{"v":1,"event":"run_end","passed":1,"failed":1,"skipped":0,"native_only":0,"total":2}
```

## 9. A real failing test

This is the specified output for these exact files, and it becomes a golden test at M4. Only the fuel figure is illustrative until M4 blesses the real count, which is deterministic.

`src/stack.en`:

```ts
export class User {
  name: string;
  age: i64;
}

export class Stack<T> {
  private items: T[] = [];

  mut push(x: T): void { this.items.push(x); }
  mut pop(): T | null { return this.items.pop(); }
  top(): &T | null { return this.items.last(); }
  get size(): isize { return this.items.length; }
}
```

`src/stack.test.en`:

```ts
function twoUsers(): Stack<User> {
  let s = new Stack<User>();
  s.push(User { name: "Ada", age: 36 });
  s.push(User { name: "Grace", age: 85 });
  return s;
}

describe("Stack", () => {
  test("pop is LIFO", () => {
    let s = twoUsers();
    expect(s.pop()).toBe(User { name: "Grace", age: 86 });
    expect(s.size).toBe(1);
  });

  test("top borrows", () => {
    const s = twoUsers();
    expect(s.top()).not.toBeNull();
  });
});
```

`enrang test --ci src/stack.test.en`, stdout, exit status 1:

```text
FAIL src/stack.test.en
  Stack > pop is LIFO  FAILED
  Stack > top borrows

fail[T0001]: `toBe` found different values
  --> src/stack.test.en:11:12
   |
11 |     expect(s.pop()).toBe(User { name: "Grace", age: 86 });
   |            ^^^^^^^ actual
   |                          ------------------------------- expected
   |
   = note: difference at `.age`:
             User {
               name: "Grace",
           -   age: 86,   expected
           +   age: 85,   actual
             }
   = note: `s.pop()` has type `User | null`; the non-null payload was compared.
   = note: ran on vm64, used 1204 of 200000000 fuel
help: rerun only this test
   |
   | enrang test src/stack.test.en -t "Stack > pop is LIFO"
   = explain: run `enrang explain T0001`

Tests  1 failed, 1 passed, 2 total
```

# Part II: the compiler's own tests

## 10. Principles and testkit

- **Written alongside each component from M0.** Tests are a condition for finishing a milestone (section 23). Test code and corpus are expected to meet or exceed implementation size.
- **`cargo test` is the single CI entry.** It calls `enrang test --reporter=json lib/` as a subprocess from M4. No third-party test crates.
- **M0-M3** run entirely under `cargo test` on testkit fixtures.
- **Stays in cargo:** compiler layers, encoder oracles, writers, matrix driver, meta-tests, runner self-tests.
- **Moves to `.test.en` after M4:** `core`, `alloc` and `os` library tests.
- **Conformance programs** stay plain, output-checked `.en` files that never depend on `expect`, so they validate new backends at M5 before native `enrang test` is trusted.
- **A broken runner cannot vouch for itself.** The must-fail suite gives each matcher and T code a test that has to fail with exact output.

`enrang-testkit` is a workspace crate used with `harness = false` test binaries, because libtest cannot generate tests dynamically.

```rust
pub struct SplitMix64(u64);  pub struct Xoshiro256([u64; 4]);          // section 14
pub trait Rng { fn next_u64(&mut self) -> u64; fn below(&mut self, n: u64) -> u64; fn edge_u64(&mut self) -> u64; }
pub fn shrink<T: Shrink>(failing: T, still_fails: impl FnMut(&T) -> bool) -> T;
pub fn golden(suite: &str, name: &str, actual: &str) -> Result<(), GoldenDiff>;   // section 17
pub fn tool(name: &str) -> Option<ToolPath>;                                      // section 20
pub fn skip(tool: &str, tests: usize, reason: &str);
pub fn skip_oracle(tool: &str, tests: usize, reason: &str);                       // the `oracle tests` wording of section 20
pub mod oracle { pub fn gas_assemble(mode: AsMode, march: &str, lines: &[String]) -> GasResult;
                 pub fn objdump_text(path: &Path) -> Vec<DisasmLine>; pub fn readelf(path: &Path) -> ElfFacts; }
pub mod decode;     // test-only x86 decoder, shares no tables with enrang-x86
pub mod x86sim;     // section 19
pub mod stepper;    // ptrace single-stepper; the only unsafe Rust in the repository
```

## 11. Layers and target counts at M10

| Layer | Cases | Generated per full run | Independent check |
|---|---:|---:|---|
| Diagnostics, explain | 300 | | Every fix-it applied and recompiled |
| Lexer | 500 | 200k byte mutations, no panics | Token re-print |
| Parser (700 recovery cases) | 2,000 | 20k programs: print, reparse, equal AST | AST printer round trip |
| Types, narrowing, generics | 2,500 | 5k programs | Maranget against brute force |
| Moves, borrows | 2,000 negative + 2,000 fixed siblings | 20k mutants | VM fault detector; `rustc` |
| MIR, drops, mono | 1,000 goldens | | Verifier after every pass; `rustc` drop traces |
| VM | 1,500 | | Fuel determinism; every fault detector fires |
| Encoder | About 800 forms, 3 modes | 300k instances, 20 `-march` names | `as` bytes; `objdump` decode; own decoder |
| ELF, PE, flat, image | 400 | | Own parser; `readelf`; `objdump -p`; execution |
| Backends | 1,000 | 100k `i64`-pair, 2M soft-float vectors | Rust host, bit for bit |
| Runtime, in `.test.en` | 1,500 | 100k allocator operations | Shadow model |
| Runner, CLI | 700, with must-fail suite | | Exact output |
| Dev, reload | 400 scenarios | 2k state walks | Migrated heap passes a typed walk |
| Boot | 300 bench scenarios | | Bench; QEMU when present |

That is about 17,000 cases, mostly table rows and rule-by-shape expansions.

## 12. Conformance corpus and implementation matrix

**Corpus.** Plain `.en` programs with headers, growing from 300 at M4 to 500 at M5 to 1,500 at M10. S1-S8, S10 and S11 are included verbatim, and S9 runs on the freestanding cells.

```ts
//! stdout: file            // or inline; expected bytes in name.stdout
//! exit: 0
//! allocs: balanced        // or an exact count
//! panic: "index 3 is out of bounds for length 3" at 7:15    // message and location
//! differs: sizeOf<usize>  // any difference between cells must be declared here
//! cells: hosted           // all | hosted | floor-only | vm ...
//! max-memory: 16MB        // VM cells: passes --max-memory
//! min-memory: 16MB        // freestanding cells skip this program, by declaration, below that
```

**Each cell compares:** stdout bytes, exit code, panic message and location, and allocation count. Stack overflow is excluded by declaration: the VM panics, and hosted targets report what the OS delivers. So is the end of a loop that grows without limit (SPEC 5.6), because overcommit can get a native process killed where the allocator would have failed: a program relying on `out of memory` declares `//! cells: vm` and `//! max-memory:`, and one that loops at constant size is tested through T0004. Allocation counts come from a hidden `--alloc-stats` build flag, which writes counts on the framed channel at exit.

**The matrix:**

| Cell | Target | `--cpu` | Float | Runs on this machine | From |
|---|---|---|---|---|---|
| `vm64` | VM | | host | Yes | M4 |
| `vm32` | VM | | host | Yes | M4 |
| `vm32-soft` | VM | | soft | Yes | M8 |
| `lx64` | `x86_64-linux` | `x86-64` | `sse2` | Natively | M5 |
| `win64` | `x86_64-windows` | `x86-64` | `sse2` | WSL interop | M7 |
| `l32-i386` | `i386-linux` | `i386` | `soft` | IA32 emulation | M8 |
| `l32-i486` | `i386-linux` | `i486` | `soft` | IA32 emulation | M8 |
| `l32-i586` | `i386-linux` | `i586` | `soft` | IA32 emulation | M8 |
| `l32-i686` | `i386-linux` | `i686` | `soft` | IA32 emulation | M8 |
| `l32-sse2s` | `i386-linux` | `sse2` | `soft` | IA32 emulation | M8 |
| `l32-sse2` | `i386-linux` | `sse2` | `sse2` | IA32 emulation | M8 |
| `none-bench` | `i386-none`, `lib/conformance/none_shim` | `i386` | `soft` | `x86sim`, models `i386-nofpu` and `pentium` | M9 |
| `none-qemu` | `i386-none`, same shim | `i386` | `soft` | Skip until QEMU; lowest model `486` | M9 |
| `none-qemu-sse2` | `i386-none`, same shim | `sse2` | `sse2` | Skip until QEMU; model `core2duo` | M9 |
| `none64-qemu` | `x86_64-none` | `x86-64` | `sse2` | Skip until QEMU | M10 |
| `efi-ovmf` | `x86_64-none --format=efi` | `x86-64` | `sse2` | Skip until OVMF | M10 |

`lib/conformance/none_shim` provides `console` on COM1, the SPEC 9.1 panic format, an allocator from `BootInfo`, and exit through `isa-debug-exit`, so hosted corpus programs run unchanged on freestanding cells. These cells build with `--stack-size=1048576` and use 32 MB of bench and QEMU memory, so recursion or heavy allocation that passes on hosted cells does not produce a false differential. A program needing more declares `//! min-memory:`. The 16 KB stack and 640 KB limits are asserted for S9 only.

`none-qemu-sse2` is the only cell that executes the freestanding SSE path, so it adds a kernel test that runs float work under a PIT interrupt whose handler also uses floats, compared bit for bit. That exercises the CR0 and CR4 enable sequence, `ldmxcsr`, `fxsave` stack alignment in stubs, and XMM survival across an interrupt.

**Cross-cuts.** `--regalloc=none|linear|chaos:<seed>` and `--opt=0|1` on `lx64` and `l32-i386`: a sample at default scale, all programs at `ENRANG_SCALE=10`. Every alias in SPEC 10.1 gets one hello build plus a golden of the note it prints; aliases add no matrix cells because they resolve to a rung.

This host supports every level on the list except AMD's 3DNow!, which we never emit, so floor-level and higher-level 32-bit binaries all run natively here [measured]. **That proves correctness of the code. The tags and audit of section 15 prove it stays within the level. Neither proves behaviour on the real chips.**

## 13. Differential testing

| Compared | What a difference means |
|---|---|
| VM against every native cell | Bug in the VM or a backend |
| `vm32` against `l32-*` and `vm64` against `lx64` | `sizeOf` included: layout bug |
| `linear` against `none` against `chaos:<seed>` | Emitter or allocator bug |
| `--opt=0` against `--opt=1` | LIR simplify bug |
| All `--cpu` levels | Level-dependent lowering bug |
| `soft` against `sse2` against Rust host | Soft-float bug (section 16) |
| `--allocator=enrang` against host allocator in VM | `FreeListHeap` bug |
| `lx64` against `win64` | OS layer bug |
| GenOwn accept and reject against `rustc` | Borrow checker bug, or a named intended disagreement |
| Drop trace against `rustc` twin | Drop elaboration bug |

**The translation fixes the loop form.** A `for...of` with a path source becomes `let mut i = 0; while i < q.len() { let x = &q[i]; i += 1; body }`, or `&mut q[i]` in exclusive mode. A `for x in &q` twin would make `rustc` reject every growing loop (E0502), a false disagreement. An evaluate-once reference source becomes `let s = &src;` followed by the same loop over `s`, which keeps the whole-loop hold, so `rustc` rejects what Enrang rejects. An owned source keeps `for x in`. `[...a]` becomes `out.extend(a.iter().cloned())`, in order. With these, `rustc` agrees on acceptance, on EN0706 when `x` is used later, and on the EN0611 cases, so no new disagreement row is needed.

**Named intended disagreements** with `rustc`: NLL problem case #3, which Enrang accepts; evaluation-order patterns from O6; Enrang's own R1 rejections, which `rustc` accepts. Each is one row in `corpus/rustc_disagreements.txt`, and a stale row fails. `rustc` is available here but its use is nightly-scale.

**Limit.** VM and native code share MIR, so they can agree on a wrong answer. Expected outputs and VM fault detection catch those, not the differential.

## 14. Generators

All generators are seeded, deterministic and written with our own PRNG. A failure prints its seed, shrinks, and lands in `corpus/regress/` as a permanent test. `ENRANG_SEED=<n>` reproduces.

**PRNG.** SplitMix64 seeds xoshiro256**. Known answers are pinned as a test [measured against a reference computation]:

```text
SplitMix64(seed 0):              0xE220A8397B1DCDAF  0x6E789E6AA1B965F4  0x06C45D188009454F
xoshiro256** seeded from above:  0x99EC5F36CB75F2B4  0xBF6E1F784956452A  0x1A5F849D4933E6E0
```

| Generator | Produces | Asserts |
|---|---|---|
| `GenBytes` | Random and mutated bytes | Lexer and parser never panic |
| `GenSyntax` | Valid ASTs | Print, reparse, equal AST |
| `GenTypes` | Typed programs and near-misses | Accept or the intended code; no panic |
| `GenExpr` | Typed arithmetic whose expected value the generator computes itself, with float-to-int edges forced at `2^31`, `2^32`, `2^63`, `2^64` and one ulp below each | Exact output on every cell |
| `GenOwn` | Classes, moves, borrows and `Drop` tracers, with a Rust twin by the translation of section 13, and `for...of` bodies that change the source with `x` both dead and live | `rustc` accept/reject and drop order; the VM's fault detector stays clean |
| `Mutants` | One violation inserted into an accepted program | Rejected with the intended code |
| Soundness | Every accepted program from the above | Runs fault-free under the VM; any fault is a soundness bug |
| `GenInstr` | Encoder instances: all registers, displacement sizes, immediate boundaries | `as` agreement |
| `GenFloat` | Edge-weighted float operands | Section 16 |
| `GenPair` | `i64` operations on edge values | i386 pairs equal Rust host |
| `GenAlloc` | Allocator operation sequences, including sizes at the `isize.MAX` capacity boundary | `FreeListHeap` equals a shadow model; no overlap; `capacity overflow` exactly at the boundary |
| `GenSchema` | Random schema edits over random heaps, weighted towards zero-sized types and empty containers | Refused with unchanged heap hash, or migrated with a clean census (`DEV_RUNTIME.md` section 16) |

**Scale.** `ENRANG_SCALE=1` is the default, a tenth of the full volume. `ENRANG_SCALE=10` is the full volume, and nightly uses 100.

## 15. Encoder oracle and level enforcement

### 15.1 Bytes

Every form, in every valid mode, runs through all registers, displacement sizes and immediate boundaries. `as` with `.intel_syntax noprefix` and `.code16/32/64` assembles each one, and the bytes are compared. One file per mode and one `as` run; the listing gives bytes per line. `as` assembled 200,000 lines in 0.13 s, or 0.55 s with a byte listing [measured], so batching makes this cheap.

- **Alternate encodings.** `{load}`, `{store}`, `{disp8}` and `{disp32}` at line start force the choice [measured: `{load} mov eax, ebx` is `8B C3`, `{store} mov eax, ebx` is `89 D8`, `{disp32} mov eax, [ebx+4]` is `8B 83 04 00 00 00`]. Where GAS has a default, the encoder uses the same one.
- **Prefix order** must match GAS: segment, `67`, `66`, `rep` or `lock`, mandatory prefix, REX. In `.code16`, `addr32 rep movsd` is `67 66 F3 A5`, `mov byte ptr es:[ebx], 1` is `26 67 C6 03 01`, and `lock add dword ptr fs:[eax], 1` is `64 67 66 F0 83 00 01` [measured].
- **Second decoder.** `objdump -D -b binary -m i8086` confirms the 16-bit forms decode as intended [measured for `66 EA`, `66 0F 01 16`, `0F 20 C0`], and the test-only decoder in `enrang-testkit` checks round trips with no shared tables.

### 15.2 Level tags against the assembler

The same files run per `-march`. For each form `f` and level `L`: `allowed(L) ⊇ f.features` must equal "`as -march=map(L)` accepts", except for rows in `tests/oracle_exceptions.txt`.

| Level | `as` name | Mode |
|---|---|---|
| `i386` | `i386`; x87 probe forms at `i386+387` | `--32` |
| `i486` | `i486`; x87 probe forms at `i486+387` | `--32` |
| `i586` | `i586` | `--32` |
| `i686` | `i686` | `--32` |
| `sse2` | `pentium4` | `--32` |
| `x86-64` | `generic64` | `--64` |
| Stage 1 (allowed set lacking `Ia32`) | `.code16` then `.arch i8086`, in that order | `--32` |

The stage 1 row has a real oracle. With `.code16` before `.arch i8086`, `as` accepts `mov ax, bx`, `int 0x10`, `div bx`, `pushf` and `shl ax, 1`, and rejects `push 1`, `shl ax, 4`, `pusha`, `mov eax, ebx`, `movzx` and `lgdt`. A long `jc` assembles to `73 03 E9 ...` where `i386` gives `0F 82 ...` [measured]. The reverse directive order is an error [measured], which is what made this look impossible. The whole of stage 1 runs through this row, byte and level.

`generic64` was chosen because it rejects `cmpxchg16b`, `lahf`, `sahf` and `popcnt` [measured], which is exactly the baseline's boundary. Named-chip cross-checks also run, per form, at `pentium`, `pentiumpro`, `pentiumii`, `pentiumiii`, `prescott`, `nocona`, `core`, `core2`, `corei7`, `k6`, `k6_2`, `athlon`, `opteron`, `k8`, `generic32`.

**Harness rules** that keep a typo from reading as a rejection:

- A canary `nop` at each `-march` proves the CPU name is valid. A bad name is `Fatal error: invalid -march= option` [measured], and there is no `penryn`.
- A level rejection is exactly one of two messages [measured]: `` `bswap' is not supported on `i386' `` or `` unsupported instruction `nop' ``.
- Any other error, such as `operand size mismatch`, fails the harness itself.

**Measured acceptance, `as --32 -march=X`, `as` 2.42** (Y accepted, `.` rejected):

```text
            bswap cmpxchg xadd cpuid rdtsc cx8b cmov fcomi fninit ud2 movcr4 nopl fxsave addsd addss mmx femms invlpg wrmsr
i386          .      .     .     .     .    .    .     .     .     Y    Y     .     .     .     .    .    .     .     .
i386+387      .      .     .     .     .    .    .     .     Y     Y    Y     .     .     .     .    .    .     .     .
i486          Y      Y     Y     Y     .    .    .     .     .     Y    Y     .     .     .     .    .    .     Y     .
i486+387      Y      Y     Y     Y     .    .    .     .     Y     Y    Y     .     .     .     .    .    .     Y     .
i586          Y      Y     Y     Y     Y    Y    .     .     Y     Y    Y     .     .     .     .    .    .     Y     Y
i686          Y      Y     Y     Y     Y    Y    Y     Y     Y     Y    Y     .     Y     .     .    .    .     Y     Y
pentiumpro    Y      Y     Y     Y     Y    Y    Y     Y     Y     Y    Y     Y     Y     .     .    .    .     Y     Y
pentiumii     Y      Y     Y     Y     Y    Y    Y     Y     Y     Y    Y     Y     Y     .     .    Y    .     Y     Y
pentiumiii    Y      Y     Y     Y     Y    Y    Y     Y     Y     Y    Y     Y     Y     .     Y    Y    .     Y     Y
pentium4      Y      Y     Y     Y     Y    Y    Y     Y     Y     Y    Y     Y     Y     Y     Y    Y    .     Y     Y
k6            Y      Y     Y     Y     Y    Y    .     .     Y     Y    Y     .     .     .     .    Y    .     Y     Y
k6_2          Y      Y     Y     Y     Y    Y    .     .     Y     Y    Y     .     .     .     .    Y    Y     Y     Y
athlon        Y      Y     Y     Y     Y    Y    .     Y     Y     Y    Y     Y     .     .     .    Y    Y     Y     Y
```

64-bit, `as --64` [measured]: `cmpxchg16b` rejected at `generic64` and `k8`, accepted at `nocona`, `core2`, `corei7`. `lahf` and `sahf` rejected at `generic64`, `nocona`, `k8`, `core2`, accepted at `corei7`. `popcnt` accepted only at `corei7`. `pshufb` accepted at `core2`, `corei7`. `pmulld` accepted only at `corei7`. `nop dword ptr [rax]`, `cvttsd2si rax, xmm0` and `fxsave` accepted at all five.

Floor forms used by the compiler, accepted at `i386` [measured]: `lock bts`, `lock inc`, `xchg`, `lock or dword ptr [esp], 0`, `rep movsd`, `shld`, `movzx`, `sete`, `bt`, three-operand `imul`, `cdq`, `jo`, `leave`, `iretd`, `lgdt`, `mov cr0, eax`. `popad` and `enter` are accepted by `as` but banned by us.

### 15.3 Recorded disagreements

Our feature table is the source of truth. `tests/oracle_exceptions.txt` holds one row per disagreement: instruction, `-march`, what `as` says, what we say, reason. **A stale row fails the test.** Seeded with:

| `as` behaviour [measured] | Our table | Reason |
|---|---|---|
| `athlon` rejects `cmov` | K7 is at `i686`, which has CMOV | Real K7 chips have it |
| `athlon` rejects `fxsave` | `fxsave` needs `sse2` level | K7 model 2+ has it, K7 model 1 lacks it; we never rely on it below `sse2` |
| `athlon` accepts `nop dword ptr` | NOPL only at `x86-64` | No K7 source found |
| `i486` accepts `cpuid` | `cpuid` needs `i586` | Early 486s lack it |
| `i386`, `i486`, `i586` accept `ud2` | `ud2` tagged P6 (`i686`) | Generated code uses neither; panics use `int3` |
| `i386`, `i486` accept `mov cr4, eax` | `cr4` needs `i586` | A 386 has no CR4 |
| `i686` rejects `nop dword ptr`; `pentiumpro` through `pentium4` accept | NOPL in no 32-bit level | Avoids the question; `x86-64` only |
| `pentiumiii` accepts `addss` and `ldmxcsr`, `i686` rejects them | Tagged `sse`; only level `sse2` has them | `sse` alone is never a rung, because it cannot do `f64` |
| `i686`, `pentiumpro`, `pentiumii` accept `fxsave` | `fxsave` needs `sse2` | Pentium Pro and Klamath lack it |
| `i386`, `i486` reject `fninit`, `i586` accepts | `fpu` is in no 32-bit level; probe forms only | `+387` names used for the probe audit |
| `nocona`, `core2` accept `cmpxchg16b` | Not in baseline | Early 64-bit parts lack it |
| `core2` rejects long-mode `lahf` | Not in baseline | Real Core 2 has it; we never emit it |

### 15.4 Enforcement tests

1. **Refusal.** `Assembler::emit` refuses each form at each level below its tag. In generated code that is an internal error; in inline assembly, EN0901.
2. **Inline diagnostics.** EN0901 per feature names the instruction, the feature, the level providing it and the current level. G15 is the byte-exact golden.
3. **Output audit.** Tags could share the emitter's mistakes, so we disassemble emitted `.text` with `objdump -d`, keep numeric branch targets, reassemble at `-march=<level>`, and require every line accepted. This was tried: it flagged only `bswap` at `i386` [measured]. Dropping branch targets gives false failures. It runs on the corpus at every level, under these rules:
   - **Audit `--symbols` builds.** Default ELF output has `e_shnum = 0`, and `objdump -d` on an ELF32 with no section headers prints no instructions and exits 0 [measured], so auditing it would pass vacuously. The test asserts that every `PT_LOAD` byte of the `--symbols` build equals the default build.
   - **No vacuous pass.** Decoded instruction bytes not equal to the text size, or zero lines, is a harness failure.
   - **Flat and images** use `objdump -D -b binary -m i386` with start and stop addresses from `<out>.map`, excluding the BPB, the parameter block and `db` ranges.
   - **Negative control.** A fixture with `bswap` injected at level `i386` must fail the audit.
4. **Independent scan.** The test-only decoder classifies every instruction in `.text` against a feature table written separately from the encoder's.
5. **Dynamic classification.** A ptrace single-stepper classifies every executed opcode across a sample of the i386-linux corpus. Feasibility [measured]: a 64-bit tracer single-stepped a 32-bit ELF here through `PTRACE_SINGLESTEP`, with the i386 regset (68 bytes), in a 7-step run. About 300 lines in `enrang-testkit`, using raw syscalls.
6. **Floor island.** Assembler records and the audit prove startup, level check and panic printing stay at the floor at every `--cpu`, with FPU probe forms audited at `i386+387`.
7. **Failing cleanly.** `checkLevel(flags)` is table-driven and tested with fake flags for every family. The real freestanding branches cannot run on this CPU, so the bench runs them (section 19). The hosted path runs end to end under the ptrace stepper with a CPU personality: after `pushfd` it clears AC or ID in the pushed image, and at `cpuid` it skips the instruction and sets registers from the family table. The real ELF32 must then print the golden message and exit 126, for each rung and family, with no emulator.
8. **Baseline.** The `x86-64` audit at `generic64` rejects CMPXCHG16B, LAHF, SAHF, POPCNT.
9. **Errata.** Compiled floor output contains no `popa`, `popad`, `enter`, `ud2` or `loop`; the decoder asserts this directly, since `as` accepts most of them.

## 16. Soft-float against hardware

**Oracle.** Rust `f32`/`f64` on this host compile to SSE2 scalar instructions, so test code computes bit-exact expected results with the real hardware. Plain Rust operators serve only for non-NaN results, because LLVM treats `fadd` and `fmul` as commutative and may swap operands, which changes which NaN propagates. For the stricter NaN test, `enrang-testkit`, the only crate allowed `unsafe`, uses `core::arch::asm!("addsd {a}, {b}")` per operation, so operand order is fixed and a `rustc` upgrade cannot fail correct soft-float code.

**Driver.** `corpus/softfloat/driver.en` reads binary vectors (`op`, operands) from stdin and writes result bits to stdout. The Rust harness generates vectors with `GenFloat` and compares.

**Implementations compared, bit for bit:**

```text
Rust host SSE2 = l32-i386 soft = vm32-soft = l32-sse2 = lx64 = win64
```

- **Language guarantee** (SPEC 9.3): non-NaN results bit-identical, NaN-ness identical, NaNs canonicalised by `toBits`.
- **Internal test, stricter:** soft-float also matches SSE2 NaN sign and payload for add, sub, mul, div, sqrt.

**Vector classes**, for both widths, weighted to edges:

| Class | Examples |
|---|---|
| Specials | `±0`, `±inf`, qNaN, sNaN, every pairing |
| Subnormals | Boundary to normal, min subnormal, results that underflow exactly at the rounding boundary |
| Rounding | Exact halfway cases, one ulp either side, ties to even in both directions |
| Exponent | Maximum differences, overflow by one, cancellation to zero and to subnormal |
| Random | Uniform bits, uniform exponents |

**Operations:** `+ - * / %`, `sqrt`, compare with all predicates, `f32`-`f64` conversions, `i32`, `u32`, `i64`, `u64` to float and back (range-checked, since `as` panics; Rust's saturating `as` is filtered), `floor`, `ceil`, `trunc`, `round`, `abs`, `min`, `max`, `fromBits`, `toBits`. `%` compares against Rust's exact `%`.

**Printing and parsing.** Dragon4 output is compared digit-for-digit against Rust `{:e}`, then the JS-style formatting rules separately; parsing against Rust `parse`. SPEC S1's `0.30000000000000004` is a golden.

**Volume.** 200k vectors by default, 2M at scale 10, 20M nightly. M8 records real soft-float instruction counts with the stepper, replacing the clock estimates in SPEC 9.3 for a documented table.

**x87 gets no cell.** It is deferred past M10 and may not ship until it passes these same vectors, including double rounding on subnormals (SPEC 9.3).

**Budget.** Soft-float code, if referenced, is at most 16 KB, and the audit runs it at `i386`.

## 17. Goldens and bless

- `tests/golden/<suite>/<name>` holds rendered output. `ENRANG_BLESS=1 cargo test` rewrites and prints diffs, and refuses under `CI=1`. Orphaned goldens fail.
- `//~` anchors are hand-written and cannot be blessed, so blessing never changes which error is expected.
- **SPEC is the golden source for its own examples.** A test extracts every G and S case, the tour, the tour's kernel and the `Ownership in three lines` block from `docs/SPEC.md` and compares compile, stderr, stdout, serial output and exit status byte for byte. If a spec example and a golden disagree, the test fails, so neither can drift. Extraction reads only the `<!-- case: ... -->` markers and the blocks after them (SPEC 14), never prose, and the same test extracts section 9 of this document, which gets its marker at M4, when that case is first enforced. Each case is enforced from the milestone its codes and features reach, by the `since` rule of section 18.
- Goldens never contain timings, absolute paths or memory addresses. `--ci` removes them; the renderer has no other source of nondeterminism.

## 18. Traceability meta-tests

`define_*!` macros generate each enum plus an `ALL` list, since Rust has no reflection. **The build fails if any row that has reached its milestone has a gap.**

**Milestone gating.** No compiler exists at M0, so an unconditional "every code has a fixture" would stay red until M10. Every macro row and extracted case carries `since(Mn)`: `define_codes!` (SPEC 13.2), `define_mir_statements!`, `define_intrinsics!`, encoder forms, lang items, and G and S cases. Meta-tests enforce only rows with `since <= CURRENT_MILESTONE`, a constant bumped by the commit that closes a milestone. A row whose `since` has not been reached must not yet have a fixture that claims to pass, so a stale `since` also fails. A case marker has no `since` field, so extracted cases take theirs from a side table, `tests/trace/case_since.txt`, added at M1 from section 23.

**Document row IDs.** Prose tables have no macro, so their rows carry stable IDs: `C01` (SPEC 4.5), `H01` (SPEC 5.8), `MIG-01`, `REF-01`, `FAIL-01`, `ADV-1` (`DEV_RUNTIME.md` sections 7, 8, 10, 12, the last of which has bare numbers in its `#` column). A test parses the IDs from the Markdown into `tests/trace/*.txt`, and fixtures declare `//! covers: MIG-07`. An uncovered ID and an orphan `covers` both fail, subject to `since`. So these gates are mechanical rather than a reviewer's judgement.

| Item | Required |
|---|---|
| Each `fixture(Compile)` code | A firing fixture, a passing near-miss, an explain page whose examples compile |
| Each `fixture(Cli)`, `fixture(Reload)` or `fixture(TestRun)` code | A firing scenario of that kind, an explain page with a transcript. EN1215 cannot be shown by a compile failure |
| Each MIR statement kind and intrinsic | Hit by probe counters in the VM and in every backend. `Drop` exists only before elaboration, so MIR goldens cover it; `HostCall` runs only in the VM, `Asm` only natively |
| Each encoder form | Byte oracle, level oracle, and one emission test or inline test |
| Each runtime function | Hit in VM block counters or, for `os/*` and asm-only code, in a native or bench cell. Exemption file must stay empty for `core` and `alloc` |
| `asm` placement | No `asm` in `core` outside `core/port` and `core/cpu`; from M4, the mono closure of S1-S8, S10 and S11 on VM rows contains no `Asm` statement |
| Floor island | No `Fp` LIR instruction in an island function |
| Stage 1 and M16 | The M16 form list equals the forms `lib/boot` assembles |
| Each `@lang` item | Exists in every target's module graph, plus a test |
| Each CLI command, flag, matcher and Jest hint | A golden |
| Each deferred feature, SPEC 16 | Fixture producing exactly its message head |
| Each VM fault detector | A test making it fire |
| Each `C`, `H`, `MIG`, `REF`, `FAIL` and `ADV` row | A fixture or scenario declaring `covers` |
| Each size budget | A failing check from its milestone |
| Each `G` and `S` heading in SPEC | A `case` marker |

**Named fixtures.** These programs reached a design review as concrete soundness or acceptance failures, so each is a permanent fixture, with a `rustc` twin where the row says so.

| Fixture | Must give |
|---|---|
| `both(() => { const e = first(r); touch(); console.log(e); }, r);`, in either argument order, with `r: &mut string[]` | EN0715 |
| `both(() => { *r += 1; }, r);` | EN0715 |
| `run(() => { *r += 1; }); run2(r);` | Compiles |
| `const f: fn(d: *mut u8, v: u8, n: usize) => void = mem.set;` | EN0803 |
| `unsafe`, `@requires`, `declare`, `@naked`, `@interrupt` functions as safe `fn` or closure argument, one each | EN0803 |
| The same five at `unsafe fn(...)`, or `InterruptHandler` for `@interrupt` | Compiles |
| `fn` value with a different `from` clause | EN0401 |
| `x.drop()`, including on `T extends Drop` and through `interface Flush { mut drop(): void; }` | EN0606, at the call and at the interface |
| `@globalAllocator let heap: Evil = ...` | EN0825 |
| A `@globalAllocator` method that builds a `string` | EN0824 |
| `@globalAllocator unsafe let heap: FreeListHeap;`, the exact G14 help snippet | Compiles |
| Satisfaction, one per clause: `from` sources differ, `unsafe` method, `private` method, `@requires` method, member only through `Box` auto-deref | EN0416 at `implements`, EN0419 at the bound |
| `twice(f, f)` | EN0718 |
| `visit(f, n); visit(f, m);` and `xs.forEach(f); xs.forEach(f);` | Compiles |
| `both(f, () => { f(); })` | EN0718 |
| A closure-typed parameter of a closure type, and an arrow passed to it | EN0705 |
| Moved and unmoved payloads, null and other variant, on `T \| null`, `Result` and a user enum: `f(null, true)` with `if (o != null && c) { take(o); }` | Drop trace equal to the `rustc` twin, no fault |
| `o.add(clear(&mut o));` and `o.n = clear(&mut o);` under `o != null` | EN0401 with a note |
| `if (n != null) { n.x = 1; n.x = 2; }`, `if (n != null) { n.bump(); n.bump(); }` | Compiles |
| `if (p != null) { xs.forEach(x => { p = null; }); console.log(p); }` | EN0419, not a tag panic |
| `bump(r.big)`, `bump(h.big)` with a live `q = &h`, `bump(K)` | VM equals native; `r.big`, `h.big` and `K` unchanged |
| `s.pushByte(0xF0)` | Panic `invalid byte 240 for a string` |
| `codePointAt` on invalid bytes built in `unsafe` | Never reads past `len`, on VM and native |
| Packed field, one per `BorrowOrigin`: explicit, auto-borrow, reborrow, match binding, `for...of` element, `for...of` hidden, capture, temp argument | EN0804 |
| `@packed class P { a: u8; b: u32[4]; g: u32[2][2]; }` with `for (const x of p.b)` (the `rustc` twin is E0793), `for (const x of p.g[r])`, `&p.b[1]`, `[...p.b]` | EN0804, at the source in the loops; the same forms over `u8` elements compile, as the near-miss |
| `@packed class P { s: string; }`, `@packed class G<T> { v: T; }` | EN0826 |
| `console.log(p.b)`, `${p.b}`, `expect(p.b).toBe(1)` on a packed `u32` | Compiles and runs; no misaligned-access fault |
| `new Atomic<string>(...)`, generic `dup<T>(a: &Atomic<T>)` | EN0419 |
| `Atomic64` at `i486`; `testAndSet` on `Atomic<u8>` | EN0910; EN0419 |
| `w<T extends Copy>(p: *mut T, v: T) { unsafe { p.writeVolatile(v); } }`; `writeVolatile` of `u64` on `i386` | EN0805 in both, at the call; `w<T extends VolatileValue>` compiles |
| `u64[536870912]` on `i386`, `A<A<u64>>` with `T[65536]` fields, a 3 GB local on `x86_64`, and near-misses of one element less | EN0435, on both pointer widths; near-misses compile |
| `b.reserve(0x80000000)` on `l32-i386` and `vm32` | Panic `capacity overflow` |
| `@interrupt` that allocates, `@panicHandler` that builds a template string, each through a `fn` value too | EN0824; the near-miss sets an `Atomic` and compiles |
| `for (const x of move a)` with `a: D[3]`, `D` non-Copy; with `a: i32[3]` | EN1015; compiles |
| `for (const c of "abc")` | EN1015 |
| `while (ok("a" + "b") && n < 3)`, `if (cond(mk()))`, `for` step temporaries, `match (make().kind)` | Drop trace equal to the `rustc` twin |
| Each row of the SPEC 5.6 `match` table and of its `for...of` table; `match (t) { null => 0, v => use(v) }` with `t: &User \| null` | Stated binding type, evaluation and loan |
| `match (move r)`, `for (const x of move r)`, `const b = move r` with `r: &mut T` | EN0603 |
| `t.isNull()` with `t: &User \| null` | EN0703 with a `== null` fix-it |
| `take(p); p.first = c;` for a plain class and a `Drop` class | EN0601 |
| Cursor walk with a held field reborrow, `const v = &mut (*cur).val; cur = &mut (*cur).next` | Compiles; `rustc` twin agrees |
| `.mir`: `(*(x as Present).0).f` and `*((*_env).i)` with overlapping `&mut` reborrows | EN0707 |
| `.mir`: read of a moved-from `class P { x: i64 }`, double `DropGlue` | Uninitialised read fault |
| `report(new Circle(2.0))`, `f(r, 1)` with `r: &i64`, `apply(x => x + 1, 5)`, `let a = 5; a.checkedAdd(1)` | Compiles |
| `let xs = []; xs[0].name; xs.push(u);` | EN0410 |
| `a ?? b ?? c`, `a?.b?.c` | Compiles |
| `a?.b.c` | EN0303 with a `?.c` fix-it |
| `0xFFFFFFFFFFFFFFFF as u64`, `0xB8000 as *mut u16`, `const m: i64 = -9223372036854775808;` | Compiles |
| `300 as u8` | EN0411 |
| `const x: f32 = 1.00000017881393432617187499;` and other known double-rounding literals | Correctly rounded bits |
| `Box<Box<Box<i64>>>`, `let x: Box<i32>= v;`, `**pp`, the type `**u8` | Compiles |
| `&&T` | EN0702 |
| `node.type`, `Point { type: 1 }`, `class Token { type: string; }`, `Stack<i64>.empty()`, `i64[].withCapacity(8)` | Compiles |
| `function f<'a>(x: &'a string)` | EN1005 |
| `const c = 'a';`, `f(x, 'a b')` | Compiles; they are strings |
| Local of `@align(A)` for A = 16, 64, 4096 under `none`, `linear`, `chaos` | Address mod A is 0 |
| LIR: `idx` in `rsi`, `len` in `rdi` at a bounds stub | Panic reports both correctly |
| `test("x", () => { fs.readFile("/home/x/.ssh/id_rsa"); }, { allow: ["read:/"] });`, `allow: ["read:../x"]` | EN1111 |
| Function-value bytes forged in guest `unsafe`, then called in the VM | Bad function pointer fault, session survives |

**`for...of` and array spread.** Where no result is stated with `rustc`, the program was traced by hand through O9-O11 and `ARCHITECTURE.md` section 6.2. "Twin" means a `rustc` twin by the translation of section 13. "Warns" means it compiles, with EN0719 anchored on the `for` line.

| Fixture | Must give |
|---|---|
| The owner's forms: `let queue = ["a", "b"]; for (const job of queue) { queue.push("retry"); }` | Warns (G21) |
| `for (const job of [...queue]) { queue.push("retry"); }` | Compiles with no warning; 2 turns, 4 items |
| `for (const job of queue) { queue.push("retry"); console.log(job); }` | EN0706 only (G08) |
| `queue.push(job.clone());` in the body | Warns; O6 takes the receiver's auto-borrow after the argument |
| `const xs = []; xs.push(1);`; `for (const x of &mut xs)` on a `const` | EN0614; EN0608 at the source |
| `let x = 12; const y = &x;` then `y = &z;`; then `x = 13;` before the last use of `y`; then after it | EN0613; EN0706; compiles |
| `const y = &mut x; *y = 13;`; `const r = &mut q; for (const x of r) { *x = 1; }` | Compiles |
| EN0719 fires on: `q.push`, `o.clear()` with source `o.items`, `reset(&mut o)`, `o = make()`, `g(q)` with `q: &mut`, `const r = &mut q; r.push(1)`, `run(() => { q.push(1); })`, `take(q); q = [];`, `if (c) { q.push(1); }` | Warns |
| No EN0719 on: `q[i] = v`, a `T[N]` source including assigning it a new fixed array (`a = [0; 3]`), a `for(;;)` loop, `[...q]`, `grid[r]`, `q.push(1); break;`, `q.clear(); return;`, `for (const x of &mut xs) { *x = 1; }` | Compiles with no warning |
| `for (const a of q) { for (const b of q) { q.push(1); } }`; `queue.push(a); queue.push(b);` | Two warnings; one warning |
| `const q = [1]; for (const x of q) { q.push(2); }` | EN0614 alone, no warning |
| An unrelated EN0706 on `q` after a growing loop | Both, ending `; 1 warning emitted` (G23) |
| Nested, outer element used after an inner push: `for (const a of xs) { for (const b of xs) { xs.push(1); } console.log(a); }` | EN0706 (twin E0502) |
| Inner source is the outer element: `for (const row of grid) { for (const c of row) { grid.push([]); } }` | EN0706, labelled `the loop reads `row` again here` (twin E0502). With `break` after the push: compiles (twin accepts) |
| Nested exclusive over `xs: &mut T[]`: live `a` at the inner `&mut (*xs)[j]`; outer `&mut` element live at an inner shared head | EN0707; EN0708 |
| `saved = job; queue.push(s); use(saved);`, and `best = x` with `q.push` while `best` is live | EN0706 (twin E0502); the head's join carries `queue[*]` |
| A `const` binding over many turns | No EN0613: `StorageDead(x)` resets its init state each turn |
| `prev = x` in `for (const x of &mut xs)`, used next turn; `let keep: &mut i64 \| null = null; for (const x of &mut q) { if (c) { keep = x; } } use(keep);` | One EN0707 each, no EN0708 (twin E0502 and E0499): the head's `Len` and the bind conflict on one key, and the `Ref` wins; `kill(x)` removes only loans rooted at `x` |
| `let keep: &mut i64 \| null = null; for (const x of &mut q) { keep = x; } use(keep);` | One EN0708 at the source, no EN0707 (twin E0502 only): `keep` is overwritten before any read on the path from the bind, so it is dead there. It is live at the head, through the exit to `use(keep)`, so only the head's `Len` conflicts |
| `const fst = xs.first();` used after `for (const x of &mut xs)`; used after a push in a shared loop | EN0706 at the bind; EN0706 at the push (twin E0502) |
| `const r = &mut q; for (const x of q) { r.push(1); }` | EN0708 at the head read |
| `const r = &queue; for (const job of r) { queue.push("x"); }` | EN0706; the head reads through `r` |
| `for (const x of &queue) { queue.push("r"); }` and `for (const x of (queue)) { queue.push("r"); }` | Warns, the same as `queue` |
| `xs = []` in the body, `x` dead; `x` live | Warns; EN0706 and no EN0711 |
| `let q = [1, 2, 3]; for (const x of q) { console.log(x); q = []; }`; the same with `q = [7, 8, 9];` | Warns. Prints `1`, then `1 8 9`, because the next head reads the assigned array at the same hidden index. JS prints `1 2 3` for both, because its iterator keeps the first array |
| `take(q);`, `consume(xs);` in the body | One EN0611 at the move, source as secondary (twin E0382) |
| `take(q); break;`; `take(q); return;`; `take(q); q = [];` | Compiles (twin accepts); the same; warns |
| `x` live across `take(q)` | EN0709 |
| `continue outer` that re-enters an inner loop after a move of its source | EN0611, through the CFG |
| `function f(arr: D[3]) { for (const d of arr) { consume(arr); } }`, including with `d` unused | EN0611: the head and the unconditional bind read `arr` |
| Source `h.items`: moving `h`, an `own` method on `h`; `take(h.other);` with no reinitialisation; a `Drop` prefix; field-by-field reassembly | EN0611; EN0611 at the move, which reaches itself (twin E0382); EN0607; EN0601 |
| Source `h.items`: `take(h.other); h.other = [];`; `take(h.other); break;`; `take(h.other); h.other = [x.clone()];` with `x` live | Compiles with no warning (twin accepts): the field is disjoint from the source |
| `q: &mut T[]`: `grow(q)` with `x` dead; `*q = []` with `x` live | Warns (twin accepts); EN0707 |
| `this.items` in a `mut` method: `x` is `&F`; `x` live across `this.items.push` or `this.reset()` | EN0706, by prefix overlap |
| `for (const x of *b)` with `b: Box<T[]>`: `b = new Box(...)` or `b.unbox()` with `x` live; with `x` dead | EN0706 or EN0709, a `BoxDeref` path is deep; `b = new Box(...)` warns, and `b.unbox()` is one EN0611 at the move, with the source as secondary |
| `for (const x of b)` with `b: Box<T[]>` | EN1015 with a `*b` help |
| `let r = &a; for (const x of r) { r = &b; }` | Warns; later turns read `b` (twin accepts) |
| `let r = &a; for (const x of r) { const b = [1]; r = &b; }` | EN0711 (twin E0597) |
| `let r = &a; for (const x of r) { saved = x; r = &b; a.push(s); use(saved); }` | EN0706 (twin E0502); `saved` keeps `held(r)` after `kill(r)` |
| `r = &mut *b` as the body, `x` dead | Warns (twin accepts) |
| Cursor descent `r = &mut x.children` as the body; `r = &mut *r` with a saved element live | Compiles, the tree keeps targets disjoint (twin accepts); EN0707, `kill` cannot launder a loan |
| `run(() => { xs = []; })` with `x` dead; `x` live; capturing `x` and writing `xs` in one arrow, in either order | Warns (twin accepts); EN0715 (twin E0502); EN0715 |
| The source forms: `this.view` with `get view(): &T[]`, `first(&q)`, `c ? a : b` of references, `r!`, `make().items`, `grid[r]`, `unsafe { for (const x of *p) { (*p).push(1); } }`, `TABLE` | Once, by the `for...of` table; EN0706 or EN0707 where a live `_src` conflicts; no loan on the last two |
| `for (const x of grid[r]) { grid.push([]); }` | EN0706, "cannot change while this loop is reading it" (twin through `let s = &grid[r];`) |
| R3 with no `_src`: `function f(xs: &mut T[]): &mut T { for (const x of xs) { if (c(x)) { return x; } } panic("none"); }` | Compiles; `held(x)` includes `Param(0)`. The twin is rejected (E0499 and E0502, the second from `xs.len()` at the head), as the existing row for NLL problem case #3 records |
| The tour, `Ownership in three lines`, S5's `longest = w`, and S5's `for (const n of &mut nums) { *n *= 2; }` | Compile under the new lowering, with no warning |
| `class H { items: string[] \| null = null; }` with `if (h.items != null) { for (const s of h.items) { wipe(h); } }` | EN0401 at the source, naming `wipe(h)`; the same for `wipe(this)`, `f(h)` through a closure parameter, and `h?.wipe()` |
| `const g = h; g.items = null;` and `const { items } = h; *items = null;` then a read of `h.items`, with no loop | The fact has died, so the read is EN0303 or EN0401 by its use, not a tag panic |
| Under `p != null`: `for (const x of p) { p = null; }`, `o.take()`, `mem.replace(&mut o, null)`, a write in an arrow, `take(p)`, a kill before `continue` | EN0401 with a note naming it |
| Under `p != null`: `for (const x of p) { p = null; break; }`; `for (const x of p) { p = null; if (p == null) { break; } }` | Compiles; warns, because the fact is back at the back edge |
| Under `p != null`, with `p: string[] \| null`: `for (const x of p) { p = null; break; } console.log(p.length);`; the same with `const r: &string[] = p;` as the read | EN0303; EN0401. The `break`'s state lacks the fact, so the join after the loop does too, and this never reaches a `CheckTag` panic |
| Under `p != null`, with `p: string[] \| null`: `outer: for (const a of p) { for (const x of p) { p = null; break outer; } } console.log(p.length);`; the same with `const r: &string[] = p;` as the read | EN0303; EN0401. `break outer` records its state for `outer` |
| Under `p != null`: `for (const x of p) { if (c) { p = null; break; } } console.log(p.length);`; `for (const x of p) { p = null; if (p == null) { break; } } console.log(p.length);` | EN0303 each. One `break` without the fact is enough, even when the back edge has it |
| Under `p != null`: `outer: for (const a of p) { while (c) { p = null; break outer; } }` | EN0401 at the source. The prescan of the `while` kills the fact at its own head, so the back edge of `outer` lacks it |
| Under `p != null`: `for (const x of p) { if (c) { break; } } console.log(p.length);`; `for (const x of p) { if (c) { p = null; return; } } console.log(p.length);`; `outer: for (const a of p) { for (const x of p) { if (c) { p = null; break outer; } } console.log(p.length); }` | Compiles with no warning. Every `break` of the loop holds the fact, a `return` never reaches the join, and `break outer` is not a `break` of the inner loop |
| Under `p != null`: `for (const x of [...p]) { p = null; }`, `for (const x of &mut p) { *x = 1; }` | Compiles |
| Under `o != null`: `for (const x of o.kids) { o = null; }` with `get kids(): &T[]` | No EN0401, because the source is evaluated once. EN0706, because `_src` holds the getter's loan on `o` |
| Under `p != null`: `for (const x of p) { p.push(1); }` | Warns |
| `.mir`: a narrowed head, with both `CheckTag` and `CheckBounds` before the projection | Passes the verifier; a statement between them fails it |
| `class M {} let xs = [new M()]; for (const x of xs) { xs.push(new M()); }` under fuel | T0004; `class M {}` at `length == isize.MAX` on `vm32` panics `capacity overflow` |
| Spread: `[...a, f(&mut a)]`, `[f(&mut a), ...a]`, `a = [...a, x]` | Compiles; order as SPEC 4.13 |
| `[...a, g()?]` with `g` failing | `Err` returned, the built part dropped, `allocs: balanced` |
| `[...move a]`; `a.extendCloned(&a)` | EN0401; EN0706, the receiver borrow is taken last |
| `const f: i32[3] = [1, 2, 3]; const c = [...f];`, `[...&f]`, `function g(a: &i32[3]): i32[] { return [...a]; }`, `[...&mut q]` on a `let`, `[...r]` with `r: &mut T[]` then a use of `r` | Compiles |
| `const r = &mut f; const c = [...f]; r[0] = 1;`; `[...&mut q]` on a `const` | EN0708; EN0608 |
| `[...b]` with `b: Box<T[]>`, `[...5]`, `[..."abc"]`, `[...o]` with `o: T[] \| null` | EN0438, with a `...*b` help on the first |
| `const a: i64[3] = [...b];`, `const n: (i64 \| null)[] = [...xs];`, `[0, ...xs]` at `(i64 \| null)[]`, `[...a, ...b]` of `i32[]` and `i64[]` | EN0401, the second and third with a `.map` help |
| `let q; const c = [...q]; q = [1];`; `let q = []; const c = [...q]; q.push(1);`; `[...[]]` with no expected type | EN0410; compiles; EN0410 |
| `<T>(xs: &T[])`, `T extends Clone`, `T extends Copy`, each with `[...xs]` | EN0438 (G22); compiles; compiles |
| Elements: `i64`, `(*u8)[]`, a Copy class with a raw pointer, a class with a `Box<Node> \| null` field, `T \| null`, `i64[2][]`, `Box<i64>[]`, `Result<i64, string>[]` | Compiles; a `.clone()` on each resolves too |
| Elements: a `Drop` class with no `clone`, a non-Copy class with a raw pointer field; a `Drop` class with one | EN0438; compiles |
| `const Y = [...X];`, top-level `let`, `RepeatLit` count, `T[N]` length, `assert`, each spreading | EN0412 with the note, before any EN0401 |
| `const ys = [...xs];` in a function, and a field initialiser `items: i64[] = [...BASE];` | Compiles |
| `[...p]` under `p != null`, `[...x]` with `x` a for...of binding of `T[]` | Compiles |
| `for (const j of [...queue]) { queue.push(s); }`, and `[...queue.clone()]` | Compiles; a statement temporary's loan dies by liveness |
| `[...a]` on a freestanding target with no allocator; reached from an `@interrupt` function | EN0820; EN0824 |
| User `clone` with `this`: it has no route to the source in safe code | Corpus trace; `Atomic` only |
| Deferred forms: `f(...a)`, `new C(...a)`, `console.log(...a)`, rest parameters, `(...a) => 1`, `{...o}`, `Point { ...p }`, `const { a, ...r } = p`, `xs[...i]`, `for (const x of ...a)`, `@d([...a])`, `[a, ...r] = xs`, `const [a, ...r] = xs` | EN1013 at `...`, and no EN0217, EN1010 or EN0114 |
| `[a, r] = xs`; `const [a, r] = xs` | EN1010 |
| `[...a; 3]`; `[...0..n]`; `for (const i of a...b)` | EN0100 at `;`; at `..`; at `...`, with a fix-it to `..` |
| Lexer: `0..n`, `[...a]`, `[....5]`, `a...b`, `5...` | The tokens of SPEC 2; `.5` is EN0006 |
| `i64[].withCapacity(8)` beside `x[...` | The first is a `TypeMember`; the second is EN1013 |

**Corpus programs for the same rules,** all cells unless stated, each with `//! allocs: balanced` where it terminates: growth visible to later turns; removal ending the loop early, and a regrow in the same turn seen at the next head; source assignment, to a longer and to a shorter array; zero-sized elements with `break`; elements with `Drop` under `ds.pop()`, `ds.truncate(0)` and `*x = v`, with a drop trace; spread order; deep clone independence; `break` over `[...q]`; `a = [...a]`; a panic mid-clone, whose partial output leaks and is exempt from the balance check (D6). On `//! cells: vm` only: `out of memory` at `--max-memory`. Accepted path-source programs also run under `--oracle`, and any fault is a soundness bug.

**Hermeticity:**
- `Cargo.lock` lists only workspace crates.
- `enrang build` succeeds with an empty `PATH`, so it cannot invoke `cc`, `as` or `ld`.
- Output has no `PT_INTERP` or `DT_NEEDED`.
- PE imports only `kernel32.dll`.
- Two builds are byte-identical.

**Production:** no VM or test machinery in release output; test items stripped byte-identically; `@was` and `@devMigrate` inert. **Cross-language:** no compiler-inserted helper reaches itself; no `HostCall` outside `os/vm`; the whole library checks clean per target.

## 19. How Windows, i386 and boot tests run here

**x86-64 Linux.** Native.

**i386-linux.** Natively through IA32 emulation (`CONFIG_IA32_EMULATION=y`). An ELF32 using `int 0x80` was built and executed here [measured]. A syscall-list test asserts `i386-linux` output uses only SPEC 8.4's old syscalls.

**Windows.** The real `.exe` runs from WSL through interop, written to the Linux filesystem. A hand-built PE32+ ran this way, and a spawn of `cmd.exe` through interop took 178 ms [measured], on Windows 10.0.26300. No Wine. Parallel interop throughput is measured at M7, and the cell's parallelism is set from that. PE structure is also checked by the own parser and `objdump -p`. Three extra tests cover what pipes and Linux cannot show:

- A 1 MiB local on the `win64` cell, plus an LIR golden of the descending probe order. Linux would hide a wrong order.
- The smallest possible program, with no statics and no fixups, runs through interop, because an empty `.data` section is refused by the loader [measured].
- Interop gives pipes, so `WriteConsoleW` never runs in the cell. A smoke test runs `cmd.exe /c start /wait /min x.exe` and asserts an exit code that encodes `WriteConsoleW`'s success.

**Boot without an emulator: the bench.** QEMU and OVMF are not installed, there is no `/dev/kvm`, and nothing else here can execute boot code or the 386 detection branches. So `enrang-testkit` contains `x86sim`, about 3,000 lines of test-only Rust:

- **Decoder and interpreter** for 16- and 32-bit floor forms, the x87 probe forms, and `cpuid`, `rdmsr`, `wrmsr` and `mov cr3`/`mov cr4`, written from the manuals and sharing no tables with `enrang-x86`. An instruction above the model's level raises #UD.
- **Descriptor caches,** because the worst boot bugs live there. All segment registers have cached base, limit, D/B and G. Decode width comes from CS.D. Caches survive clearing PE, so a protected-to-real toggle without 16-bit descriptors keeps decoding as 32-bit and fails. Limits raise #GP. Interrupts deliver through the IVT in real mode and the IDT in protected mode, and a triple fault is a test failure.
- **CPU models:** `i386-nofpu`, `i386-387`, `i386-287` (FPU probe passes, CR0.ET clear), `i486sx`, `i486dx`, `pentium`, `k6`, `p6`, `p4`. They differ in the AC toggle, ID toggle, CPUID table and FPU presence. `pentium` and `p6` return leaf-2 style data for out-of-range high leaves, as the SDM describes.
- **Scriptable BIOS:** INT 10h, 12h, 13h, 15h. Injects what QEMU cannot easily: no LBA extensions, `AH=41h` with CF=0 but no `AA55`, `AH=42h` failing where CHS works, `AH=08h` with SPT=0, int 13h errors N times, absent port `0x92`, stuck 8042, A20 already on, `AX=2401h` failing, no E820, no E801, an 8 GiB E820 table, overlapping and unsorted E820 entries, a non-text video mode, disk geometry.
- **Devices:** VGA text memory, mono adapter, COM1 as 8250, 16450, 16550, or absent, PIC, PIT, A20 gate with a configurable 8042 latency (including a retest that stays false for the first 20 ms), `isa-debug-exit`.

**Bench assertions (300 scenarios):**

- Each stage 1 and stage 2 path, every injected failure gives its error letter or falls back correctly. No path divides by zero.
- 8086 and 286 flag behaviour gives `C`.
- **Long-mode check.** A long-mode image on `i386-nofpu`, `pentium` and `p6` prints `L` in real mode, with no false LM from out-of-range leaves and no `cpuid` on the 386.
- **Protected-mode toggle.** A kernel at `--base=0x100000` loads through the toggle and runs. Negative control: a test-only image whose GDT lacks the 16-bit descriptors must hang or fault on the bench.
- **`--base`.** One scenario per rejected range of `ARCHITECTURE.md` section 9.6, plus `bss_end` past INT 12h top and past extended memory, which print `M`.
- **Memory view.** An 8 GiB E820 table, overlapping entries, and an allocator kernel filling all of low memory on the long-mode path with a page-table checksum assertion.
- **Kernel start.** Entered with an invalid GDTR, a garbage ESP and no magic in EAX, `_start` still zeroes BSS, loads its own GDT and delivers an exception to the early IDT. A panic before `BootInfo` is recorded uses `0xB8000` and no serial.
- **Interrupts.** IRQ0 through the remapped PIC into a stub, with full register and EFLAGS comparison. Vectors with and without error codes. A panic from a handler. IRQ0 fired inside `alloc`, with a handler that does not allocate, leaves the heap consistent.
- **Stack.** A 128 KB local on a 16 KB stack reports `stack overflow`. Every panic message at the limit stays inside the reserve.
- **`cpu.has` and SSE state.** Each combination of level, float strategy and model: `--cpu=i386 --float=soft` on `p4` reports `sse2` false until `cpu.enableSse()`; `--cpu=sse2 --float=soft` leaves EM clear and OSFXSR set. The `p4` scenario at `--cpu=sse2 --float=sse2` asserts CR0 and CR4 up to the first SSE instruction, then stops, because the bench has no SSE. `i386-287` reports `fpu` false.
- S9 produces its exact COM1 bytes, with the same text in VGA memory, on `i386-nofpu`.
- A `--cpu=i686` kernel on `i386-nofpu` prints `needs i686 (CMOV); this CPU lacks it` on VGA and COM1, then halts.
- Hello kernel runs in 640 KB with no extended memory; an allocator kernel runs in 2 MB.
- A stray x87 opcode under soft-float traps through CR0.EM to the early IDT message.
- The `none-bench` conformance cell (section 12).
- From M10, stage 2's long-mode tail up to the far jump: page table contents, CR4, EFER, CR0 and selector `0x28`. The bench has no 64-bit interpreter.

**The bench proves logic, not hardware.** It shares its author's reading of the manuals. It is never counted as C3 or any other class, and the ledger shows it separately.

**Static image checks,** which run with no execution at all: floppy is exactly 1,474,560 bytes; `55 AA`; partition table fields; the six GDT descriptors of `ARCHITECTURE.md` section 9.6; `66 EA` far jump; patched parameters; stage budgets; two builds byte-identical; 16-bit `objdump` decode of stages. A corpus-level static test builds a 512-byte sector from user code with `--format=flat --base=0x7C00` and asserts `55 AA` at offset 510.

**UEFI memory map, no OVMF needed.** A unit test translates a synthetic OVMF-style memory map: only `EfiConventionalMemory` becomes usable.

**QEMU** (qemu-system-x86 8.2.2 from apt; TCG only). The owner approved installing it when M9 begins, and not before. Until it is present on a machine, these tests skip visibly:

```text
qemu-system-i386 -cpu 486 -m 32 -display none -no-reboot -serial stdio \
  -device isa-debug-exit,iobase=0xf4,iosize=4 -drive file=x.img,format=raw,if=ide
```

Use `if=floppy` for floppy images, and `-cpu core2duo` for `none-qemu-sse2`. Writing `0x10` to port `0xF4` exits with status 33, which counts as a pass. Any other status or a timeout fails. Serial bytes are compared with expected output. Tests repeat across available models. **QEMU evidence proves the boot flow, not level conformance.** Whether TCG rejects instructions above a model is unverified.

**OVMF, when installed.** The `efi-ovmf` cell puts the output at `EFI/BOOT/BOOTX64.EFI` under a directory `$ESP`, since the prototype has no FAT writer, and runs the following. Confirm the OVMF path when the package is installed.

```text
qemu-system-x86_64 -bios /usr/share/ovmf/OVMF.fd -drive format=raw,file=fat:rw:$ESP \
  -serial stdio -display none -net none -no-reboot -device isa-debug-exit,iobase=0xf4,iosize=4
```

**Bochs,** not installed; the owner approved trying it when M9 begins. It is the only emulator route to executing the AC, ID and no-FPU branches. 386 emulation needs a custom build with `--enable-cpu-level=3` per older docs, unverified for 2.7. `ENRANG_BOCHS=<path>` enables those tests.

**Owner checklist for the Q8400 (C4), from M9.** The machine is an old Acer Aspire with legacy BIOS, confirmed by the owner, who does not know the exact model and has no other old machines, so this is the only real-hardware evidence the project can get:

1. `enrang build --target=i386-none --image=hdd kernel.en`, using S9.
2. Write the image to a USB stick with a Windows raw writer: Rufus in DD mode, or Win32 Disk Imager, reading the file through `\\wsl$\...`. In WSL2 a USB stick is not a visible raw block device without usbipd, so `dd` from where the image is built does not work; use `dd` only from a bare-metal Linux. The toolchain never writes to raw devices. Double-check the device name.
3. In the BIOS setup, enable `Legacy USB Support`, and select the USB-HDD boot entry.
4. Expect `Hello from Enrang` on screen. COM1 output needs a serial cable, if the board has a header.
5. Error letters, if one appears instead:

   | Letter | Meaning |
   |---|---|
   | `C` | CPU older than 386 |
   | `D` | Disk read failed through both LBA and CHS |
   | `A` | A20 could not be enabled |
   | `M` | Kernel does not fit in memory |
   | `L` | No long mode (64-bit images only) |

6. Record the result in `evidence/hardware.txt`: board, BIOS, image, what appeared, and any error letter. Only this file fills the C4 column.
7. Repeat at M10 with `x86_64-none --image=hdd`. This machine has no UEFI, so `--format=efi` cannot be tested on it: UEFI output runs only on OVMF, or on a newer PC with Secure Boot off.

## 20. Skip notices

A missing tool never fails silently and never fails the build by default.

```text
SKIP qemu-system-i386 not found: 212 tests not run
SKIP OVMF not found: 40 tests not run
SKIP as not found: 2400 oracle tests not run
```

- Every skip appears in the final summary and in the JSON evidence.
- `ENRANG_REQUIRE=qemu,as` turns the named skips into failures. A name matches exactly or as a prefix ending at `-`, ignoring case, so `qemu` covers `qemu-system-i386`.
- OVMF is a firmware file rather than a program, so a `PATH` lookup cannot find it; the OVMF cells check its path when they arrive at M10.
- `as`, `objdump`, `readelf`, `nm`, `gcc` and `rustc` may be used only as test-time oracles. Tests using them must skip visibly if absent. They are never required to compile an Enrang program, and the empty-`PATH` hermeticity test proves it.
- gdb, strace and valgrind are not installed and nothing depends on them.
- `/mnt/c` absent: Windows cell skips with a notice.

## 21. Evidence ledger and what cannot be verified here

**Ledger.** From M4, `enrang targets --evidence` prints `evidence/ledger.json`, which the matrix driver generates from test results, plus owner-entered `evidence/hardware.txt`. Four columns per CPU family: C1 level-proven, C2 run at that level on the dev host, C3 emulated naming the model, C4 real hardware. A class is printed only if reached, and the output says which commit proved it. Today C1, C2 and C3 read `planned`, and C4 reads `no hardware` for every family except the Q8400 and `Newer` rows, which read `planned`.

**Cannot be verified on this machine, today or by any test in this repository:**

- Any behaviour on a real 386, 486, Pentium, K5, K6, K7, P6, NetBurst, Atom or mobile chip. There is no such hardware. Running a level natively here proves the code, not the chip.
- Real AC, ID and no-FPU branches of detection, on real silicon. The i5-12400F takes the modern branch only. Bench or Bochs only.
- Real CPUID values of old chips. The bench models them from the matrix in `ARCHITECTURE.md` section 8.1, whose cells have mixed evidence.
- Errata behaviour: POPAD, F00F, FDIV, K6 stepping defects, 386 multiply.
- BIOS quirks: USB type guessing, BPB patching, A20 on real chipsets, 8042 timing, floppy timing.
- 3DNow!, which this host lacks. We never emit it.
- Boot on QEMU and UEFI on OVMF until they are installed, including GOP output and the framebuffer console.
- Whether stage 1 fits 350 bytes of code with the BIOS checks of `ARCHITECTURE.md` section 9.6, until it is assembled at M9.
- Stack probes and PE loader rules on any Windows build other than 10.0.26300, where they were measured.
- Early 64-bit parts lacking CMPXCHG16B and LAHF, beyond the static audit.

**Unverified facts carried in the design:** 486 CPUID per stepping, Prescott LAHF and CMPXCHG16B per stepping, Am386 POPAD behaviour, x87 clocks, A-step CMPXCHG opcode, soft-float sizes. Docs must never claim real-chip verification that did not happen.

## 22. Speed

| Tier | Command | Budget | Contents |
|---|---|---|---|
| Default | `cargo test` | 60 s | In-process compiles, one shared parse of `core`, batched `as`, `vm64`, `lx64`, `l32-i386`, a tenth of generated volume |
| Full | `ENRANG_SCALE=10 cargo test` | 10 min | Full matrix |
| Nightly | `ENRANG_SCALE=100` | No hard limit | `rustc` twins, stepper, QEMU if present |

Exceeding a budget prints a warning and goes in the JSON evidence, because a wall-clock failure in `cargo test` would be flaky on WSL2 under load, in a suite whose principle is determinism. Only `ENRANG_REQUIRE=speed`, used on a controlled run, turns an overrun into a failure. Compiles run in-process through `enrang-driver`. For scale, `rustc` checked a 1,000-function file in 0.29 s and `/bin/true` spawned in 0.51 ms [both measured].

## 23. Definition of done per milestone

Every milestone also requires all earlier cells and meta-tests green, zero `rustc` warnings, and a runnable proof (`ARCHITECTURE.md` section 12). Counts are minimums at that milestone. "Every code" means every SPEC 13.2 row with `since` at or below that milestone.

| M | Gate |
|---|---|
| **M0** | Testkit self-tests; PRNG known answers; bless and orphan logic; code registry holds every SPEC 13.2 row with its phase, owner, `since` and fixture kind; `since` gating tested with a fake registry; renderer passes hand-built G01 shape; hermetic `Cargo.lock`; `explain` and `targets` goldens; deferred commands EN1301 and EN1302 goldens; feature and level tables tested against SPEC 10.1 |
| **M1** | 2,500 cases; 20k mutated files with no panic; AST print-reparse round trip on 2k generated programs; G01-G04 byte-exact; every `since(M1)` code; the tour and the `Ownership in three lines` block parse; parser fixtures for `a < b > (c)`, `a<b>(c)`, `f(a < b, c > (d))`, `x as usize < n`, `x as Box<i32>`; lexer fixtures for `0..n`, `[...a]`, `[....5]`, `a...b`; every EN1013 form of section 18, `[...a; 3]` and `[...0..n]` |
| **M2** | 2,500 more cases; Maranget against brute force; G05, G06, G12, G13, G17, G19, G20, G22 byte-exact; the spread typing and `Clone` rows of section 18; narrowed `for...of` sources checked at their back edges, and the state after the loop joined over its `break`s; SPEC 11 worked sizes for both `P`; every `since(M2)` code; every `C` row covered with an accept and a reject; the exact-satisfaction rule of SPEC 4.4 has a fixture per clause |
| **M3** | 4,000 more cases, half negative with fixed siblings; MIR verifier after every pass, including a narrowed `for...of` head; `.mir` module round trip, with fixtures needing no front end; `remap_ids` text fixtures; G07-G11, G16, G18, G21, G23 byte-exact; every row of the `for...of` table and the EN0719 fire and no-fire lists of section 18; `rustc` twin disagreements all named; every `since(M3)` code; every `H` row covered; drop-trace fixtures for the D2 temporary table and for partly moved `T \| null`, `Result` and a user enum |
| **M4** | 300 corpus programs on `vm64` and `vm32`, including those of section 18 for `for...of` and spread; S1-S8, S10, S11 byte-exact; all accepted programs fault-free; every fault detector fires; every MIR statement kind hit; no `Asm` in the mono closure of S1-S8, S10 and S11; must-fail suite exact for each matcher and T code; leak gate on; reporters and snapshots golden; VM speed measured and recorded |
| **M5** | All forms through byte oracle and level oracle, all exceptions recorded, no stale row; 500 corpus programs VM equals `lx64`; 10k `GenExpr` differential; `none`, `linear`, `chaos` agree; output audit on the corpus; hello ELF64 at most 12 KB; empty-`PATH` build; G15 byte-exact; `readelf` and own parser agree |
| **M6** | 400 reload scenarios; every `MIG`, `REF`, `FAIL` and `ADV` row covered; worked scenario golden; each grant denied; refused means unchanged heap hash; `GenSchema` 2k walks; release output free of machinery; `@was` and `@devMigrate` inert byte-identically |
| **M7** | Full corpus through interop equals `lx64`; PE checks by own parser and `objdump -p`; only `kernel32.dll` imported; `.reloc` covers all absolute data (tested by loading with `DYNAMIC_BASE`); hello PE at most 16 KB; 1 MiB local and smallest-program tests pass; `WriteConsoleW` smoke test; parallel interop throughput measured |
| **M8** | Full corpus at all `l32-*` cells; audit at every level; 2M soft-float vectors bit-exact across the section 16 chain; 100k `GenPair` vectors; old-syscall list; level diagnostics and clean-failure messages golden; stepper sample clean; allocator at most 2 KB; soft-float at most 16 KB; `core`+`alloc`+`os` no floats at most 32 KB; hello ELF32 at most 12 KB |
| **M9** | 300 bench scenarios, including the toggle's negative control; S9 exact on bench; `none-bench` cell green; `none-qemu-sse2` written and skipping visibly; static image checks; user-code boot sector test; floppy exactly 1,474,560 bytes; stage 1 at most 350 B code, stage 2 at most 4 KB, hello kernel at most 16 KB in 640 KB; G14 byte-exact; floor audit of kernel and stages; QEMU tests written and skipping visibly, run if installed; owner checklist published |
| **M10** | Static checks of `x86_64-none` images; bench runs the long-mode check on `i386-nofpu`, `pentium` and `p6`, then stage 2's tail up to the far jump, and asserts page tables, CR4, EFER, CR0 and selector `0x28`; UEFI memory-map translation tested with no OVMF; 64-bit kernel code runs only under QEMU, skipping visibly until then; audit at `generic64` rejects CMPXCHG16B, LAHF, SAHF, POPCNT in baseline; PE32+ EFI checks with mandatory `.reloc` and no imports; OVMF tests written and skipping visibly; ledger generated with every family's classes accurate |
