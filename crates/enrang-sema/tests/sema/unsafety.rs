//! The five unsafe powers (plan d.17; SPEC 5.9 S:1096-1102; owner 4E): outside
//! `unsafe`, dereferencing a raw pointer (`*p` and the `*T` access methods), calling
//! an `unsafe`, `declare` or `@abi` function or an `unsafe fn` value, `asm`, and
//! reading, writing or borrowing an `unsafe let` or `@at` storage are EN0801 (G13
//! byte for byte); a `@requires` function is EN0907 instead; calling an `@interrupt`
//! function is EN0807; a safe function that reads or writes through a raw-pointer
//! parameter gets warning EN0828, unless a base method or an interface member fixes
//! its signature (T:912).

use enrang_testkit::Harness;

use crate::positions::{check, check_on, compiles, golden, renders, reports, shown};

pub fn register(h: &mut Harness) {
    g13(h);
    derefs(h);
    calls(h);
    asm_and_statics(h);
    inside_unsafe(h);
    requires_and_interrupts(h);
    en0828(h);
    review(h);
}

fn g13(h: &mut Harness) {
    h.case("unsafety/G13 byte-exact through load and analyze", || {
        golden("G13");
    });
}

/// Power 1: dereferencing a raw pointer.
fn derefs(h: &mut Harness) {
    h.case("unsafety/reading `*p` outside `unsafe` is EN0801, wrapped by its help", || {
        renders(
            "private unsafe function f(p: *u8): u8 { return g(p); }\nprivate function g(p: *u8): u8 { return *p; }\n",
            "error[EN0801]: reading through a raw pointer needs `unsafe`
 --> main.en:2:41
  |
2 | private function g(p: *u8): u8 { return *p; }
  |                                         ^^ this dereferences `p`, a `*u8`
  |
  = rule: `unsafe` grants exactly five powers; this one is \"dereference a raw pointer\". Nothing checks the address for you.
help: state that you have checked the address
  |
2 | private function g(p: *u8): u8 { unsafe { return *p; } }
  |                                  +++++++++          ++
  = explain: run `enrang explain EN0801`

error: aborting due to 1 previous error
",
        );
    });
    h.case("unsafety/writing `*p = 1` outside `unsafe` is EN0801", || {
        reports(
            "private function f(p: *u8): void { *p = 1; }\n",
            &["EN0801 `*p` writing through a raw pointer needs `unsafe` [this dereferences `p`, a `*u8`]"],
        );
    });
    h.case(
        "unsafety/borrowing `&*p` outside `unsafe` is EN0801, with a help that edits nothing",
        || {
            let r = check("private function f(p: *u8): void { const r = &*p; }\n");
            assert_eq!(
                shown(&r),
                ["EN0801 `*p` borrowing through a raw pointer needs `unsafe` [this dereferences `p`, a `*u8`]"],
                "{}",
                r.rendered()
            );
            let help = &r.diags[0].helps[0];
            assert_eq!(
                help.message,
                "state that you have checked the address, in an `unsafe { }` block"
            );
            assert!(help.edits.is_empty());
        },
    );
    h.case("unsafety/each `*T` access method outside `unsafe` is EN0801", || {
        reports(
            "private function f(p: *u16): void {
  p.write(1);
  p.read();
  p.writeVolatile(1);
  p.readVolatile();
  p.writeUnaligned(1);
  p.readUnaligned();
}
",
            &[
                "EN0801 `p.write(1)` writing through a raw pointer needs `unsafe` [`write` dereferences `p`, a `*u16`]",
                "EN0801 `p.read()` reading through a raw pointer needs `unsafe` [`read` dereferences `p`, a `*u16`]",
                "EN0801 `p.writeVolatile(1)` writing through a raw pointer needs `unsafe` [`writeVolatile` dereferences `p`, a `*u16`]",
                "EN0801 `p.readVolatile()` reading through a raw pointer needs `unsafe` [`readVolatile` dereferences `p`, a `*u16`]",
                "EN0801 `p.writeUnaligned(1)` writing through a raw pointer needs `unsafe` [`writeUnaligned` dereferences `p`, a `*u16`]",
                "EN0801 `p.readUnaligned()` reading through a raw pointer needs `unsafe` [`readUnaligned` dereferences `p`, a `*u16`]",
            ],
        );
    });
    h.case("unsafety/a raw pointer's safe members compile outside `unsafe`", || {
        compiles(
            "private function f(p: *u8): usize { const q = p.add(1); const n = q.isNull(); return q as usize; }\n",
        );
    });
}

/// Power 2: calls.
fn calls(h: &mut Harness) {
    h.case("unsafety/calling an `unsafe function` outside `unsafe` is EN0801", || {
        renders(
            "private function f(): void { g(); }\nprivate unsafe function g(): void {}\n",
            "error[EN0801]: calling `g` needs `unsafe`
 --> main.en:1:30
  |
1 | private function f(): void { g(); }
  |                              ^^^ `g` is `unsafe`
  |
  = rule: `unsafe` grants exactly five powers; this one is \"call an `unsafe` function\". Nothing checks that its conditions hold.
help: state that you have met its conditions
  |
1 | private function f(): void { unsafe { g(); } }
  |                              +++++++++    ++
  = explain: run `enrang explain EN0801`

error: aborting due to 1 previous error
",
        );
    });
    h.case(
        "unsafety/an `unsafe` method, through a class and through a bound, is EN0801",
        || {
            reports(
                "public interface U { unsafe poke(): void; }
public class A { public unsafe poke(): void {} }
private function g<T extends U>(x: &T, a: &A): void { x.poke(); a.poke(); }
",
                &[
                    "EN0801 `x.poke()` calling `poke` needs `unsafe` [`poke` is `unsafe`]",
                    "EN0801 `a.poke()` calling `poke` needs `unsafe` [`poke` is `unsafe`]",
                ],
            );
        },
    );
    h.case(
        "unsafety/an `unsafe` library function outside `unsafe` is EN0801",
        || {
            reports(
                "private function f(d: *u8): void { mem.set(d, 0, 4); }\n",
                &["EN0801 `mem.set(d, 0, 4)` calling `set` needs `unsafe` [`set` is `unsafe`]"],
            );
        },
    );
    h.case("unsafety/calling a `declare function` outside `unsafe` is EN0801", || {
        let r = check_on(
            "@dll(\"kernel32.dll\") private declare function GetTickCount(): u32;\nprivate function f(): u32 { return GetTickCount(); }\n",
            "x86_64-windows",
        );
        assert_eq!(
            shown(&r),
            ["EN0801 `GetTickCount()` calling `GetTickCount` needs `unsafe` [`GetTickCount` is a `declare function`]"],
            "{}",
            r.rendered()
        );
    });
    h.case(
        "unsafety/calling through an `unsafe fn` value is EN0801",
        || {
            reports(
                "private function f(g: unsafe fn() => void): void { g(); }\n",
                &["EN0801 `g()` calling `g` needs `unsafe` [`g` is an `unsafe fn`]"],
            );
        },
    );
    h.case("unsafety/calling through an `@abi` function pointer is EN0801", || {
        reports(
            "private type Cb = @abi(\"win64\") fn(x: u32) => u32;\nprivate function f(cb: Cb): u32 { return cb(1); }\n",
            &["EN0801 `cb(1)` calling `cb` needs `unsafe` [`cb` runs foreign code through `@abi(\"win64\")`]"],
        );
    });
    h.case("unsafety/a safe `fn` value and a safe function compile", || {
        compiles(
            "private function f(g: fn() => void): void { g(); h(); }\nprivate function h(): void {}\n",
        );
    });
    h.case(
        "unsafety/Q39-from-raw: `Slice<u8>.fromRaw` outside `unsafe` is EN0801, `asPtr` compiles",
        || {
            reports(
                "private function f(p: *u8): void { const v = Slice<u8>.fromRaw(p, 4); }\n",
                &["EN0801 `Slice<u8>.fromRaw(p, 4)` calling `fromRaw` needs `unsafe` [`fromRaw` is `unsafe`]"],
            );
            compiles(
                "let backing: u8[6] = [0; 6];\nconst q = backing.asPtr();\n",
            );
        },
    );
}

/// Powers 3, 4 and 5.
fn asm_and_statics(h: &mut Harness) {
    h.case("unsafety/`asm` outside `unsafe` is EN0801", || {
        renders(
            "private function f(): void { asm(`nop`); }\n",
            "error[EN0801]: `asm` needs `unsafe`
 --> main.en:1:30
  |
1 | private function f(): void { asm(`nop`); }
  |                              ^^^^^^^^^^ this runs instructions no check can see into
  |
  = rule: `unsafe` grants exactly five powers; this one is \"`asm`\". Nothing checks what the instructions do.
help: state that you have checked the instructions
  |
1 | private function f(): void { unsafe { asm(`nop`); } }
  |                              +++++++++           ++
  = explain: run `enrang explain EN0801`

error: aborting due to 1 previous error
",
        );
    });
    h.case(
        "unsafety/reading, writing and borrowing an `unsafe let` outside `unsafe` is EN0801",
        || {
            reports(
                "private unsafe let count: i64 = 0;
private function f(): void {
  count = 1;
  console.log(count);
  const r = &count;
}
",
                &[
                    "EN0801 `count` using `count`, an `unsafe let`, needs `unsafe` [this writes the static storage `count`]",
                    "EN0801 `count` using `count`, an `unsafe let`, needs `unsafe` [this reads the static storage `count`]",
                    "EN0801 `count` using `count`, an `unsafe let`, needs `unsafe` [this borrows the static storage `count`]",
                ],
            );
        },
    );
    h.case("unsafety/`@at` storage outside `unsafe` is EN0801, power 5", || {
        let r = check_on(
            "@at(0xB8000) private unsafe let screen: u16[2000];\nprivate function f(): void { screen[0] = 0x0741; }\n",
            "i386-none",
        );
        assert_eq!(
            shown(&r),
            ["EN0801 `screen` using `screen`, an `unsafe let`, needs `unsafe` [this writes the static storage `screen`]"],
            "{}",
            r.rendered()
        );
        assert_eq!(
            r.diags[0].entries[0].text,
            "`unsafe` grants exactly five powers; this one is \"access `@at` storage\". Nothing checks the address for you."
        );
    });
}

/// Inside `unsafe`, the powers are granted.
fn inside_unsafe(h: &mut Harness) {
    h.case(
        "unsafety/every power compiles inside an `unsafe` block",
        || {
            compiles(
                "private unsafe let count: i64 = 0;
private unsafe function g(): void {}
private function f(h: unsafe fn() => void): void {
  const p = 0x1000 as *u16;
  unsafe {
    const x = *p;
    g();
    h();
    asm(`nop`);
    count += 1;
    const r = &count;
  }
}
",
            );
        },
    );
    h.case(
        "unsafety/an `unsafe function`'s body is inside `unsafe`, and so is a `@naked` one",
        || {
            compiles(
                "private unsafe function f(p: *u8): u8 { p.write(1); return *p; }\n@naked private unsafe function n(): void { asm(`ret`); }\n",
            );
        },
    );
    h.case(
        "unsafety/G13's statement wrapped as its help says compiles",
        || {
            compiles("const VGA = 0xB8000 as *u16;\nunsafe { VGA.writeVolatile(0x0741); }\n");
        },
    );
    h.case(
        "unsafety/an arrow inside `unsafe` may use the powers, one outside may not",
        || {
            reports(
                "private function f(): void {
  const p = 0x1000 as *u8;
  unsafe { const g = (): u8 => *p; }
  const h = (): u8 => *p;
}
",
                &["EN0801 `*p` reading through a raw pointer needs `unsafe` [this dereferences `p`, a `*u8`]"],
            );
        },
    );
}

/// EN0907 and EN0807.
fn requires_and_interrupts(h: &mut Harness) {
    h.case(
        "unsafety/a `@requires` function outside `unsafe` is EN0907, not EN0801",
        || {
            renders(
                "@requires(\"cmov\") private function pick(): void {}\nprivate function f(): void { pick(); }\n",
                "error[EN0907]: calling `pick` needs `unsafe`, because it requires `cmov`
 --> main.en:2:30
  |
2 | private function f(): void { pick(); }
  |                              ^^^^^^ the CPU this runs on may lack what it requires
  |
help: state that you have met its conditions
  |
2 | private function f(): void { unsafe { pick(); } }
  |                              +++++++++       ++
  = explain: run `enrang explain EN0907`

error: aborting due to 1 previous error
",
            );
        },
    );
    h.case("unsafety/a `@requires` function inside `unsafe` compiles", || {
        compiles(
            "@requires(\"cmov\") private function pick(): void {}\nprivate function f(): void { unsafe { pick(); } }\n",
        );
    });
    h.case(
        "unsafety/calling an `@interrupt` function is EN0807, inside `unsafe` too",
        || {
            let src = "@interrupt private function onTimer(frame: &InterruptFrame): void {}
private function f(frame: &InterruptFrame): void {
  onTimer(frame);
  unsafe { onTimer(frame); }
}
";
            let r = check_on(src, "i386-none");
            assert_eq!(
                shown(&r),
                [
                    "EN0807 `onTimer(frame)` an interrupt handler can't be called [`onTimer` is an `@interrupt` function, which only the CPU calls]",
                    "EN0807 `onTimer(frame)` an interrupt handler can't be called [`onTimer` is an `@interrupt` function, which only the CPU calls]",
                ],
                "{}",
                r.rendered()
            );
        },
    );
}

/// Warning EN0828 and its exemptions (S:1197, T:614, T:912).
fn en0828(h: &mut Harness) {
    h.case(
        "unsafety/EN0828: a safe function writing through a raw-pointer parameter",
        || {
            renders(
                "private function fill(p: *u8): void { unsafe { p.write(1); p.write(2); } }\n",
                "warning[EN0828]: `fill` writes through the raw pointer `p`
 --> main.en:1:48
  |
1 | private function fill(p: *u8): void { unsafe { p.write(1); p.write(2); } }
  |                                                ^^^^^^^^^^ `p` holds whatever address a caller passes
  |
help: mark it `unsafe function`, or take a reference
",
            );
        },
    );
    h.case(
        "unsafety/EN0828 once per parameter, reading through `*q` and through `p.add(1)`",
        || {
            let r = check(
                "private function f(p: *u8, q: *u8): void { unsafe { p.add(1).write(*q); *q = 0; } }\n",
            );
            assert_eq!(
                shown(&r),
                [
                    "EN0828 `p.add(1).write(*q)` `f` writes through the raw pointer `p` [`p` holds whatever address a caller passes]",
                    "EN0828 `*q` `f` reads through the raw pointer `q` [`q` holds whatever address a caller passes]",
                ],
                "{}",
                r.rendered()
            );
            assert!(r.program.is_some(), "a warning stops nothing");
        },
    );
    h.case(
        "unsafety/EF-06: with its help applied (`unsafe function`) EN0828 is gone",
        || {
            compiles(
                "private unsafe function bufSink(ctx: *u8, bytes: *u8, n: usize): void { const b = *bytes; }\n",
            );
        },
    );
    h.case(
        "unsafety/EF-06: a method whose signature a base method or an interface member fixes",
        || {
            compiles(
                "public interface Reader { readAt(p: *u8): u8; }
public class Base { public get(p: *u8): u8 { return 0; } }
public class Raw extends Base implements Reader {
  public readAt(p: *u8): u8 { unsafe { return *p; } }
  public override get(p: *u8): u8 { unsafe { return p.read(); } }
}
",
            );
        },
    );
    h.case(
        "unsafety/a base method no base or interface fixes gets EN0828",
        || {
            reports(
                "public class Base { public get(p: *u8): u8 { unsafe { return p.read(); } } }\n",
                &["EN0828 `p.read()` `get` reads through the raw pointer `p` [`p` holds whatever address a caller passes]"],
            );
        },
    );
    h.case(
        "unsafety/T:614: the safe copy of `w` compiles with warning EN0828",
        || {
            reports(
                "public function w<T extends ptr.VolatileValue>(p: *T, v: T): void { unsafe { p.writeVolatile(v); } }\n",
                &["EN0828 `p.writeVolatile(v)` `w` writes through the raw pointer `p` [`p` holds whatever address a caller passes]"],
            );
        },
    );
    h.case(
        "unsafety/a raw pointer only passed on or compared gets no EN0828",
        || {
            compiles(
                "private function f(p: *u8): bool { return p.isNull(); }\nprivate function g(p: *u8): usize { return p as usize; }\n",
            );
        },
    );
}

/// Stage 6's review fixes of the five powers.
fn review(h: &mut Harness) {
    h.case(
        "unsafety/S:1096: the callee of an indirect call is walked: `(*p)()` and `pick()()`",
        || {
            reports(
                "public function f(p: *(fn() => void)): void { (*p)(); }
public function noop(): void { }
public unsafe function pick(): fn() => void { return noop; }
public function g(): void { pick()(); }
",
                &[
                    "EN0801 `*p` reading through a raw pointer needs `unsafe` [this dereferences `p`, a `*(fn() => void)`]",
                    "EN0801 `pick()` calling `pick` needs `unsafe` [`pick` is `unsafe`]",
                ],
            );
        },
    );
    h.case(
        "unsafety/S:1197: an overload no interface member fixes is not exempt from EN0828",
        || {
            reports(
                "public interface I { m(): void; }
public class C implements I {
  public m(): void { }
  public m(p: *u8): u8 { unsafe { return p.read(); } }
}
",
                &["EN0828 `p.read()` `m` reads through the raw pointer `p` [`p` holds whatever address a caller passes]"],
            );
            compiles(
                "public interface J { m(p: *u8): u8; }
public class D implements J { public m(p: *u8): u8 { unsafe { return p.read(); } } }
",
            );
        },
    );
    h.case(
        "unsafety/EN0828 through a raw-to-raw cast of the parameter (mutant M22)",
        || {
            reports(
                "public function f(p: *u8): u32 { unsafe { return (p as *u32).read(); } }\n",
                &["EN0828 `(p as *u32).read()` `f` reads through the raw pointer `p` [`p` holds whatever address a caller passes]"],
            );
        },
    );
}
