<img src="assets/icon.svg" width="64" height="64" alt="">

# Enrang

**TypeScript's feel. Rust's power. Native code, from the 80386 to today.**

Enrang is a programming language being built from scratch. It reads like TypeScript and manages memory like Rust, with no garbage collector and no lifetime syntax. Its compiler goes all the way down to machine code by itself, with no LLVM, no libc, and no external assembler or linker. It is meant for applications and for operating systems, on every x86 CPU back to the 80386.

> [!IMPORTANT]
> **Enrang can't compile a program yet, and this repository holds only its documentation.** The language is designed and the foundation is built, but the compiler doesn't exist so far. All the Enrang code and compiler output on this page is specified behaviour, not something you can run today. [Status](#status) says what exists.

## The story

I think in TypeScript. In 2019 I started my own Minecraft Bedrock server, [jukebox](https://github.com/enricoangelon/jukebox), and since 2020 I've worked on [JSPrismarine](https://github.com/JSPrismarine/JSPrismarine), a much bigger one that I still contribute to. When I wanted more speed, I wrote Rust for Node ([bytebuf](https://github.com/enricoangelon/bytebuf)), and I kept wishing for one language with Rust's power and TypeScript's feel.

There's also a machine behind this: my family's old Acer, with a Core 2 Quad Q8400. I love that era of PCs, and I don't think working machines should stop getting new software because toolchains moved on. I want to write my own operating system for it, in a language I enjoy, with a dev loop where saving a file doesn't kill the running program.

In 2024 I tried. [enan](https://github.com/enricoangelon/enan) stopped at a README and a licence, because a compiler felt too big for one person. AI agents changed that: I design and decide, agents help write and attack the code, and independent tests check it.

The name is mine too: **Enr**ico **Ang**elon. Enrang can't compile a program yet. One day it will boot that Acer.

## A first look

It reads like TypeScript:

<!-- excerpt: examples/mistakes/use-after-move.en -->
```ts
class User {
  constructor(public name: string) {}
}

function archive(u: User): void {
  console.log(u.name);
}

function main(): void {
  const u = new User("Ada");
  archive(u);
  console.log(u.name);
}
```

Then the compiler stops you, says why, and offers two ways out:

<!-- excerpt: examples/mistakes/use-after-move.stderr -->
```text
error[EN0601]: `u` is used after it was moved
  --> use-after-move.en:12:15
   |
10 |   const u = new User("Ada");
   |         - `u` owns this `User`, which is not Copy because it has a `string` field
11 |   archive(u);
   |           - moved here: `archive` takes `u: User` by value
12 |   console.log(u.name);
   |               ^ used here, after the move
   |
   = from TypeScript: both names would share one object. In Enrang a value has one owner, so passing `u` hands it over.
help: `archive` only reads `u`, so borrow it instead
   |
 5 | function archive(u: &User): void {
   |                     +
help: or pass a copy
   |
11 |   archive(u.clone());
   |            ++++++++
   = explain: run `enrang explain EN0601`

error: aborting due to 1 previous error
```

That text is the specification. The diagnostics renderer already prints it, byte for byte apart from the file name, from a hand-built error. The borrow checker that will find this mistake by itself arrives at M3.

## What makes it different

Everything in this section is the design. [Status](#status) says what exists today.

### Ownership without lifetimes

`T` hands a value over, `&T` lends it for reading, and `&mut T` lends it exclusively. There is no garbage collector. There is no lifetime syntax either, because of one rule: references live only in stack-frame slots (locals, parameters, temporaries and return values), never inside data. That single restriction removes lifetime annotations, region inference and variance, while the borrow check stays flow-sensitive. Bounds, overflow and division are checked in every build, with no flag to turn them off.

The price is real. A class can't hold a reference, a closure can't be stored, and there is no async, no threads and no dynamic dispatch yet. Each gap gets [its own diagnostic, and most suggest a way around it](docs/SPEC.md#16-deferred-features).

### A compiler that knows where you came from

Errors say what went wrong, why, and how to fix it, and `enrang explain` gives each code its own page. TypeScript habits get redirected rather than just rejected: `===` to `==`, `var` to `let`, `any` to a generic, `undefined` to `null`, `throw` to `Err`, `switch` to `match`.

### One binary, from a 386 to today

By default, 32-bit output uses only 80386 integer instructions and software floating point, so one binary is meant to run on all of these: i386 and Am386, the 486, Pentium, K5, K6, Pentium Pro to III, K7, Pentium 4, Pentium M, Atom, Core 2 and anything newer whose OS or firmware can still load 32-bit code. The known exceptions are early 386s with the multiply bug and defective K6 steppings. `--cpu` is an option, never a requirement: it unlocks optimisations and a few level-specific features, and a chip too old for the level you chose gets a clear message rather than a crash. Size budgets are tests too: at most 12 KB for a hello ELF, and 16 KB for a hello kernel running in 640 KB.

| Target, in build order | Output |
|---|---|
| `x86_64-linux` | Static ELF64, raw syscalls |
| `x86_64-windows` | PE32+, importing only `kernel32.dll` |
| `i386-linux` | Static ELF32, using only syscalls old kernels provide |
| `i386-none` | Flat binary, or a bootable floppy or hard-disk image for a legacy BIOS |
| `x86_64-none` | Flat binary, a bootable image for a legacy BIOS, or a UEFI application |

### A kernel in the same language

<!-- excerpt: docs/SPEC.md -->
```ts
// hello.en: enrang build --target=i386-none --image=hdd hello.en
import { vga, serial } from "os";

@entry function kmain(boot: &BootInfo): never {
  serial.init(boot);
  let screen = vga.Screen.fromBoot(boot);
  screen.write("Hello from Enrang\n");
  serial.write(boot, "Hello from Enrang\n");
  halt();
}

@panicHandler function onPanic(info: &PanicInfo): never {
  vga.emergency(info.message);
  halt();
}
```

Inline assembly, port I/O, interrupt handlers, packed layouts and raw boot sectors are all part of the language, and the ones that can break memory safety need `unsafe`.

### Save a file, keep your state

`enrang dev` runs your program in a VM on the same intermediate code the native backend compiles. It starts with no access to files, the environment or the clock unless you grant it. Save a file and the running program updates in place: add a field to a class, and the live objects are migrated. A panic pauses the program with its state intact, so you can fix the line, save, and retry. Production binaries contain none of this.

<!-- excerpt: docs/DEV_RUNTIME.md -->
```text
[v2] compiled in 38 ms; applied at os.sleep (server.en:25:5)
     Player +level: i32 = 1 (field initialiser); 32 -> 40 bytes
     migrated 2 Player via game.players; 0 references retargeted
     main rebased; step replaced
```

That transcript is a design target, and the timings are illustrative. Hot reload across changing data layouts is the project's most ambitious idea, and [the design says plainly where it stops working](docs/DEV_RUNTIME.md#13-what-will-not-work).

### Tests in the language

<!-- excerpt: docs/SPEC.md -->
```ts
describe("gcd", () => {
  test("common factor", () => {
    expect(gcd(84, 36)).toBe(12);
  });

  test("zero", () => {
    expect(gcd(7, 0)).toBe(7);
  });

  compileFails("rejects mixed widths", raw`
    function f(a: i32, b: i64): i64 { return a + b; } //~ EN0402
    function main(): void {}
  `);
});
```

One binary does `build`, `run`, `dev`, `test` and `check`. Tests run in the VM by default, where fuel replaces the wall clock so timeouts never flake, and a test that passes but leaks memory fails.

Enrang borrows ideas, and no code, from Rust, TypeScript, TinyCC, Bun, Deno, Erlang and Miri.

## Status

The design is complete. Milestone M0 is built. There is no compiler yet, so Enrang cannot compile, check or run a program today.

M0 is the foundation the compiler will stand on. It has the diagnostic code registry and renderer, the tables of targets and CPU levels, a test kit, and a command line that reports honestly what it can and cannot do. It is Rust with the standard library only, with no external dependency and more than 7,000 tests, many of them generated from tables. Every other feature named in the documents below is a design, not code. No CPU family has any support evidence yet.

This repository holds the documentation only: the design, the logo and the examples. The code isn't in it, so there is nothing to build or run here.

## Roadmap

Each milestone is planned to end with something runnable and tested. The full list, with what each one has to prove, is in [ARCHITECTURE.md](docs/ARCHITECTURE.md#12-milestones).

| | Milestone | What you can do then |
|---|---|---|
| ✅ | **M0** Foundation | `enrang explain` and `enrang targets`, though the code isn't in this repository |
| | **M1** Lexer and parser | `enrang check` finds syntax errors, and `enrang init` starts a project |
| | **M2** Types | `enrang check` finds type errors |
| | **M3** Borrow checker | `enrang check` finds ownership errors |
| | **M4** VM, standard library, test runner | `enrang run --vm` and `enrang test` |
| | **M5** x86-64 backend, own assembler, ELF writer | `enrang build`, for native Linux binaries |
| | **M6** Dev runtime | `enrang dev`, with the sandbox and hot reload |
| | **M7** Windows | Real `.exe` files |
| | **M8** i386 | 32-bit Linux at every `--cpu` level, with soft-float |
| | **M9** Freestanding i386 | Bootable floppy and hard-disk images, and the first kernel |
| | **M10** Freestanding x86-64 | 64-bit kernels and UEFI |

## Examples

[`examples/`](examples) has small programs for the features above, from [`hello.en`](examples/hello.en) to [a kernel for the family PC](examples/kernel/family-pc.en), plus [programs that must not compile](examples/mistakes) with the exact errors they get. None of them can run yet, and that page says how they were checked and when each one can.

## Documents

- [SPEC.md](docs/SPEC.md): the language, normative
- [ARCHITECTURE.md](docs/ARCHITECTURE.md): the implementation blueprint and its milestones
- [DEV_RUNTIME.md](docs/DEV_RUNTIME.md): the planned VM, sandbox and hot reload
- [TESTING.md](docs/TESTING.md): the planned `enrang test`, and the compiler's own tests

## Contributing

The code isn't in this repository, so the most useful thing right now is a close read of the design. Open an issue about anything that looks wrong or unclear. [CONTRIBUTING.md](CONTRIBUTING.md) has the rules the project holds itself to.

## Star history

<a href="https://www.star-history.com/?repos=enricoangelon%2Fenlang&type=date&legend=top-left">
 <picture>
   <source media="(prefers-color-scheme: dark)" srcset="https://api.star-history.com/chart?repos=enricoangelon/enlang&type=date&theme=dark&legend=top-left" />
   <source media="(prefers-color-scheme: light)" srcset="https://api.star-history.com/chart?repos=enricoangelon/enlang&type=date&legend=top-left" />
   <img alt="Star history of enricoangelon/enlang" src="https://api.star-history.com/chart?repos=enricoangelon/enlang&type=date&legend=top-left" />
 </picture>
</a>

## Licence

Enrang is licensed under either of the [MIT licence](LICENSE-MIT) or the [Apache License 2.0](LICENSE-APACHE), at your option. Unless you say otherwise, any contribution you submit for inclusion is licensed the same way, with no additional terms.
