<div align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/logo-dark.svg">
    <source media="(prefers-color-scheme: light)" srcset="assets/logo.svg">
    <img alt="Enrang" src="assets/logo.svg" width="50%">
  </picture>

**TypeScript's feel. Rust's power. Native code, from the 80386 to today.**

[Language reference](docs/SPEC.md) | [Examples](examples) | [Roadmap](docs/ARCHITECTURE.md#12-milestones) | [Contributing](CONTRIBUTING.md)
</div>

Enrang is a programming language being built from scratch, for applications and for operating systems.

> [!IMPORTANT]
> **Enrang can't build or run a program yet.** The language is designed, and the compiler checks programs for syntax, type and borrow errors, but it doesn't generate machine code yet. The Enrang code on this page is specified behaviour, not something you can run today.

## Hello, world

```ts
console.log(greeting("world"));

private function greeting(name: &string): string {
  return `Hello, ${name}!`;
}
```

Tests sit next to the code, in `main.test.en`:

```ts
test("greets by name", () => {
  expect(greeting("Ada")).toBe("Hello, Ada!");
});
```

`enrang init hello` starts a project with this program and its test, and `enrang check` accepts both today. Running the program, which prints `Hello, world!`, arrives with the VM in the [next milestone](docs/ARCHITECTURE.md#12-milestones).

## The story

I think in TypeScript. In 2019 I started my own Minecraft Bedrock server, [jukebox](https://github.com/enricoangelon/jukebox), and since 2020 I've worked on [JSPrismarine](https://github.com/JSPrismarine/JSPrismarine), a much bigger one that I still contribute to. When I wanted more speed, I wrote Rust for Node ([bytebuf](https://github.com/enricoangelon/bytebuf)), and I kept wishing for one language with Rust's power and TypeScript's feel.

There's also a machine behind this: my family's old Acer, with a Core 2 Quad Q8400. I love that era of PCs, and I don't think working machines should stop getting new software because toolchains moved on. I want to write my own operating system for it, in a language I enjoy, with a dev loop where saving a file doesn't kill the running program.

In 2024 I tried. [enan](https://github.com/enricoangelon/enan) stopped at a README and a licence, because a compiler felt too big for one person. AI agents changed that: I design and decide, agents help write and attack the code, and independent tests check it.

The name is mine too: **Enr**ico **Ang**elon. Enrang can't compile a program yet. One day it will boot that Acer.

## Why Enrang?

- **Familiar:** It reads like TypeScript, and when a TypeScript habit doesn't apply, the compiler says what to write instead.
- **Safe:** Ownership works like Rust's, with no garbage collector and no lifetime syntax.
- **Close to the machine:** It compiles to machine code by itself, with no LLVM and no libc, for programs and operating systems on x86 CPUs from the 80386 to today.
- **Alive while you work:** In development, saving a file updates the running program and keeps its state. Production binaries contain none of that.

## Ownership

A value has one owner. `&` lends it, and passing it without `&` hands it over:

```ts
const ada = new User("Ada");
greet(&ada);   // lent: still ours
archive(ada);  // moved
greet(&ada);   // error[EN0601]: `ada` was moved into `archive`

private class User {
  public constructor(public name: string) {}
}

private function greet(u: &User): void {
  console.log(`Hello, ${u.name}`);
}

private function archive(u: User): void {}
```

The compiler explains the move and suggests two fixes: change the parameter to `u: &User` if `archive` only needs to look at it, or pass a copy with `archive(ada.clone())`.

## Documentation

- [Language reference](docs/SPEC.md): the language, normative
- [Architecture](docs/ARCHITECTURE.md): how the compiler will be built, and its milestones
- [Dev runtime](docs/DEV_RUNTIME.md): the planned VM, sandbox and hot reload
- [Testing](docs/TESTING.md): the planned `enrang test`, and the compiler's own tests
- [Examples](examples): small programs, including some that must not compile

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). Enrang is at an early stage, so the most useful thing right now is a close read of the design.

## Licence

Enrang is licensed under either of the [MIT licence](LICENSE-MIT) or the [Apache License 2.0](LICENSE-APACHE), at your option.

## Star history

<a href="https://www.star-history.com/?repos=enricoangelon%2Fenrang&type=date&legend=top-left">
 <picture>
   <source media="(prefers-color-scheme: dark)" srcset="https://api.star-history.com/chart?repos=enricoangelon/enrang&type=date&theme=dark&legend=top-left" />
   <source media="(prefers-color-scheme: light)" srcset="https://api.star-history.com/chart?repos=enricoangelon/enrang&type=date&legend=top-left" />
   <img alt="Star history of enricoangelon/enrang" src="https://api.star-history.com/chart?repos=enricoangelon/enrang&type=date&legend=top-left" />
 </picture>
</a>
