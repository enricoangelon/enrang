# Contributing to Enrang

This repository holds Enrang's documentation: the design, the logo and the examples. The compiler's code isn't in it, so the most useful contribution right now is a close read. If something in the design looks wrong, unsound or unclear, open an issue.

## The rules the project holds itself to

- **No third-party code** in the toolchain or in the programs it emits: no crates, no LLVM or Cranelift, no `cc`, `as` or `ld`, no libc. Rust and its standard library build the compiler. Outside tools may only check results in tests.
- **Tests are part of the change.** A component isn't finished until it is tested. Every diagnostic gets a test that makes it fire and a near miss that doesn't.
- **The spec decides.** [`docs/SPEC.md`](docs/SPEC.md) is normative for everything a programmer can observe. If the behaviour and the spec disagree, fix one of them in the same change. The spec's examples are tests.
- **Claim nothing that didn't happen.** The docs say only what exists. Running on a modern machine proves the code, not an old chip, so a CPU family counts as verified only on evidence from that family.
- **Output is deterministic.** Two builds of the same input are byte-identical.

## If an agent wrote your change

Agents are welcome here, and the same rules apply, with one more: a report is not evidence. Check the result yourself, read how the agent's work ended, and compare what git would commit with what is on disk (`git ls-files --others --cached --exclude-standard`) before you trust it.

## Licence

Enrang is licensed under either of the [MIT licence](LICENSE-MIT) or the [Apache License 2.0](LICENSE-APACHE), at your option. Unless you say otherwise, any contribution you submit for inclusion is licensed the same way, with no additional terms.
