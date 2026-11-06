<img src="assets/icon.svg" width="64" height="64" alt="">

# Enrang

Enrang is a new programming language being built: TypeScript-like syntax, native machine code with no libc and no external tools, Rust-style ownership, and diagnostics treated as a first-class feature.

## Status

The design is complete. Milestone M0 is built. There is no compiler yet, so Enrang cannot compile, check or run a program today.

M0 is the foundation the compiler will stand on. It has the diagnostic code registry and renderer, the tables of targets and CPU levels, a test kit, and a command line that reports honestly what it can and cannot do. Every other feature named in the documents below is a design, not code. No CPU family has any support evidence yet, and `enrang targets --evidence` says so.

The workspace is Rust with the standard library only, and it has no external dependency.

## Commands that work today

```sh
cargo build --workspace

./target/debug/enrang --help
./target/debug/enrang --version
./target/debug/enrang explain EN1301
./target/debug/enrang explain EN0601
./target/debug/enrang targets
./target/debug/enrang targets --evidence
```

- `explain` prints a code's page when it has one. Only `EN1301` and `EN1302` do so far. For any other code it prints the title and the milestone its page arrives in.
- `targets` lists the targets, CPU levels and aliases from the design tables. Nothing can be built for them yet.
- `targets --evidence` prints the per-family support table. C1 to C3 read `planned`, and C4 reads `no hardware` except on the Q8400 and `Newer` rows.

`build`, `run`, `dev`, `test`, `check` and `init` report which later milestone delivers them. Commands outside the prototype report `EN1301`, and an unknown command reports `EN1302`. All of these stop with exit status 2, and none of them touches your files.

## Tests

```sh
cargo test --workspace --locked
```

`--locked` makes a tampered `Cargo.lock` an error, where plain `cargo test` would quietly rewrite it. Golden output lives in `tests/golden/`. To accept a changed output and see its diff, run `ENRANG_BLESS=1 cargo test --workspace`, which is refused under `CI=1`.

## Documents

- [SPEC.md](docs/SPEC.md): the language, normative
- [ARCHITECTURE.md](docs/ARCHITECTURE.md): the implementation blueprint and its milestones
- [DEV_RUNTIME.md](docs/DEV_RUNTIME.md): the planned VM, sandbox and hot reload
- [TESTING.md](docs/TESTING.md): the planned `enrang test`, and the compiler's own tests
