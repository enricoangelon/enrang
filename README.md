<img src="assets/icon.svg" width="64" height="64" alt="">

# Enrang

Enrang is a new programming language being built: TypeScript-like syntax, native machine code with no libc and no external tools, Rust-style ownership, and diagnostics treated as a first-class feature.

## Status

The design is complete. Milestone M3 is built. Enrang can read a program and report its syntax, type and borrow errors, format it and start a project, but nothing is turned into machine code yet.

M0 is the foundation: the diagnostic code registry and renderer, the tables of targets and CPU levels, a test kit, and a command line that reports honestly what it can and cannot do. M1 adds the front end's first phase: the lexer, the parser with error recovery and hints for TypeScript habits, and the formatter. M2 adds the second: modules and name resolution, type inference and checking, null narrowing, exhaustiveness, constant evaluation, data layout, and the signatures of the `core` library. M3 adds the third: the mid-level IR and its verifier, and the borrow checker with permissions inferred from function bodies (moves, read-only marks, loans, the `for...of` hold, returned references, closures and local functions), contract inference, drop elaboration and module interface files. Every other feature named in the documents below is a design, not code. No CPU family has any support evidence yet, and `enrang targets --evidence` says so.

The workspace is Rust with the standard library only, and it has no external dependency.

## Commands that work today

```sh
cargo build --workspace

./target/debug/enrang --help
./target/debug/enrang --version
./target/debug/enrang init hello
./target/debug/enrang check hello/src/main.en
./target/debug/enrang check --emit=summary hello/src/main.en
./target/debug/enrang fmt --check hello
./target/debug/enrang explain EN0101
./target/debug/enrang explain EN0601
./target/debug/enrang targets
./target/debug/enrang targets --evidence
```

- `init hello` makes a project in `hello/`: `enrang.json`, `src/main.en`, `src/main.test.en` with one passing test, and a `.gitignore`. It never overwrites a file.
- `check` reads a file and its `.test.en` part and prints each syntax, type and borrow error, with a fix where one is known. With `--emit=mir` or `--emit=summary` it also prints the checked IR or the inferred contracts.
- `fmt` rewrites files in the canonical style. With `--check` it changes nothing and lists the files it would change.
- `explain` prints a code's page when it has one. Every code due by M3 has one. For any other code it prints the title and the milestone its page arrives in.
- `targets` lists the targets, CPU levels and aliases from the design tables. Nothing can be built for them yet.
- `targets --evidence` prints the per-family support table. C1 to C3 read `planned`, and C4 reads `no hardware` except on the Q8400 and `Newer` rows.

`build`, `run`, `dev` and `test` report which later milestone delivers them. Commands outside the prototype report `EN1301`, and an unknown command reports `EN1302`. All of these stop with exit status 2, and none of them touches your files.

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
