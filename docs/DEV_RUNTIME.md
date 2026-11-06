# Enrang dev runtime

The VM, sandbox, hot reload and state migration behind `enrang dev`. Language semantics are in `SPEC.md`, the compiler in `ARCHITECTURE.md`, tests in `TESTING.md`.

**Status: design only. Nothing here has been run.** Transcripts are design targets, and every performance number is an estimate that M4 or M6 must measure. The compiler and `enrang dev` run only on a modern x86-64 development machine. Production binaries contain none of this machinery (section 15).

## 1. Verdict

Keep the MIR VM, with four amendments to the starting recommendation.

1. **Predecode.** Run post-mono, post-elaboration MIR, the native backend's exact input, after a mechanical lowering to flat register code. Estimate: 30-100x slower than our unoptimised native code. M4 measures it. If it exceeds 200x, predecode gains superinstructions before M6. No JIT.
2. **Safe Rust only.** `enrang-vm` is `#![forbid(unsafe_code)]`. Guest `unsafe` can damage guest bytes, never the host.
3. **The heap is a tree only after proof.** `T[]` and `string` are raw pointers inside Enrang-written `alloc`, so "ownership makes the heap a tree" is a claim that must be checked. The tree comes from declared owner shapes plus a census (section 7).
4. **Function versioning is not enough.** Erlang relies on the next fully qualified call, but `while (true)` in `main` never makes one. Frames need rebasing and loop-head replacement (section 6).

**Rejected, with reasons:**

| Alternative | Why not |
|---|---|
| Native hot patching (Live++ style) | Guest `asm` and syscalls bypass capabilities, there is no provenance and no oracle, and layout changes stay the user's problem |
| Own JIT | Heavy, needs `unsafe` in the VM. A later tier is not precluded |
| Wasm | Third-party engines are banned, and an own engine adds an IR that erases types and ownership exactly where migration needs them |

**Verdict on the novel idea.** The idea survives, narrowed. R1 is what really carries it: every reference is in a frame slot, so every reference can be found and retargeted exactly. The tree property holds for safe code and is verified at run time for library code. It fails for type-erased `unsafe` data and for meaning (units, caches, sorted order), and there the runtime must refuse or warn rather than guess. Section 12 tries to break it, and section 13 lists what stays broken.

## 2. The VM

### 2.1 Position and API

```text
MonoProgram (target row vm64 or vm32) -> prepare -> PreparedProgram -> Vm::run
```

```rust
pub struct VmConfig {
    pub layout: VmLayout,            // Vm64 | Vm32: a TargetSpec row, arch = Mir, os = Vm
    pub float: VmFloat,              // Host | Soft (interprets lib/core/softfloat)
    pub allocator: VmAllocator,      // Host (vm.alloc) | Enrang (interprets FreeListHeap over a VM region)
    pub oracle: bool,                // borrow tags, section 3
    pub limits: Limits,              // max_memory, max_stack, fuel, spin_limit
    pub caps: Capabilities,          // section 4
    pub clock: ClockMode,            // Virtual | Real
    pub on_panic: PanicAction,       // Exit101 | Pause | ReturnToRunner
    pub journal: Option<JournalCfg>, // dev only
}
pub enum RunUntil { Exit, Fuel(u64), NextSafePoint(SafePointClass) }
pub enum VmEvent {
    Exited(i32), Panicked(PanicReport), Fault(VmFault), OutOfFuel,
    SafePoint(SafePointId), SpinLimit, NeedCapability(CapRequest),
}
impl Vm {
    pub fn new(p: Arc<PreparedProgram>, c: VmConfig) -> Vm;
    pub fn run(&mut self, until: RunUntil) -> VmEvent;
    pub fn stack(&self) -> Vec<FrameView>;           // function, pc, span, locals with types
    pub fn counters(&self) -> AllocCounters;         // live blocks and bytes, per site
    pub fn heap_hash(&self) -> u64;                  // for "refused means unchanged" tests
    pub fn coverage(&self) -> &BlockCounts;
    pub fn swap_program(&mut self, tx: CommittedReload);   // enrang-dev only
}
```

### 2.2 Predecode

Each mono body lowers to `Code { ops: Vec<Op>, pc_map: Vec<MirPoint>, span_map, frame: FrameShape }`. This is mechanical and has no optimisation that could mask a MIR bug.

- `Op` is a Rust enum over frame-slot indices with widths and resolved offsets. For example, `AddChecked { dst, a, b, width, signed, site }` and `Load { dst, ptr, disp, width }`. A `match` loop dispatches.
- Field offsets are resolved here against the layout, and rebasing re-runs this step (section 6).
- **Fuel:** one unit per MIR statement or terminator (SPEC 12.4), charged at block entry and refunded for unexecuted statements on a mid-block panic, so counts are exact and deterministic.
- **Safe-point polls:** at function entry and loop back edges, one flag read. MIR has no safe points; predecode inserts them.
- **Block counters:** one per block, read by the traceability meta-tests. User-facing `--coverage` is deferred (EN1041).
- **Traceability:** a per-`StatementKind` probe counter, read by the meta-test that requires every MIR statement kind to have executed.

### 2.3 Values and memory

A mix, decisively byte-addressed, because `core` and `alloc` do pointer arithmetic and casts that structured values cannot run.

```rust
pub struct AllocId(u64);                         // never reused
pub struct Pointer { pub addr: u64, pub prov: Option<AllocId> }
pub struct Slot { pub bits: u64, pub prov: Option<AllocId>, pub init: bool }   // never-borrowed scalar in a frame
pub enum AllocKind { Heap, Static, Rodata, Frame(FrameId), Fn(FnId, SigHash) }
pub enum AllocState { Live, Freed { site: Span } }
pub struct Allocation {
    pub id: AllocId, pub kind: AllocKind, pub state: AllocState, pub align: u32,
    pub bytes: Vec<u8>, pub init: InitMask,          // one bit per byte
    pub prov: BTreeMap<u32, AllocId>,            // offset of a stored pointer -> its provenance
    pub tag: Option<TypeTag>,                    // element type, from allocArray<T>
    pub exposed: bool, pub site: Span,
}
```

- **Allocations** hold heap blocks, statics, rodata, aggregates and address-taken locals. Frame allocations are created at `StorageLive` and freed at `StorageDead`, so a dangling reference to a dead local faults.
- **Scalars** that are never borrowed stay in frame slots as `(bits, prov)`.
- **Every access** checks provenance, liveness, bounds, initialisation and alignment (unless packed or `readUnaligned`).
- **Moves de-initialise.** Every `Operand::Move` clears the source's init bits and provenance, for slots and allocations alike, and so does `DropGlue` once its glue returns. A later typed read is therefore an "Uninitialised read" fault, even though the bytes are still there, so the oracle catches a borrow-checker bug such as accepting `const b = a; console.log(a.x);`, or a double drop of a `Drop` type with no heap.
- **Function values** are pointers whose provenance names a `Fn(FnId, sigHash)` record. Each indirect call compares the expected signature hash. A mismatch or a value forged from integers is a "Bad function pointer" fault, which pauses like any other, rather than an internal VM error.
- **Addresses.** A bump counter hands out addresses. `AllocId`s are never reused, so use-after-free is always caught. On `vm32`, addresses stay below 2^32; on exhaustion, freed ranges are reused with fresh `AllocId`s, and stale pointers still fault by provenance.
- **Exposure.** `ptr as usize`, or reading pointer bytes as integers, marks the allocation exposed. Integer-to-pointer resolves among exposed allocations by address. No match is a fault; a fixed address such as `0xB8000` gets EN1204, "this touches physical memory".
- **Allocator.** The global allocator binds to `vm.alloc(size, align, tag)`, as Miri hooks its allocator, because one arena would hide every error inside a single allocation. `--allocator=enrang` interprets `FreeListHeap` over a VM region, for testing that code. `T[]`, `string` and `Box` code is always interpreted, so their `unsafe` is exercised either way.
- **Type tags** come from an `AllocArray` intrinsic that compiles away natively. Raw `alloc(bytes)` is untagged, which section 8 treats as "erased".
- **Layout.** `vm64` borrows the `x86_64-linux` layout and is the dev default; `vm32` borrows `i386-linux`. The corpus compares each with its native twin, so printed `sizeOf` values match.
- **Floats.** Default is Rust `f32`/`f64` with NaN bits canonicalised at `toBits`, since Rust does not pin them. `--float=soft` interprets the Enrang soft-float library, for a bit-for-bit differential from M8.
- **Intrinsics.** `MemCopy`, `MemCopyOverlap` and `MemSet` run with full provenance, bounds and init checks, and copy provenance with the bytes. `DivWideU32` checks its precondition `hi < d` and faults otherwise, as hardware would raise #DE.

### 2.4 Fault detectors

Faults report two spans where they have them (allocated here, freed here). A fault in a program with no `unsafe` is labelled a soundness bug. Every detector has a test that makes it fire. Where no accepted source should produce a fault, as with a read of moved-from memory, the test is a hand-written `.mir` fixture.

| Fault | Trigger |
|---|---|
| Use after free | Access through provenance of a freed allocation |
| Double free | `dealloc` of a freed allocation |
| Bad free | `dealloc` with an interior pointer, wrong size or wrong alignment |
| Out of bounds | `offset + size` beyond the allocation |
| Uninitialised read | Init bits clear on a typed read, including moved-from and dropped memory |
| Bad function pointer | Indirect call whose target has no `Fn` provenance, or a different signature hash |
| Misaligned | Address not aligned for the access type, outside packed and unaligned forms |
| Invalid value | `bool` not 0 or 1; enum tag not declared |
| Wild pointer | No provenance, or int-to-pointer with no exposed match (EN1204) |
| Write to rodata | Store into `Rodata` |
| Bad host pointer | Host call given a range that fails the same checks |
| Aliasing (`--oracle` only) | Use of a popped borrow tag |
| Leak | Live blocks at test end (T0003); at exit in `--ci` corpus runs |

## 3. The VM as oracle

**Same corpus.** The VM runs every conformance program, and results must match each native cell (`TESTING.md` section 12).

**Soundness check on the borrow checker.** Every accepted safe program runs under fault detection. Any fault means the borrow checker accepted something it should not have, or the compiler or `alloc` has a bug.

**`--oracle`** adds borrow tags to references, a Stacked-Borrows-lite in about 400 lines. It is small because R1 keeps tags in frame slots, so nothing retags through memory. Each byte range keeps a stack of tags. `&mut` pushes a unique tag, `&` pushes a shared one, a use pops everything above its tag, and using a popped tag or writing through a shared tag faults. Raw pointers have allocation-level provenance only: a raw access clears tags on the touched range and proves nothing. Closure env fields are frame slots of a known type, so they are covered.

**Limits, plainly.** VM and native code can agree on a wrong answer, since they share MIR. Only dynamic checks and expected outputs catch shared MIR bugs. Raw-pointer aliasing is not fully checked.

**Blocked before start** by reachability over mono MIR, and again on every reload:

```text
error[EN1201]: this program cannot run in the VM: inline assembly is reachable
  --> vga.en:14:14
   |
14 |     unsafe { asm(`out dx, al`, { in: { dx: port, al: value } }); }
   |              ^^^^^^^^^^^^^^^^ inline assembly cannot be interpreted
   |
   = note: reached through main -> console.write -> vga.putc
help: build it natively: enrang build --target=i386-none
   = explain: run `enrang explain EN1201`
```

Also EN1202 (raw `syscall`, `int 0x80`), EN1203 (`core/port`), EN1205 (interrupt handler). The classification looks at the mnemonic or lang item. Under `enrang test` these tests are counted `native-only`, and `--strict` fails them.

## 4. Sandbox

The program reaches the host only through `HostCall` statements, which are legal only in `lib/os/vm`. The VM validates guest pointers before copying, and host addresses never enter guest memory.

```text
enrang dev <file> [-- args]
  --allow-read[=paths]  --allow-write[=paths]  --allow-net[=host:port,...]
  --allow-env[=NAMES]   --allow-clock          --deny-read|write|net|env|clock[=...]   (deny wins)
  -A                    grant everything above
  --no-prompt           deny instead of asking
  --layout=vm64|vm32    --max-memory=1G  --max-stack=8M  --spin-limit=20G
```

**Default grants:** stdin, stdout, stderr and sleep. Nothing else. There is no run or FFI grant, because Deno documents those as sandbox escapes; those host calls do not exist.

| Host call | Capability | Denied result in the guest |
|---|---|---|
| `write`, `read` on 0, 1, 2 | None | n/a |
| `fs.open`, `fs.read`, `fs.close` for read | `read` | `Err(PermissionDenied)` |
| `fs.open`, `fs.write`, `fs.delete` for write | `write` | `Err(PermissionDenied)` |
| `env.get` | `env` | `null`, with a notice on the session's stderr |
| `clock.now` | `clock` | Deterministic virtual clock: starts at 0, advances by fuel and by `sleep` |
| `sleep` | None | n/a; interruptible; advances the virtual clock |
| `args`, `exit` | None | n/a |
| `vm.alloc`, `vm.dealloc`, `vm.realloc` | Limits only | Panic `out of memory` past `--max-memory` |

**Handles.** Guest file handles come from a virtual handle table, never from host descriptors. Handles 0, 1 and 2 exist from the start and a guest close of them is refused. Rights are per open, so a handle opened for read cannot write.

**Network.** `--allow-net` parses and its grant logic is tested, but SPEC's EN1028 means no guest API exists yet, so no host call reaches it. The flag prints a note saying so. When the net API ships, it needs only the host calls.

**Missing grant.** A TTY pauses at the call:

```text
capability needed: read "/home/me/app/data/scores.json" (server.en:12:5)
type "once k7q" to allow this one, "all k7q" for all reads under /home/me/app/data, anything else denies
```

The guest chooses the path and shares the terminal, so the prompt treats both as hostile. This is the class of Deno's CVE-2023-28446:

- Every control character in a printed path is escaped, so a path cannot rewrite the screen.
- The path and the `all` scope print from the canonical path, never from what the guest passed.
- A grant needs a typed line containing a token chosen for this prompt from `/dev/urandom`, because guest output could coach a single key, and Rust std has no way to flush type-ahead.

Non-TTY, `--no-prompt` and `enrang test` deny immediately with a notice line. **Reloads cannot widen grants**: new code gets exactly the session's grants.

**Paths** are canonicalised and matched by component, and the guest has no symlink host call. Paths under `/mnt/*` match case-insensitively, because Windows drives mount there, so `--deny-read=/mnt/c/Users/me/.ssh` also stops `/mnt/c/users/me/.SSH`; paths there containing `:` are refused, because they can name NTFS streams. Rust std has no `openat`, so another host process racing a symlink swap can beat the check. The sandbox contains guest code, not a hostile process beside it.

**Limits.** Memory counts live data, journal and migration shadow. Exceeding memory or stack is an ordinary panic, which pauses in `dev`. `--spin-limit` pauses after that many statements with no host call, and saving a fix can still rescue an infinite loop. `enrang test` instead uses a hard per-test fuel budget (T0004).

**Environment visibility** is the only program-observable difference from a native run: capability failures as `Err(PermissionDenied)`, a virtual clock without `--allow-clock`, and the same stdout otherwise (SPEC 8.5).

## 5. Reload model

**Compile errors.** Compilation runs on a background thread while the program keeps running. Errors print full diagnostics and a `still running v3` status; nothing else changes. A failing v5 leaves a good pending v4 pending.

**Safe points:**

| Class | Where | Code-only reload | Schema reload |
|---|---|---|---|
| Function entry | Every function | Yes | If walkable |
| Loop back edge | Every loop | Yes, plus loop-head replacement | If walkable |
| Parked host call | `sleep`, blocked stdin | Yes | If walkable |

**Walkable** means both of these hold:
- No frame is in `core`, `alloc`, `os` or drop glue, and no pc is inside an `unsafe` region. The tree invariant is broken inside those (mid-growth of `T[]`, for instance). A user `clone` called under `extendCloned` has an `alloc` frame beneath it, so a schema reload defers until the spread is done, as under `map`.
- **Exception:** a top frame chain in `os/vm` parked in an interruptible host call is allowed, provided its locals are scalars only, which prepare checks statically. Without this exception a program sleeping in `os.sleep` could never take a schema reload.

If no walkable point occurs within 5 s, the session names the blocker and offers restart.

**Identity.**

| Thing | Identity |
|---|---|
| Function | `FnId` = module + qualified name + mono args |
| Type | `TypeId` = module + name |
| Field, variant | Name |
| Arrow | Enclosing `FnId` + ordinal + capture hash (type and mode of each captured path, in order) |
| Rename | `@was("old")` carries identity; inert outside `dev`. `@was` naming something that still exists is EN0806 |

**Versioning.** The code table maps `(FnId, sigHash)` to a body. `sigHash` covers parameter types, return type, receiver mode, `RetSources`, unsafety, required features and ABI. A call binds to the latest body with its `sigHash`, so old frames reach new bodies when the signature is unchanged, and a retired body otherwise. This is sound because borrow checking is modular over signatures: same signature, same R3 contract, same preconditions, and the caller's checked assumptions still hold.

**Arrows are different,** because a closure's contract includes its captures. A live `ClosureValue` pins its exact old arrow body until the call that received it returns, so a running `forEach` never rebinds to a new arrow, however the ordinals shift. A new call binds to a new arrow only when the capture hash matches, and a mismatch never rebinds. So code-only swaps can proceed during a `sort` callback, and the callback in flight stays old.

`bodyHash` excludes spans. If a frame's function is unchanged by `bodyHash`, the frame adopts the new body in place at the same pc, so stack traces show the new line numbers.

**Coalescing.** Saves during compile, pause or migration coalesce: latest wins.

## 6. Running frames

**Rebase.** An old body can be re-lowered against the new types and continue at the same statement:
1. Take the frame's elaborated generic MIR.
2. Run `mir::remap_ids`. MIR's `FieldIdx` and `VariantIdx` are positional, so this rewrites `Field`, `Variant`, `Aggregate` operand order and `Switch` tag values by name, through `Body.names`. A reordered class or an inserted variant therefore means what it meant.
3. Re-run substitution and predecode against the new type table. Statement indices are unchanged, so the pc maps by identity.
4. Map drop flags through `Body.drop_flags` by move path key.
5. **Analyse the code reachable from the suspended pc,** transitively through any retired bodies this frame would bind.

Rebase fails, creating a **blocking frame**, if any of these hold:

- Reachable code, or a retired body it would bind, reads or writes a removed or retyped field, copies a type that lost Copy, or constructs a removed variant.
- A local of a dirty type is partly moved at the pc. Elaboration fixed its drop ladder to the old field list, so a removed field would still be in it, a new field would leak, and a class gaining `implements Drop` would skip its destructor.
- A live local's type lost Copy. No `Drop` was ever scheduled for it, so it would leak on return even with no later read.

A whole-value `DropGlue(p)` is not a problem, because its shim is re-derived from the new type at step 3. The reload waits for a blocking frame to return; unlike Erlang's purge, nothing is killed.

**Literals of grown types.** Field initialisers compile to dev-only shims, so a rebased `Player { name, score }` calls the shim for `level`. A field with no initialiser takes the zero value of section 7, or blocks if none exists.

**Constructor frames.** A frame running a constructor of a dirty class holds a partly initialised `this`, so it is always a blocking frame.

**New variant reaches an old `match`.** The rebased switch gets a synthesised arm: panic `v3 of `f` met variant `Frozen`, added in v4`, then pause and retry. Never undefined.

**Loop-head replacement.** A frame whose own body changed runs the old body until return (Smalltalk behaviour), except at a back edge, where it jumps to the new body if all of these hold:

- the same-identity loop exists (nesting path plus label) and the signature is unchanged;
- neither body contains `unsafe`;
- every user local live into the new loop head maps by name, scope and type, with matching init state;
- every hidden local live into the new loop head maps by (loop identity, role), and only to an old local of the equal `LoopRole` and equal type. A new head needing a role with no old local refuses;
- an old `IntoIter` has a counterpart in the new loop. It is refused, not dropped, because it owns the elements still to come;
- no reference local is live in, except never-reassigned parameters. A reference-typed `Source` falls under this.

Hidden locals have no name, which is why they map by role: a mapping by position could pair `_i` with an unrelated hidden local. `_n` is assigned at every head, so it is never live in. `_i` may carry across a change of source array, with a note, because the next head reads the length again and the bind is bounds-checked. Unmapped initialised old user locals drop in reverse declaration order, with a note. References are refused because the new borrow check assumed origins that the old code did not establish. If replacement is refused, the frame stays old and the status line says so.

**A new body may assume a fact the old code never established.** The same nesting path can hold `if (o == null) { for (const x of other) {} }` in v1 and `if (o != null) { for (const x of o) {} }` in v2, and the same goes for range locals and any other head. Every head and bind re-reads through `CheckTag` and `CheckBounds`, so this is never memory unsafety: a `CheckTag` failing in a replaced body takes the synthesised panic-and-pause path of ADV-2.

**Frames in `for...of` loops.** A path source (SPEC 5.6) adds no hidden reference: at a back edge the loop itself has only `_i`, and a binding `x` that is dead there is ignored (REF-02). So when no other reference is live in, such a frame can take loop-head replacement, which is what lets a saved fix rescue the growing loop of SPEC 5.6 under `--spin-limit` (ADV-20). The reference rule above still covers what the program itself holds. A path through a reference local keeps that local live at the back edge, because the next head reads it. A never-reassigned parameter such as `xs` in `function f(xs: &mut T[])`, or `this`, may carry over (ADV-52), while `const r = &queue; for (const job of r)` refuses, and so does a frame with a saved element such as `longest = x` (ADV-51). A live `x` at a callee's safe point is an ordinary reference: REF-01 retargets it, and REF-03 blocks. A frame whose reachable code reads a source field that was removed or retyped is a blocking frame by step 5 above, and a fixed-array length change through a hook blocks the same way, so a stale static length never reaches a shorter array. An evaluate-once source holds `_src`, so a frame in such a loop refuses replacement by the reference rule until the loop ends. A consumed `T[]` holds `ArrayIntoIter`, which is a typed frame local that the census walks. The output of `[...queue]` in flight is a typed `Temp`, so the census covers it too. The compiler's loop for a `T[N]` spread has no `LoopId`, so its back edge is a safe point and never a replacement point.

## 7. State migration

**Applies when** the schema diff is non-empty, compilation is clean, a walkable safe point is reached and no frame blocks. Only dirty types (changed, or inlining a changed type) and paths reaching them are walked. Exactly one schema is live at any time.

**Roots.** Frame locals, filtered by move dataflow and drop flags at the pc, plus closure env locals, plus statics. Since MIR locals are typed, in-flight temporaries are covered.

**Owner edges.** `Box`, `T[]`, `string` and `ArrayIntoIter` declare `@owner` shapes, restricted to `alloc` in the prototype (EN0806 elsewhere). The walker verifies that each edge targets the start of a live allocation. An edge with `cap == 0` or a zero-sized target holds a dangling pointer by design, so the census skips it.

**Census.** Every live allocation must be visited exactly once, or be rodata, or be an untouched island with no dirty tag. Otherwise the reload is refused (EN1215, naming both paths when one was visited twice). Provenance tables locate every raw pointer exactly.

**Rules.** Row IDs are stable, and each has a reload scenario (`TESTING.md` section 18).

| ID | Edit | Rule |
|---|---|---|
| MIG-01 | Field added | Hook, else field initialiser (pure, fuel-limited), else zero value with a note for numbers, `bool`, `string`, `T[]`, `T \| null` and classes of those. Otherwise refuse (EN1210) |
| MIG-02 | Field removed | Its value goes to quarantine, migrated like any live value of its type. User `drop` runs after commit, count reported. If the field's own type was deleted, refuse (EN1210): its `drop` belongs to a schema that no longer exists |
| MIG-03 | Renamed | `@was`. A same-typed remove plus add is never guessed: a TTY asks; otherwise remove plus add, with a fix-it |
| MIG-04 | Reordered, visibility | By name, through `remap_ids`; no value effect |
| MIG-05 | Retyped, lossless | Integer widening, `f32` to `f64`, `i32` to `f64`, `T` to `T \| null`: automatic |
| MIG-06 | Retyped, narrowing | Integer narrowing, exact `f64` to `f32`, `T \| null` to `T`: value-checked; first failure refuses and names the path (EN1216) |
| MIG-07 | Other retype, fixed-array length | Hook or refuse (EN1210) |
| MIG-08 | Variant added | Tags rewritten by name, since tags number from declaration order; payloads follow field rules |
| MIG-09 | Variant removed | Allowed if no live value has it; otherwise refuse with path (EN1210) |
| MIG-10 | Class to enum, deleted type still live | Hook or refuse (EN1210) |
| MIG-11 | Generics | Per mono instance; parameters match by name; adding or removing one refuses (EN1210) |
| MIG-12 | Static `let` | Value kept, by the same rules; new statics initialise; removed statics drop |
| MIG-13 | `T[]` of a dirty `T` | New buffer. New `cap` is the old `cap` when old and new sizes are both non-zero, and `len` when `T` was zero-sized (no allocation if `len` is 0). If `T` becomes zero-sized, free the buffer and use the maximum `cap` |
| MIG-14 | `Box` of a dirty `T` | Migrates the block. A zero-sized `T` that gains fields allocates; one that loses them all frees the block |

**Hook: yes**, as in Erlang's `code_change`, because rules cannot infer intent:

```ts
@devMigrate
function migratePlayer(old: { first: string, last: string, hp: i32 }): Player {
  return Player { fullName: `${old.first} ${old.last}`, hp: old.hp * 10 };
}
```

The object type states the old schema, the only place object types are legal (EN0407), and is checked against the real one. A stale hook warns (EN1212) and is ignored. `old` is owned, its children are already migrated (the walk is bottom-up), there are no capabilities, and fuel is limited. Production builds strip it, and calling it from code is EN1211.

**A hook is pure by static check.** A hook runs new-version code before commit, against a heap still in transition, so it takes only `old` and returns only the new value. Its reachable mono call graph may not contain user `unsafe`, a top-level `let` or a host call (EN1217). Library-internal `unsafe` in `core` and `alloc` is exempt, because a hook reaches it only through safe APIs, and so are `vm.alloc`, `vm.dealloc` and `vm.realloc`, which are limits rather than capabilities. Fields of `old` the hook does not consume go to quarantine and drop after commit, so a leftover field whose `drop` logs does not refuse the reload.

**Transaction.** Migration is all-or-nothing before commit.

```text
plan: schema diff, dirty set, per-type copy plan        (no guest state touched)
walk: iterative, explicit stack, builds shadow allocations, forward map, runs hooks in shadow;
      moves each removed field's value, children migrated, into a typed quarantine allocation
checks: census (quarantine counted), narrowing values, references (section 8), memory limit
---- commit point ----
swap code and type tables; retarget references and pointers through the forward map;
free old allocations; run user drops from quarantine, in walk order; free quarantine
```

Quarantine is what makes the order safe. A removed inline field lived in an old allocation, and its glue needs a layout, so its value is moved out during the walk, under a type that still exists. Old allocations can then be freed before any user `drop` runs, and no drop can touch them. If a quarantine `drop` panics, that is a normal pause under new code, and the remaining entries stay allocated until restart. The order is tested under the VM's fault detector.

Any failure before commit leaves the heap byte-identical and old code running; tests assert this by heap hash. After commit the only way back is restart.

## 8. References and raw pointers across a reload

Row IDs are stable, and each has a reload scenario (`TESTING.md` section 18).

| ID | Held value | Rule |
|---|---|---|
| REF-01 | Live reference, subobject survives with the same type | Retargeted through the forward map, like a moving GC |
| REF-02 | Reference dead at the pc | Ignored |
| REF-03 | Live reference, pointee removed or retyped | Blocking frame; after 5 s refused (EN1213), naming local and field, restart offered |
| REF-04 | Closure env field | Same rules: env locals are typed frame slots |
| REF-05 | Raw pointer to an untouched allocation | Stays valid |
| REF-06 | Raw pointer into a moved or rewritten allocation | Refuse, never retarget: code may hold old-layout offsets (EN1214) |
| REF-07 | Exposed allocation touched | Refuse (EN1214) |
| REF-08 | Non-null `*mut T` with dirty `T` | Refuse (EN1214) |
| REF-09 | Erased data (`*mut u8` cast later, classes stored as bytes) | Undetectable. Accesses stay checked, values may be stale; a warning counts untagged allocations kept |
| REF-10 | Function value | Holds `FnId` + `sigHash`. Deleted or re-signatured targets pin the retired body with a warning; refuse if it cannot rebase |
| REF-11 | Live `ClosureValue` | Pins its exact old arrow body until the call that received it returns (section 5) |
| REF-12 | Literal strings | Old-version rodata lives for the session |

## 9. Panic pause and retry

A dev panic stops at the faulting statement with frames and heap intact and no drops, matching production's no-unwind rule. Non-interactive VM runs print the same message and exit 101.

**There is no resume at the faulting statement,** because no sound map exists from an old pc to a new one. Retry means rollback to a checkpoint, then re-entry using the latest code.

**Journal.** A 64 MB ring records stores (old bytes and provenance), allocations, frees (bytes retained until evicted) and host effects. Checkpoints sit at each frame entry and at back-edge register snapshots, throttled to one per 10k statements per frame. Journal memory counts against `--max-memory`. It exists only in `dev`.

**Retry target.** The outermost changed frame on the stack, else the panicking frame; `[u]` moves outward. A target needs its checkpoint in the ring, an unchanged signature, and no barrier crossed.

**Sequence.**
1. Roll back under the old layout.
2. Migrate if the pending reload needs it, which resets the journal.
3. Re-enter with the original arguments, or take loop-head replacement.

This is sound because rollback recreates the exact state of a valid call, including by-value arguments the callee consumed and heap it freed. Allocations since the checkpoint vanish without drops: they never happened.

| Since the checkpoint | Treatment |
|---|---|
| Clock, env, sleep, file reads | Repeatable; opened handles are closed |
| stdout, stderr | Repeated, with a note saying how many lines |
| File write, delete or close; network; consumed stdin | **Barrier**: retried only with explicit `[f]orce`, which can duplicate effects |

A clean retry runs automatically on save. A barrier asks. Restart is the only option after an evicted checkpoint, a committed migration, or a changed signature at every eligible frame.

## 10. Failure rules

One principle: **never corrupt state. Either the old program keeps running unchanged, or the reload commits completely, or the user is told to restart.**

Row IDs are stable, and each has a reload scenario (`TESTING.md` section 18).

| ID | Failure | State afterwards | Report | Offered |
|---|---|---|---|---|
| FAIL-01 | Compile error in new code | Old program running | Diagnostics, `still running vN` | Save again |
| FAIL-02 | Program became VM-incompatible | Old program running | EN1201-EN1205 | Build natively |
| FAIL-03 | No walkable point in 5 s | Old program running | Names the blocking frame | Restart |
| FAIL-04 | Blocking frame, reference to removed data | Old program running, reload pending | EN1213 | Wait, or restart |
| FAIL-05 | Migration impossible, including a removed field whose type was deleted | Heap byte-identical, old code | EN1210 with path | Hook, or restart |
| FAIL-06 | Raw pointer into rewritten allocation | Heap byte-identical, old code | EN1214 | Restart |
| FAIL-07 | Census failure | Heap byte-identical, old code | EN1215 with both paths | Restart |
| FAIL-08 | Narrowing retype failed on a value | Heap byte-identical, old code | EN1216 with path and value | Restart, or widen |
| FAIL-09 | Hook panics or loops | Journal rollback, old code | Panic report of the hook | Fix the hook |
| FAIL-10 | Hook reaches user `unsafe`, a top-level `let` or a host call | Old program running; refused before any walk | EN1217 naming the path | Fix the hook |
| FAIL-11 | Stale hook | Reload proceeds without it | EN1212 warning | Remove it |
| FAIL-12 | Removed field's `drop` panics | Post-commit: new code, normal pause | Panic report, "restart is the only retry" | Restart |
| FAIL-13 | Out of memory during shadow | Heap byte-identical, old code | EN1210 naming `--max-memory` | Raise the limit, or restart |

Exit codes: `[q]` after a panic exits 101, a clean program exit returns its code, and an internal VM error exits 3.

## 11. Worked scenario

`server.en`, v1:

```ts
import { os } from "os";

class Player {
  name: string;
  score: i64;
}

class Game {
  players: Player[];
  tick: isize;
}

function step(g: &mut Game): void {
  g.tick += 1;
  const who = g.tick % g.players.length;
  g.players[who].score += 10;
  console.log(`tick ${g.tick}: ${g.players[who].name} = ${g.players[who].score}`);
}

function main(): void {
  let game = Game { players: [Player { name: "Ada", score: 0 },
                              Player { name: "Grace", score: 0 }], tick: 0 };
  while (true) {
    step(&mut game);
    os.sleep(1000);
  }
}
```

**v2** adds `level: i32 = 1;` to `Player`, adds `if (g.players[who].score % 30 == 0) { g.players[who].level += 1; }` after the score line, and prints `L${g.players[who].level}` in the log line.

**v3** inserts these before the `+= 10` line, so they become lines 17 and 18:

```ts
  const rival = who + 1;
  g.players[rival].score -= 1;
```

**v4** changes line 17 to `const rival = (who + 1) % g.players.length;`.

Timings are illustrative.

```text
$ enrang dev server.en
enrang dev | layout vm64 | no grants | watching 1 file
[v1] running
tick 1: Grace = 10
tick 2: Ada = 10
tick 3: Grace = 20
[v2] compiled in 38 ms; applied at os.sleep (server.en:25:5)
     Player +level: i32 = 1 (field initialiser); 32 -> 40 bytes
     migrated 2 Player via game.players; 0 references retargeted
     main rebased; step replaced
tick 4: Ada L1 = 20
tick 5: Grace L2 = 30
[v3] compiled in 31 ms; code only; step replaced
tick 6: Ada L2 = 30

panic: index 2 is out of bounds for length 2
  --> server.en:18:3
stack:
  step (server.en:18:3)
  main (server.en:28:5)
   |
17 |   const rival = who + 1;
   |                 ------- 2 here, because `who` is 1
18 |   g.players[rival].score -= 1;
   |   ^^^^^^^^^^^^^^^^ out of bounds
paused; state intact, nothing dropped
retry plan: step, from entry; undoes 1 write; no external effects
save a fix, or: [r]etry [u]p [s]tart over [q]uit

[v4] compiled in 29 ms; code only; step replaced
retry step: game.tick 7 -> 6
tick 7: Grace L2 = 39
tick 8: Ada L2 = 39
```

**Why each step behaves that way:**

- **v1 to v2.** The safe point is `os.sleep`: `main` is user code, and the `os/vm` frame is parked with scalars only, so it is walkable (section 5). `game` is an address-taken local whose `Game` shape does not change size, but `players` owns a buffer of 2 x 32 bytes, which becomes a new allocation of 2 x 40. `name` and `score` copy by name, and `level` runs its initialiser shim. No reference is live: `step` has returned, and its `&mut game` died with it. Census: `game` frame allocation, the one array buffer, and rodata for the two literal names. `main` keeps its pc by rebase.
- **v2 values.** Tick 4: `who` 0, Ada 20. Tick 5: `who` 1, Grace 30, and `30 % 30 == 0` makes her level 2.
- **v3 is code only.** No schema change, so `step` is replaced at the next call. `main` is unchanged by `bodyHash`, so it adopts the new spans, which is why its line reads 28 although the frame is older.
- **Tick 6.** `who` 0, `rival` 1: Grace 29. Ada 30, level 2.
- **Tick 7 panics.** `g.tick` is already 7, the single journalled write. `who` 1, `rival` 2. The stack format matches SPEC 9.1 exactly, followed by a dev-only snippet.
- **Retry target.** `main` is unchanged and `step` changed, so the outermost changed frame is `step`. Its checkpoint undoes `g.tick`, and there was no external effect, so v4 retries automatically on save.
- **After retry.** Tick 7: `who` 1, `rival` 0, Ada 29, Grace 39. Tick 8: `who` 0, `rival` 1, Grace 38, Ada 39. Nothing else was lost.

This transcript becomes a golden test at M6, with timings removed under `--ci`.

## 12. Adversarial scenarios

Each has defined behaviour and a test at M6. Its ID is `ADV-` plus the number.

| # | Attack | Defined behaviour |
|---|---|---|
| 1 | Reload during `T[]` growth, a sort callback or drop glue | The tree is broken there. Not walkable: schema reload defers, code-only swaps proceed, and a callback in flight stays on its pinned old arrow |
| 2 | A new variant reaches an old frame's `match` | Synthesised arm panics with a precise message, then pause and retry. Never undefined |
| 3 | XOR linked list | `ptr as usize` exposes the nodes. A reload touching them is refused (EN1214) |
| 4 | Two `Box`es built from one raw pointer | The census visits it twice: refused, naming both paths (EN1215) |
| 5 | Million-node `Box` list grows | The walker is iterative, so no host stack risk; the shadow counts against `--max-memory`, so it refuses rather than exhaust the host |
| 6 | Hook panics, loops or calls the host | A host call is refused statically (EN1217). A panic or fuel exhaustion rolls back the journal: reload refused, old code runs |
| 7 | A removed field's `drop` panics | After commit: new code is live, the normal pause applies, restart is the only retry |
| 8 | Comparator edited, array no longer sorted | Undetected. A future `Map` would declare derived structure and rehash; user caches get nothing |
| 9 | `price` changes from dollars to cents, same type | Undetected unless the user writes a hook |
| 10 | Edit above `while (true)` | Replacement skips it. A note says those lines already ran; restart to apply |
| 11 | `const first = &names[0]` live at the loop head | Replacement refused; the frame stays old and the status line says so |
| 12 | Saves during compile, pause or migration | Coalesced; latest wins. A failing v5 leaves a good pending v4 pending |
| 13 | Guest forges `0x7fff0000 as *mut u8`, or passes a huge length to a host call | No such allocation exists, so it faults inside the VM (EN1204); host memory is never touched |
| 14 | Constructor of a dirty class is on the stack | Blocking frame until it returns: `this` is partly initialised, so there is no value to walk |
| 15 | A local is partly moved when its class grows | Blocking frame: its elaborated drop ladder names the old field list. The reload applies when the frame returns |
| 16 | User function holding a closure parameter when a captured path's class changes | Env fields are typed frame slots, so they retarget or block by the reference rules |
| 17 | `T \| null` retyped to `T` while a null is live | Value check fails, heap unchanged, EN1216 with path |
| 18 | `Player` loses `implements Copy` while an old frame's reachable code copies it | Blocking frame |
| 19 | Program stores `sizeOf<Player>()` in a variable | Stale value; undetected. Listed in section 13 |
| 20 | Spin loop with no host call, or a growing `for...of` that SPEC 5.6 accepts with EN0719 | A spin loop, or a growing loop of zero-sized elements, never reaches the host: `--spin-limit` pauses, and saving a fix can apply at the back edge by loop-head replacement. Any other growing loop reaches the host whenever a push reallocates: it panics `out of memory` at `--max-memory`, which pauses, and saving a fix retries (section 9) |
| 21 | Allocation loop during journalling | `out of memory` panic pause at `--max-memory`, which counts the journal |
| 22 | Reload adds a capability-needing call | Grants unchanged: `Err(PermissionDenied)`, or a prompt on a TTY |
| 23 | Reload makes `asm` reachable | EN1201 before anything changes; old program keeps running |
| 24 | Rename guessed wrongly: same-typed remove plus add | Never guessed. A TTY asks; otherwise remove plus add with a `@was` fix-it |
| 25 | Hostile host process swaps a symlink during the path check | Out of the threat model, stated in section 4 |
| 26 | v2 inserts an arrow above a running `xs.forEach(...)`, shifting ordinals | The running call keeps its pinned old arrow; it never binds the new arrow at the old ordinal |
| 27 | v2 keeps an arrow's ordinal and changes its captures | New calls see a different capture hash and do not rebind to the old body; the running call stays pinned |
| 28 | Class gains `implements Drop` while a frame holds it partly moved | Blocking frame; the destructor is never silently skipped |
| 29 | Class loses Copy, and a frame has a live local of it with no later read | Blocking frame; the value does not leak on return |
| 30 | A removed field's class was also deleted | Refused (EN1210); no `drop` runs from a schema that no longer exists |
| 31 | A removed inline field's `drop` runs under the fault detector | Runs from quarantine after commit; no use-after-free of the old allocation |
| 32 | Hook reads a top-level `let`, or contains `unsafe` | Refused statically (EN1217) before the walk |
| 33 | Hook leaves a field of `old` whose `drop` logs | Reload proceeds; the `drop` runs after commit from quarantine |
| 34 | Safe `get(i)` becomes `unsafe function get(i)` | `sigHash` changes, so old frames bind the retired safe body |
| 35 | An old frame calls `helper`, whose signature changed, and retired `helper` reads a removed field | Blocking frame, by transitive analysis |
| 36 | `class M {}` gains a field with an `M[]` live | New buffer with `cap == len`; census clean |
| 37 | A class loses all its fields with a `T[]` live | Buffer freed, `cap` becomes the maximum; census clean |
| 38 | `Box<M>` of a zero-sized `M` grows, and later shrinks | Allocates on growth, frees on shrink; no false census failure |
| 39 | Class fields reordered and a variant inserted, with an old frame live | `remap_ids` keeps field reads and `Switch` arms correct |
| 40 | Guest `unsafe` forges a function value from integers, or reinterprets one at another signature, and calls it | Bad function pointer fault pauses; the session survives |
| 41 | v2 edits the body of `for (const job of queue)`, adding `if (turns > 2) { break; }`, while the loop grows under `--spin-limit` | Replacement takes at the back edge: `_i` maps by (loop identity, `Index`) and `turns` by name. The saved fix stops the loop |
| 42 | v2 changes the source to a shorter array, `for (const job of other)` | Replacement takes, with a note that the index carried over. The next head reads the new length and leaves if the index is past it; no bounds panic |
| 43 | v2 changes a path source to `[...queue]` | Refused: the new head needs `IntoIter`, and the old frame has none. The frame stays old and the status line says so |
| 44 | v2 changes a path source to `grid[r]` | Refused: the new head needs a reference-typed `Source`, and no value exists for it |
| 45 | v1 `if (o == null) { for (const x of other) {} }`, v2 `if (o != null) { for (const x of o) {} }`, on the same nesting path | Replacement may take with the fact never established. `CheckTag` at the new head fails into the panic-and-pause path of ADV-2. Never undefined |
| 46 | v1 `for (const x of [...q])` in flight, v2 a path source | Refused: the old `IntoIter` has no counterpart, and it owns elements, so it is not dropped |
| 47 | Source field removed or retyped while a frame is in that loop | Blocking frame by rebase step 5; applied when the frame returns |
| 48 | Schema reload while a user `clone` runs under `extendCloned` in `[...a]` | The `alloc` frame is not walkable, so it defers. Code-only swaps proceed |
| 49 | Back edge of the compiler's loop for `[...fixed]`, with `T[N]` | A safe point with no loop identity, so no replacement. `_out`, `_s`, `_k` are typed, so a schema reload at it retargets or blocks by the reference rules, and the census counts `_out` |
| 50 | `x` live at a callee's safe point in a growing loop, then a reload that moves the array | REF-01 retargets `x`; if the element was removed or retyped, REF-03 blocks. No stale pointer survives |
| 51 | `const r = &queue; for (const job of r)`, or a saved `longest = x`, at a back edge | Replacement refused: `r` or `longest` is a live reference local and not a never-reassigned parameter, even though the loop adds no hidden reference. The frame stays old and the status line says so |
| 52 | `function f(xs: &mut T[]) { for (const x of xs) { g(x); } }`, or `for (const x of this.items)`, at a back edge with `x` dead | Replacement can apply: `xs` and `this` are never-reassigned parameters, and the loop adds only `_i` |

## 13. What will not work

Stated plainly:

- **Semantic staleness:** units, caches, sorted order, changed invariants, stored `sizeOf` values.
- **Re-running startup code** without restart.
- **Live edits to a body under an evaluate-once `for...of` source such as `for (const x of grid[r])`,** or with other live references, or a live element binding, until that loop ends. A path source adds no hidden reference of its own, but these limits still reach a path through a non-parameter reference local, as in `const r = &queue; for (const job of r)`, and any other live reference, such as a saved `longest = x`.
- **Undoing the outside world.**
- **Guarantees for type-erased `unsafe` data.**
- **Kernels, inline `asm` or port I/O in the VM; any hot reload in production.**
- **Threads:** they would need stop-the-world safe points and a new journal.
- **Catching shared MIR bugs by differential alone.**
- **Full aliasing proof for raw-pointer code.**
- **Debugger features.** Stepping, breakpoints and variable inspection are `enrang debug`, which is EN1301.

## 14. File watching

Std has no inotify, and inotify is commonly reported to miss Windows-side edits under `/mnt/c` on WSL2, the owner's platform. So one thread polls `fs::metadata` (mtime, size) on module-graph files and unresolved-import directories every 100 ms. Polling by path handles atomic-rename saves. On change it waits one more stable poll, reads, hashes to drop no-op saves, and sends over `mpsc`. A same-size, same-mtime edit on a coarse-timestamp filesystem can be missed, so an `[R]` key forces reload. About 180 lines plus 200 of tests. `enrang test --watch` shares it.

## 15. Production boundary

`enrang-vm` and `enrang-dev` are never linked into emitted programs: emitted code contains only reachable mono MIR lowered by `enrang-codegen`.

- `os/vm` is selected only by the VM rows of `TargetSpec`.
- `@was` is inert and `@devMigrate` functions are stripped before mono, so a file with them builds byte-identical to a file without them.
- `HostCall` in a non-VM body is a verifier failure, and in codegen an internal error.
- Field-initialiser shims and journal hooks exist only in `enrang-dev`.
- Meta-test: release output of every target contains no `HostCall`, no `os/vm` symbol and no dev string.

## 16. Budget and tests

**Estimated lines:**

| Part | Rust lines | Crate | From |
|---|---|---:|---|
| Predecode | 1,200 | `enrang-vm` | M4 |
| Interpreter | 2,500 | `enrang-vm` | M4 |
| Memory and provenance | 900 | `enrang-vm` | M4 |
| Oracle tags | 400 | `enrang-vm` | M4 |
| Host calls and capabilities | 1,000 | `enrang-vm` | M4 |
| Schema diff and planner | 900 | `enrang-dev` | M6 |
| Walker, migration, hooks | 1,500 | `enrang-dev` | M6 |
| Rebase and loop-head replacement | 800 | `enrang-dev` | M6 |
| Journal and retry | 500 | `enrang-dev` | M6 |
| Session UI | 500 | `enrang-dev` | M6 |
| Watcher | 180 | `enrang-dev` | M6 |

Total 10,380: 6,000 at M4 and 4,380 at M6. There is no reserve: the former 620-line one pays for `enrang-sema`. If `enrang-dev` overruns, loop-head replacement is cut first, and frames then simply run the old body until return.

**Tests** (`TESTING.md` section 11 has counts):

- **Reload corpus.** Version files, pause scripts and expected transcripts, 400 scenarios. Fixtures declare `//! covers: MIG-07`. A meta-test requires a fixture for each `MIG-`, `REF-`, `FAIL-` and `ADV-` ID in this document, and fails on orphans (`TESTING.md` section 18).
- **Generative schema editor.** With our own PRNG, it makes random schema edits over random heaps, weighted towards zero-sized types and empty containers, and asserts one of exactly two outcomes: refused with an unchanged heap hash, or migrated with retained fields equal, census clean, no leaks and a typed walk of the new heap passing.
- **Every grant denied:** one test per capability, proving denial and the mapped result.
- **Every detector fires:** section 2.4.
- **Production free of machinery:** section 15.
