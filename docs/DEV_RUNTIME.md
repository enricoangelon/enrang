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

**Verdict on the novel idea.** The idea survives, narrowed. R1 is what really carries it: every reference is in a frame slot, or in a reference field of a borrowing value that is itself in one, so every reference can be found and retargeted exactly. The tree property holds for safe code and is verified at run time for library code. It fails for type-erased `unsafe` data and for meaning (units, caches, sorted order), and there the runtime must refuse or warn rather than guess. Section 12 tries to break it, and section 13 lists what stays broken.

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
- **Moves de-initialise.** Every `Operand::Move` clears the source's init bits and provenance, for slots and allocations alike, and so does `DropGlue` once its glue returns. A later typed read is therefore an "Uninitialised read" fault, even though the bytes are still there, so the oracle catches a borrow-checker bug such as accepting `const b = a; console.log(a.x);`, or a double drop of a class with a destructor and no heap.
- **Function values** are pointers whose provenance names a `Fn(FnId, sigHash)` record. Predecode resolves every function reference in a body version, a direct call, an `FnAddr`, an `FnToPtr` or `FnAsClosure` and the callee of a `StringForm` shim alike, to the `(FnId, sigHash)` that version was compiled against, and a rebase keeps that `sigHash` (section 6). An `FnToPtr` or `FnAsClosure` of a function with an `&I` or `&I | null` parameter names its dynamic copy, because a call through the value passes that argument in the two-word form (section 5, SPEC 4.4). A function with a by-value interface parameter has no dynamic copy, so it never becomes a function value (EN1006, SPEC 4.5). So a function value that an old frame makes after a reload names the body its coercion was checked against, the retired one when the target's `sigHash` changed, just as a value made before the reload does (REF-10, ADV-65). Each indirect call compares the target's pointer hash with the one its `fn` type expects. The pointer hash covers only the parameter types and the result type. It leaves out the whole contract (permissions, sources, `through_fields`, result writability and stores), unsafety and required features, because the coercion to the `fn` type has already checked that they fit. So a function stored where the declared contract differs from its own still calls cleanly, and prints in `dev` what it prints in a native build (ADV-54). A mismatch or a value forged from integers is a "Bad function pointer" fault, which pauses like any other, rather than an internal VM error.
- **Addresses.** A bump counter hands out addresses. `AllocId`s are never reused, so use-after-free is always caught. On `vm32`, addresses stay below 2^32; on exhaustion, freed ranges are reused with fresh `AllocId`s, and stale pointers still fault by provenance. So a printed address (a raw pointer printed in hex, `p as usize` printed as a number, or an `fn` value or closure printed as the address of its code in hex, SPEC 4.4) shows a VM address, which a native run does not share: addresses, and any output computed from one, are outside the rule that stdout matches native (section 4).
- **Exposure.** `ptr as usize`, or reading pointer bytes as integers, marks the allocation exposed. Integer-to-pointer never faults, because SPEC 4.6 makes it safe to create: it takes the provenance of the exposed allocation that holds the address, or none. Comparing, printing or converting such a pointer back is not an access, so `console.log(0xB8000 as *u16)` prints its address on a VM cell as on a native one. The first read or write through a pointer with no provenance faults (Wild pointer), and for a fixed address such as `0xB8000` that fault is EN1204, "this touches physical memory".
- **Nullable interface references.** An `&I | null` is always the two-word form, a parameter included, and an object word of 0 means `null` (SPEC 11). `null` writes 0 to both words, so a later typed read finds both initialised. A typed read, the census (section 7), REF-13 and MIG-16 look at the table word only when the object word is not 0, and MIG-06's check of a narrowing to `&I` tests the object word. The object word of a present value is never 0, because a reference is never null, and an element of a `T[]` of a zero-sized `T` is no exception: once the array has elements its `ptr` is `alignOf<T>()` (SPEC 11), so `&units[0]` is not read as `null`.
- **Allocator.** The global allocator binds to `vm.alloc(size, align, tag)`, as Miri hooks its allocator, because one arena would hide every error inside a single allocation. `--allocator=enrang` interprets `FreeListHeap` over a VM region, for testing that code. `T[]`, `string` and `Box` code is always interpreted, so their `unsafe` is exercised either way.
- **Type tags** come from an `AllocArray` intrinsic that compiles away natively. Raw `alloc(bytes)` is untagged, which section 8 treats as "erased".
- **Layout.** `vm64` borrows the `x86_64-linux` layout and is the dev default; `vm32` borrows `i386-linux`. The corpus compares each with its native twin, so printed `sizeOf` values match.
- **Floats.** Default is Rust `f32`/`f64` with NaN bits canonicalised at `toBits`, since Rust does not pin them. `--float=soft` interprets the Enrang soft-float library, for a bit-for-bit differential from M8. These are the VM's only float modes: `--float=sse2` and `--float=x87` on a VM row are EN0911.
- **Intrinsics.** `MemCopy`, `MemCopyOverlap` and `MemSet` run with full provenance, bounds and init checks, and copy provenance with the bytes. A call for 0 elements, or 0 bytes for `MemSet`, accepts any pointer, null included, since an empty array's `ptr` may be 0 (SPEC 7.1, SPEC 11). `DivWideU32` checks its precondition `hi < d` and faults otherwise, as hardware would raise #DE. `SliceFromRaw`, with which `Slice<T>.fromRaw` and the library's `slice` and `splitAt` build their views (SPEC 8.2), checks at once what it can of `fromRaw`'s obligations (SPEC 5.9): a misaligned pointer is Misaligned, a negative `n` is an Invalid value fault, and for `n > 0` a null pointer is an Invalid value fault and the `n` elements must lie inside one live allocation that the pointer's provenance names, or it faults as an access there would (Wild pointer, Use after free, Out of bounds). The view keeps that provenance, so each later access is checked like any other, and a store through a view of read-only data, such as `Slice<i64>.fromRaw(primes.asPtr(), 4)` after `const primes: &Slice<i64> = &[2, 3, 5, 7];`, faults as Write to rodata, since memory written through a view must be writable (SPEC 5.9). A `slice` whose clamping went wrong faults where it builds the view.

### 2.4 Fault detectors

Faults report two spans where they have them (allocated here, freed here). A fault in a program with no `unsafe` is labelled a soundness bug. Every detector has a test that makes it fire. Where no accepted source should produce a fault, as with a read of moved-from memory, the test is a hand-written `.mir` fixture.

| Fault | Trigger |
|---|---|
| Use after free | Access through provenance of a freed allocation |
| Double free | `dealloc` of a freed allocation |
| Bad free | `dealloc` with an interior pointer, wrong size or wrong alignment |
| Out of bounds | `offset + size` beyond the allocation |
| Uninitialised read | Init bits clear on a typed read, including moved-from and dropped memory |
| Bad function pointer | Indirect call whose target has no `Fn` provenance, or a different pointer hash: other parameter or result types |
| Misaligned | Address not aligned for the access type, outside packed and unaligned forms |
| Invalid value | `bool` not 0 or 1; enum tag not declared; a null pointer given to `SliceFromRaw` for one or more elements, or a negative length |
| Wild pointer | Access through a pointer with no provenance, such as an int-to-pointer with no exposed match (EN1204); the conversion itself never faults |
| Write to rodata | Store into `Rodata` |
| Bad host pointer | Host call given a range that fails the same checks |
| Aliasing (`--oracle` only) | Use of a popped borrow tag |
| Leak | Live blocks at test end (T0003); at exit in `--ci` corpus runs |

## 3. The VM as oracle

**Same corpus.** The VM runs every conformance program, and results must match each native cell (`TESTING.md` section 12). Besides the exclusions that section 12 declares, a printed address is outside the comparison too, since it is a VM address (section 2.3), and addresses also differ between native targets. So is any other output that depends on an address value, such as an integer computed from one or a branch taken on it. A program that prints an address, unless it comes from a constant, declares `//! differs: address`, which masks it, and one whose other output depends on an address restricts its cells with `//! cells:` (`TESTING.md` section 12).

**Soundness check on the borrow checker.** Every accepted safe program runs under fault detection. Any fault means the borrow checker accepted something it should not have, or the compiler or `alloc` has a bug.

**`--oracle`** adds borrow tags to references, a Stacked-Borrows-lite in about 400 lines. It is small because R1 keeps references in frame slots and in the reference fields of borrowing values, which live only in frames themselves (SPEC 5.1), so tags live there too and nothing retags through heap memory. A store into a borrowing value copies the stored tag into its field, so a reference read back out of the field is checked like any other. A store into a `readonly &` field never borrows for writing (SPEC 4.3), so the tag it copies is a shared one, and a result that reaches its source only through such fields keeps that tag, the loan of the value's read set, and none on the value itself (SPEC 5.1): writing through the value's other fields, or moving or dropping the value, pops nothing that result uses. Such a field never takes a reference reached through another reference field of the same value whose class writes through its reference fields (SPEC 5.1), whose writes could pop it, and one reached through such a field of another value keeps the checker's loan on that value as well (SPEC 4.3), so that value's writes never pop it while the field holds it. Each byte range keeps a stack of tags. An exclusive borrow pushes a unique tag, a shared borrow pushes a shared one, a use pops everything above its tag, and using a popped tag or writing through a shared tag faults. Whether a borrow is exclusive is inferred (SPEC 5), and each MIR `Ref` carries the mode the borrow checker gave its loan. A callee proves no exclusive access for a writable result with one reference part, so its own borrow may be shared: at a call whose result is later written through, the caller retags the result from the exclusive tag of its source argument. A writable result holds that argument's own loan, because only a read-only result may reach its source through reference fields alone (SPEC 5.1). The retag is sound only because no callee slot survives the return and the callee kept no other copy of that argument: a source it also stores into a borrowing value makes the result read-only (SPEC 5.4, N6). A result with several reference parts was checked part by part in the callee (N6), and the caller retags each part on its own range. Raw pointers have allocation-level provenance only: a raw write pops the shared tags on the touched range, except on the bytes of a `@lang` atomic type, which may change under a shared borrow, and a raw access proves nothing. Closure env fields are frame slots of a known type, so they are covered.

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
| `fs.open`, `fs.read`, `fs.close` for read | `read` | `Err(IoError.PermissionDenied)` |
| `fs.open`, `fs.write`, `fs.delete` for write | `write` | `Err(IoError.PermissionDenied)` |
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

**Environment visibility** and VM addresses are the only program-observable differences from a native run: capability failures as `Err(IoError.PermissionDenied)`, a virtual clock without `--allow-clock`, printed addresses (a raw pointer, an `fn` value or closure, `p as usize`), which are the VM's (section 2.3) and which no native run shares, and any output computed from an address, and the same stdout otherwise (SPEC 8.5).

## 5. Reload model

**Compile errors.** Compilation runs on a background thread while the program keeps running. Errors print full diagnostics and a `still running v3` status; nothing else changes. A failing v5 leaves a good pending v4 pending.

**Safe points:**

| Class | Where | Code-only reload | Schema reload |
|---|---|---|---|
| Function entry | Every function | Yes | If walkable |
| Loop back edge | Every loop | Yes, plus loop-head replacement | If walkable |
| Parked host call | `sleep`, blocked stdin | Yes | If walkable |

**Walkable** means both of these hold:
- No frame is in `core`, `alloc`, `os`, drop glue or a synthesised printer, and no pc is inside an `unsafe` region, which MIR records explicitly (`ARCHITECTURE.md` section 2.5). The tree invariant is broken inside those (mid-growth of `T[]`, for instance). A user `clone` called under `extendCloned` has an `alloc` frame beneath it, so a schema reload defers until the spread is done, as under `map`.
- **Exception:** a top frame chain in `os/vm` parked in an interruptible host call is allowed, provided its locals are scalars only, which prepare checks statically. Without this exception a program sleeping in `os.sleep` could never take a schema reload.

If no walkable point occurs within 5 s, the session names the blocker and offers restart.

**Identity.**

| Thing | Identity |
|---|---|
| Function | `FnId` = module + qualified name + mono args, a constructor's override set and a fill function's set of left-out fields included (`ARCHITECTURE.md` section 5), so a frame keeps the instance its body named (ADV-72). The dynamic copy of a function with an `&I` or `&I \| null` parameter, which a two-word `&I` reaches (SPEC 4.4), is one more instance; a by-value interface parameter has none |
| Type | `TypeId` = module + name |
| Field, variant | Name. A subclass field that gives an inherited field a new default with `override` is that same field, one slot (SPEC 4.3), so adding or removing it changes no schema, only the default that later constructions and MIG-01 use |
| Arrow | Enclosing `FnId` + ordinal + capture hash (type and mode of each captured path, in order, a captured reference or borrowing value included). A mode is inferred from the arrow's body, so a body edit can change the hash |
| Rename | `@was("old")` carries identity; inert outside `dev`. `@was` naming something that still exists is EN0806 |
| Glue | Its kind and its type's `TypeId`. Drop, clone and printing glue (`DisplayGlue`) are re-derived from the new type, so each follows its type's schema |

**Versioning.** The code table maps `(FnId, sigHash)` to a body. `sigHash` covers parameter types, which parameters have defaults, which type parameters may bind a view such as `Slice<u8>` because the body uses them only behind `&`, and which may bind `string` because the body never converts their `&T` to an interface reference (SPEC 4.10), return type, the whole contract of `ARCHITECTURE.md` section 6.7 but for the bit that says whether a body moves or writes a by-value parameter, which only a compile-time help reads, unsafety, required features and ABI. Defaults count because a call to a function with defaults passes the number of parameters it supplied, which the body's default statements read (SPEC 4.14, `ARCHITECTURE.md` section 5), so a reload that adds or removes a default binds old frames to the retired body. The contract is the permission of each reference parameter, of each reference part of a by-value borrowing parameter and of `this`; the result's sources, which of them it reaches only through a borrowing value's reference fields (`through_fields`), and which only through the value's `readonly &` fields, so that the result holds only the loans of the value's read set (SPEC 5.1); whether the result is writable; and its stores, the parameters it stores into a borrowing value behind another parameter, each marked when it takes only what the stored value's reference fields hold (`fields_only`) or only what its `readonly &` fields hold, its read set (`read_set_only`), and whether each also joins the value's read set, as a store into a `readonly &` field does (its read bit, SPEC 5.3). Which type parameters may bind a view or `string` is no part of the contract, though it is inferred from the body too: it decides which calls are accepted, a question of types, so it is stated with the declaration (`ARCHITECTURE.md` section 4). A call binds to the latest body with its `sigHash`, so old frames reach new bodies when the signature is unchanged, and a retired body otherwise, and a function value that a body makes names the `sigHash` that body was compiled against (section 2.3). This is sound because borrow checking is modular over contracts: a caller is checked against the contracts of its callees, never their bodies, so the same `sigHash` means the same contract, the same preconditions, and the caller's checked assumptions still hold. That is as true of a module that has only an interface file. Every load of the file, a reload's included, runs the MIR verifier over its stored code, even in a release build of the compiler, checking the code's types against the current declarations and its `unsafe` boundary (EN0801, EN0803, EN0907) against the regions the MIR records. It reruns, against the current declarations, every phase-2 rule whose verdict phase 3, mono, codegen or the VM rely on: visibility of every member and item the stored code names, the class rules, the string clause of satisfaction for every satisfaction the stored code relies on (SPEC 4.4), the construction rules of every stored `new` and named form, and the position rules for every type the stored declarations and code use. It also checks that every run-time guard the MIR builder places is present: a `CheckBounds` before each `Index`, a `CheckTag` before each `Variant` projection, a `CheckClass` at each exact-class event, each `Intrinsic` of a kind that needs `unsafe` inside a recorded `unsafe` region, a `Virtual` call only where `ARCHITECTURE.md` section 2.5 allows one, a `Convert` only between the type pairs its kind allows, `&T[N]` or `&T[]` to `&Slice<T>`, a class to a base class, and a class to an interface it satisfies, and `SetTable` only on a class with a hidden pointer (`ARCHITECTURE.md` section 2.5 has the lists). It then recomputes the contracts and flags from the stored MIR and reruns phase 3 on it, its comparisons included: the borrow check, the narrowing check, EN0615 for a stored override, satisfaction, bound or `fn` coercion that no longer fits, EN0714, and EN0418 for `implements Copy` against the recomputed flags. A file whose stored code fails the verifier or does not match its contracts is EN0316, naming the file (`ARCHITECTURE.md` section 6.8). A reload that changes any module in such a module's import closure, not only a direct import, reaches its key, because each API hash covers those of its module's own imports (`ARCHITECTURE.md` section 6.8). That key leaves out `cpu` and `float`, because nothing the file stores depends on them, so a VM run with `--float=soft` reads the same files as one with the host's floats (section 2.3). The checks over code are never cached: phase 4's level checks run over every module's MIR, stored or fresh, whenever a command reaches phase 4 (`ARCHITECTURE.md` section 6.8), and the VM's reachability check (section 3) reads the mono MIR of every module, a stored one included, at start and at every reload, so a reachable `asm` in a module that has only an interface file is EN1201, as it would be if built from source. If only contracts and flags moved under its stored code, it is rechecked against them by the same pass, and a borrow or contract error that the recheck finds is reported with its ordinary code at the stored span, with `` note: this module has no source; it was rechecked against the new `lib` ``, which is FAIL-01. Any other change to an item its stored MIR mentions, whichever module declares it, a class reached only through an import's result type or a re-export included, is EN0315, also FAIL-01: a change to its type, layout or existence, to `final` or `abstract`, to which of its type parameters may bind a view or `string`, to its method set or to a constant's value, because the stored MIR may have fixed a field index, a direct call or a copied constant under the old declaration, which a recheck of contracts would not see. A body edit that adds a store changes the `sigHash`, so an old frame binds the retired body, which stores nothing (ADV-59). A contract is inferred from its body, so an edit to a body alone can change a `sigHash`: an unchanged signature means an unchanged contract as well as unchanged text. Such an edit can also make an unedited caller fail the borrow check, which is FAIL-01 with the error in a file that was not edited. Two facts a caller relies on are in no `sigHash`, so each has its own rule: the method table an object names (below), and whether a borrowing class it stores into writes through its reference fields (section 6).

**Arrows are different,** because a closure's contract includes its captures. A live `ClosureValue` pins its exact old arrow body until the call that received it returns, so a running `forEach` never rebinds to a new arrow, however the ordinals shift. A new call binds to a new arrow only when the capture hash matches, and a mismatch never rebinds. So code-only swaps can proceed during a `sort` callback, and the callback in flight stays old.

`bodyHash` covers the post-inference MIR and excludes spans. If a frame's function is unchanged by both `sigHash` and `bodyHash`, the frame adopts the new body in place at the same pc, so stack traces show the new line numbers. Both are needed, because an edit to another function can change this one's inferred MIR without touching its text (ADV-55).

**Method tables** are versioned with the code table. A class's table for a version names, in each slot, the `(FnId, sigHash)` of the method a call through that slot reaches, or of the `StringForm` shim in front of it: a slot keeps the `&string` forms of the declaration that introduces it, so an override whose forms differ gets a slot of its own, and the slot it overrides names the shim (SPEC 11). The slot of an abstract method, in an abstract class's own table and in its tables for interfaces, names a synthesised panic stub. Only code that an abstract base's destructor runs, once the subclass's part is cleaned up and the hidden pointer names the base's table (SPEC 5.7), can reach one, and the stub panics `` `Shape.area` is abstract, and the subclass that implements it is already cleaned up `` (SPEC 9.1), which pauses like any panic, so such a call is never a Bad function pointer fault. A slot, or an interface table's entry, for a method with an `&I` or `&I | null` parameter names the method's dynamic copy, because a call through a table, like one through an `fn` value or a closure, passes that argument in the two-word form; per-class copies serve direct calls only (SPEC 4.4). An `&Self` result of a call through a table is paired with the receiver's table. A method compiled once per type, one with type parameters of its own, a by-value interface parameter or an object-type parameter, has no slot: it is never overridable, so every call to it is direct with its declaring class's body (SPEC 5.4). An interface with such a member never gets an interface table, because a `Box<I>` or a two-word `&I` of it is EN1006 (SPEC 4.4), so only per-class copies and generic instances call that member, directly. The table also records the class's size and alignment, which freeing a `Box<A>` reads before the contents' cleanup runs, because drop glue writes each base's table into the hidden pointer before that base's cleanup, so that a base's destructor dispatches and prints as the base (SPEC 11). For each interface that mono sees one of its classes converted to, the table points at the class's table for that interface, which lists the interface's members in its order with the size, alignment, name, drop glue, `fmt` and `fmtNested`, the printer for the value nested in another, which quotes what SPEC 4.4 quotes there, such as a string or a text case, and the table word of a `Box<I>`, or of a two-word `&I`, names that interface table (SPEC 11). An `&I` is two words, the object and its class's table for `I`, everywhere except as a per-class copy's own `&I` parameter, where its class is known and it is one pointer. An `&I | null` is two words everywhere, a parameter included, so a function gets per-class copies for a non-null `&I` parameter or a by-value `I` one, never for an `&I | null` one, and a call that passes `null` there reaches the dynamic copy (section 2.3). So an `&I` taken from a box is two words, and so is one that a per-class copy returns, stores in a field, puts in a tuple part or wraps as `&I | null`, since the copy attaches its class's table (SPEC 11). A two-word `&I` passed to an `&I` parameter reaches the function's dynamic copy (SPEC 4.4), which calls its members through that word. Which calls go through a table is SPEC 5.4's rule: a call to an overridable method is Virtual when its receiver place's last step dereferences a `&C` or `Box<C>` of a class `C` that is not `final`, or it is `this` in such a class, and so is one whose receiver's type is a type parameter bounded by such a class, by value or behind `&` (SPEC 4.10); a call on a `Box<I>` or a two-word `&I` goes through the interface table its word names. In a per-class copy (SPEC 4.4) or a generic instance (SPEC 4.10) for a class that can be extended, a call to an interface or bound member also goes through the object's own table, whatever the place, so a subclass's override runs (SPEC 4.3, `ARCHITECTURE.md` section 2.6), unless the member is compiled once per type. A call on any other place of a class type, and a call to a `private` or `static` method or to one compiled once per type, is direct and binds by `sigHash` as a function call does. The MIR builder decides under the class's `final` whether a call is Virtual and whether a `new` writes a hidden pointer (`ARCHITECTURE.md` sections 2.5 and 5), and predecode does not decide either again, so old code that calls a method on, or builds with `new`, a class that gained or lost `final` blocks its frame (section 6, ADV-73, ADV-74). A named form writes no table itself: the class's fill function, which it binds by `sigHash`, writes it (`ARCHITECTURE.md` section 5). A table that changes makes its class dirty even when its fields do not (MIG-15): at commit, every hidden pointer, and every table word of a `Box<I>` or of a two-word `&I`, that names a changed table moves to the new version's table of the class that table belongs to, for the same interface if it is an interface table, so new code checked against a new contract never dispatches to a retired override (REF-13, ADV-57, ADV-63). That class is the object's own, except inside a base class's destructor, where no table change commits because a drop glue frame is never walkable (MIG-15 needs a walkable point). A base class's constructor is no exception: a subclass sets its own fields before its base part is built, and a call through `this` in a base constructor, or printing `this` there, runs the object's own class's code (SPEC 4.3), so the hidden pointer names the object's own class's table throughout construction; a constructor frame for a dirty object blocks anyway (section 6). A live object whose class no longer fits the place it is held through refuses the reload instead (MIG-16). Old code meets the new tables too, so a frame whose reachable code calls through an entry whose `sigHash` changed, or that is in the middle of such a call, blocks the reload (section 6, ADV-58). Code names a table by its class, the base's table that drop glue writes included, and predecode resolves that to the live version's table, as it resolves a field offset, so every rebase resolves it again (section 2.2). The exact-class check of a whole-object copy or move through a `Box<A>`, an `&A` or `this` (SPEC 4.3) therefore compares like with like after a commit: an old frame's `unbox()` of an `Animal` still succeeds, and of a `Dog` still panics, `` `unbox` expected an `Animal`, but the box holds a `Dog` ``, which pauses like any panic (ADV-62). The entry check of a `move` method, which every `move` method of a class that can be extended makes on entry, and which only a call from a generic instance or a per-class copy can fail, since any other call that would fail it is EN0458 (SPEC 4.3), reads the object's table the same way, so after a commit it follows the new version's overrides.

**Coalescing.** Saves during compile, pause or migration coalesce: latest wins.

## 6. Running frames

**Rebase.** An old body can be re-lowered against the new types and continue at the same statement:
1. Take the frame's elaborated generic MIR.
2. Run `mir::remap_ids`. MIR's `FieldIdx` and `VariantIdx` are positional, so this rewrites `Field`, `Variant`, `Aggregate` operand order and `Switch` tag values by name, through `Body.names`. A reordered class or an inserted variant therefore means what it meant.
3. Re-run substitution and predecode against the new type table. Statement indices are unchanged, so the pc maps by identity. Function references keep the `sigHash` the body was compiled against (section 2.3), and the instance they name, a constructor's override set included (section 5, ADV-72).
4. Map drop flags through `Body.drop_flags` by move path key.
5. **Analyse the code reachable from the suspended pc,** transitively through any retired bodies this frame would bind or would make a function value of. Old code past a back edge at which the frame takes loop-head replacement (below) is not reachable, because the new body runs from there. Prepare decides that from the replacement conditions, which are all static.

Rebase fails, creating a **blocking frame**, if any of these hold:

- Reachable code, or a retired body it would bind or make a function value of, reads or writes a removed or retyped field, copies a type that lost Copy, constructs a removed variant, would build, through a retired constructor or an implicit one, a class that gained a field with no default (below), or converts a class to a base class it no longer extends or to an interface it no longer satisfies: an upcast to `&A` or `Box<A>`, a conversion to `Box<I>` or `&I`, a call to the per-class copy made for that class (ADV-69), or a call to a generic function's instance for that class under a bound `T extends A` or `T extends I` (SPEC 4.10). MIG-16 checks the values that already exist; this condition stops old code from making a new one.
- Reachable code, or a retired body it would bind or make a function value of, builds a value of a class `C` with `new` or a named form, or stores into a value that is or holds a `C` (a write of one of `C`'s reference or borrowing fields, or a call whose contract stores into a parameter whose pointee is or holds a `C`), where this reload turns on `C`'s flag, or drops `readonly` from one of `C`'s reference fields, or from a reference part of one of its tuple fields while its flag is on. The flag rule below checks the values that already exist; this condition stops old code from making a new one, or storing into one, with the shared loans that its old checks gave (ADV-75).
- A local of a dirty type is partly moved at the pc. Elaboration fixed its drop ladder to the old field list, so a removed field would still be in it, a new field would leak, and a class gaining a destructor would skip it.
- A live local's type lost Copy. No MIR `Drop` was ever scheduled for it, so it would leak on return even with no later read.
- Reachable code calls through a method table to a method whose `sigHash` changed, or the frame is in the middle of such a call. Commit moves objects to the new tables (section 5), so the call would run a body whose contract this frame was not checked against.
- Reachable code, or a retired body it would bind or make a function value of, calls a method on a place of a class `C`, in a per-class copy or generic instance for `C` too, or builds a `C` with `new`, where `C` gained or lost `final` in this reload. The MIR builder fixed the call's kind and the `new`'s `SetTable` under the old declaration (section 5), as stored MIR fixes them for EN0315, so old code would load a table from the hidden pointer that commit drops, or build an object without the one that new code's Virtual calls read (MIG-15, ADV-73, ADV-74).

A whole-value `DropGlue(p)` is not a problem, because its shim is re-derived from the new type at step 3. Nor is printing a value whose class has no written `fmt`, of its own or inherited: its synthesised printer (`DisplayGlue`, SPEC 4.4) follows the class's schema across a reload as drop glue does, re-derived at step 3, so old code that prints a `Player` after a reload added `level` prints `Player { name: 'Ada', score: 10, level: 1 }`. The reload waits for a blocking frame to return; unlike Erlang's purge, nothing is killed.

**Bodies pinned by function values.** A retired body that a live function value names (REF-10) is checked at every reload, not only at the one that retired it. The VM finds every live function value by its `Fn` provenance, in frame slots and in the provenance table of each allocation (sections 2.3 and 7), and each body such a value pins counts as reachable code, as a frame's does, through the retired bodies it would bind or make a function value of. If that code reads or writes a removed or retyped field, copies a type that lost Copy, constructs a removed variant, would build, through a retired constructor or an implicit one, a class that gained a field with no default, converts a class to a base class it no longer extends or to an interface it no longer satisfies, calls through a method table to a method whose `sigHash` changed, calls a method on, or builds with `new`, a class that gained or lost `final`, or builds or stores into a value of a class whose flag this reload turns on, or that loses a `readonly`, as the rebase rule above says, the reload is refused with EN1213, naming the value's path, and a restart is offered (FAIL-14, ADV-64). Waiting cannot help, because a pin lasts as long as the value, not until a frame returns.

**A class that starts writing through its reference fields.** A reload that turns on a borrowing class's flag for writing through its reference fields (SPEC 5.3, N3 (e)), or that drops `readonly` from a reference field, or from a reference part of a tuple field's type, of a class whose flag is already on, makes every frame with a live local whose type is or holds that class a blocking frame, and the reload waits like a schema reload even when no field changed. Old code stored references into such a value with shared loans, and new code may now write through them (ADV-61). Old code that would build such a value, or store into one, after the reload blocks its frame by the rebase rule above, and makes a function value that pins it EN1213 (ADV-75), so the check covers new values as well as live ones. New bodies need nothing: a new body bound with an unchanged `sigHash` has the same contract, so any store it makes into the class already took the exclusive loan the new flag needs, and a free function that stores into the class changes its contract when the flag turns on, so old callers bind its retired body, which that rule then sees. Putting the flag into every method's `sigHash` instead would not be enough: a free function whose contract does not change, as `run(c: &Cursor) { c.step(); }`, would still pass an old caller's shared-loaned `Cursor` to the new pushing body. A store into a field declared `readonly &` never borrows for writing, even in a class whose flag another field sets (SPEC 4.3, N3 (e)), so dropping that `readonly` makes such stores exclusive, as turning the flag on does. The flag comes only from the bodies that see the class's private fields: its methods, `static` ones included, its constructors, parameter properties included, its destructor, and the arrows nested in any of them, and from its base class's flag, which it includes (SPEC 4.3), so a reload that turns on a base's flag turns on each subclass's as well, and a frame with a live subclass value blocks the same way. So it is the same in `dev` as under `enrang test`, and it never comes from a reference field whose type is `readonly &`, or from a tuple field whose reference parts at every depth are all `readonly`, while a tuple field with a reference part that is not `readonly`, nested or not, always sets it (SPEC 4.3): an edit that drops such a `readonly` can turn the flag on, as one that adds a write can. Turning the flag off, or adding `readonly` to a field or to a tuple field's reference part, needs nothing, because old code then made more of its stores exclusive than new code needs.

**Literals of grown types.** Field initialisers compile to dev-only shims, so a rebased `new Player { name, score }` calls the shim for `level`. A field with no initialiser takes its type's default (SPEC 4.3), as in MIG-01, or blocks if the type has none. A named form, in its class's module or another, fills the fields it leaves out by calling the class's fill function for that set, which the declaring module owns and which writes the class's table first (`ARCHITECTURE.md` section 5). That call binds by `sigHash` as any call does, so an edited default reaches an old frame's named form as a new body would, and the shim adds only the fields the class gained.

**Retired constructors.** A call that binds a retired constructor body, written or synthesised (that of a subclass with no constructor of its own, or the implicit one of a chain with none, SPEC 4.3), never assigns a field its class gained since. So each level of the chain that runs a retired body first stores each field its own class gained, through the field's most derived initialiser shim, as in MIG-01, or else its type's default. A level that runs its latest written body stores its fields itself. A gained field with neither blocks the frame whose reachable code would make the call (rebase step 5), and refuses the reload with EN1213 when a pinned body would make it (ADV-70). The implicit constructor of a chain with none never stores a field with no default: a subclass's constructor assigns each such inherited field itself after its `super()`, which EN0610 enforces (SPEC 4.3). So a latest body whose `super()` reaches the implicit constructor stores the field, while old code that binds the implicit constructor by `new C()`, or a retired subclass body whose `super()` reaches it, blocks the same way when the chain gained such a field.

**Constructor frames.** A frame running a constructor for an object of a dirty class, a base class's constructor included, whether a `super(...)` call reached it, it runs for a subclass with no constructor of its own, or it is the implicit constructor of a chain with none (SPEC 4.3), holds a partly initialised `this`, so it is always a blocking frame, and so is a frame running a dirty class's fill function for a named form. That covers the time a base constructor spends in an override it calls through `this`, which runs the object's own class's code (SPEC 4.3). A constructor frame of any class, dirty or not, never takes loop-head replacement (below).

**New variant reaches an old `match`.** The rebased switch gets a synthesised arm: panic `v3 of `f` met variant `Frozen`, added in v4`, then pause and retry. Never undefined.

**Loop-head replacement.** A frame whose own body changed runs the old body until return (Smalltalk behaviour), except at a back edge, where it jumps to the new body if all of these hold:

- the same-identity loop exists (nesting path plus label) and the signature is unchanged, contract included (section 5);
- the frame is not running a constructor, whose `this` is partly initialised and tracked field by field (SPEC 4.3), so the new body could assume a field the old frame never set, and its D3 drop would drop it (ADV-71);
- neither body contains `unsafe`;
- every user local live into the new loop head maps by name, scope and type, with matching init state;
- every hidden local live into the new loop head maps by (loop identity, role), and only to an old local of the equal `LoopRole` and equal type. A new head needing a role with no old local refuses;
- an old `IntoIter` has a counterpart in the new loop. It is refused, not dropped, because it owns the elements still to come;
- no ref-carrying local is live in, that is a reference, a borrowing class or tuple, or a nullable of one (SPEC 5.1), except parameters that are never reassigned, as a reference parameter and `this` never are. A reference-typed `Source` falls under this.

Hidden locals have no name, which is why they map by role: a mapping by position could pair `_i` with an unrelated hidden local. `_n` is assigned at every head, so it is never live in. `_i` may carry across a change of source array, with a note, because the next head reads the length again and the bind is bounds-checked. Unmapped initialised old user locals drop in reverse declaration order, with a note. Ref-carrying locals are refused because the new borrow check assumed origins that the old code did not establish, and a borrowing value carries the loans its old stores made just as a reference does (ADV-56). If replacement is refused, the frame stays old and the status line says so, naming the cause, such as a changed contract or a constructor frame. Whether a new body whose contract only reads where the old one wrote may still replace, as a function that reads fits where a write is declared (SPEC 4.4), is to be considered at M6.

**A new body may assume a fact the old code never established.** The same nesting path can hold `if (o == null) { for (const x of &other) {} }` in v1 and `if (o != null) { for (const x of &o) {} }` in v2, and the same goes for range locals and any other head. Every head and bind re-reads through `CheckTag` and `CheckBounds`, so this is never memory unsafety: a `CheckTag` failing in a replaced body takes the synthesised panic-and-pause path of ADV-2.

**Frames in `for...of` loops.** A path source (SPEC 5.6) adds no hidden reference: the loop holds its source until it ends, but that hold is a phantom slot that only the borrow checker sees, with no run-time storage, and each head reads the path again. At a back edge the loop itself therefore has only `_i`, and a binding `x` that is dead there is ignored (REF-02). So when no other ref-carrying local is live in, such a frame can take loop-head replacement (ADV-53). The ref-carrying rule above still covers what the program itself holds, a borrowing value included. A path through a reference local keeps that local live at the back edge, because the next head reads it. A parameter such as `xs` in `function f(xs: &Slice<T>)`, or `this`, may carry over, since neither is ever repointed (ADV-52), while `const r = &queue; for (const job of r)` refuses, and so does a frame with a saved element such as `longest = x` (ADV-51). A live `x` at a callee's safe point is an ordinary reference: REF-01 retargets it, and REF-03 blocks. A frame whose reachable code reads a source field that was removed or retyped is a blocking frame by step 5 above, and a fixed-array length change through a hook blocks the same way, so a stale static length never reaches a shorter array. An evaluate-once source holds `_src`, so a frame in such a loop refuses replacement by the ref-carrying rule until the loop ends. A consumed `T[]` holds `ArrayIntoIter`, which is a typed frame local that the census walks. The output of `[...queue]` in flight is a typed `Temp`, so the census covers it too. A `T[N]` spread is a `FixedToSlice` and the same `extendCloned` call as any spread, so it has no loop of its own, and a user `clone` under it defers a schema reload as ADV-48 says.

## 7. State migration

**Applies when** the schema diff is non-empty or a method table changed (MIG-15), compilation is clean, a walkable safe point is reached and no frame blocks. Only dirty types (changed, inlining a changed type, or with a changed method table) and paths reaching them are walked. A `&A`, `Box<A>` or `Box<I>`, or a two-word `&I` (section 5), can hold a subclass or any implementing class, so a path through one reaches each dirty class it could hold, and the class the value holds must still fit that static type in the new version (MIG-16). Exactly one schema is live at any time.

**Roots.** Frame locals, filtered by move dataflow and drop flags at the pc, plus closure env locals, plus statics. Since MIR locals are typed, in-flight temporaries are covered.

**Owner edges.** `Box`, `T[]`, `string` and `ArrayIntoIter` declare `@owner` shapes, restricted to `alloc` in the prototype (EN0806 elsewhere). The walker verifies that each edge targets the start of a live allocation. An edge with `cap == 0` or a zero-sized target holds a dangling pointer by design, so the census skips it.

**Census.** Every live allocation must be visited exactly once, or be rodata, or be an untouched island with no dirty tag. Otherwise the reload is refused (EN1215, naming both paths when one was visited twice). Provenance tables locate every raw pointer exactly. The census also counts hidden pointers and the table words of `Box<I>` values and of two-word `&I` references, a field or tuple part of a borrowing value included: each one that names a changed table is retargeted exactly once, and after commit none names an old table. An `&I | null` holding `null` has 0 in both words and names no table, so the census skips its table word (section 2.3). It reads each one against the static type of the place it was reached through, which is how MIG-16 finds a class that no longer fits, and it finds every live function value by its `Fn` provenance, for the check of pinned bodies (section 6).

**Rules.** Row IDs are stable, and each has a reload scenario (`TESTING.md` section 18).

| ID | Edit | Rule |
|---|---|---|
| MIG-01 | Field added | Hook, else field initialiser (pure, fuel-limited), the one in the object's own class when a subclass gives the field a new default, else the type's default (SPEC 4.3), with a note. Otherwise refuse (EN1210): a class, enum, `Box`, `Result` or reference has no default |
| MIG-02 | Field removed | Its value goes to quarantine, migrated like any live value of its type. A user destructor runs after commit, count reported. If the field's own type was deleted, refuse (EN1210): its destructor belongs to a schema that no longer exists |
| MIG-03 | Renamed | `@was`. A same-typed remove plus add is never guessed: a TTY asks; otherwise remove plus add, with a fix-it |
| MIG-04 | Reordered, visibility | By name, through `remap_ids`; no value effect |
| MIG-05 | Retyped, lossless | Integer widening, `f32` to `f64`, `i32` to `f64`, `T` to `T \| null`: automatic |
| MIG-06 | Retyped, narrowing | Integer narrowing, exact `f64` to `f32`, `T \| null` to `T`: value-checked, for an `&I \| null` on its object word alone (section 2.3); first failure refuses and names the path (EN1216) |
| MIG-07 | Other retype, fixed-array length | Hook or refuse (EN1210) |
| MIG-08 | Variant added | Tags rewritten by name, since tags number from declaration order; payloads follow field rules |
| MIG-09 | Variant removed | Allowed if no live value has it; otherwise refuse with path (EN1210) |
| MIG-10 | Class to enum, deleted type still live | Hook or refuse (EN1210) |
| MIG-11 | Generics | Per mono instance; parameters match by name; adding or removing one refuses (EN1210) |
| MIG-12 | `unsafe let` | Value kept, by the same rules; new statics initialise; removed statics drop |
| MIG-13 | `T[]` of a dirty `T` | New buffer. New `cap` is the old `cap` when old and new sizes are both non-zero, and `len` when `T` was zero-sized (no allocation if `len` is 0). If `T` becomes zero-sized, free the buffer and use the maximum `cap`, with `ptr` set to `alignOf<T>()` when `len` is above 0, never 0, so `&I \| null` never reads an element as `null` (SPEC 11) |
| MIG-14 | `Box` of a dirty `T` | Migrates the block. A zero-sized `T` that gains fields allocates; one that loses them all frees the block. A `Box<A>` or `Box<I>` migrates by the class its table names, so a `Box<Animal>` holding a `Dog` follows `Dog`'s changes and its block takes `Dog`'s new size, provided that `Dog` still extends `Animal` (MIG-16) |
| MIG-15 | Method table changed: a method or interface implementation added, removed or re-signatured, the class's size, or `final` gained or lost | The class is dirty even if its fields are not, and so are its tables for the interfaces it is converted to, which its table points at (SPEC 11). At commit every hidden pointer that names its table moves to its new table, and every table word of a `Box<I>` or of a two-word `&I` that names its table for `I` moves to its new table for `I`, which also gives the size a later free reads. A class that gains the hidden pointer by losing `final` gets the word; one that loses it drops the word. A frame whose reachable code calls a method on such a class or builds one blocks, because the MIR builder fixed those under the old `final` (section 6) |
| MIG-16 | Base class or interface removed or changed: `extends` dropped or replaced, a class losing or changing a member that an interface it is held as needs, an interface gaining or changing a member, or a base class made `final`, which makes its subclasses drop `extends` (EN0442) | Allowed if every live value reached through a place of static type `&A`, `Box<A>` or `Box<I>`, or through a two-word `&I`, names a class that in the new version is still `A` or a subclass of `A`, or still satisfies `I` (SPEC 4.4). An `&I \| null` holding `null` names no class and always passes (section 2.3). Otherwise refuse with path (EN1210), as MIG-09 does: old code would read the object as an `A`, and no new table fits the place. Satisfaction is structural, so dropping only `implements I` from a class that keeps `I`'s members changes nothing here: commit builds the class's v2 table for `I` for each live table word that names its v1 one, also when v2's code converts no such class (MIG-15). Old code that would make a value that no longer fits blocks its frame (section 6) |

**Hook: yes**, as in Erlang's `code_change`, because rules cannot infer intent:

```ts
@devMigrate
private function migratePlayer(old: { first: string, last: string, hp: i32 }): Player {
  return new Player { fullName: `${old.first} ${old.last}`, hp: old.hp * 10 };
}
```

The parameter's anonymous object type states the old schema and is checked against the real one. A stale hook warns (EN1212) and is ignored. `old` is owned, its children are already migrated (the walk is bottom-up), there are no capabilities, and fuel is limited. Production builds strip it, and calling it from code is EN1211.

**A hook is pure by static check.** A hook runs new-version code before commit, against a heap still in transition, so it takes only `old` and returns only the new value. Its reachable mono call graph may not contain user `unsafe`, an `unsafe let` or a host call (EN1217). Library-internal `unsafe` in `core` and `alloc` is exempt, because a hook reaches it only through safe APIs, and so are `vm.alloc`, `vm.dealloc` and `vm.realloc`, which are limits rather than capabilities. A local function with hidden arguments, its own or those of the local functions it calls, cannot be a hook (EN0806, SPEC 5.5): the runtime calls it, so no call site would supply them. Fields of `old` the hook does not consume go to quarantine and drop after commit, so a leftover field whose destructor logs does not refuse the reload.

**Transaction.** Migration is all-or-nothing before commit.

```text
plan: schema diff, dirty set, per-type copy plan        (no guest state touched)
walk: iterative, explicit stack, builds shadow allocations, forward map, runs hooks in shadow;
      moves each removed field's value, children migrated, into a typed quarantine allocation
checks: census (quarantine counted), narrowing values, references (section 8), memory limit
---- commit point ----
swap code, type and method tables; retarget references and pointers through the forward map,
and hidden pointers and table words to the new tables;
free old allocations; run destructors from quarantine, in walk order; free quarantine
```

Quarantine is what makes the order safe. A removed inline field lived in an old allocation, and its glue needs a layout, so its value is moved out during the walk, under a type that still exists. Old allocations can then be freed before any destructor runs, and no destructor can touch them. If a destructor run from quarantine panics, that is a normal pause under new code, and the remaining entries stay allocated until restart. The order is tested under the VM's fault detector.

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
| REF-08 | Non-null `*T` with dirty `T` | Refuse (EN1214) |
| REF-09 | Erased data (`*u8` cast later, classes stored as bytes) | Undetectable. Accesses stay checked, values may be stale; a warning counts untagged allocations kept |
| REF-10 | Function value | Holds `FnId` + `sigHash`, the `sigHash` that the body version which made it was compiled against, also when an old frame makes it after a reload, and a call through it compares the pointer hash, which covers only parameter and result types (section 2.3). Deleted or re-signatured targets, a changed contract included, such as a new store, pin the retired body for these values, with a warning. A pinned body is checked again at every later reload, as a frame's reachable code is: refuse (EN1213), naming the value's path, if it cannot rebase (section 6, FAIL-14) |
| REF-11 | Live `ClosureValue` | Pins its exact old arrow body until the call that received it returns (section 5) |
| REF-12 | Literal strings, and literal views of constants such as `&[2, 3, 5, 7]`, which are read-only statics (SPEC 4.7) | Old-version rodata lives for the session. A live reference into it whose element type is dirty, such as an enum whose tags were renumbered (MIG-08), is a blocking frame, as REF-03: rodata is never rewritten |
| REF-13 | Hidden method-table pointer, table word of a `Box<I>` or of a two-word `&I` | Retargeted at commit to the new table of the class the table belongs to, for a table word its new table for the same interface (MIG-15), never left on a retired one. An `&I \| null` holding `null`, whose object word is 0, names no table: its table word, also 0, is left as it is (section 2.3). A value whose class no longer fits its place refuses instead (MIG-16). A frame in, or reaching, a call through an entry whose `sigHash` changed blocks, as REF-03 does (section 6) |
| REF-14 | Live `&Slice<T>`, a `&T` whose `T` is bound to a view included (SPEC 4.10) | Retargeted only if all `len` elements it views survive, in order and contiguous, with the same type, so its length still holds; otherwise a blocking frame, as REF-03. An empty view retargets by its index: the new base plus the index times the new element size, inside the migrated array. A view with no provenance, of an array that holds no allocation, keeps a dangling pointer aligned for the new `T`. A view that `Slice<T>.fromRaw` made over untagged memory, such as a raw `alloc(bytes)` block, refuses as REF-08 (EN1214) when `T` is dirty, and otherwise stays valid, as REF-05 |

## 9. Panic pause and retry

A dev panic stops at the faulting statement with frames and heap intact and no drops, matching production's no-unwind rule. Non-interactive VM runs print the same message and exit 101.

**There is no resume at the faulting statement,** because no sound map exists from an old pc to a new one. Retry means rollback to a checkpoint, then re-entry using the latest code.

**Journal.** A 64 MB ring records stores (old bytes and provenance), allocations, frees (bytes retained until evicted) and host effects. Checkpoints sit at each frame entry and at back-edge register snapshots, throttled to one per 10k statements per frame. Journal memory counts against `--max-memory`. It exists only in `dev`.

**Retry target.** The outermost changed frame on the stack, else the panicking frame; `[u]` moves outward. A target needs its checkpoint in the ring, an unchanged signature (its `sigHash`, so a body edit that changes the contract counts as a change), and no barrier crossed.

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

A clean retry runs automatically on save. A barrier asks. Restart is the only option after an evicted checkpoint, a committed migration, or a changed signature, contract included, at every eligible frame.

## 10. Failure rules

One principle: **never corrupt state. Either the old program keeps running unchanged, or the reload commits completely, or the user is told to restart.**

Row IDs are stable, and each has a reload scenario (`TESTING.md` section 18).

| ID | Failure | State afterwards | Report | Offered |
|---|---|---|---|---|
| FAIL-01 | Compile error in new code, including an unedited file whose callee's contract changed, a module with no source that fails its recheck against an import's new contracts or whose used items changed in more than contracts and flags (EN0315), and an interface file whose stored code fails the MIR verifier or does not match its contracts (EN0316) | Old program running | Diagnostics, `still running vN` | Save again |
| FAIL-02 | Program became VM-incompatible | Old program running | EN1201-EN1203, EN1205 | Build natively |
| FAIL-03 | No walkable point in 5 s | Old program running | Names the blocking frame | Restart |
| FAIL-04 | Blocking frame, reference to removed data | Old program running, reload pending | EN1213 | Wait, or restart |
| FAIL-05 | Migration impossible, including a removed field whose type was deleted | Heap byte-identical, old code | EN1210 with path | Hook, or restart |
| FAIL-06 | Raw pointer into rewritten allocation | Heap byte-identical, old code | EN1214 | Restart |
| FAIL-07 | Census failure | Heap byte-identical, old code | EN1215 with both paths | Restart |
| FAIL-08 | Narrowing retype failed on a value | Heap byte-identical, old code | EN1216 with path and value | Restart, or widen |
| FAIL-09 | Hook panics or loops | Journal rollback, old code | Panic report of the hook | Fix the hook |
| FAIL-10 | Hook reaches user `unsafe`, an `unsafe let` or a host call | Old program running; refused before any walk | EN1217 naming the path | Fix the hook |
| FAIL-11 | Stale hook | Reload proceeds without it | EN1212 warning | Remove it |
| FAIL-12 | Removed field's destructor panics | Post-commit: new code, normal pause | Panic report, "restart is the only retry" | Restart |
| FAIL-13 | Out of memory during shadow | Heap byte-identical, old code | EN1210 naming `--max-memory` | Raise the limit, or restart |
| FAIL-14 | A live function value pins a retired body that reaches removed or retyped data, a changed table entry or another case that section 6 lists for pinned bodies | Old program running; reload refused | EN1213 naming the value's path | Restart |

Exit codes: `[q]` after a panic exits 101, a clean program exit returns its code, and an internal VM error exits 3.

## 11. Worked scenario

`server.en`, v1. It has no top-level statements, so `main` is its entry point (SPEC 6):

```ts
import { os } from "os";

private class Player {
  public name: string;
  public score: i64;
}

private class Game {
  public players: Player[];
  public tick: isize;
}

private function step(g: &Game): void {
  g.tick += 1;
  const who = g.tick % g.players.length();
  g.players[who].score += 10;
  console.log(`tick ${g.tick}: ${g.players[who].name} = ${g.players[who].score}`);
}

private function main(): void {
  let game = new Game {
    players: [
      new Player { name: "Ada", score: 0 },
      new Player { name: "Grace", score: 0 },
    ],
    tick: 0,
  };
  while (true) {
    step(&game);
    os.sleep(1000);
  }
}
```

**v2** adds `public level: i32 = 1;` to `Player`, adds `if (g.players[who].score % 30 == 0) { g.players[who].level += 1; }` after the score line, and prints `L${g.players[who].level}` in the log line.

**v3** inserts these before the `+= 10` line, so they become lines 17 and 18:

```ts
  const rival = who + 1;
  g.players[rival].score -= 1;
```

**v4** changes line 17 to `const rival = (who + 1) % g.players.length();`.

Timings are illustrative.

```text
$ enrang dev server.en
enrang dev | layout vm64 | no grants | watching 1 file
[v1] running
tick 1: Grace = 10
tick 2: Ada = 10
tick 3: Grace = 20
[v2] compiled in 38 ms; applied at os.sleep (server.en:30:5)
     Player +level: i32 = 1 (field initialiser); 40 -> 48 bytes
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
  main (server.en:33:5)
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

- **v1 to v2.** The safe point is `os.sleep`: `main` is user code, and the `os/vm` frame is parked with scalars only, so it is walkable (section 5). `game` is an address-taken local whose `Game` shape does not change size, but `players` owns a buffer of 2 x 40 bytes, which becomes a new allocation of 2 x 48; each `Player` carries an 8-byte method-table pointer, because the class is not `final` (SPEC 11). `name` and `score` copy by name, and `level` runs its initialiser shim. `Player`'s table records its size, so it changed too, and each pointer moves to v2's table (MIG-15). No reference is live: `step` has returned, and the `&game` borrow it received died with it. Census: `game` frame allocation, the one array buffer, and rodata for the two literal names. `main` keeps its pc by rebase.
- **v2 values.** Tick 4: `who` 0, Ada 20. Tick 5: `who` 1, Grace 30, and `30 % 30 == 0` makes her level 2.
- **v3 is code only.** No schema change, so `step` is replaced at the next call. `main` is unchanged by `sigHash` and `bodyHash`, so it adopts the new spans, which is why its line reads 33 although the frame is older.
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
| 7 | A removed field's destructor panics | After commit: new code is live, the normal pause applies, restart is the only retry |
| 8 | Comparator edited, array no longer sorted | Undetected. A future `Map` would declare derived structure and rehash; user caches get nothing |
| 9 | `price` changes from dollars to cents, same type | Undetected unless the user writes a hook |
| 10 | Edit above `while (true)` | Replacement skips it. A note says those lines already ran; restart to apply |
| 11 | `const first = &names[0]` live at the loop head | Replacement refused; the frame stays old and the status line says so |
| 12 | Saves during compile, pause or migration | Coalesced; latest wins. A failing v5 leaves a good pending v4 pending |
| 13 | Guest forges `0x7fff0000 as *u8`, or passes a huge length to a host call | The cast makes a pointer with no provenance and does not fault; the first read or write through it faults inside the VM (EN1204), and a host call given a range that fails the checks is a bad host pointer. Host memory is never touched |
| 14 | Constructor of a dirty class is on the stack | Blocking frame until it returns: `this` is partly initialised, so there is no value to walk |
| 15 | A local is partly moved when its class grows | Blocking frame: its elaborated drop ladder names the old field list. The reload applies when the frame returns |
| 16 | User function holding a closure parameter when a captured path's class changes | Env fields are typed frame slots, so they retarget or block by the reference rules |
| 17 | `T \| null` retyped to `T` while a null is live | Value check fails, heap unchanged, EN1216 with path |
| 18 | `Player` loses `implements Copy` while an old frame's reachable code copies it | Blocking frame |
| 19 | Program stores `sizeOf<Player>()` in a variable | Stale value; undetected. Listed in section 13 |
| 20 | Spin loop with no host call, or an index loop that keeps pushing to its own array | A spin loop, or a growing loop of zero-sized elements, never reaches the host: `--spin-limit` pauses, and saving a fix can apply at the back edge by loop-head replacement. Any other growing loop reaches the host whenever a push reallocates: it panics `out of memory` at `--max-memory`, which pauses, and saving a fix retries (section 9). A `for...of` cannot grow its source: a push to it inside the loop is a compile error (EN0706) unless the loop is left right after |
| 21 | Allocation loop during journalling | `out of memory` panic pause at `--max-memory`, which counts the journal |
| 22 | Reload adds a capability-needing call | Grants unchanged: `Err(IoError.PermissionDenied)`, or a prompt on a TTY |
| 23 | Reload makes `asm` reachable | EN1201 before anything changes; old program keeps running |
| 24 | Rename guessed wrongly: same-typed remove plus add | Never guessed. A TTY asks; otherwise remove plus add with a `@was` fix-it |
| 25 | Hostile host process swaps a symlink during the path check | Out of the threat model, stated in section 4 |
| 26 | v2 inserts an arrow above a running `xs.forEach(...)`, shifting ordinals | The running call keeps its pinned old arrow; it never binds the new arrow at the old ordinal |
| 27 | v2 keeps an arrow's ordinal and changes its captures | New calls see a different capture hash and do not rebind to the old body; the running call stays pinned |
| 28 | Class gains a destructor while a frame holds it partly moved | Blocking frame; the destructor is never silently skipped |
| 29 | Class loses Copy, and a frame has a live local of it with no later read | Blocking frame; the value does not leak on return |
| 30 | A removed field's class was also deleted | Refused (EN1210); no destructor runs from a schema that no longer exists |
| 31 | A removed inline field's destructor runs under the fault detector | Runs from quarantine after commit; no use-after-free of the old allocation |
| 32 | Hook reads an `unsafe let`, or contains `unsafe` | Refused statically (EN1217) before the walk |
| 33 | Hook leaves a field of `old` whose destructor logs | Reload proceeds; the destructor runs after commit from quarantine |
| 34 | Safe `get(i)` becomes `unsafe function get(i)` | `sigHash` changes, so old frames bind the retired safe body |
| 35 | An old frame calls `helper`, whose signature changed, and retired `helper` reads a removed field | Blocking frame, by transitive analysis |
| 36 | `private final class M {}` gains a field with an `M[]` live | New buffer with `cap == len`; census clean |
| 37 | A `final` class loses all its fields with a `T[]` live | Buffer freed, `cap` becomes the maximum; census clean |
| 38 | `Box<M>` of a zero-sized `M` grows, and later shrinks | Allocates on growth, frees on shrink; no false census failure |
| 39 | Class fields reordered and a variant inserted, with an old frame live | `remap_ids` keeps field reads and `Switch` arms correct |
| 40 | Guest `unsafe` forges a function value from integers, or reinterprets one at other parameter or result types, and calls it | Bad function pointer fault pauses; the session survives |
| 41 | v2 edits the body of a running `for (const job of &queue)`, adding `if (turns > 2) { break; }` | Replacement takes at the back edge: `_i` maps by (loop identity, `Index`) and `turns` by name. The saved fix ends the loop early |
| 42 | v2 changes the source to a shorter array, `for (const job of &other)` | Replacement takes, with a note that the index carried over. The next head reads the new length and leaves if the index is past it; no bounds panic |
| 43 | v2 changes a path source to `[...queue]` | Refused: the new head needs `IntoIter`, and the old frame has none. The frame stays old and the status line says so |
| 44 | v2 changes a path source to `&grid[r]`, which is evaluated once | Refused: the new head needs a reference-typed `Source`, and no value exists for it. The old path source had none, because its hold exists only in the borrow checker |
| 45 | v1 `if (o == null) { for (const x of &other) {} }`, v2 `if (o != null) { for (const x of &o) {} }`, on the same nesting path | Replacement may take with the fact never established. `CheckTag` at the new head fails into the panic-and-pause path of ADV-2. Never undefined |
| 46 | v1 `for (const x of [...q])` in flight, v2 a path source | Refused: the old `IntoIter` has no counterpart, and it owns elements, so it is not dropped |
| 47 | Source field removed or retyped while a frame is in that loop | Blocking frame by rebase step 5, unless the frame takes loop-head replacement at the next back edge and its old code reads the field nowhere before it; applied when the frame returns |
| 48 | Schema reload while a user `clone` runs under `extendCloned` in `[...a]` | The `alloc` frame is not walkable, so it defers. Code-only swaps proceed |
| 49 | `[...fixed]` with `T[N]`, and a schema reload while a user `clone` runs under its `extendCloned` | A `FixedToSlice` and the same `extendCloned` call as any spread, with no back edge of the compiler's own, so the `alloc` frame is not walkable and the reload defers, as in ADV-48. `_out` is a typed `Temp` that the census counts |
| 50 | `x` live at a callee's safe point in a `for...of` loop, then a reload that moves the array | REF-01 retargets `x`; if the element was removed or retyped, REF-03 blocks. No stale pointer survives |
| 51 | `const r = &queue; for (const job of r)`, or a saved `longest = x`, at a back edge | Replacement refused: `r` or `longest` is a live ref-carrying local and not a parameter, even though the loop's hold adds no hidden reference. A live borrowing value refuses the same way (ADV-56). The frame stays old and the status line says so |
| 52 | `private function f(xs: &Slice<T>) { for (const x of xs) { g(x); } }`, or `for (const x of &this.items)`, at a back edge with `x` dead | Replacement can apply: `xs` and `this` are parameters, which are never repointed, and the loop adds only `_i`, since its hold has no run-time storage |
| 53 | A frame in `for (const job of &queue)` reaches a back edge while the loop holds `queue`, with `job` dead and no other ref-carrying local live | Replacement can apply: the hold is a phantom slot that only the borrow checker sees, with no run-time storage, so the loop adds only `_i` |
| 54 | A function that only reads its argument is stored in a field of type `fn(let x: &i64) => void`, and called through it; or `private function first(a: &string, b: &string): &string { return a; }`, whose result comes only from `a`, is stored as `const pick: fn(a: &string, b: &string) => &string = first;` and called through `pick` | Each call compares the pointer hash, which covers only parameter and result types and leaves the whole contract out, so neither faults, and `console.log(pick(&ada, &grace));` prints `Ada`, as a native build does. The function's own `sigHash` still picks its body |
| 55 | `mid`, on the stack, passes its parameter on to `leaf`. v2 makes `leaf` write through it, so the unedited `mid` now writes too, and v2's `main` drops a later read of `r`, which the new write would forbid | `mid`'s frame keeps its old body, because `bodyHash` covers post-inference MIR and adoption needs both hashes. It calls the retired `leaf`, so the old `main` prints 1, never 42 |
| 56 | `let cur = new Cursor(&dummy); cur.set(&xs[0]);` runs above a `while` loop that prints `cur.get()`; v2 deletes the `set` line and pushes to `xs` in the loop | Replacement refused: `cur` is a live borrowing local, whose loan on `xs` v1 made and v2's check never saw. The frame stays old and the status line says so; replacing it would let the push free the buffer `cur.get()` reads |
| 57 | `Dog.speak` stops writing `this.name` and only reads it, a `Dog` built under v1 sits in a `Box<Animal>`, and v2's `tick` keeps a part of `p.name` across `p.speak()` | `Dog`'s table changed, so the reload walks it and moves the object's hidden pointer to v2's table at commit (MIG-15). v2's `tick` calls the reading `speak`, never the retired body that would free what the part reads |
| 58 | v2 makes `speak` write `this.name` and changes `tick` to drop its part; an old `tick` frame is parked in `os.sleep` after taking its part of `p.name` and before calling `p.speak()` | Blocking frame (REF-13): after commit the new table would give that call the writing body, which the old frame was not checked against. The reload applies when the frame returns |
| 59 | v2 changes only the body of `rewind(s: &string)` so it stores `s` in `this`, keeping every permission, while an old `step` frame parked in `os.sleep` still has `lx.rewind(&tmp)` ahead, with `tmp` its own local | Stores are in `sigHash`, so the old frame binds the retired `rewind`, which stores nothing, and `lx` never keeps a reference to `tmp` past its frame |
| 60 | `Dog` gains a field while a `Box<Animal>[]` holds a `Dog`, and `Animal` is unchanged | The box migrates by the class its table names: its block grows to `Dog`'s new size, and its hidden pointer moves to v2's table, whose size a later free reads. No census failure and no bad free |
| 61 | v2 makes a `Cursor` method push through its reference field, turning on the class's flag for writing through its reference fields, while `main` holds a live `cur` whose v1 store took a shared loan | Blocking frame: `cur`'s loans were checked as shared. The reload stays pending until the frame returns, or the user restarts |
| 62 | v2 adds a method to `Animal`, which changes its table (MIG-15), while an old frame parked in `os.sleep` still has `pet.unbox()` ahead, for a `Box<Animal>` holding an `Animal`; the same with a `Dog` in the box | Commit moves the object's hidden pointer to v2's table, and the rebased frame's exact-class check compares it with v2's `Animal` table, so the `Animal` unboxes with no false panic. The `Dog` still panics `` `unbox` expected an `Animal`, but the box holds a `Dog` `` and pauses |
| 63 | `for (const s of &all) { introduce(s); }` runs over a `Box<Speaker>[]` holding a `Dog` and a `Robot`, and v2 gives `Dog` a field while a frame of `introduce`'s dynamic copy, holding `s` for the `Dog`, is parked in `os.sleep` before calling `s.speak()` | `s` is two words. REF-01 retargets its object word to the migrated `Dog`, and commit moves its table word to v2's `Dog` table for `Speaker` (REF-13), which the census counts once, so the call prints `woof` through v2's table. No word of `s` names a v1 table after commit |
| 64 | `op(&lab, &title)` runs every turn, with `const op: fn(let l: &Labeler, t: &string) => void = measure;`, and `measure` keeps `const r = l.label(title, &fb);` across `fb = "z";`, which v1 allows because `Labeler.label` returns `name`. v2 makes `measure` write `l.count`, so `op` pins the retired `measure` (REF-10); v3 makes `label` return `fallback` and drops the assignment from the new `measure` | Refused at v3 with EN1213, naming `op`, and restart offered (FAIL-14): the pinned body counts as reachable code at every reload, and it calls through a table entry whose `sigHash` changed. Committing would let it assign `fb` while `r` points into it |
| 65 | A `tick` frame parked in `os.sleep` has `const f: fn(x: &string) => void = show;` ahead, then `f(s)` while `const first = s.slice(0, 1);` is live; v2 makes `show` append to `x` and changes `tick` to match, so the frame keeps its v1 body | The value the old frame makes after the commit names the `sigHash` its body was compiled against (section 2.3), so `f(s)` runs the retired `show`, which only reads, and `first` stays valid. Naming v2's `show` would pass a two-word string to a body that expects the whole descriptor, and grow it under `first` |
| 66 | v2 removes `extends Animal` from `Dog` while a `Box<Animal>[]` holds a v1 `Dog`, and `main`, parked in `os.sleep`, reads `p.name` and calls `p.speak()` through each box | Refused with EN1210, naming the path to the box (MIG-16): in v2 the object's class is not a subclass of `Animal`, so old code would read `name` past the end of a v2 `Dog`. The heap stays byte-identical and the old program runs |
| 67 | v2 removes `speak` from `Robot`, so `Robot` no longer satisfies `Speaker`, while a `Box<Speaker>[]` holds a `Robot`; the same with only `implements Speaker` removed and `speak` kept | Refused with EN1210, naming the path (MIG-16): `Robot` has no v2 table for `Speaker`, so the box's table word has nothing to move to. With only `implements Speaker` removed, `Robot` still satisfies `Speaker` (SPEC 4.4), so the reload commits, and the box's table word moves to the v2 `Robot` table for `Speaker` that commit builds (MIG-15) |
| 68 | v2 makes `Animal` `final`, so `Dog` drops `extends Animal` (EN0442 otherwise), while a `Box<Animal>` holds a `Dog` | Refused with EN1210, naming the path, as in ADV-66 (MIG-16). Without that `Dog`, a `Box<Animal>` holding an `Animal` migrates, and its hidden pointer is dropped (MIG-15) |
| 69 | v2 removes `extends Animal` from `Dog` while no `Dog` is live, and `main`, parked in `os.sleep`, still has `const b: Box<Animal> = new Box(new Dog("Rex")); console.log(b.name);` ahead | MIG-16 passes, since no live value has the class, but the frame blocks (section 6): its reachable code upcasts a `Dog` to `Animal`, which v2's `Dog` no longer extends, so committing would let it read `name` at `Animal`'s offset in a v2 `Dog`. The reload waits, as for a removed field, and FAIL-03 names the frame if no walkable point comes |
| 70 | v2 gives `Dog` the field `private owner: Box<Person>;`, the constructor `public constructor(name: string, owner: Box<Person>) { this.owner = owner; super(name); }` and a `describe` override that reads `this.owner.name`, while an old `adopt` frame, parked in `os.sleep`, still has `new Dog(n.toString())` ahead, and `Animal`'s constructor prints `` `hello, ${this.describe()}` `` | Blocking frame (section 6): the call would bind the retired one-parameter constructor, which never assigns `owner`, and `owner` has no default, so the reload waits until `adopt` returns, and nothing reads an uninitialised field. If the new field is `private tricks: string[] = [];` instead, and the constructor gains a parameter as above, the reload commits: the call binds the retired constructor, and its level first stores `[]` through the field's initialiser shim |
| 71 | v1's constructor of `Pack`, a class v2 does not make dirty, is parked at the back edge of `while (i < n) { i++; }` and sets `this.items = new Box(new Item(i));` after the loop; v2, with the same signature, sets `this.items = new Box(new Item(0));` before the loop and again inside it | Replacement refused: a frame running a constructor never takes loop-head replacement (section 6), so v2's loop body never drops an `items` that the v1 frame did not set. The frame stays old and the status line names the constructor frame |
| 72 | v2 adds `protected override sound: string = "woof";` to `Dog` while a v1 `Dog` constructor frame is parked in `os.sleep` before `super()`, and `Animal`'s constructor prints `` `ctor: ${this.sound}` `` | The override changes no schema (section 5), so the frame does not block. Its `super()` binds the instance of `Animal`'s constructor for the override set its body named, the empty one, which stores `Animal`'s own default, so it prints `ctor: ...` with no fault. A `Dog` built after the commit runs the instance for the set that holds `sound`, and prints `ctor: woof` |
| 73 | v2 makes `Counter` `final` while an old `tick(c: &Counter)` frame, parked in `os.sleep(100)`, still has `c.bump()` ahead, which v1 compiled as a Virtual call; the same edit while a frame runs `while (true) { c.bump(); os.sleep(100); }` | Blocking frame (section 6): commit drops the object's hidden pointer (MIG-15), from which the old call would load its table. The reload commits once `tick` returns, and the next call is direct; nothing faults. The loop frame does not block: after the sleep it reaches the back edge, where it takes loop-head replacement, so the reload commits at the sleep and the old call never runs again |
| 74 | v2 removes `final` from `Counter` and adds `Double extends Counter`, which overrides `bump`, while an old `make()` frame, parked in `os.sleep(100)`, still has `let c = new Counter(); feed(&c);` ahead, where `feed(c: &Counter)` calls `c.bump()`; the same edit while a frame runs `while (true) { let c = new Counter(); feed(&c); os.sleep(100); }`; the same `make` with the named form `let c = new Counter { n: 1 };` | Blocking frame: the old `new`, built under `final`, writes no hidden pointer, and `feed`'s latest body, whose `sigHash` is unchanged, calls `c.bump()` through one, so the reload waits until `make` returns, and nothing reads an uninitialised hidden pointer. The loop frame does not block: its live `c` migrates and gains the word (MIG-15), and after the sleep it reaches the back edge, where it takes loop-head replacement. The named form does not block either: it writes no table itself, and the class's fill function, which it binds by `sigHash`, writes the table under v2's declaration (section 6) |
| 75 | v2 makes `Cursor.step` push through its reference field `v`, which turns on the class's flag, while `main`, parked in `os.sleep` before `let cur = new Cursor(&data);`, still has the construction ahead, and moves `console.log(*e);` above it, since v2 rejects the old order (EN0706 at `&data`) | Blocking frame (section 6): `main`'s reachable code builds a `Cursor` with the shared loan its old check gave, so the reload stays pending until `main` returns, and the status line names the frame. A live function value whose retired body builds one makes the reload EN1213 instead |

## 13. What will not work

Stated plainly:

- **Semantic staleness:** units, caches, sorted order, changed invariants, stored `sizeOf` values.
- **Re-running startup code** without restart.
- **Live edits to a body under an evaluate-once `for...of` source such as `for (const x of &grid[r])`,** or with other live references or borrowing values, or a live element binding, until that loop ends. A path source adds no hidden reference of its own, because its hold exists only in the borrow checker, but these limits still reach a path through a non-parameter reference local, as in `const r = &queue; for (const job of r)`, and any other live ref-carrying local, such as a saved `longest = x` or a `Cursor` that holds a reference.
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
