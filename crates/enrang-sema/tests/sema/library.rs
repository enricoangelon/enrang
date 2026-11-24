//! The sema suite's cases for the library (owner 2B, plan g.1): every module of
//! `lib/` parses in library mode with no diagnostic and prints back unchanged, and
//! the embedded library loads and lowers with no diagnostic on every target, each
//! lang item of M2 declared once, in its layer's graph (TESTING 13: "Each `@lang`
//! item exists in every target's module graph", per layer, plan doc gap G5).
//!
//! The stub's signatures and marks are what M3 reads before the bodies arrive
//! (ARCHITECTURE 10 "Marks on library declarations"), so each one SPEC 8.2-8.4 and
//! ARCHITECTURE 10 spell out is compared, lowered, with a table: `unsafe`, type
//! parameters and bounds, the receiver, each parameter's mark and `?`, the result
//! with `readonly`, and the `where` clause. The table follows plan f where the
//! documents give no mark, as the stub does.

use std::path::PathBuf;
use std::sync::Arc;

use enrang_base::{FileOrigin, SourceMap};
use enrang_diag::{DiagCtx, Milestone, RenderOpts, render_text};
use enrang_hir::{BoundId, DefId, LangItem, LangLayer, Mark, ParamId, Receiver, Tcx, TyKind};
use enrang_sema::{LibSource, LoadError, ProgramInput, analyze, load};
use enrang_syntax::{NodeIdGen, ParseMode, parse_file, print_file};
use enrang_target::{TargetOpts, all_targets, resolve};
use enrang_testkit::Harness;

/// The entry of the embedded-library runs: no library name, so only the
/// library's own declarations can report.
const MAIN: &str = "public function f(a: i64, b: &i64[]): bool { return true; }\n";

/// Parses library module `key` as the loader does, under `lib/<key>.en` with
/// `FileOrigin::Library`: the rendered diagnostics, and the printed tree.
fn parse_lib(key: &str, text: &str) -> (String, String) {
    parse_as(key, text, FileOrigin::Library)
}

fn parse_as(key: &str, text: &str, origin: FileOrigin) -> (String, String) {
    let mut map = SourceMap::new();
    let file = map.add(
        PathBuf::from(format!("lib/{key}.en")),
        Arc::from(text),
        origin,
    );
    let mut ids = NodeIdGen::new();
    let mut dcx = DiagCtx::new();
    let ast = parse_file(map.file(file), &mut ids, ParseMode::Build, &mut dcx);
    let printed = print_file(map.file(file), &ast);
    let diags = dcx.take();
    (
        render_text(&diags, &map, &RenderOpts { color: false }),
        printed,
    )
}

/// Loads and analyzes [`MAIN`] with the embedded library for `target`.
fn lower(target: &str, mode: ParseMode) -> (String, bool, Tcx, &'static str) {
    let (spec, _) = resolve(target, &TargetOpts::default()).expect("a target");
    let input = ProgramInput {
        entry: PathBuf::from("main.en"),
        mode,
        overrides: [(PathBuf::from("main.en"), Arc::from(MAIN))]
            .into_iter()
            .collect(),
        dir: PathBuf::from("/nonexistent/enrang-sema-library"),
        lib: LibSource::Embedded,
        library_entry: false,
    };
    let mut map = SourceMap::new();
    let mut ids = NodeIdGen::new();
    let mut dcx = DiagCtx::new();
    let loaded = match load(&input, &spec, &mut map, &mut ids, &mut dcx) {
        Ok(program) => Some(program),
        Err(LoadError::Aborted(_)) => None,
        Err(LoadError::Unreadable { path, error }) => panic!("{}: {error}", path.display()),
    };
    let os_folder = loaded.as_ref().map_or("", |p| p.os_folder);
    let map = Arc::new(map);
    let mut tcx = Tcx::new(Arc::new(spec), Arc::clone(&map));
    let analyzed = loaded.and_then(|p| analyze(&p, &mut tcx, &mut dcx).ok());
    let diags = dcx.take();
    let rendered = render_text(&diags, &map, &RenderOpts { color: false });
    (rendered, analyzed.is_some(), tcx, os_folder)
}

/// A bound as written: the interface or class with its arguments.
fn bound_string(tcx: &Tcx, b: BoundId) -> String {
    let b = tcx.bound(b);
    tcx.ty_string(tcx.intern_ty(TyKind::Adt(b.adt(), b.args())))
}

/// `T`, or `T extends A & B`.
fn param_string(tcx: &Tcx, p: ParamId, bounds: &[BoundId]) -> String {
    let name = tcx.param(p).name.as_str();
    if bounds.is_empty() {
        return name.to_owned();
    }
    let bounds: Vec<String> = bounds.iter().map(|&b| bound_string(tcx, b)).collect();
    format!("{name} extends {}", bounds.join(" & "))
}

/// A signature as the documents spell it:
/// `unsafe <U extends B>(let this, const a: &T, b?: isize | null) => readonly &T where T extends Ord`.
fn spelled(tcx: &Tcx, def: DefId) -> String {
    let sig = tcx.sig(def);
    let mut out = String::new();
    if sig.unsafety {
        out.push_str("unsafe ");
    }
    let own: Vec<String> = tcx
        .generics(sig.generics)
        .params
        .iter()
        .filter(|&&p| tcx.param(p).implicit.is_none())
        .map(|&p| param_string(tcx, p, &tcx.param(p).bounds))
        .collect();
    if !own.is_empty() {
        out.push_str(&format!("<{}>", own.join(", ")));
    }
    let mut parts = Vec::new();
    match sig.receiver {
        Some(Receiver::Ref(Mark::None)) => parts.push("this".to_owned()),
        Some(Receiver::Ref(Mark::Let)) => parts.push("let this".to_owned()),
        Some(Receiver::Ref(Mark::Const)) => parts.push("const this".to_owned()),
        Some(Receiver::Move) => parts.push("move this".to_owned()),
        Some(Receiver::Static) => parts.push("static".to_owned()),
        None => {}
    }
    for p in &sig.params {
        let mark = match p.mark {
            Mark::None => "",
            Mark::Let => "let ",
            Mark::Const => "const ",
        };
        let default = if p.has_default { "?" } else { "" };
        parts.push(format!(
            "{mark}{}{default}: {}",
            p.name,
            tcx.ty_string(p.ty)
        ));
    }
    out.push_str(&format!("({}) => ", parts.join(", ")));
    if sig.ret_readonly {
        out.push_str("readonly ");
    }
    out.push_str(&tcx.ty_string(sig.ret));
    for (p, bounds) in &sig.where_bounds {
        out.push_str(&format!(" where {}", param_string(tcx, *p, bounds)));
    }
    out
}

/// The definition at `path` (`core/mem::swap`, `core/option::#extend0::take`).
fn def_at(tcx: &Tcx, path: &str) -> DefId {
    let found: Vec<DefId> = tcx
        .defs()
        .filter(|(_, d)| d.path.to_string() == path)
        .map(|(def, _)| def)
        .collect();
    assert_eq!(found.len(), 1, "{path}: {found:?}");
    found[0]
}

/// Hosted signatures (`x86_64-linux`): SPEC 8.2, 8.3, 8.4's hosted API, 7.1 for
/// `ptr.null`, ARCHITECTURE 10's marks, and plan f where the documents give none.
const HOSTED: &[(&str, &str)] = &[
    // SPEC 8.2 `core/mem`: `copy`, `copyOverlapping` and `set` are `@intrinsic`
    // declarations, so `unsafe`; `swap` and `replace` are safe, with `let`.
    (
        "core/mem::copy",
        "unsafe <T>(d: *T, s: *T, n: usize) => void",
    ),
    (
        "core/mem::copyOverlapping",
        "unsafe <T>(d: *T, s: *T, n: usize) => void",
    ),
    ("core/mem::set", "unsafe (d: *u8, v: u8, n: usize) => void"),
    ("core/mem::swap", "<T>(let a: &T, let b: &T) => void"),
    ("core/mem::replace", "<T>(let x: &T, v: T) => T"),
    ("core/ptr::null", "<T>() => *T"),
    // SPEC 8.2 `Slice<T>`; ARCHITECTURE 10: `public const splitAt(i)`, and `const`
    // where an `unsafe` body only reads (`slice`), `let` where a method changes its
    // object; `fromRaw` is `unsafe` and `static`.
    ("core/slice::Slice::length", "(this) => isize"),
    ("core/slice::Slice::isEmpty", "(this) => bool"),
    (
        "core/slice::Slice::slice",
        "(const this, a: isize, b?: isize | null) => &Slice<T>",
    ),
    (
        "core/slice::Slice::splitAt",
        "(const this, i: isize) => [&Slice<T>, &Slice<T>]",
    ),
    ("core/slice::Slice::first", "(this) => &T | null"),
    ("core/slice::Slice::last", "(this) => &T | null"),
    ("core/slice::Slice::get", "(this, i: isize) => &T | null"),
    (
        "core/slice::Slice::find",
        "(this, f: (&T) => bool) => &T | null",
    ),
    (
        "core/slice::Slice::findIndex",
        "(this, f: (&T) => bool) => isize",
    ),
    ("core/slice::Slice::some", "(this, f: (&T) => bool) => bool"),
    (
        "core/slice::Slice::every",
        "(this, f: (&T) => bool) => bool",
    ),
    (
        "core/slice::Slice::forEach",
        "(this, f: (&T) => void) => void",
    ),
    (
        "core/slice::Slice::reduce",
        "<U>(this, init: U, f: (U, &T) => U) => U",
    ),
    (
        "core/slice::Slice::swap",
        "(let this, i: isize, j: isize) => void",
    ),
    ("core/slice::Slice::reverse", "(let this) => void"),
    (
        "core/slice::Slice::sort",
        "(let this) => void where T extends Ord",
    ),
    (
        "core/slice::Slice::sortBy",
        "(let this, f: (&T, &T) => int) => void",
    ),
    (
        "core/slice::Slice::includes",
        "(this, x: &T) => bool where T extends Eq",
    ),
    ("core/slice::Slice::asPtr", "(this) => *T"),
    (
        "core/slice::Slice::fromRaw",
        "unsafe (static, p: *T, n: isize) => &Slice<T>",
    ),
    // SPEC 8.2 integers: `checked*` return `T | null`, `overflowing*`
    // `Overflowing<T>` (S:718).
    ("core/int::#extend0::wrap", "<U extends __Int>(this) => U"),
    ("core/int::#extend0::checkedAdd", "(this, o: I) => I | null"),
    ("core/int::#extend0::checkedNeg", "(this) => I | null"),
    ("core/int::#extend0::wrappingAdd", "(this, o: I) => I"),
    ("core/int::#extend0::saturatingSub", "(this, o: I) => I"),
    (
        "core/int::#extend0::overflowingMul",
        "(this, o: I) => Overflowing<I>",
    ),
    // SPEC 8.2 `core/fmt`: the `static unsafe` factory `Formatter.fromFn`.
    (
        "core/fmt::Formatter::write",
        "(let this, const s: &string) => void",
    ),
    (
        "core/fmt::Formatter::writeByte",
        "(let this, b: u8) => void",
    ),
    (
        "core/fmt::Formatter::fromFn",
        "unsafe (static, sink: unsafe fn(*u8, *u8, usize) => void, ctx: *u8) => Formatter",
    ),
    // SPEC 8.2 `core/string`: a part of a string is read-only (8.3, ARCHITECTURE 10
    // `readonly` results).
    ("core/string::string::length", "(this) => isize"),
    ("core/string::string::charCount", "(this) => isize"),
    ("core/string::string::byteAt", "(this, i: isize) => u8"),
    (
        "core/string::string::codePointAt",
        "(this, i: isize) => u32",
    ),
    (
        "core/string::string::slice",
        "(this, a: isize, b?: isize | null) => readonly &string",
    ),
    (
        "core/string::string::splitAt",
        "(this, i: isize) => readonly [&string, &string]",
    ),
    ("core/string::string::parseInt", "(this) => i64 | null"),
    ("core/string::string::parseFloat", "(this) => f64 | null"),
    ("core/string::string::asPtr", "(this) => *u8"),
    // SPEC 8.2 `core/option`, through `extend<T> T | null`.
    ("core/option::#extend0::take", "(let this) => T | null"),
    ("core/option::#extend0::isNull", "(this) => bool"),
    (
        "core/option::#extend0::orElse",
        "(move this, d: () => T) => T",
    ),
    (
        "core/option::#extend0::clone",
        "(this) => T | null where T extends Clone",
    ),
    // SPEC 8.3 `alloc`: `GlobalAllocator` and `FreeListHeap` as its block writes them.
    (
        "alloc/heap::GlobalAllocator::alloc",
        "unsafe (let this, size: usize, align: usize) => *u8",
    ),
    (
        "alloc/heap::GlobalAllocator::dealloc",
        "unsafe (let this, p: *u8, size: usize, align: usize) => void",
    ),
    (
        "alloc/heap::FreeListHeap::alloc",
        "unsafe (this, size: usize, align: usize) => *u8",
    ),
    (
        "alloc/heap::FreeListHeap::dealloc",
        "unsafe (this, p: *u8, size: usize, align: usize) => void",
    ),
    (
        "alloc/heap::FreeListHeap::addRegion",
        "unsafe (this, start: usize, bytes: usize) => void",
    ),
    // SPEC 8.3 `T[]`; ARCHITECTURE 10: `public let push`, `public get(i): &T | null`,
    // `public last(): &T | null`, `public const slice(a, b?): &Slice<T>`.
    (
        "alloc/array::Array::withCapacity",
        "(static, n: isize) => T[]",
    ),
    ("alloc/array::Array::length", "(this) => isize"),
    ("alloc/array::Array::capacity", "(this) => isize"),
    ("alloc/array::Array::isEmpty", "(this) => bool"),
    (
        "alloc/array::Array::slice",
        "(const this, a: isize, b?: isize | null) => &Slice<T>",
    ),
    ("alloc/array::Array::get", "(this, i: isize) => &T | null"),
    ("alloc/array::Array::last", "(this) => &T | null"),
    ("alloc/array::Array::push", "(let this, x: T) => void"),
    ("alloc/array::Array::pop", "(let this) => T | null"),
    (
        "alloc/array::Array::insert",
        "(let this, i: isize, x: T) => void",
    ),
    ("alloc/array::Array::remove", "(let this, i: isize) => T"),
    (
        "alloc/array::Array::swapRemove",
        "(let this, i: isize) => T",
    ),
    ("alloc/array::Array::clear", "(let this) => void"),
    (
        "alloc/array::Array::truncate",
        "(let this, n: isize) => void",
    ),
    ("alloc/array::Array::extend", "(let this, o: T[]) => void"),
    (
        "alloc/array::Array::extendCloned",
        "(let this, o: &Slice<T>) => void where T extends Clone",
    ),
    (
        "alloc/array::Array::reserve",
        "(let this, n: isize) => void",
    ),
    (
        "alloc/array::Array::clone",
        "(this) => T[] where T extends Clone",
    ),
    (
        "alloc/array::#extend0::map",
        "<U>(this, f: (&T) => U) => U[]",
    ),
    (
        "alloc/array::#extend0::filter",
        "(this, f: (&T) => bool) => T[] where T extends Clone",
    ),
    (
        "alloc/array::#extend0::join",
        "(this, sep: &string) => string",
    ),
    // SPEC 8.3 `Box<T>`: `move` on the consuming `unbox` (ARCHITECTURE 10).
    ("alloc/box::Box::#ctor", "(v: T) => void"),
    ("alloc/box::Box::unbox", "(move this) => T"),
    (
        "alloc/box::Box::clone",
        "(this) => Box<T> where T extends Clone",
    ),
    // SPEC 8.3 `string`'s growing members.
    (
        "alloc/string::#extend0::withCapacity",
        "(static, n: isize) => string",
    ),
    ("alloc/string::#extend0::clone", "(this) => string"),
    ("alloc/string::#extend0::trim", "(this) => string"),
    (
        "alloc/string::#extend0::split",
        "(this, sep: &string) => string[]",
    ),
    (
        "alloc/string::#extend0::replace",
        "(this, a: &string, b: &string) => string",
    ),
    (
        "alloc/string::#extend0::repeat",
        "(this, n: isize) => string",
    ),
    (
        "alloc/string::#extend0::pushByte",
        "(let this, b: u8) => void",
    ),
    (
        "alloc/string::#extend0::pushCodePoint",
        "(let this, c: u32) => void",
    ),
    (
        "alloc/string::#extend0::pushByteUnchecked",
        "unsafe (let this, b: u8) => void",
    ),
    (
        "alloc/string::#extend0::fromUtf8",
        "(static, b: u8[]) => string | null",
    ),
    // SPEC 8.4's hosted API.
    ("os/linux_x64/os::args", "() => string[]"),
    (
        "os/linux_x64/os::env",
        "(const name: &string) => string | null",
    ),
    ("os/linux_x64/os::exit", "(code: int) => never"),
    ("os/linux_x64/os::now", "() => i64"),
    ("os/linux_x64/os::sleep", "(ms: i64) => void"),
    (
        "os/linux_x64/fs::readFile",
        "(const p: &string) => Result<string, IoError>",
    ),
    (
        "os/linux_x64/fs::writeFile",
        "(const p: &string, const s: &string) => Result<void, IoError>",
    ),
    ("os/linux_x64/stdin::readLine", "() => string | null"),
];

/// Freestanding signatures (`i386-none`): SPEC 8.4's `os/none` table.
const FREESTANDING: &[(&str, &str)] = &[
    ("os/none/prelude::halt", "() => never"),
    ("os/none/prelude::BootInfo::regionCount", "(this) => usize"),
    (
        "os/none/prelude::BootInfo::region",
        "(this, i: usize) => MemRegion",
    ),
    ("os/none/prelude::BootInfo::bootDrive", "(this) => u8"),
    ("os/none/prelude::BootInfo::com1Port", "(this) => u16"),
    ("os/none/prelude::BootInfo::crtcPort", "(this) => u16"),
    ("os/none/prelude::BootInfo::textBase", "(this) => usize"),
    ("os/none/prelude::BootInfo::columns", "(this) => u32"),
    ("os/none/prelude::BootInfo::rows", "(this) => u32"),
    (
        "os/none/prelude::#extend0::addBootRegions",
        "unsafe (this, const boot: &BootInfo) => void",
    ),
    (
        "os/none/vga::Screen::fromBoot",
        "(static, const b: &BootInfo) => Screen",
    ),
    (
        "os/none/vga::Screen::write",
        "(let this, const s: &string) => void",
    ),
    (
        "os/none/vga::Screen::writeByte",
        "(let this, b: u8) => void",
    ),
    ("os/none/vga::Screen::clear", "(let this) => void"),
    (
        "os/none/vga::Screen::setColor",
        "(let this, fg: u8, bg: u8) => void",
    ),
    ("os/none/vga::emergency", "(const s: &string) => void"),
    ("os/none/serial::init", "(const b: &BootInfo) => void"),
    (
        "os/none/serial::write",
        "(const b: &BootInfo, const s: &string) => void",
    ),
    (
        "os/none/serial::writeByte",
        "(const b: &BootInfo, v: u8) => void",
    ),
    ("os/none/serial::kind", "() => UartKind"),
    ("os/none/idt::init", "() => void"),
    (
        "os/none/idt::set",
        "(vector: u8, h: InterruptHandler) => void",
    ),
    ("os/none/idt::enable", "() => void"),
    ("os/none/idt::disable", "() => void"),
    ("os/none/pic::mask", "(irq: u8) => void"),
    ("os/none/pic::unmask", "(irq: u8) => void"),
    ("os/none/pic::eoi", "(irq: u8) => void"),
    ("os/none/pit::setHz", "(hz: u32) => void"),
    ("os/none/cpu::withoutInterrupts", "(f: () => void) => void"),
    ("os/none/cpu::setStackLimit", "unsafe (addr: usize) => void"),
    ("os/none/cpu::enableSse", "unsafe () => void"),
];

pub fn register(h: &mut Harness) {
    for (target, table) in [("x86_64-linux", HOSTED), ("i386-none", FREESTANDING)] {
        h.case(
            format!("library/signatures and marks are the documented ones on {target}"),
            move || {
                let (rendered, analyzed, tcx, _) = lower(target, ParseMode::Build);
                assert_eq!(rendered, "");
                assert!(analyzed);
                let mut wrong = Vec::new();
                for &(path, expected) in table {
                    let found = spelled(&tcx, def_at(&tcx, path));
                    if found != expected {
                        wrong.push(format!("{path}\n  expected {expected}\n     found {found}"));
                    }
                }
                assert!(wrong.is_empty(), "{}", wrong.join("\n"));
            },
        );
    }
    h.case("library/Result bounds its error type by Error", || {
        let (_, _, tcx, _) = lower("x86_64-linux", ParseMode::Build);
        let result = tcx.lang_adt(LangItem::Result).expect("Result");
        let params = tcx.generics(tcx.adt(result).generics).params.clone();
        let header: Vec<String> = params
            .iter()
            .map(|&p| param_string(&tcx, p, &tcx.param(p).bounds))
            .collect();
        assert_eq!(header, ["T", "E extends Error"], "plan f.1, S:638, S:762");
    });
    h.case(
        "library/every module parses in library mode with no diagnostic",
        || {
            let mut modules = 0;
            for (key, text) in enrang_rtlib::all_modules() {
                let (rendered, _) = parse_lib(key, text);
                assert_eq!(rendered, "", "{key}");
                modules += 1;
            }
            assert!(modules > 40, "{modules} modules");
        },
    );
    h.case("library/every module prints back unchanged", || {
        for (key, text) in enrang_rtlib::all_modules() {
            let (_, printed) = parse_lib(key, text);
            assert_eq!(printed, *text, "{key} is not in the canonical style");
        }
    });
    h.case(
        "library/the cases parse in library mode, not as user files",
        || {
            let text = "public function null<T>(): *T { unreachable(); }\n";
            assert_eq!(parse_lib("core/ptr", text).0, "");
            assert_ne!(parse_as("core/ptr", text, FileOrigin::User).0, "");
        },
    );
    h.case(
        "library/the embedded library lowers with no diagnostic on every target",
        || {
            for target in all_targets() {
                for mode in [ParseMode::Build, ParseMode::Test] {
                    let (rendered, analyzed, _, _) = lower(target, mode);
                    assert_eq!(rendered, "", "{target} {mode:?}");
                    assert!(analyzed, "{target} {mode:?}");
                }
            }
        },
    );
    h.case(
        "library/each lang item of M2 is declared once, in its layer's graph",
        || {
            for target in all_targets() {
                let (_, _, tcx, os_folder) = lower(target, ParseMode::Build);
                let freestanding = os_folder == "os/none" || os_folder == "os/uefi";
                for &item in LangItem::ALL {
                    if item.since() > Milestone::M2 {
                        continue;
                    }
                    let (expected, folder) = match item.layer() {
                        LangLayer::OsNone => (freestanding, os_folder),
                        layer => (true, layer.folder()),
                    };
                    let declaring: Vec<_> = tcx
                        .defs()
                        .filter(|(_, d)| d.attrs.lang == Some(item))
                        .map(|(def, d)| (def, d.path.module.as_str().to_owned()))
                        .collect();
                    if !expected {
                        assert!(declaring.is_empty(), "{target}: {item} in {declaring:?}");
                        continue;
                    }
                    assert_eq!(declaring.len(), 1, "{target}: {item} in {declaring:?}");
                    let (def, module) = &declaring[0];
                    assert_eq!(tcx.lang_opt(item), Some(*def), "{target}: {item}");
                    assert!(
                        module.starts_with(&format!("{folder}/")),
                        "{target}: {item} is in {module}, not {folder}"
                    );
                }
            }
        },
    );
}
