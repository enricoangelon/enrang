//! The embedded runtime library (ARCHITECTURE 1, 10): the `include_str!` table of
//! `lib/` and the per-target module map.
//!
//! `build.rs` walks `lib/` and generates [`all_modules`], so the binary needs no
//! file at run time. A module's key is its path under `lib/` without `.en`
//! (`core/mem`, `os/linux_x64/fs`). `os` is selected by the target's OS layer
//! ([`os_root`]). `ENRANG_LIB_DIR` (ARCHITECTURE 10) is left to M4, when library
//! bodies are developed (plan choice).
//!
//! This crate depends on nothing (ARCHITECTURE 1's graph), so it cannot name
//! `enrang_target::OsLayer`: [`os_root`] takes the layer's name as `enrang-target`
//! spells the variant (plan doc gap G1; ARCHITECTURE 3 writes `os_root(os:
//! OsLayer)`).

#![forbid(unsafe_code)]

mod table {
    include!(concat!(env!("OUT_DIR"), "/lib_table.rs"));
}

/// The library folders a program's modules come from, below the OS layer's.
pub const LAYERS: [&str; 2] = ["core", "alloc"];

/// Each OS layer, `(enrang-target's OsLayer variant, folder under lib/os)`.
pub const OS_LAYERS: [(&str, &str); 6] = [
    ("LinuxX64", "linux_x64"),
    ("LinuxInt80", "linux_i386"),
    ("Win64Imports", "windows"),
    ("Vm", "vm"),
    ("None", "none"),
    ("Uefi", "uefi"),
];

/// Every library module, `(key, source)`, sorted by key.
pub fn all_modules() -> &'static [(&'static str, &'static str)] {
    table::MODULES
}

/// The source of the module `path` (`"core/mem"`, `"os/linux_x64/start"`).
pub fn lookup(path: &str) -> Option<&'static str> {
    let modules = all_modules();
    modules
        .binary_search_by(|(key, _)| (*key).cmp(path))
        .ok()
        .map(|i| modules[i].1)
}

/// The folder of an OS layer (`"os/linux_x64"`), from the name of its `OsLayer`
/// variant (`"LinuxX64"`).
pub fn os_root(layer: &str) -> Option<&'static str> {
    const ROOTS: [&str; 6] = [
        "os/linux_x64",
        "os/linux_i386",
        "os/windows",
        "os/vm",
        "os/none",
        "os/uefi",
    ];
    OS_LAYERS
        .iter()
        .position(|(variant, _)| *variant == layer)
        .map(|i| ROOTS[i])
}

/// Whether `path` names a library folder, a key prefix such as `core` or
/// `os/linux_x64`.
pub fn is_folder(path: &str) -> bool {
    !path.is_empty() && all_modules().iter().any(|(key, _)| is_below(key, path))
}

/// The modules under folder `path`, at any depth, in key order.
pub fn modules_under(path: &str) -> impl Iterator<Item = (&'static str, &'static str)> + '_ {
    all_modules()
        .iter()
        .copied()
        .filter(move |(key, _)| is_below(key, path))
}

fn is_below(key: &str, folder: &str) -> bool {
    key.strip_prefix(folder)
        .is_some_and(|rest| rest.starts_with('/'))
}
