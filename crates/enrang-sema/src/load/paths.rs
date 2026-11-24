//! Import paths (SPEC 3.1, 4.12): `./x` and `../x` relative to the importing file,
//! extension omitted; `core`, `alloc`, `os` and paths below them name library
//! modules or folders, `os` being the target's layer (`os/fs` is
//! `os/linux_x64/fs`).
//!
//! A user path is normalised before anything reads it (`.` dropped, `..` taken back
//! lexically, a leading `..` kept), so no module path depends on how the entry was
//! spelled. A user module's path is that relative path; when it reads as a library
//! key (a folder named `core`, `alloc` or `os` in the input's directory), it is
//! spelled as an import from that directory writes it, `./core/prelude`, so user and
//! library modules never share a path, and everything keyed or ordered by paths
//! keeps them apart (plan choice; the docs are silent).

use std::path::{Component, Path, PathBuf};

use enrang_hir::ModulePath;
use enrang_target::OsLayer;

/// What an import path names, before the file system is asked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Spec {
    /// A library key (`core/mem`) or folder (`core`).
    Library(String),
    /// A user path relative to the input's directory, without `.en`.
    User(String),
    /// Nothing an import may name: a bare word, or a relative path that leaves the
    /// library from inside it.
    Invalid,
}

/// The library folder of an OS layer (`enrang-rtlib`'s `os_root`).
pub(crate) fn os_folder(os: OsLayer) -> &'static str {
    let variant = match os {
        OsLayer::LinuxX64 => "LinuxX64",
        OsLayer::LinuxInt80 => "LinuxInt80",
        OsLayer::Win64Imports => "Win64Imports",
        OsLayer::None => "None",
        OsLayer::Uefi => "Uefi",
        OsLayer::Vm => "Vm",
    };
    enrang_rtlib::os_root(variant).expect("every OS layer has a library folder")
}

/// Classifies `spec` as written in the module whose user path or library key is
/// `from`.
pub(crate) fn classify(spec: &str, from: &str, library: bool, os: &str) -> Spec {
    if spec.starts_with("./") || spec.starts_with("../") {
        let base = match from.rsplit_once('/') {
            Some((dir, _)) => dir,
            None => "",
        };
        let Some(joined) = join(base, spec) else {
            return Spec::Invalid;
        };
        if library {
            return if ModulePath::new(&joined).is_library() {
                Spec::Library(joined)
            } else {
                Spec::Invalid
            };
        }
        return Spec::User(joined);
    }
    if spec == "os" {
        return Spec::Library(os.to_owned());
    }
    if let Some(rest) = spec.strip_prefix("os/") {
        return Spec::Library(format!("{os}/{rest}"));
    }
    if ModulePath::new(spec).is_library() {
        return Spec::Library(spec.to_owned());
    }
    Spec::Invalid
}

/// `rel` (`./x`, `../y/z`) joined to the folder `base`, `.` and `..` resolved; a
/// `..` above the root is kept, since a user path may lead out of the directory.
/// An absolute `base` (an entry given by an absolute path, `/tmp/x`) keeps its
/// leading `/`, so the import is read beside the importing file.
fn join(base: &str, rel: &str) -> Option<String> {
    let root = if base.starts_with('/') { "/" } else { "" };
    let mut parts: Vec<&str> = base
        .split('/')
        .filter(|p| !p.is_empty() && *p != ".")
        .collect();
    for segment in rel.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                if parts.last().is_some_and(|p| *p != "..") {
                    parts.pop();
                } else {
                    parts.push("..");
                }
            }
            name => parts.push(name),
        }
    }
    (!parts.is_empty()).then(|| format!("{root}{}", parts.join("/")))
}

/// `path` with `.` dropped and each `..` taking back the folder before it; a `..`
/// with nothing before it to take back is kept.
pub(crate) fn normalize(path: &Path) -> PathBuf {
    let mut out: Vec<Component> = Vec::new();
    for c in path.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => match out.last() {
                Some(Component::Normal(_)) => {
                    out.pop();
                }
                _ => out.push(c),
            },
            _ => out.push(c),
        }
    }
    out.iter().collect()
}

/// A user file's path relative to the input's directory, normalised, with `/`
/// separators and without `.en`; an absolute path (an entry given that way) keeps
/// its root as a leading `/`.
pub(crate) fn rel_of(file: &Path) -> String {
    let normal = normalize(file);
    let text: Vec<String> = normal
        .components()
        .filter(|c| matches!(c, Component::Normal(_) | Component::ParentDir))
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    let root = if normal.has_root() { "/" } else { "" };
    let joined = format!("{root}{}", text.join("/"));
    joined.strip_suffix(".en").unwrap_or(&joined).to_owned()
}

/// The module path of the user file or folder at `rel` (normalised, without
/// `.en`): `rel` itself, or `./rel` when `rel` reads as a library key.
pub(crate) fn user_module(rel: &str) -> ModulePath {
    if ModulePath::new(rel).is_library() {
        ModulePath::new(&format!("./{rel}"))
    } else {
        ModulePath::new(rel)
    }
}

/// The relative path of a user module's file or folder: [`user_module`] undone.
pub(crate) fn user_rel(path: ModulePath) -> &'static str {
    let text = path.as_str();
    text.strip_prefix("./").unwrap_or(text)
}

/// The `.test.en` part of a module's file, as the driver names it.
pub(crate) fn test_part_of(path: &Path) -> Option<PathBuf> {
    let name = path.file_name()?.to_str()?;
    let stem = name.strip_suffix(".en")?;
    if stem.is_empty() || stem.ends_with(".test") {
        return None;
    }
    Some(path.with_file_name(format!("{stem}.test.en")))
}
