//! The library's layering, read from its text (ARCHITECTURE 10, TESTING 13): each
//! module names its SPEC section, imports point only downward, `asm` stays in
//! `core/port` and `core/cpu`, and each layer declares each lang item once.

use std::collections::{BTreeMap, BTreeSet};

use enrang_rtlib::{OS_LAYERS, all_modules, is_folder, lookup, modules_under};
use enrang_testkit::Harness;

/// The layer of a module key: `core`, `alloc` or `os/<layer>`.
fn layer(key: &str) -> String {
    let mut parts = key.split('/');
    match parts.next() {
        Some("os") => format!("os/{}", parts.next().unwrap_or("")),
        Some(first) => first.to_owned(),
        None => String::new(),
    }
}

/// How low a layer is: `core` below `alloc` below the OS layers.
fn rank(layer: &str) -> usize {
    match layer {
        "core" => 0,
        "alloc" => 1,
        _ => 2,
    }
}

/// The key or folder an import path of module `key` names: relative to the
/// module's folder, or a library path as written.
fn target_of(key: &str, path: &str) -> String {
    if !(path.starts_with("./") || path.starts_with("../")) {
        return path.to_owned();
    }
    let mut parts: Vec<&str> = key.split('/').collect();
    parts.pop();
    for segment in path.split('/') {
        match segment {
            "." => {}
            ".." => {
                parts.pop();
            }
            other => parts.push(other),
        }
    }
    parts.join("/")
}

/// The path of each import of `source`.
fn imports(source: &str) -> Vec<String> {
    source
        .lines()
        .filter(|l| l.starts_with("import ") || l.starts_with("public import "))
        .map(|l| {
            let open = l.find('"').expect("an import path");
            let close = l[open + 1..].find('"').expect("its end") + open + 1;
            l[open + 1..close].to_owned()
        })
        .collect()
}

/// Each `@lang("name")` of `source`.
fn langs(source: &str) -> Vec<String> {
    source
        .match_indices("@lang(\"")
        .map(|(at, m)| {
            let rest = &source[at + m.len()..];
            rest[..rest.find('"').expect("the name's end")].to_owned()
        })
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "layers/every module begins with a comment naming its SPEC section",
        || {
            for (key, source) in all_modules() {
                let first = source.lines().next().unwrap_or("");
                let section = first.strip_prefix("// SPEC ").unwrap_or("");
                assert!(
                    section.starts_with(|c: char| c.is_ascii_digit()),
                    "{key}: {first:?}"
                );
                assert!(first.contains(&format!("`{key}`")), "{key}: {first:?}");
            }
        },
    );
    h.case(
        "layers/imports point only downward, inside one OS layer",
        || {
            let mut seen = 0;
            for (key, source) in all_modules() {
                let from = layer(key);
                for path in imports(source) {
                    seen += 1;
                    let to = target_of(key, &path);
                    assert!(
                        lookup(&to).is_some() || is_folder(&to),
                        "{key}: `{path}` names nothing"
                    );
                    let to_layer = layer(&to);
                    assert!(
                        rank(&to_layer) <= rank(&from),
                        "{key} imports `{path}`, a layer above its own"
                    );
                    if rank(&to_layer) == 2 {
                        assert_eq!(to_layer, from, "{key} imports `{path}`, another OS layer");
                    }
                }
            }
            assert!(seen > 0, "the preludes import their modules");
        },
    );
    h.case("layers/the import checks see an upward import", || {
        assert_eq!(target_of("core/prelude", "./fmt"), "core/fmt");
        assert_eq!(target_of("os/none/vga", "../../alloc/box"), "alloc/box");
        assert!(rank(&layer("alloc/box")) > rank(&layer("core/fmt")));
        assert_eq!(layer("os/vm/fs"), "os/vm");
        assert_eq!(
            imports("public import { Box } from \"./box\";\nimport * as m from \"core/mem\";\n"),
            ["./box", "core/mem"]
        );
    });
    h.case(
        "layers/no asm in core outside core/port and core/cpu",
        || {
            for (key, source) in modules_under("core") {
                if key == "core/port" || key == "core/cpu" {
                    continue;
                }
                for line in source.lines().filter(|l| !l.trim_start().starts_with("//")) {
                    assert!(!line.contains("asm("), "{key}: {line}");
                }
            }
        },
    );
    h.case("layers/each layer declares each lang item once", || {
        let mut by_layer: BTreeMap<String, Vec<(String, &str)>> = BTreeMap::new();
        for (key, source) in all_modules() {
            for name in langs(source) {
                by_layer.entry(layer(key)).or_default().push((name, key));
            }
        }
        for (layer, items) in &by_layer {
            let mut seen = BTreeSet::new();
            for (name, key) in items {
                assert!(seen.insert(name), "{layer}: `{name}` again in {key}");
            }
        }
        let core: BTreeSet<&String> = by_layer["core"].iter().map(|(n, _)| n).collect();
        let alloc: BTreeSet<&String> = by_layer["alloc"].iter().map(|(n, _)| n).collect();
        assert!(core.is_disjoint(&alloc), "{core:?} {alloc:?}");
        for (_, folder) in OS_LAYERS {
            let os: BTreeSet<&String> = by_layer
                .get(&format!("os/{folder}"))
                .map(|items| items.iter().map(|(n, _)| n).collect())
                .unwrap_or_default();
            assert!(os.is_disjoint(&core) && os.is_disjoint(&alloc), "{folder}");
        }
    });
    h.case(
        "layers/the built-in types are lang classes where SPEC 3.1 puts them",
        || {
            for (name, folder, class) in [
                ("string", "core/string", "class string"),
                ("slice", "core/slice", "class Slice<T>"),
                ("array", "alloc", "class Array<T>"),
                ("box", "alloc", "class Box<T>"),
            ] {
                let decl = format!("@lang(\"{name}\") public final {class} {{");
                let found: Vec<&str> = all_modules()
                    .iter()
                    .filter(|(_, s)| s.lines().any(|l| l == decl))
                    .map(|(k, _)| *k)
                    .collect();
                assert_eq!(found.len(), 1, "{decl}: {found:?}");
                assert!(
                    found[0] == folder || found[0].starts_with(&format!("{folder}/")),
                    "{name} is in {}",
                    found[0]
                );
            }
        },
    );
    h.case(
        "layers/the freestanding layers declare the same modules and lang items",
        || {
            let keys = |root: &str| -> BTreeSet<String> {
                modules_under(root)
                    .map(|(k, _)| k[root.len()..].to_owned())
                    .collect()
            };
            assert_eq!(keys("os/none"), keys("os/uefi"));
            let hosted = ["os/linux_x64", "os/linux_i386", "os/windows", "os/vm"];
            for root in hosted {
                assert_eq!(keys(root), keys(hosted[0]), "{root}");
            }
            let lang_set = |root: &str| -> BTreeSet<String> {
                modules_under(root).flat_map(|(_, s)| langs(s)).collect()
            };
            assert_eq!(lang_set("os/none"), lang_set("os/uefi"));
            for root in hosted {
                assert!(lang_set(root).is_empty(), "{root}");
            }
        },
    );
}
