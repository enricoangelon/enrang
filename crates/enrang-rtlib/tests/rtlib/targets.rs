//! The per-target module map against `enrang-target` and ARCHITECTURE 2.7 and
//! 10. This crate may not depend on `enrang-target` (ARCHITECTURE 1), so the
//! cases read its source: the target list, and each preset's OS layer.

use std::collections::BTreeSet;

use enrang_rtlib::{LAYERS, OS_LAYERS, is_folder, lookup, os_root};
use enrang_testkit::Harness;

use crate::support::{read, section, spans};

/// The variants of `enum OsLayer` in `text`, between `enum OsLayer {` and `}`.
fn os_layer_variants(text: &str) -> BTreeSet<String> {
    let start = text.find("enum OsLayer {").expect("enum OsLayer") + "enum OsLayer {".len();
    let end = text[start..].find('}').expect("its end") + start;
    text[start..end]
        .split([',', '\n'])
        .map(str::trim)
        .filter(|v| !v.is_empty() && !v.starts_with("//"))
        .map(str::to_owned)
        .collect()
}

/// Every target of `enrang-target`, with the `OsLayer` variant its preset names.
fn targets() -> Vec<(String, String)> {
    let resolve = read("crates/enrang-target/src/resolve.rs");
    let start = resolve
        .find("const TARGETS: &[&str] = &[")
        .expect("the target list");
    let end = resolve[start..].find("];").expect("its end") + start;
    let names: Vec<String> = resolve[start..end]
        .split('"')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect();
    let presets = read("crates/enrang-target/src/presets.rs");
    names
        .into_iter()
        .map(|name| {
            let arm = format!("\"{name}\" =>");
            let at = presets
                .find(&arm)
                .unwrap_or_else(|| panic!("no preset arm for {name}"))
                + arm.len();
            let next_arm = presets[at..]
                .find("\" =>")
                .map_or(presets.len(), |i| i + at);
            let layer = presets[at..next_arm]
                .find("OsLayer::")
                .map(|i| i + at + "OsLayer::".len())
                .unwrap_or_else(|| panic!("the preset of {name} names no OsLayer"));
            let variant: String = presets[layer..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect();
            (name, variant)
        })
        .collect()
}

/// ARCHITECTURE 10's "Per target" table: each row's first cell and the library
/// folders of its second.
fn per_target_rows() -> Vec<(String, Vec<String>)> {
    let arch = read("docs/ARCHITECTURE.md");
    let runtime = section(&arch, "## 10. ");
    let table = &runtime[runtime.find("**Per target.**").expect("the table")..];
    table
        .lines()
        .skip_while(|l| !l.starts_with('|'))
        .take_while(|l| l.starts_with('|'))
        .skip(2)
        .map(|row| {
            let cells: Vec<&str> = row.split('|').map(str::trim).collect();
            let folders = spans(cells[2])
                .into_iter()
                .flat_map(|s| s.text.split(' ').map(str::to_owned).collect::<Vec<_>>())
                .filter(|w| ["core", "alloc", "os"].contains(&w.split('/').next().unwrap_or("")))
                .collect();
            (cells[1].to_owned(), folders)
        })
        .collect()
}

pub fn register(h: &mut Harness) {
    h.case(
        "targets/every target of enrang-target has its OS layer's folder",
        || {
            let targets = targets();
            assert!(targets.len() >= 7, "{targets:?}");
            for (name, variant) in &targets {
                let root =
                    os_root(variant).unwrap_or_else(|| panic!("{name}: no folder for {variant}"));
                assert!(is_folder(root), "{name}: {root}");
                assert!(
                    lookup(&format!("{root}/prelude")).is_some(),
                    "{name}: {root}/prelude"
                );
            }
            let names: BTreeSet<&str> = targets.iter().map(|(n, _)| n.as_str()).collect();
            for expected in ["x86_64-linux", "i386-none", "vm32"] {
                assert!(names.contains(expected), "{names:?}");
            }
        },
    );
    h.case(
        "targets/the map's OS layers are enrang-target's and ARCHITECTURE 2.7's",
        || {
            let ours: BTreeSet<String> = OS_LAYERS.iter().map(|(v, _)| (*v).to_owned()).collect();
            let crate_enum = os_layer_variants(&read("crates/enrang-target/src/spec.rs"));
            let arch = read("docs/ARCHITECTURE.md");
            let doc_enum = os_layer_variants(section(&arch, "### 2.7 "));
            assert_eq!(ours, crate_enum);
            assert_eq!(ours, doc_enum);
            let folders: BTreeSet<&str> = OS_LAYERS.iter().map(|(_, f)| *f).collect();
            assert_eq!(folders.len(), OS_LAYERS.len(), "one folder per layer");
        },
    );
    h.case(
        "targets/each target's library is ARCHITECTURE 10's row",
        || {
            let rows = per_target_rows();
            assert!(rows.len() >= 6, "{rows:?}");
            for (name, variant) in targets() {
                let row = rows
                    .iter()
                    .find(|(first, _)| first.contains(&format!("`{name}`")))
                    .or_else(|| {
                        (variant == "Vm")
                            .then(|| rows.iter().find(|(first, _)| first == "VM"))
                            .flatten()
                    })
                    .unwrap_or_else(|| panic!("ARCHITECTURE 10 has no row for {name}"));
                let os: Vec<&String> = row.1.iter().filter(|f| f.starts_with("os/")).collect();
                assert_eq!(os.len(), 1, "{name}: {:?}", row.1);
                assert_eq!(Some(os[0].as_str()), os_root(&variant), "{name}");
                assert!(row.1.iter().any(|f| f == "core"), "{name}: {:?}", row.1);
                for folder in &row.1 {
                    assert!(is_folder(folder), "{name}: {folder}");
                    assert!(
                        folder.starts_with("os/") || LAYERS.contains(&folder.as_str()),
                        "{name}: {folder}"
                    );
                }
            }
            let uefi = rows
                .iter()
                .find(|(first, _)| first == "UEFI")
                .expect("the UEFI row");
            assert!(
                uefi.1.iter().any(|f| Some(f.as_str()) == os_root("Uefi")),
                "{uefi:?}"
            );
        },
    );
}
