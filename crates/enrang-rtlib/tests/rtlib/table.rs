//! The table `build.rs` generates.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use enrang_rtlib::{OS_LAYERS, all_modules, is_folder, lookup, modules_under, os_root};
use enrang_testkit::{Harness, workspace_root};

/// The keys of every `.en` file under `dir`, read from disk.
fn on_disk(dir: &Path, prefix: &str, out: &mut BTreeSet<String>) {
    for entry in fs::read_dir(dir).expect("lib/ is readable") {
        let path = entry.expect("an entry").path();
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .expect("a name")
            .to_owned();
        if path.is_dir() {
            on_disk(&path, &format!("{prefix}{name}/"), out);
        } else if let Some(stem) = name.strip_suffix(".en") {
            out.insert(format!("{prefix}{stem}"));
        }
    }
}

pub fn register(h: &mut Harness) {
    h.case("table/sorted by key, each key once", || {
        let keys: Vec<&str> = all_modules().iter().map(|(k, _)| *k).collect();
        let mut sorted = keys.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(keys, sorted);
        assert!(!keys.is_empty());
    });
    h.case("table/every file of lib/ and nothing else", || {
        let mut disk = BTreeSet::new();
        on_disk(&workspace_root().join("lib"), "", &mut disk);
        let table: BTreeSet<String> = all_modules().iter().map(|(k, _)| (*k).to_owned()).collect();
        assert_eq!(table, disk);
    });
    h.case("table/the sources are the files' text", || {
        for (key, source) in all_modules() {
            let path = workspace_root().join("lib").join(format!("{key}.en"));
            let text = fs::read_to_string(&path).expect("the file");
            assert_eq!(*source, text, "{key}");
            assert!(!key.ends_with(".en") && !key.contains('\\'), "{key}");
        }
    });
    h.case("table/lookup", || {
        assert!(lookup("core/prelude").is_some());
        assert!(lookup("alloc/array").is_some());
        assert!(lookup("os/linux_x64/fs").is_some());
        assert_eq!(lookup("core"), None, "a folder is no module");
        assert_eq!(lookup("core/nothing"), None);
        assert_eq!(lookup(""), None);
    });
    h.case("table/folders", || {
        for folder in ["core", "alloc", "os", "os/linux_x64", "os/none"] {
            assert!(is_folder(folder), "{folder}");
        }
        for not in ["", "co", "core/mem", "os/linux", "lib"] {
            assert!(!is_folder(not), "{not}");
        }
        let core: Vec<&str> = modules_under("core").map(|(k, _)| k).collect();
        assert!(core.contains(&"core/prelude") && core.iter().all(|k| k.starts_with("core/")));
        assert!(modules_under("os").count() > modules_under("os/vm").count());
    });
    h.case("table/each OS layer has a folder with a prelude", || {
        for (variant, folder) in OS_LAYERS {
            let root = os_root(variant).unwrap_or_else(|| panic!("{variant}"));
            assert_eq!(root, format!("os/{folder}"));
            assert!(is_folder(root), "{root}");
            assert!(
                lookup(&format!("{root}/prelude")).is_some(),
                "{root}/prelude"
            );
        }
        assert_eq!(os_root("Bogus"), None);
    });
    h.case("table/core and alloc have preludes", || {
        for layer in enrang_rtlib::LAYERS {
            assert!(lookup(&format!("{layer}/prelude")).is_some(), "{layer}");
        }
    });
}
