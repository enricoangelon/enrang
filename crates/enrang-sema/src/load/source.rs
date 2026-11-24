//! Where a module's text comes from: the input's overrides first, then files under
//! its directory; library keys through the embedded table or a test's map.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use enrang_syntax::decode_source;

use super::paths::normalize;
use crate::{LibSource, ProgramInput};

/// A user file's text, with the places of invalid UTF-8 (EN0001) when it was read
/// from disk.
pub(crate) struct UserText {
    pub text: Arc<str>,
    pub invalid: Vec<u32>,
}

/// One entry of a folder: a module file (`x.en`, named `x`) or a sub-folder.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Child {
    File(String),
    Folder(String),
}

pub(crate) struct SourceProvider<'i> {
    input: &'i ProgramInput,
    /// The input's overrides under their normalised paths, the form every user
    /// path the loader asks for has.
    overrides: BTreeMap<PathBuf, Arc<str>>,
}

impl<'i> SourceProvider<'i> {
    pub fn new(input: &'i ProgramInput) -> SourceProvider<'i> {
        let overrides = input
            .overrides
            .iter()
            .map(|(path, text)| (normalize(path), Arc::clone(text)))
            .collect();
        SourceProvider { input, overrides }
    }

    /// A user path (normalised, `/`-separated, without `.en`) that leaves the
    /// input's directory and comes back into it, as `../app/main` read from
    /// `app/`, spelled from inside it (`main`, or `.` for the directory itself),
    /// so one file is one module whichever way it is reached (plan d.2, G31).
    pub fn reenter(&self, rel: &str) -> String {
        if !rel.starts_with("..") {
            return rel.to_owned();
        }
        let Ok(dir) = std::path::absolute(&self.input.dir) else {
            return rel.to_owned();
        };
        let dir = normalize(&dir);
        let full = normalize(&dir.join(rel));
        match full.strip_prefix(&dir) {
            Ok(inside) => {
                let parts: Vec<String> = inside
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect();
                if parts.is_empty() {
                    ".".to_owned()
                } else {
                    parts.join("/")
                }
            }
            Err(_) => rel.to_owned(),
        }
    }

    pub fn read_user(&self, rel: &Path) -> io::Result<UserText> {
        if let Some(text) = self.overrides.get(rel) {
            return Ok(UserText {
                text: Arc::clone(text),
                invalid: Vec::new(),
            });
        }
        let bytes = fs::read(self.input.dir.join(rel))?;
        let decoded = decode_source(&bytes);
        Ok(UserText {
            text: Arc::from(decoded.text),
            invalid: decoded.invalid,
        })
    }

    pub fn user_exists(&self, rel: &Path) -> bool {
        self.overrides.contains_key(rel) || self.input.dir.join(rel).is_file()
    }

    pub fn user_is_dir(&self, rel: &Path) -> bool {
        self.overrides
            .keys()
            .any(|key| key.starts_with(rel) && key != rel)
            || self.input.dir.join(rel).is_dir()
    }

    /// The module files (`.en`, not `.test.en`) and sub-folders directly inside the
    /// user folder `rel`, from the overrides and the disk, sorted by name.
    pub fn user_children(&self, rel: &Path) -> Vec<Child> {
        let mut out = BTreeSet::new();
        for key in self.overrides.keys() {
            let Ok(rest) = key.strip_prefix(rel) else {
                continue;
            };
            let parts: Vec<String> = rest
                .components()
                .filter_map(|c| match c {
                    Component::Normal(s) => Some(s.to_string_lossy().into_owned()),
                    _ => None,
                })
                .collect();
            match parts.as_slice() {
                [] => {}
                [file] => {
                    if let Some(child) = module_child(file) {
                        out.insert(child);
                    }
                }
                [folder, ..] => {
                    out.insert(Child::Folder(folder.clone()));
                }
            }
        }
        if let Ok(entries) = fs::read_dir(self.input.dir.join(rel)) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                // A linked folder is not followed, so a link back up cannot loop.
                if entry.file_type().is_ok_and(|t| t.is_dir()) {
                    out.insert(Child::Folder(name));
                } else if entry.path().is_file()
                    && let Some(child) = module_child(&name)
                {
                    out.insert(child);
                }
            }
        }
        out.into_iter().collect()
    }

    pub fn lib(&self, key: &str) -> Option<Arc<str>> {
        match &self.input.lib {
            LibSource::Embedded => enrang_rtlib::lookup(key).map(Arc::from),
            LibSource::Fake(map) => map.get(key).cloned(),
        }
    }

    pub fn lib_is_folder(&self, key: &str) -> bool {
        match &self.input.lib {
            LibSource::Embedded => enrang_rtlib::is_folder(key),
            LibSource::Fake(map) => map.keys().any(|k| {
                k.strip_prefix(key)
                    .is_some_and(|rest| rest.starts_with('/'))
            }),
        }
    }

    /// The modules and sub-folders directly inside the library folder `key`.
    pub fn lib_children(&self, key: &str) -> Vec<Child> {
        let prefix = format!("{key}/");
        let mut out = BTreeSet::new();
        for k in self.lib_keys() {
            let Some(rest) = k.strip_prefix(&prefix) else {
                continue;
            };
            match rest.split_once('/') {
                Some((folder, _)) => out.insert(Child::Folder(folder.to_owned())),
                None => out.insert(Child::File(rest.to_owned())),
            };
        }
        out.into_iter().collect()
    }

    /// Every library key, sorted.
    pub fn lib_keys(&self) -> Vec<String> {
        match &self.input.lib {
            LibSource::Embedded => enrang_rtlib::all_modules()
                .iter()
                .map(|(key, _)| (*key).to_owned())
                .collect(),
            LibSource::Fake(map) => map.keys().cloned().collect(),
        }
    }
}

/// `x.en` is the module `x`; a `.test.en` part is no module of its own.
fn module_child(file: &str) -> Option<Child> {
    let stem = file.strip_suffix(".en")?;
    if stem.is_empty() || stem.ends_with(".test") {
        return None;
    }
    Some(Child::File(stem.to_owned()))
}
