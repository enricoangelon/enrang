//! Scratch directories for tests, under the system temporary directory.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};

/// A fresh directory, removed with everything in it when dropped.
#[derive(Debug)]
pub struct TempDir(PathBuf);

impl TempDir {
    /// # Panics
    ///
    /// If the directory cannot be created, since the test cannot then run.
    pub fn new(label: &str) -> TempDir {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT.fetch_add(1, Ordering::Relaxed);
        let path =
            env::temp_dir().join(format!("enrang-testkit-{label}-{}-{unique}", process::id()));
        fs::create_dir_all(&path)
            .unwrap_or_else(|error| panic!("cannot create a temporary directory: {error}"));
        TempDir(path)
    }

    pub fn path(&self) -> &Path {
        &self.0
    }

    /// `relative` under this directory.
    pub fn join(&self, relative: &str) -> PathBuf {
        self.0.join(relative)
    }

    /// Writes a file under this directory, creating its parents.
    ///
    /// # Panics
    ///
    /// If the file cannot be written.
    pub fn write(&self, relative: &str, contents: &str) -> PathBuf {
        let path = self.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .unwrap_or_else(|error| panic!("cannot create {relative}'s parent: {error}"));
        }
        fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("cannot write {relative}: {error}"));
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
