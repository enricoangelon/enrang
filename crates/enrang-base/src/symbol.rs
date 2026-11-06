//! Interned strings. The interner is global, and interned text lives for the
//! rest of the process.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Mutex, MutexGuard, PoisonError};

/// An interned string: equal strings give equal symbols within a process.
///
/// Ids depend on interning order, which differs between sessions and threads,
/// so nothing observable exposes them. `Ord` compares the text and `Debug`
/// prints it, which keeps a `BTreeMap<Symbol, _>` deterministic.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Symbol(u32);

struct Interner {
    ids: BTreeMap<&'static str, u32>,
    strings: Vec<&'static str>,
}

static INTERNER: Mutex<Interner> = Mutex::new(Interner {
    ids: BTreeMap::new(),
    strings: Vec::new(),
});

/// Each critical section leaves the tables consistent, so a panic elsewhere on
/// a thread holding the lock cannot have damaged them.
fn interner() -> MutexGuard<'static, Interner> {
    INTERNER.lock().unwrap_or_else(PoisonError::into_inner)
}

pub fn intern(s: &str) -> Symbol {
    let mut table = interner();
    if let Some(&id) = table.ids.get(s) {
        return Symbol(id);
    }
    let id = u32::try_from(table.strings.len()).expect("interner exceeds u32 entries");
    let text: &'static str = String::from(s).leak();
    table.strings.push(text);
    table.ids.insert(text, id);
    Symbol(id)
}

impl Symbol {
    pub fn as_str(self) -> &'static str {
        interner().strings[self.0 as usize]
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad(self.as_str())
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({:?})", self.as_str())
    }
}
