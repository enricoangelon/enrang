//! Stable item paths (ARCHITECTURE 2.4's freeze list, 6.8): "the module path, the
//! item, the member, and for an overload its parameter types".
//!
//! Ids follow load and interning order, so everything that reaches output or an
//! interface file is ordered by these paths instead (ARCHITECTURE 1).

use std::fmt;

use enrang_base::{Symbol, intern};

/// A module's path: a user module's file path relative to the entry's directory,
/// normalised and without `.en` (`src/main`, `util`), or a library module's
/// `enrang-rtlib` key (`core/mem`, `os/linux_x64/fs`). A user path that would read
/// as a library key is spelled as an import from the entry's directory writes it
/// (`./core/mem`), so the two never meet. It orders by its text.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ModulePath(pub Symbol);

impl ModulePath {
    pub fn new(path: &str) -> ModulePath {
        ModulePath(intern(path))
    }

    pub fn as_str(self) -> &'static str {
        self.0.as_str()
    }

    /// Whether the module is part of the embedded library (`core`, `alloc`, `os`).
    pub fn is_library(self) -> bool {
        let text = self.as_str();
        ["core", "alloc", "os"]
            .iter()
            .any(|root| text == *root || text.starts_with(&format!("{root}/")))
    }
}

impl fmt::Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The segment of a class's constructor in an [`ItemPath`].
pub const CTOR_SEGMENT: &str = "#ctor";
/// The segment of a class's destructor in an [`ItemPath`].
pub const DTOR_SEGMENT: &str = "#dtor";

/// A definition's stable path. `segments` holds the item, then the member
/// (`Animal`, `speak`); a constructor is `#ctor`, a destructor `#dtor`, the n-th
/// `extend` block of a module `#extend<n>`, the n-th test item `#test<n>`, the n-th
/// static `assert` `#assert<n>`, each counted from 0 in source order. `overload`
/// holds the parameter types as `Tcx::ty_path_string` spells them, every class,
/// enum and interface by its own path (`&src/b::Node`), set when the name has more
/// than one overload.
///
/// `Ord` compares the module, then the segments, then the overload: every list
/// that reaches output or an interface file is sorted by it.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ItemPath {
    pub module: ModulePath,
    pub segments: Vec<Symbol>,
    pub overload: Option<Vec<String>>,
}

impl ItemPath {
    /// The path of a module itself: no segment.
    pub fn module(module: ModulePath) -> ItemPath {
        ItemPath {
            module,
            segments: Vec::new(),
            overload: None,
        }
    }

    /// An item of `module`.
    pub fn item(module: ModulePath, name: Symbol) -> ItemPath {
        ItemPath {
            module,
            segments: vec![name],
            overload: None,
        }
    }

    /// This path with one more segment: a member of this item.
    pub fn child(&self, name: Symbol) -> ItemPath {
        let mut segments = self.segments.clone();
        segments.push(name);
        ItemPath {
            module: self.module,
            segments,
            overload: None,
        }
    }

    /// This path naming one overload by its parameter types.
    pub fn with_overload(mut self, params: Vec<String>) -> ItemPath {
        self.overload = Some(params);
        self
    }

    /// The `#extend<n>` segment.
    pub fn extend_segment(n: usize) -> Symbol {
        intern(&format!("#extend{n}"))
    }

    /// The `#test<n>` segment.
    pub fn test_segment(n: usize) -> Symbol {
        intern(&format!("#test{n}"))
    }

    /// The `#assert<n>` segment.
    pub fn assert_segment(n: usize) -> Symbol {
        intern(&format!("#assert{n}"))
    }

    /// The last segment, the definition's own name; `None` for a module.
    pub fn name(&self) -> Option<Symbol> {
        self.segments.last().copied()
    }
}

/// `src/main::Animal::speak`, and `(i64, &src/b::Node)` after an overload's path.
impl fmt::Display for ItemPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.module)?;
        for segment in &self.segments {
            write!(f, "::{segment}")?;
        }
        if let Some(params) = &self.overload {
            write!(f, "({})", params.join(", "))?;
        }
        Ok(())
    }
}
