//! The diagnostic model (ARCHITECTURE 2.2).

use std::fmt;

use enrang_base::{BytePos, Span};

use crate::codes::Code;

/// How serious a diagnostic is. `Fail` is a test verdict, rendered `fail[T0001]`.
/// `Note` reports something true about a command that is correct, such as the level
/// a `--cpu` alias resolves to (SPEC 10.1): it renders with no code, fails nothing,
/// and no count mentions it.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Severity {
    Error,
    Warning,
    Fail,
    Note,
}

impl Severity {
    /// The word that opens a rendered diagnostic.
    pub fn name(self) -> &'static str {
        match self {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Fail => "fail",
            Severity::Note => "note",
        }
    }

    /// Whether a diagnostic of this severity fails its phase and the run.
    pub fn fails(self) -> bool {
        matches!(self, Severity::Error | Severity::Fail)
    }
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A span and what to say about it. Text may be empty.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Label {
    pub span: Span,
    pub text: String,
}

/// The kinds of `= ...` entry under a snippet.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum EntryKind {
    Note,
    Why,
    Rule,
    FromTypeScript,
}

impl EntryKind {
    /// The word between `=` and `:` when rendered.
    pub fn name(self) -> &'static str {
        match self {
            EntryKind::Note => "note",
            EntryKind::Why => "why",
            EntryKind::Rule => "rule",
            EntryKind::FromTypeScript => "from TypeScript",
        }
    }
}

/// Free text under the snippet. Line breaks in it become continuation lines.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Entry {
    pub kind: EntryKind,
    pub text: String,
}

/// How far a fix-it can be trusted.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Applicability {
    /// Applying it needs no human: the result compiles and means what was meant.
    MachineApplicable,
    MaybeIncorrect,
    /// The text has parts a human must fill in.
    HasPlaceholders,
}

impl Applicability {
    /// The spelling in JSON output.
    pub fn name(self) -> &'static str {
        match self {
            Applicability::MachineApplicable => "machine-applicable",
            Applicability::MaybeIncorrect => "maybe-incorrect",
            Applicability::HasPlaceholders => "has-placeholders",
        }
    }
}

/// Replaces `span` with `replacement`. A zero-width span is an insertion.
///
/// A `DUMMY` span means the edit changes no source and `replacement` is a command
/// to show as it is, as in the `enrang test -t` help of TESTING 9. [`apply_fixes`]
/// refuses such an edit.
///
/// [`apply_fixes`]: crate::apply_fixes
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Edit {
    pub span: Span,
    pub replacement: String,
}

impl Edit {
    pub fn insert(at: BytePos, text: impl Into<String>) -> Edit {
        Edit {
            span: Span { lo: at, hi: at },
            replacement: text.into(),
        }
    }

    pub fn replace(span: Span, text: impl Into<String>) -> Edit {
        Edit {
            span,
            replacement: text.into(),
        }
    }

    pub fn delete(span: Span) -> Edit {
        Edit::replace(span, "")
    }

    /// A command for the reader to run, with no source location.
    pub fn command(text: impl Into<String>) -> Edit {
        Edit::replace(Span::DUMMY, text)
    }
}

/// A `help:` block. With no edits it is the single line of its message.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Help {
    pub message: String,
    pub edits: Vec<Edit>,
    pub applicability: Applicability,
}

impl Help {
    /// A help with no code.
    pub fn text(message: impl Into<String>) -> Help {
        Help::suggest(message, Vec::new())
    }

    /// A help whose edits can be applied without a human.
    pub fn machine(message: impl Into<String>, edits: Vec<Edit>) -> Help {
        Help {
            message: message.into(),
            edits,
            applicability: Applicability::MachineApplicable,
        }
    }

    /// A help whose edits a human should check.
    pub fn suggest(message: impl Into<String>, edits: Vec<Edit>) -> Help {
        Help {
            message: message.into(),
            edits,
            applicability: Applicability::MaybeIncorrect,
        }
    }
}

/// One finding. A `DUMMY` primary span means it has no place in any source, as
/// for a command-line error: it renders with no location line and no snippet.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: Code,
    pub message: String,
    pub primary: Label,
    pub secondary: Vec<Label>,
    pub entries: Vec<Entry>,
    pub helps: Vec<Help>,
}

impl Diagnostic {
    /// A diagnostic with the severity its registry row gives.
    pub fn new(
        code: Code,
        message: impl Into<String>,
        span: Span,
        label: impl Into<String>,
    ) -> Diagnostic {
        Diagnostic {
            severity: code.severity(),
            code,
            message: message.into(),
            primary: Label {
                span,
                text: label.into(),
            },
            secondary: Vec::new(),
            entries: Vec::new(),
            helps: Vec::new(),
        }
    }

    /// A diagnostic with no place in any source.
    pub fn spanless(code: Code, message: impl Into<String>) -> Diagnostic {
        Diagnostic::new(code, message, Span::DUMMY, "")
    }

    /// A note with no place in any source. `code` says what it is about and is not
    /// shown: it names a rejection, which this is not.
    pub fn bare_note(code: Code, message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            severity: Severity::Note,
            ..Diagnostic::spanless(code, message)
        }
    }

    pub fn with_secondary(mut self, span: Span, text: impl Into<String>) -> Diagnostic {
        self.secondary.push(Label {
            span,
            text: text.into(),
        });
        self
    }

    pub fn with_entry(mut self, kind: EntryKind, text: impl Into<String>) -> Diagnostic {
        self.entries.push(Entry {
            kind,
            text: text.into(),
        });
        self
    }

    pub fn note(self, text: impl Into<String>) -> Diagnostic {
        self.with_entry(EntryKind::Note, text)
    }

    pub fn why(self, text: impl Into<String>) -> Diagnostic {
        self.with_entry(EntryKind::Why, text)
    }

    pub fn rule(self, text: impl Into<String>) -> Diagnostic {
        self.with_entry(EntryKind::Rule, text)
    }

    pub fn from_typescript(self, text: impl Into<String>) -> Diagnostic {
        self.with_entry(EntryKind::FromTypeScript, text)
    }

    pub fn with_help(mut self, help: Help) -> Diagnostic {
        self.helps.push(help);
        self
    }

    /// The command of the `= explain` line, which SPEC 13.1 gives errors. A test
    /// verdict has one too (TESTING 9), and a warning or a note does not.
    pub(crate) fn explain_command(&self) -> Option<String> {
        self.severity
            .fails()
            .then(|| format!("enrang explain {}", self.code))
    }
}
