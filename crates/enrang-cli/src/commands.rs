//! The names the command line knows (ARCHITECTURE 11, SPEC 13.2 and 16).

use enrang_diag::Milestone;

/// A command that works at this milestone.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Working {
    pub name: &'static str,
    /// As `--help` and ARCHITECTURE 11 write it, without the leading `enrang`.
    pub usage: &'static str,
    pub summary: &'static str,
}

pub(crate) const EXPLAIN: Working = Working {
    name: "explain",
    usage: "explain <code>",
    summary: "Print the page of a diagnostic code, or its title until the page arrives",
};

pub(crate) const TARGETS: Working = Working {
    name: "targets",
    usage: "targets [--evidence]",
    summary: "List targets, CPU levels and aliases; --evidence prints the support table",
};

/// Every command that works, in the order `--help` shows them.
pub const WORKING: &[Working] = &[EXPLAIN, TARGETS];

/// A command a later milestone delivers.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct LaterCommand {
    pub name: &'static str,
    /// As `--help` and ARCHITECTURE 11 write it, without the leading `enrang`.
    pub usage: &'static str,
    /// The first milestone that delivers any of it.
    pub since: Milestone,
    /// What arrives when, for the reader of the diagnostic and of `--help`.
    pub delivers: &'static str,
}

/// Every such command, in the order of the table in ARCHITECTURE 11.
pub const LATER: &[LaterCommand] = &[
    LaterCommand {
        name: "build",
        usage: "build [file]",
        since: Milestone::M5,
        delivers: "M5 builds native output",
    },
    LaterCommand {
        name: "run",
        usage: "run [file] [-- args]",
        since: Milestone::M4,
        delivers: "M4 runs programs in the VM with `--vm`, and M5 runs them natively",
    },
    LaterCommand {
        name: "dev",
        usage: "dev <file>",
        since: Milestone::M6,
        delivers: "M6 delivers the dev session with hot reload",
    },
    LaterCommand {
        name: "test",
        usage: "test [paths]",
        since: Milestone::M4,
        delivers: "M4 runs tests in the VM, and M5 runs them natively",
    },
    LaterCommand {
        name: "check",
        usage: "check [file]",
        since: Milestone::M1,
        delivers: "M1 checks syntax, M2 adds types and M3 adds borrows",
    },
    LaterCommand {
        name: "init",
        usage: "init [name] [--kernel]",
        since: Milestone::M1,
        delivers: "M1 creates a project, and M9 adds `--kernel`",
    },
];

/// The commands outside the prototype, in the order SPEC 13.2 lists them. EN1301.
pub const DEFERRED: &[&str] = &[
    "install", "add", "publish", "doc", "lsp", "repl", "bench", "debug", "upgrade", "fmt",
];

/// A name from another toolchain, pointed at its counterpart. EN1302.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Alias {
    pub name: &'static str,
    /// The `enrang` command it points to.
    pub target: &'static str,
}

/// Every alias, in the order SPEC 13.2 lists them.
pub const ALIASES: &[Alias] = &[
    Alias {
        name: "tsc",
        target: "check",
    },
    Alias {
        name: "lint",
        target: "check",
    },
    Alias {
        name: "compile",
        target: "build",
    },
    Alias {
        name: "start",
        target: "run",
    },
];

/// The names a typo can be corrected to: the commands that exist (SPEC 13.2).
pub(crate) fn command_names() -> Vec<&'static str> {
    let working = WORKING.iter().map(|command| command.name);
    let later = LATER.iter().map(|command| command.name);
    working.chain(later).collect()
}

/// The long flags a typo in the place of a command can be corrected to.
pub(crate) const TOP_LEVEL_FLAGS: &[&str] = &["--help", "--version"];
