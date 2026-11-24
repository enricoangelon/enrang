//! The names the command line knows (ARCHITECTURE 11, SPEC 13.2 and 16).

use enrang_diag::Milestone;

/// A command that works at this milestone.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Working {
    pub name: &'static str,
    /// As `--help` and ARCHITECTURE 11 write it, without the leading `enrang`.
    pub usage: &'static str,
    pub summary: &'static str,
    /// The milestone that delivers it. One above the current milestone is the one
    /// being built, whose commands work before the commit that closes it.
    pub since: Milestone,
}

pub(crate) const CHECK: Working = Working {
    name: "check",
    usage: "check [file]",
    summary: "Check a file's syntax, types and borrows",
    since: Milestone::M1,
};

pub(crate) const FMT: Working = Working {
    name: "fmt",
    usage: "fmt [paths] [--check]",
    summary: "Format files in the canonical style, or report those that would change",
    since: Milestone::M1,
};

pub(crate) const EXPLAIN: Working = Working {
    name: "explain",
    usage: "explain <code>",
    summary: "Print the page of a diagnostic code, or its title until the page arrives",
    since: Milestone::M0,
};

pub(crate) const INIT: Working = Working {
    name: "init",
    usage: "init [name] [--kernel]",
    summary: "Create a project without overwriting anything; M9 adds `--kernel`",
    since: Milestone::M1,
};

pub(crate) const TARGETS: Working = Working {
    name: "targets",
    usage: "targets [--evidence]",
    summary: "List targets, CPU levels and aliases; --evidence prints the support table",
    since: Milestone::M0,
};

/// Every command that works, in the order of the table in ARCHITECTURE 11, which
/// is the order `--help` shows them in.
pub const WORKING: &[Working] = &[CHECK, FMT, EXPLAIN, INIT, TARGETS];

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
];

/// The commands outside the prototype, in the order SPEC 13.2 lists them. EN1301.
pub const DEFERRED: &[&str] = &[
    "install", "add", "publish", "doc", "lsp", "repl", "bench", "debug", "upgrade",
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
