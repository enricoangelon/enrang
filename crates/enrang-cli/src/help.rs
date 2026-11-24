//! `--help` and `--version`.

use enrang_diag::CURRENT_MILESTONE;

use crate::commands::{DEFERRED, LATER, WORKING};
use crate::table::table;

/// The shape of a command line.
pub(crate) const USAGE: &str = "enrang <command> [arguments]";

pub(crate) fn version() -> String {
    format!(
        "enrang {} (milestone {CURRENT_MILESTONE})\n",
        env!("CARGO_PKG_VERSION")
    )
}

pub(crate) fn text() -> String {
    let working: Vec<Vec<String>> = WORKING
        .iter()
        .map(|command| vec![format!("  {}", command.usage), command.summary.to_owned()])
        .collect();
    let later: Vec<Vec<String>> = LATER
        .iter()
        .map(|command| vec![format!("  {}", command.usage), command.delivers.to_owned()])
        .collect();
    let flags: Vec<Vec<String>> = [
        ("  -h, --help", "Print this help"),
        ("  -V, --version", "Print the version"),
    ]
    .iter()
    .map(|(flag, what)| vec![(*flag).to_owned(), (*what).to_owned()])
    .collect();
    format!(
        "The Enrang command line, milestone {CURRENT_MILESTONE}.

Enrang is being built: it checks syntax and formats code, and it cannot yet
compile or run a program.

Usage: {USAGE}

Commands that work today:
{working}
Commands that later milestones deliver, each saying which one today:
{later}
Outside the prototype, each reported as EN1301:
  {deferred}

Flags:
{flags}
Exit status: 0 success, 1 compile errors, failed tests, lost output or a file that
`fmt --check` would change, 2 usage, 3 internal compiler error.
",
        working = table(&working),
        later = table(&later),
        deferred = DEFERRED.join(" "),
        flags = table(&flags),
    )
}
