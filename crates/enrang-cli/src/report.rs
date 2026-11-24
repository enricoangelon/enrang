//! What a run has to say about a name it cannot act on.

use std::io;
use std::path::Path;

use enrang_diag::{
    CURRENT_MILESTONE, Code, Diagnostic, Help, Milestone, RenderOpts, did_you_mean, shown,
};
use enrang_driver::Session;

use crate::commands::{
    ALIASES, Alias, DEFERRED, LATER, LaterCommand, TOP_LEVEL_FLAGS, command_names,
};
use crate::help::USAGE;
use crate::outcome::{EXIT_USAGE, Outcome};

/// A malformed use of a command that does exist. SPEC 13.2 has no code for one at
/// this milestone, so it reports with no code rather than under an unrelated one.
pub(crate) fn complaint(message: &str, help: Option<&str>, usage: Option<&str>) -> Outcome {
    noted_complaint(message, help, None, usage)
}

/// A [`complaint`] with a note, its lines in the order SPEC 13.1 names them.
pub(crate) fn noted_complaint(
    message: &str,
    help: Option<&str>,
    note: Option<&str>,
    usage: Option<&str>,
) -> Outcome {
    let mut text = format!("error: {message}\n");
    if let Some(help) = help {
        text.push_str(&format!("help: {help}\n"));
    }
    if let Some(note) = note {
        text.push_str(&format!("note: {note}\n"));
    }
    if let Some(usage) = usage {
        text.push_str(&format!("usage: {usage}\n"));
    }
    Outcome::fail(text, EXIT_USAGE)
}

/// EN1305 for a path that names nothing.
pub(crate) fn not_found(path: &Path) -> Diagnostic {
    Diagnostic::spanless(
        Code::EN1305,
        format!("file not found: `{}`", path.to_string_lossy()),
    )
}

/// EN1305 for a path that cannot be read as a file, with the reason.
pub(crate) fn unreadable(path: &Path, error: &io::Error) -> Diagnostic {
    if error.kind() == io::ErrorKind::NotFound {
        return not_found(path);
    }
    Diagnostic::spanless(
        Code::EN1305,
        format!("cannot read `{}`: {}", path.to_string_lossy(), error.kind()),
    )
}

/// The report of a file that could not be written, which fails the run as lost
/// output does (SPEC 13.2).
pub(crate) fn write_failure(path: &Path, error: &io::Error) -> String {
    format!(
        "error: cannot write to {}: {}\n",
        shown(&path.to_string_lossy()),
        error.kind()
    )
}

/// Whichever diagnostic `name` deserves, given that no working command has it.
pub(crate) fn not_a_working_command(name: &str, color: bool) -> Outcome {
    if name.starts_with('-') {
        return unknown_flag(name);
    }
    if let Some(command) = LATER.iter().find(|command| command.name == name) {
        return later_milestone(command);
    }
    let diag = if DEFERRED.contains(&name) {
        deferred(name)
    } else if let Some(alias) = ALIASES.iter().find(|alias| alias.name == name) {
        alias_of(alias)
    } else {
        unknown(name)
    };
    let mut session = Session::new();
    session.dcx.emit(diag);
    Outcome::fail(session.render(&RenderOpts { color }), EXIT_USAGE)
}

/// A command that exists and has not arrived. It has no code: EN1301 is for the ten
/// commands SPEC 13.2 and 16 put outside the prototype, and EN1302 for a name that is
/// no command.
fn later_milestone(command: &LaterCommand) -> Outcome {
    later_feature(command.name, command.since, command.delivers)
}

/// What arrives with a later milestone, as `enrang <what>` names it: a command, or a
/// flag of a working one, such as `init --kernel`.
pub(crate) fn later_feature(what: &str, since: Milestone, delivers: &str) -> Outcome {
    let text = format!(
        "error: `enrang {what}` arrives with milestone {since}\nnote: {delivers}\nnote: this is milestone {CURRENT_MILESTONE}, so nothing was done\n",
    );
    Outcome::fail(text, EXIT_USAGE)
}

fn deferred(name: &str) -> Diagnostic {
    Diagnostic::spanless(
        Code::EN1301,
        format!("`enrang {name}` is not part of the prototype"),
    )
}

fn alias_of(alias: &Alias) -> Diagnostic {
    let target = alias.target;
    let help = match LATER.iter().find(|command| command.name == target) {
        Some(later) => format!(
            "the command for this is `enrang {target}`, which arrives with milestone {}",
            later.since
        ),
        None => format!("the command for this is `enrang {target}`"),
    };
    not_a_command(alias.name).with_help(Help::text(help))
}

/// A flag in the place of a command: a usage message (SPEC 13.1), not a diagnostic.
fn unknown_flag(flag: &str) -> Outcome {
    let help = did_you_mean(flag, TOP_LEVEL_FLAGS).map(|close| format!("did you mean `{close}`?"));
    complaint(
        &format!("`{}` is not a flag of `enrang`", shown(flag)),
        help.as_deref(),
        Some(USAGE),
    )
}

fn unknown(name: &str) -> Diagnostic {
    let suggestion =
        did_you_mean(name, &command_names()).map(|command| format!("enrang {command}"));
    let help = match suggestion {
        Some(suggestion) => format!("did you mean `{suggestion}`?"),
        None => "run `enrang --help` to see the commands".to_owned(),
    };
    not_a_command(name).with_help(Help::text(help))
}

fn not_a_command(name: &str) -> Diagnostic {
    Diagnostic::spanless(Code::EN1302, format!("`{name}` is not an `enrang` command"))
}
