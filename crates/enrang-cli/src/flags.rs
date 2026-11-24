//! The common flags of `build`, `run`, `check` and `test` (ARCHITECTURE 11), and the
//! deferred flags of SPEC 16 that a compile command refuses with a code.
//!
//! A flag takes its value after `=`, as the tables of ARCHITECTURE 11 write it. Values
//! that `TargetSpec` resolution rejects are diagnostics with codes, so `--target`,
//! `--cpu` and `--float` take any word here; the other values, and every malformed
//! flag, are usage messages (SPEC 13.1).

use enrang_diag::{Code, Diagnostic, Help, did_you_mean, shown};

use crate::outcome::Outcome;
use crate::report::{complaint, noted_complaint};

/// When diagnostics are painted.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Color {
    /// As the caller decided from what stderr is.
    Auto,
    Always,
    Never,
}

impl Color {
    pub(crate) fn paints(self, auto: bool) -> bool {
        match self {
            Color::Auto => auto,
            Color::Always => true,
            Color::Never => false,
        }
    }
}

/// The common flags as given.
#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) struct Common {
    pub target: Option<String>,
    pub cpu: Option<String>,
    pub float: Option<String>,
    pub color: Color,
    pub json: bool,
    /// `--emit=`'s value as written; the command checks it (M3 plan D23).
    pub emit: Option<String>,
    /// The deferred flags given, in order.
    pub deferred: Vec<&'static str>,
}

/// The flags that take a value.
const VALUED: &[&str] = &[
    "--target",
    "--cpu",
    "--float",
    "--color",
    "--error-format",
    "--emit",
];

/// Flags of SPEC 16's deferred features: `--debug-info` is EN1034, the others EN1041.
const DEFERRED_FLAGS: &[&str] = &["--debug-info", "--multiboot", "--coverage"];

const COLORS: &[&str] = &["auto", "always", "never"];
const ERROR_FORMATS: &[&str] = &["human", "json"];

/// `a`, `b` and `c`, each in backticks.
pub(crate) fn listed(names: &[&str]) -> String {
    let mut text = String::new();
    for (index, name) in names.iter().enumerate() {
        if index > 0 {
            text.push_str(if index + 1 == names.len() {
                " and "
            } else {
                ", "
            });
        }
        text.push('`');
        text.push_str(name);
        text.push('`');
    }
    text
}

/// Splits `args` into the common flags and the other arguments, `-` among those. Any
/// other word starting with `-` that is no flag here is a usage message, with a
/// did-you-mean over these flags and `extra`, the command's own.
pub(crate) fn parse<'a>(
    args: &'a [String],
    command: &str,
    usage: &str,
    extra: &[&str],
) -> Result<(Common, Vec<&'a str>), Outcome> {
    let mut common = Common {
        target: None,
        cpu: None,
        float: None,
        color: Color::Auto,
        json: false,
        emit: None,
        deferred: Vec::new(),
    };
    let mut seen: Vec<&str> = Vec::new();
    let mut rest = Vec::new();
    for arg in args {
        if !arg.starts_with('-') || arg == "-" {
            rest.push(arg.as_str());
            continue;
        }
        let (name, value) = match arg.split_once('=') {
            Some((name, value)) => (name, Some(value)),
            None => (arg.as_str(), None),
        };
        let Some(known) = VALUED
            .iter()
            .chain(DEFERRED_FLAGS)
            .find(|flag| **flag == name)
        else {
            return Err(unknown_flag(name, value, command, usage, extra));
        };
        if seen.contains(known) {
            return Err(complaint(
                &format!("`{known}` is given twice"),
                None,
                Some(usage),
            ));
        }
        seen.push(known);
        if DEFERRED_FLAGS.contains(known) {
            common.deferred.push(known);
            continue;
        }
        let value = match value {
            Some(value) if !value.is_empty() => value,
            _ => {
                return Err(complaint(
                    &format!("`{known}` needs a value"),
                    Some(&format!("write it as `{known}=<value>`")),
                    Some(usage),
                ));
            }
        };
        match *known {
            "--target" => common.target = Some(value.to_owned()),
            "--cpu" => common.cpu = Some(value.to_owned()),
            "--float" => common.float = Some(value.to_owned()),
            "--emit" => common.emit = Some(value.to_owned()),
            "--color" => {
                common.color = match value {
                    "auto" => Color::Auto,
                    "always" => Color::Always,
                    "never" => Color::Never,
                    _ => return Err(bad_value(known, value, COLORS, usage)),
                }
            }
            _ => {
                common.json = match value {
                    "human" => false,
                    "json" => true,
                    _ => return Err(bad_value(known, value, ERROR_FORMATS, usage)),
                }
            }
        }
    }
    Ok((common, rest))
}

fn unknown_flag(
    name: &str,
    value: Option<&str>,
    command: &str,
    usage: &str,
    extra: &[&str],
) -> Outcome {
    let written = match value {
        Some(value) => format!("{name}={value}"),
        None => name.to_owned(),
    };
    let mut candidates: Vec<&str> = VALUED.iter().chain(DEFERRED_FLAGS).copied().collect();
    candidates.extend_from_slice(extra);
    let help = did_you_mean(name, &candidates).map(|close| match value {
        Some(value) if VALUED.contains(&close) => format!("did you mean `{close}={value}`?"),
        _ => format!("did you mean `{close}`?"),
    });
    complaint(
        &format!("`{}` is not a flag of `enrang {command}`", shown(&written)),
        help.as_deref(),
        Some(usage),
    )
}

fn bad_value(flag: &str, value: &str, values: &[&str], usage: &str) -> Outcome {
    let help = did_you_mean(value, values).map(|close| format!("did you mean `{flag}={close}`?"));
    noted_complaint(
        &format!("`{flag}={}` is not a value of `{flag}`", shown(value)),
        help.as_deref(),
        Some(&format!("the values of `{flag}` are {}", listed(values))),
        Some(usage),
    )
}

/// The diagnostics of the deferred flags given: EN1034, then one EN1041 naming every
/// flag it covers, since its message head is the same for each (SPEC 16).
pub(crate) fn deferred_diagnostics(deferred: &[&str]) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    if deferred.contains(&"--debug-info") {
        diags.push(
            Diagnostic::spanless(Code::EN1034, "DWARF output is not supported yet")
                .note("debug information in the DWARF format is outside the prototype")
                .with_help(Help::text("`--symbols` plus stack traces")),
        );
    }
    let later: Vec<&str> = deferred
        .iter()
        .copied()
        .filter(|flag| *flag != "--debug-info")
        .collect();
    if !later.is_empty() {
        let verb = if later.len() == 1 { "is" } else { "are" };
        diags.push(
            Diagnostic::spanless(Code::EN1041, "this flag is not supported yet")
                .note(format!("{} {verb} outside the prototype", listed(&later)))
                .with_help(Help::text(
                    "Boot through `--image`; the VM counts blocks internally but reports no coverage yet",
                )),
        );
    }
    diags
}
