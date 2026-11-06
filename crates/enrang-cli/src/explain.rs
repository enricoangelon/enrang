//! `enrang explain <code>` (SPEC 13.1).

use enrang_diag::{CURRENT_MILESTONE, Code, did_you_mean, explain, shown};

use crate::commands::EXPLAIN;
use crate::outcome::Outcome;
use crate::report::complaint;

const USAGE: &str = "enrang explain <code>";

/// Codes the catalog retired, and what took their place (SPEC 13.2). Codes are never
/// reused, so a retired code stays an answerable question.
const RETIRED: &[(&str, &str)] = &[(
    "EN0704",
    "R3's rule 4 with EN0710 and EN0712 covers what it named",
)];

pub(crate) fn command(args: &[String]) -> Outcome {
    match args {
        [] => complaint("`enrang explain` needs a code", None, Some(USAGE)),
        [flag] if flag == "--help" || flag == "-h" => Outcome::print(help()),
        [flag] if flag.starts_with('-') => {
            let suggestion = did_you_mean(flag, &["--help"]);
            let help = suggestion.map(|flag| format!("did you mean `{flag}`?"));
            complaint(
                &format!("`{}` is not a flag of `enrang explain`", shown(flag)),
                help.as_deref(),
                Some(USAGE),
            )
        }
        [name] => explain_name(name),
        [..] => complaint("`enrang explain` takes one code", None, Some(USAGE)),
    }
}

fn help() -> String {
    format!(
        "{}.\n\nUsage: {USAGE}\n\nCodes look like `EN0601` and `T0001`.\n",
        EXPLAIN.summary
    )
}

fn explain_name(name: &str) -> Outcome {
    match Code::from_name(name) {
        Some(code) => Outcome::print(match explain(code) {
            Some(page) => page.to_string(),
            None => title_only(code),
        }),
        None => unknown_code(name),
    }
}

fn title_only(code: Code) -> String {
    format!(
        "{code}: {}\n\nNo explain page yet: it arrives with milestone {}, and this is milestone {CURRENT_MILESTONE}.\n",
        code.title(),
        code.since(),
    )
}

/// SPEC 13.2 has no code for a code that does not exist, so this has none either.
/// Nothing was compiled and no test failed: it is a bad argument, so a usage error.
fn unknown_code(name: &str) -> Outcome {
    if let Some((_, replaced_by)) = RETIRED.iter().find(|(retired, _)| *retired == name) {
        let message = format!("`{name}` is retired: {replaced_by}");
        return complaint(&message, None, None);
    }
    let names: Vec<&str> = Code::ALL.iter().map(|code| code.name()).collect();
    let help = match did_you_mean(name, &names) {
        Some(close) => format!("did you mean `{close}`?"),
        None => "codes look like `EN0601` and `T0001`".to_owned(),
    };
    let message = format!("`{}` is not a diagnostic code", shown(name));
    complaint(&message, Some(&help), None)
}
