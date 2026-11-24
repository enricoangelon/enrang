//! `enrang explain <code>` (SPEC 13.1).

use enrang_diag::{CURRENT_MILESTONE, Code, did_you_mean, explain, shown};

use crate::commands::EXPLAIN;
use crate::outcome::Outcome;
use crate::report::complaint;

const USAGE: &str = "enrang explain <code>";

/// Codes the catalog retired, in code order, and why each went (SPEC 13.2). Codes are
/// never reused, so a retired code stays an answerable question.
const RETIRED: &[(&str, &str)] = &[
    ("EN0204", "classes may extend a class now; see EN0442"),
    (
        "EN0212",
        "`protected`, `abstract` and `super` are valid now",
    ),
    (
        "EN0217",
        "an object literal without a class is an anonymous object now",
    ),
    ("EN0223", "`x?: T` is valid now, on fields and parameters"),
    (
        "EN0306",
        "user folders have namespaces now; a private item is EN0311",
    ),
    ("EN0407", "object types are valid everywhere now"),
    (
        "EN0431",
        "`length()` is a method now; a bare `.length` is EN0441",
    ),
    ("EN0505", "`match` arms bind no variables now"),
    (
        "EN0620",
        "a method with type parameters of its own is never overridden; an override of one is EN0460",
    ),
    (
        "EN0704",
        "R3's rule 3 with EN0710 and EN0712 covers what it named",
    ),
    (
        "EN0716",
        "`from` is removed; returned-reference sources are inferred",
    ),
    (
        "EN0719",
        "a `for...of` source is locked for the loop; changing it is EN0706",
    ),
    (
        "EN0720",
        "a part of an array is a `&Slice<T>`, and one passed where a growable `&T[]` is expected is EN0401",
    ),
    ("EN0810", "there is one raw pointer kind, `*T`"),
    ("EN1008", "`match` guards and ranges are supported now"),
    (
        "EN1016",
        "default parameters and overloads are supported now",
    ),
    (
        "EN1020",
        "`--float=x87` is accepted; it is the default at `i586` and `i686`",
    ),
    (
        "EN1040",
        "enum cases may carry texts now: `Negative = \"negative age\"`",
    ),
];

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
