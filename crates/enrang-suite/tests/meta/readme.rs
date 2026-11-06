//! The README claims nothing beyond what exists.

use enrang_cli::{DEFERRED, LATER, WORKING};
use enrang_diag::{Code, explain};
use enrang_testkit::{BlessMode, Harness, workspace_root};

use crate::support::{backticked, read, run_cli};

const ICON: &str = r#"<img src="assets/icon.svg" width="64" height="64" alt="">"#;

/// The `enrang` commands in the README's code blocks, without the binary's path.
fn readme_commands(readme: &str) -> Vec<Vec<String>> {
    let mut commands = Vec::new();
    let mut in_block = false;
    for line in readme.lines() {
        if line.starts_with("```") {
            in_block = !in_block;
            continue;
        }
        if !in_block {
            continue;
        }
        if let Some(rest) = line.strip_prefix("./target/debug/enrang") {
            commands.push(rest.split_whitespace().map(str::to_owned).collect());
        }
    }
    commands
}

/// The paragraph about the commands that stop.
fn stopped_commands_line(readme: &str) -> &str {
    readme
        .lines()
        .find(|line| line.starts_with("`build`,"))
        .expect("the paragraph about the commands that stop")
}

pub fn register(h: &mut Harness) {
    h.case("readme/states the evidence column as the command prints it", || {
        let readme = read("README.md");
        let sentence = "C1 to C3 read `planned`, and C4 reads `no hardware` except on the Q8400 and `Newer` rows.";
        assert!(readme.contains(sentence), "the README's evidence sentence has changed");
        let table = enrang_cli::run(&["targets".to_owned(), "--evidence".to_owned()], false).stdout;
        for row in table.lines().filter(|line| line.contains("  planned  planned  planned  ")) {
            let testable = row.starts_with("Core 2 Duo") || row.starts_with("Newer");
            let cell = if testable { "planned" } else { "no hardware" };
            assert!(row.trim_end().ends_with(&format!("planned  {cell}")), "{row}");
        }
    });
    h.case("readme/the first line is still the icon", || {
        assert_eq!(read("README.md").lines().next(), Some(ICON));
    });
    h.case("readme/the icon it shows exists", || {
        assert!(workspace_root().join("assets/icon.svg").is_file());
    });
    h.case("readme/it links the four documents, which exist", || {
        let readme = read("README.md");
        for doc in ["SPEC", "ARCHITECTURE", "DEV_RUNTIME", "TESTING"] {
            let path = format!("docs/{doc}.md");
            assert!(readme.contains(&format!("({path})")), "{path}");
            assert!(workspace_root().join(&path).is_file(), "{path}");
        }
    });
    h.case("readme/it says plainly that there is no compiler", || {
        let readme = read("README.md");
        for phrase in [
            "There is no compiler yet",
            "cannot compile",
            "Milestone M0 is built",
        ] {
            assert!(readme.contains(phrase), "{phrase}");
        }
    });
    h.case("readme/its status comes before any command", || {
        let readme = read("README.md");
        let status = readme.find("## Status").expect("a status section");
        let commands = readme.find("## Commands").expect("a commands section");
        assert!(status < commands);
    });
    h.case("readme/every command it shows runs, and succeeds", || {
        let commands = readme_commands(&read("README.md"));
        assert!(commands.len() >= 6, "{commands:?}");
        for args in commands {
            let ran = run_cli(&args);
            assert_eq!(ran.code, 0, "{args:?}: {ran:?}");
        }
    });
    h.case("readme/it shows every flag and working command", || {
        let commands = readme_commands(&read("README.md"));
        let shows = |wanted: &[&str]| {
            commands.iter().any(|args| {
                args.len() == wanted.len() && args.iter().zip(wanted).all(|(a, b)| a == b)
            })
        };
        assert!(shows(&["--help"]));
        assert!(shows(&["--version"]));
        assert!(shows(&["targets"]));
        assert!(shows(&["targets", "--evidence"]));
        for command in WORKING {
            assert!(
                commands
                    .iter()
                    .any(|args| args.first().is_some_and(|a| a == command.name)),
                "{}",
                command.name
            );
        }
    });
    h.case("readme/it never shows a stopped command as working", || {
        let commands = readme_commands(&read("README.md"));
        for args in commands {
            let first = args.first().map_or("", String::as_str);
            assert!(!DEFERRED.contains(&first), "{args:?}");
            assert!(
                !LATER.iter().any(|command| command.name == first),
                "{args:?}"
            );
        }
    });
    h.case(
        "readme/the codes it says have pages are the ones that do",
        || {
            let readme = read("README.md");
            let line = readme
                .lines()
                .find(|line| line.starts_with("- `explain` prints"))
                .expect("the line about explain");
            let sentence = line
                .split("Only ")
                .nth(1)
                .and_then(|rest| rest.split('.').next())
                .expect("the sentence naming the pages");
            let with_pages: Vec<String> = Code::ALL
                .iter()
                .filter(|code| explain(**code).is_some())
                .map(|code| code.name().to_owned())
                .collect();
            assert_eq!(backticked(sentence), with_pages);
        },
    );
    h.case("readme/it names how to run the tests", || {
        let readme = read("README.md");
        assert!(readme.contains("cargo test --workspace --locked\n"));
        assert!(readme.contains("ENRANG_BLESS=1 cargo test --workspace"));
    });
    h.case("readme/it says bless is refused under CI", || {
        let readme = read("README.md");
        let line = readme
            .lines()
            .find(|line| line.contains("ENRANG_BLESS=1"))
            .expect("the line about bless");
        assert!(line.contains("refused under `CI=1`"), "{line}");
        assert_eq!(
            BlessMode::from_values(Some("1"), Some("1")),
            BlessMode::Refuse
        );
    });
    h.case("readme/the commands it defers are the later ones", || {
        let readme = read("README.md");
        let line = stopped_commands_line(&readme);
        let head = line.split(" report which").next().expect("the sentence");
        let named = backticked(head);
        let later: Vec<&str> = LATER.iter().map(|command| command.name).collect();
        assert_eq!(named, later, "{line}");
    });
    h.case("readme/the exit status it gives is the real one", || {
        let readme = read("README.md");
        let line = stopped_commands_line(&readme);
        let status: i32 = line
            .split("exit status ")
            .nth(1)
            .and_then(|rest| rest.split(',').next())
            .expect("the sentence names a status")
            .parse()
            .expect("a number");
        let unknown = "frobnicate";
        let names = LATER
            .iter()
            .map(|command| command.name)
            .chain(DEFERRED.iter().copied())
            .chain([unknown]);
        for name in names {
            assert_eq!(run_cli(&[name.to_owned()]).code, status, "{name}");
        }
    });
    h.case("readme/the codes it gives are the real ones", || {
        let readme = read("README.md");
        let line = stopped_commands_line(&readme);
        let codes = backticked(line.split(" report which").nth(1).expect("the rest"));
        assert_eq!(codes, ["EN1301", "EN1302"], "{line}");
        for name in DEFERRED {
            let stderr = run_cli(&[(*name).to_owned()]).stderr;
            assert!(stderr.starts_with("error[EN1301]: "), "{stderr}");
        }
        let stderr = run_cli(&["frobnicate".to_owned()]).stderr;
        assert!(stderr.starts_with("error[EN1302]: "), "{stderr}");
        for command in LATER {
            let stderr = run_cli(&[command.name.to_owned()]).stderr;
            assert!(!stderr.contains("[EN13"), "{stderr}");
        }
    });
    h.case("readme/the template's text is gone", || {
        let readme = read("README.md");
        assert!(!readme.contains("Created in"), "{readme}");
        assert!(!readme.contains("# enlang"), "{readme}");
    });
    let rows: &[(&str, &[&[&str]])] = &[
        ("no block\n", &[]),
        ("```sh\n./target/debug/enrang --help\n```\n", &[&["--help"]]),
        ("./target/debug/enrang outside\n", &[]),
        (
            "```\n./target/debug/enrang\n./target/debug/enrang a b\ncargo x\n```\n",
            &[&[], &["a", "b"]],
        ),
    ];
    for (text, expected) in rows {
        let (text, expected) = (*text, *expected);
        h.case(
            format!("readme/reads the commands of {text:?}"),
            move || {
                let wanted: Vec<Vec<String>> = expected
                    .iter()
                    .map(|args| args.iter().map(|arg| (*arg).to_owned()).collect())
                    .collect();
                assert_eq!(readme_commands(text), wanted);
            },
        );
    }
}
