//! The README claims nothing beyond what exists.
//!
//! Every claim is checked against the command line as it is, at `CURRENT_MILESTONE`:
//! the milestone the README says is built, the commands and pages it says work, and
//! the commands it says arrive later. The README is the owner's to write, so after a
//! bump it can be stale until the owner rewrites it. A claim known to be stale then is
//! listed in [`KNOWN_STALE`]: its case asserts that the check fails, and the run says
//! so in its skip notices (`SKIP README.md ...`, which `ENRANG_REQUIRE=README.md`
//! turns into a failure). So a stale README is never taken for a true one, and once it
//! is rewritten each listed case fails until its entry is removed.
//!
//! What it says each command does is run, in a fresh directory, as a reader would run
//! it, and what it says is not done yet is checked against the code registry and the
//! commands: no sentence of its status or its commands may claim a step whose codes
//! are not due yet, or a native build before `build` works.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;

use enrang_cli::{DEFERRED, LATER, WORKING};
use enrang_diag::{CURRENT_MILESTONE, Code, Milestone, Phase, explain};
use enrang_testkit::{BlessMode, Harness, TempDir, catch_panic, skip, workspace_root};

use crate::support::{CLI, backticked, files_under, finished, milestone_in, read, run_cli};

/// The README's claims known to be false today. Empty while the README describes the
/// current milestone; after a bump, list here each claim that is stale until the
/// README is rewritten, each with the sentence that is now false. The README
/// describes M3, the current milestone.
const KNOWN_STALE: &[&str] = &[];

/// Registers the check of one claim, and records its name in `claims`. A claim in
/// [`KNOWN_STALE`] must fail its check.
fn claim(h: &mut Harness, claims: &mut Vec<&'static str>, name: &'static str, check: fn()) {
    claims.push(name);
    h.case(name, move || {
        if KNOWN_STALE.contains(&name) {
            assert!(
                catch_panic(check).is_some(),
                "the README now makes this claim truly: remove it from KNOWN_STALE"
            );
        } else {
            check();
        }
    });
}

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

/// The milestone the README describes: the one its status section says is built.
fn described(readme: &str) -> Milestone {
    let (_, rest) = readme
        .split_once("Milestone ")
        .expect("the README names the milestone that is built");
    let (name, tail) = rest.split_once(' ').expect("a word after the milestone");
    assert!(tail.starts_with("is built."), "{name} {tail}");
    milestone_in(name)
        .filter(|milestone| format!("{milestone:?}") == name)
        .unwrap_or_else(|| panic!("`{name}` is not a milestone"))
}

/// The paragraph about the commands that stop.
fn stopped_commands_line(readme: &str) -> &str {
    readme
        .lines()
        .find(|line| line.starts_with("`build`,"))
        .expect("the paragraph about the commands that stop")
}

/// The README from the heading `from` up to the heading `to`, or to its end.
fn between<'r>(readme: &'r str, from: &str, to: &str) -> &'r str {
    let start = readme
        .find(from)
        .unwrap_or_else(|| panic!("the README has no `{from}`"));
    let rest = &readme[start..];
    rest.find(to).map_or(rest, |end| &rest[..end])
}

/// The status section.
fn status(readme: &str) -> &str {
    between(readme, "## Status", "\n## ")
}

/// The bullet of the commands section that starts with `head`.
fn bullet<'r>(readme: &'r str, head: &str) -> &'r str {
    let start = format!("- {head}");
    readme
        .lines()
        .find(|line| line.starts_with(&start))
        .unwrap_or_else(|| panic!("the README has no bullet `{start}`"))
}

/// The sentence of the status that says what is not done yet: from `nothing is` to
/// its `yet.`.
fn not_yet(status: &str) -> Option<&str> {
    let start = status.find("nothing is ")?;
    let rest = &status[start..];
    let end = rest.find(" yet.")?;
    let sentence = &rest[..end + " yet.".len()];
    (!rest[..end].contains('.')).then_some(sentence)
}

/// Whether the checks of `phase` run today: some code of it is due.
fn checks(phase: Phase) -> bool {
    Code::ALL
        .iter()
        .any(|code| code.phase() == phase && code.reached())
}

/// The milestone the checks of `phase` arrive in: the first one any of its codes is
/// due by.
fn arrives(phase: Phase) -> Milestone {
    Code::ALL
        .iter()
        .filter(|code| code.phase() == phase)
        .map(|code| code.since())
        .min()
        .unwrap_or_else(|| panic!("no code of phase {phase}"))
}

/// Whether anything is turned into machine code today: `build` works.
fn builds() -> bool {
    WORKING.iter().any(|command| command.name == "build")
}

/// Each step of the compiler after the syntax, whether it runs today, the word the
/// status uses for it while it does not, and words that would claim it does.
fn steps() -> [(bool, &'static str, &'static [&'static str]); 3] {
    [
        (
            checks(Phase::Types),
            "type-checked",
            &[
                "type checker",
                "type-checks",
                "type-checking",
                "type error",
                "typeck",
            ],
        ),
        (
            checks(Phase::Borrows),
            "borrow-checked",
            &[
                "borrow checker",
                "borrow-checks",
                "borrow-checking",
                "borrow error",
                "borrowck",
            ],
        ),
        (
            builds(),
            "turned into machine code",
            &[
                "compiles",
                "compiled",
                "code generator",
                "native code",
                "executable",
            ],
        ),
    ]
}

/// What the status's sentence about the compiler gets wrong: a step that does not run
/// and that the sentence `nothing is ... yet.` leaves out, or a step that runs and
/// that it names among those that do not. `Ok` when it says each truly.
fn compiler_sentence(
    status: &str,
    steps: &[(bool, &'static str, &'static [&'static str])],
) -> Result<(), String> {
    let sentence = not_yet(status);
    let missing: Vec<&str> = steps
        .iter()
        .filter(|(done, ..)| !done)
        .map(|(_, word, _)| *word)
        .collect();
    if !missing.is_empty() {
        let sentence = sentence.ok_or("the status does not say `nothing is ... yet.`")?;
        if let Some(word) = missing.iter().find(|word| !sentence.contains(**word)) {
            return Err(format!("`{word}` is missing from: {sentence}"));
        }
    }
    if let Some(sentence) = sentence
        && let Some((_, word, _)) = steps
            .iter()
            .find(|(done, word, _)| *done && sentence.contains(word))
    {
        return Err(format!(
            "`{word}` runs, but the status says it does not: {sentence}"
        ));
    }
    Ok(())
}

/// What the `check` bullet gets wrong about when types and borrows arrive: before
/// either runs it says when both do, while only borrows wait it says when they
/// arrive, and once both run it says neither arrives. `types` and `borrows` are
/// whether each runs and the milestone it arrives in.
fn arrival(line: &str, types: (bool, Milestone), borrows: (bool, Milestone)) -> Result<(), String> {
    let both = format!("Types and borrows arrive at {} and {}.", types.1, borrows.1);
    let later = format!("Borrows arrive at {}.", borrows.1);
    let (wanted, stale): (Option<&str>, &[&str]) = match (types.0, borrows.0) {
        (false, false) => (Some(&both), &[]),
        (true, false) => (Some(&later), &["Types and borrows arrive"]),
        _ => (None, &["Types and borrows arrive", "Borrows arrive"]),
    };
    if let Some(wanted) = wanted
        && !line.contains(wanted)
    {
        return Err(format!("`{wanted}` is missing from: {line}"));
    }
    if let Some(said) = stale.iter().find(|said| line.contains(**said)) {
        return Err(format!("`{said}` is stale in: {line}"));
    }
    Ok(())
}

/// What the status gets wrong about what each milestone delivered: from M1 to
/// `current` each must have its `Mn adds` sentence, as `M0 is the foundation` opens
/// the list, and no later milestone may have one.
fn milestones_described(status: &str, current: Milestone) -> Result<(), String> {
    use Milestone::*;
    if !status.contains("M0 is the foundation") {
        return Err("the status does not say what M0 is".to_owned());
    }
    for milestone in [M1, M2, M3, M4, M5, M6, M7, M8, M9, M10] {
        let says = status.contains(&format!("{milestone} adds "));
        if says != (milestone <= current) {
            let wrong = if says { "says" } else { "does not say" };
            return Err(format!(
                "the status {wrong} what {milestone} adds, at {current}"
            ));
        }
    }
    Ok(())
}

/// What the `check` bullet's first sentence gets wrong about what `check` reports:
/// the kinds it lists between `prints each ` and ` error`, read as whole words split
/// at `,` and ` and `, must be exactly those whose phase runs, of `syntax`, `type`
/// and `borrow`. So naming `borrow` before borrows run fails as dropping `type`
/// does, and `type` inside another word counts for nothing.
fn check_reports(line: &str, kinds: &[(bool, &str)]) -> Result<(), String> {
    let first = line.split(". ").next().unwrap_or(line);
    let listed = first
        .split_once("prints each ")
        .and_then(|(_, rest)| rest.split_once(" error"))
        .map(|(list, _)| list)
        .ok_or_else(|| format!("no `prints each ... error` in: {first}"))?;
    let named: Vec<&str> = listed
        .split(',')
        .flat_map(|part| part.split(" and "))
        .map(str::trim)
        .filter(|word| !word.is_empty())
        .collect();
    if let Some((_, word)) = kinds
        .iter()
        .find(|(runs, word)| *runs && !named.contains(word))
    {
        return Err(format!("`{word}` errors are missing from: {first}"));
    }
    if let Some(word) = named
        .iter()
        .find(|word| !kinds.iter().any(|(runs, kind)| *runs && kind == *word))
    {
        return Err(format!(
            "`{word}` errors do not run, but are named in: {first}"
        ));
    }
    Ok(())
}

/// The status's first sentence about what Enrang does: its first paragraph, up to
/// `, but nothing is` when it says what is not done yet.
fn status_head(status: &str) -> &str {
    let paragraph = status
        .lines()
        .skip(1)
        .find(|line| !line.trim().is_empty())
        .unwrap_or("");
    paragraph
        .split_once(", but nothing is")
        .map_or(paragraph, |(head, _)| head)
}

/// What the status's first sentence claims that does not run: any stem of a step
/// that does not run, whatever the wording around it (`check its types and
/// borrows`, `emit x86 machine code`). `Ok` when it names none.
fn head_claims(head: &str, stems: &[(bool, &[&str])]) -> Result<(), String> {
    let lower = head.to_lowercase();
    for (runs, words) in stems {
        if let Some(word) = words.iter().find(|word| !*runs && lower.contains(**word)) {
            return Err(format!(
                "the status's first sentence claims `{word}`, which does not run: {head}"
            ));
        }
    }
    Ok(())
}

/// The stems that claim each step after the syntax, with whether it runs today.
fn step_stems() -> [(bool, &'static [&'static str]); 3] {
    [
        (checks(Phase::Types), TYPE_STEMS),
        (checks(Phase::Borrows), BORROW_STEMS),
        (builds(), BUILD_STEMS),
    ]
}

const TYPE_STEMS: &[&str] = &["type"];
const BORROW_STEMS: &[&str] = &["borrow"];
const BUILD_STEMS: &[&str] = &[
    "machine code",
    "emit",
    "compiles",
    "compiled",
    "native",
    "executable",
    "code generat",
];

/// The kinds of error `check` reports today, by the word the README names each with.
fn error_kinds() -> [(bool, &'static str); 3] {
    [
        (checks(Phase::Syntax), "syntax"),
        (checks(Phase::Types), "type"),
        (checks(Phase::Borrows), "borrow"),
    ]
}

/// The entries of `stale` that name no claim. Any other case runs strictly whatever
/// the list says, so listing it would report a README stale that is not.
fn not_claims<'a>(stale: &[&'a str], claims: &[&str]) -> Vec<&'a str> {
    stale
        .iter()
        .copied()
        .filter(|name| !claims.contains(name))
        .collect()
}

/// `enrang` with `args`, in `dir`.
fn cli_in(dir: &Path, args: &[&str]) -> crate::support::Ran {
    finished(Command::new(CLI).args(args).current_dir(dir))
}

/// The files under `dir` with their bytes, in path order.
fn snapshot(dir: &Path) -> Vec<(String, Vec<u8>)> {
    files_under(dir)
        .into_iter()
        .map(|name| {
            let bytes = fs::read(dir.join(&name)).expect("a file it listed");
            (name, bytes)
        })
        .collect()
}

/// A fresh directory holding the project `init hello` made.
fn initialised() -> TempDir {
    let dir = TempDir::new("meta-readme-claim");
    let ran = cli_in(dir.path(), &["init", "hello"]);
    assert_eq!(ran.code, 0, "{ran:?}");
    dir
}

pub fn register(h: &mut Harness) {
    let mut claims: Vec<&'static str> = Vec::new();
    let claims = &mut claims;
    if !KNOWN_STALE.is_empty() {
        skip(
            "README.md",
            KNOWN_STALE.len(),
            &format!("is stale at {CURRENT_MILESTONE} until the owner rewrites it"),
        );
    }
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
    claim(
        h,
        claims,
        "readme/the milestone it describes is the current one",
        || {
            assert_eq!(described(&read("README.md")), CURRENT_MILESTONE);
        },
    );
    claim(
        h,
        claims,
        "readme/it says plainly whether there is a compiler",
        || {
            let readme = read("README.md");
            // M0 has no compiler at all; from M1 `check` runs the front end, and the
            // status names each later step that does not run yet.
            for phrase in ["There is no compiler yet", "cannot compile"] {
                assert_eq!(
                    status(&readme).contains(phrase),
                    CURRENT_MILESTONE == Milestone::M0,
                    "{phrase}"
                );
            }
            if CURRENT_MILESTONE == Milestone::M0 {
                return;
            }
            // Each step that does not run is named as not done yet, and none that
            // runs is (M2 bump: `type-checked` left that sentence once types ran).
            if let Err(error) = compiler_sentence(status(&readme), &steps()) {
                panic!("{error}");
            }
        },
    );
    claim(
        h,
        claims,
        "readme/its status says what each built milestone adds",
        || {
            let readme = read("README.md");
            if let Err(error) = milestones_described(status(&readme), CURRENT_MILESTONE) {
                panic!("{error}");
            }
        },
    );
    claim(
        h,
        claims,
        "readme/it claims no step that does not run yet",
        || {
            let readme = read("README.md");
            let claimed = between(&readme, "## Status", "## Tests").to_lowercase();
            for (done, _, words) in steps() {
                for word in words.iter().filter(|_| !done) {
                    assert!(!claimed.contains(word), "it claims `{word}`");
                }
            }
        },
    );
    claim(
        h,
        claims,
        "readme/its status's first sentence names no step that does not run",
        || {
            let readme = read("README.md");
            if let Err(error) = head_claims(status_head(status(&readme)), &step_stems()) {
                panic!("{error}");
            }
        },
    );
    claim(
        h,
        claims,
        "readme/it says when types and borrows arrive",
        || {
            let readme = read("README.md");
            let line = bullet(&readme, "`check`");
            let types = (checks(Phase::Types), arrives(Phase::Types));
            let borrows = (checks(Phase::Borrows), arrives(Phase::Borrows));
            // M3 bump: once borrows run, `Borrows arrive at M3.` is stale.
            if let Err(error) = arrival(line, types, borrows) {
                panic!("{error}");
            }
        },
    );
    claim(
        h,
        claims,
        "readme/init makes the files it lists, and never overwrites one",
        || {
            let readme = read("README.md");
            let line = bullet(&readme, "`init hello`");
            let (_, rest) = line
                .split_once("`hello/`:")
                .expect("the bullet lists the files after `hello/`:");
            let (files, after) = rest.split_once(". ").expect("the list ends a sentence");
            let named: BTreeSet<String> = backticked(files)
                .into_iter()
                .map(|file| format!("hello/{file}"))
                .collect();
            assert!(files.contains("with one passing test"), "{line}");
            assert_eq!(after, "It never overwrites a file.", "{line}");

            let dir = TempDir::new("meta-readme-init");
            let ran = cli_in(dir.path(), &["init", "hello"]);
            assert_eq!(ran.code, 0, "{ran:?}");
            let made: BTreeSet<String> = files_under(&dir.join("hello"))
                .into_iter()
                .map(|file| format!("hello/{file}"))
                .collect();
            assert_eq!(made, named, "{line}");
            let created: BTreeSet<String> = ran
                .stdout
                .lines()
                .filter_map(|line| line.strip_prefix("created "))
                .map(str::to_owned)
                .collect();
            assert_eq!(created, named, "{ran:?}");
            let tests =
                fs::read_to_string(dir.join("hello/src/main.test.en")).expect("the test part");
            let count = tests
                .lines()
                .filter(|line| line.starts_with("test("))
                .count();
            assert_eq!(count, 1, "{tests}");

            // Run again over its own project, and over a project with one file in
            // its way: it fails, and every byte stays as it was.
            let before = snapshot(&dir.join("hello"));
            let again = cli_in(dir.path(), &["init", "hello"]);
            assert_eq!(again.code, 2, "{again:?}");
            assert!(again.stderr.starts_with("error[EN1307]: "), "{again:?}");
            assert_eq!(snapshot(&dir.join("hello")), before);
            let other = TempDir::new("meta-readme-init-in-the-way");
            fs::create_dir_all(other.join("hello/src")).expect("a directory");
            fs::write(other.join("hello/src/main.en"), "mine\n").expect("a file");
            let refused = cli_in(other.path(), &["init", "hello"]);
            assert_eq!(refused.code, 2, "{refused:?}");
            assert_eq!(
                snapshot(&other.join("hello")),
                [("src/main.en".to_owned(), b"mine\n".to_vec())]
            );
        },
    );
    claim(
        h,
        claims,
        "readme/check reads the test part, and shows a fix",
        || {
            let readme = read("README.md");
            let line = bullet(&readme, "`check`");
            // The kinds of error it names are checked by the claim below, per milestone.
            for says in [
                "reads a file and its `.test.en` part and prints each ",
                ", with a fix where one is known.",
            ] {
                assert!(line.contains(says), "`{says}` is missing from: {line}");
            }
            // The module's own file is clean; only its test part has a mistake.
            let dir = initialised();
            fs::write(
                dir.join("hello/src/main.test.en"),
                "test(\"t\", () => { expect(1 === 1).toBe(true); });\n",
            )
            .expect("the test part");
            let ran = cli_in(dir.path(), &["check", "hello/src/main.en"]);
            assert_eq!(ran.code, 1, "{ran:?}");
            assert!(ran.stderr.starts_with("error[EN0201]: "), "{ran:?}");
            assert!(
                ran.stderr.contains(" --> hello/src/main.test.en:1:"),
                "{ran:?}"
            );
            assert!(!ran.stderr.contains("hello/src/main.en:"), "{ran:?}");
            assert!(ran.stderr.contains("\nhelp: "), "{ran:?}");
            // And a type error in the test part, once types are checked: a matcher's
            // value of another type than the actual (SPEC 12.2's `__eq<T>`).
            if checks(Phase::Types) {
                fs::write(
                    dir.join("hello/src/main.test.en"),
                    "test(\"t\", () => { expect(1 + 1).toBe(\"2\"); });\n",
                )
                .expect("the test part");
                let ran = cli_in(dir.path(), &["check", "hello/src/main.en"]);
                assert_eq!(ran.code, 1, "{ran:?}");
                assert!(ran.stderr.starts_with("error[EN0401]: "), "{ran:?}");
                assert!(
                    ran.stderr.contains(" --> hello/src/main.test.en:1:"),
                    "{ran:?}"
                );
                assert!(!ran.stderr.contains("hello/src/main.en:"), "{ran:?}");
            }
            // And a borrow error in the test part, once borrows are checked: a loan
            // still used after its source changed (SPEC 5.4, EN0706).
            if checks(Phase::Borrows) {
                fs::write(
                    dir.join("hello/src/main.test.en"),
                    "test(\"t\", () => {\n  let queue = [\"a\"];\n  const first = &queue[0];\n  queue.clear();\n  expect(first.length()).toBe(1);\n});\n",
                )
                .expect("the test part");
                let ran = cli_in(dir.path(), &["check", "hello/src/main.en"]);
                assert_eq!(ran.code, 1, "{ran:?}");
                assert!(ran.stderr.starts_with("error[EN0706]: "), "{ran:?}");
                assert!(
                    ran.stderr.contains(" --> hello/src/main.test.en:4:"),
                    "{ran:?}"
                );
                assert!(!ran.stderr.contains("hello/src/main.en:"), "{ran:?}");
            }
        },
    );
    claim(
        h,
        claims,
        "readme/check's bullet names each kind of error it reports",
        || {
            let readme = read("README.md");
            if let Err(error) = check_reports(bullet(&readme, "`check`"), &error_kinds()) {
                panic!("{error}");
            }
            // And `check` does report each kind it runs: a type error, at M2.
            if checks(Phase::Types) {
                let dir = TempDir::new("meta-readme-type-error");
                fs::write(dir.join("main.en"), "const a: string = 5;\n").expect("a file");
                let ran = cli_in(dir.path(), &["check", "main.en"]);
                assert_eq!(ran.code, 1, "{ran:?}");
                assert!(ran.stderr.starts_with("error[EN0401]: "), "{ran:?}");
            }
            // And a borrow error, at M3: a use after a move (SPEC 5.2, EN0601).
            if checks(Phase::Borrows) {
                let dir = TempDir::new("meta-readme-borrow-error");
                fs::write(
                    dir.join("main.en"),
                    "const a = [1, 2];\nconst b = a;\nconsole.log(a);\n",
                )
                .expect("a file");
                let ran = cli_in(dir.path(), &["check", "main.en"]);
                assert_eq!(ran.code, 1, "{ran:?}");
                assert!(ran.stderr.starts_with("error[EN0601]: "), "{ran:?}");
            }
        },
    );
    claim(
        h,
        claims,
        "readme/fmt rewrites, and with --check changes nothing and lists",
        || {
            let readme = read("README.md");
            let line = bullet(&readme, "`fmt`");
            assert_eq!(
                line,
                "- `fmt` rewrites files in the canonical style. With `--check` it changes nothing and lists the files it would change."
            );
            let dir = initialised();
            fs::write(dir.join("hello/src/main.en"), "const   x=1;\n").expect("a file");
            let before = snapshot(&dir.join("hello"));
            let checked = cli_in(dir.path(), &["fmt", "--check", "hello"]);
            assert_eq!(checked.code, 1, "{checked:?}");
            assert_eq!(
                checked.stdout,
                "hello/src/main.en would be reformatted\n1 of 2 files would change\n"
            );
            assert_eq!(snapshot(&dir.join("hello")), before);
            let rewritten = cli_in(dir.path(), &["fmt", "hello"]);
            assert_eq!(rewritten.code, 0, "{rewritten:?}");
            let text = fs::read_to_string(dir.join("hello/src/main.en")).expect("the file");
            assert_eq!(text, "const x = 1;\n");
            let again = cli_in(dir.path(), &["fmt", "--check", "hello"]);
            assert_eq!((again.code, again.stdout.as_str()), (0, ""), "{again:?}");
        },
    );
    h.case("readme/its status comes before any command", || {
        let readme = read("README.md");
        let status = readme.find("## Status").expect("a status section");
        let commands = readme.find("## Commands").expect("a commands section");
        assert!(status < commands);
    });
    h.case("readme/every command it shows runs, and succeeds", || {
        // In order, in one fresh directory, as a reader runs them: `init hello` makes
        // the project that the `check` and `fmt` lines after it read.
        let commands = readme_commands(&read("README.md"));
        assert!(commands.len() >= 6, "{commands:?}");
        let dir = TempDir::new("meta-readme");
        let project = commands
            .iter()
            .find_map(|args| match args.as_slice() {
                [init, name] if init == "init" => Some(name.clone()),
                _ => None,
            })
            .expect("an `init` line names its project");
        for args in &commands {
            let ran = finished(Command::new(CLI).args(args).current_dir(dir.path()));
            assert_eq!(ran.code, 0, "{args:?}: {ran:?}");
        }
        // The project is in the fresh directory, and nowhere a reader did not ask.
        assert!(
            dir.join(&project).join("enrang.json").is_file(),
            "the commands did not run in their directory"
        );
        assert!(
            !Path::new(&project).exists(),
            "a command wrote `{project}` into this suite's directory"
        );
    });
    claim(
        h,
        claims,
        "readme/it shows every flag and working command",
        || {
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
        },
    );
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
    claim(
        h,
        claims,
        "readme/the codes it says have pages are the ones that do",
        || {
            let readme = read("README.md");
            let line = readme
                .lines()
                .find(|line| line.starts_with("- `explain` prints"))
                .expect("the line about explain");
            let named = line
                .split("Every code due by ")
                .nth(1)
                .and_then(|rest| rest.split(' ').next())
                .expect("the sentence naming the milestone whose codes have pages");
            let milestone = milestone_in(named)
                .filter(|milestone| format!("{milestone:?}") == named)
                .unwrap_or_else(|| panic!("`{named}` is not a milestone"));
            assert_eq!(milestone, CURRENT_MILESTONE, "{line}");
            let with_pages: Vec<&str> = Code::ALL
                .iter()
                .filter(|code| explain(**code).is_some())
                .map(|code| code.name())
                .collect();
            let due: Vec<&str> = Code::ALL
                .iter()
                .filter(|code| code.since() <= milestone)
                .map(|code| code.name())
                .collect();
            assert_eq!(with_pages, due, "{line}");
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
    claim(
        h,
        claims,
        "readme/the commands it defers are the later ones",
        || {
            let readme = read("README.md");
            let line = stopped_commands_line(&readme);
            let head = line.split(" report which").next().expect("the sentence");
            let later: Vec<&str> = LATER.iter().map(|command| command.name).collect();
            assert_eq!(backticked(head), later, "{line}");
        },
    );
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
    let milestones: &[(&str, Option<Milestone>)] = &[
        (
            "The design is complete. Milestone M0 is built. There is",
            Some(Milestone::M0),
        ),
        ("Milestone M10 is built.\n", Some(Milestone::M10)),
        ("Milestone M11 is built.\n", None),
        ("Milestone M1 will be built.\n", None),
        ("No milestone here.\n", None),
    ];
    for (text, expected) in milestones {
        let (text, expected) = (*text, *expected);
        h.case(
            format!("readme/reads the milestone of {text:?}"),
            move || {
                let read = enrang_testkit::catch_panic(|| described(text));
                match expected {
                    Some(milestone) => {
                        assert_eq!(read, None, "{text:?}");
                        assert_eq!(described(text), milestone);
                    }
                    None => assert!(read.is_some(), "{text:?}"),
                }
            },
        );
    }
    let claimed = claims.clone();
    h.case(
        "readme/every known stale claim is a claim of this module",
        move || {
            assert_eq!(not_claims(KNOWN_STALE, &claimed), Vec::<&str>::new());
        },
    );
    let claimed = claims.clone();
    let names: Vec<String> = h.names().map(str::to_owned).collect();
    h.case(
        "readme/a case that is no claim cannot be listed as stale",
        move || {
            let plain = "readme/its status comes before any command";
            assert!(names.iter().any(|name| name == plain), "{plain}");
            assert_eq!(not_claims(&[plain], &claimed), [plain]);
            let real = "readme/the milestone it describes is the current one";
            assert_eq!(not_claims(&[real], &claimed), Vec::<&str>::new());
        },
    );
    // The checks the M2 bump added, each shown to pass on the README the owner would
    // write and to fail on the one written for M1.
    const M2_STEPS: [(bool, &str, &[&str]); 3] = [
        (true, "type-checked", &[]),
        (false, "borrow-checked", &[]),
        (false, "turned into machine code", &[]),
    ];
    let compilers: &[(&str, Result<(), &str>)] = &[
        (
            "Enrang can read a program, but nothing is type-checked, borrow-checked or turned into machine code yet.",
            Err("`type-checked` runs, but the status says it does not"),
        ),
        (
            "Enrang reports its syntax and type errors, but nothing is borrow-checked or turned into machine code yet.",
            Ok(()),
        ),
        (
            "But nothing is turned into machine code yet.",
            Err("`borrow-checked` is missing from"),
        ),
        (
            "It checks types.",
            Err("the status does not say `nothing is ... yet.`"),
        ),
    ];
    for (text, expected) in compilers {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the compiler sentence of {text:?} at M2"),
            move || match (compiler_sentence(text, &M2_STEPS), expected) {
                (Ok(()), Ok(())) => {}
                (Err(error), Err(head)) => assert!(error.starts_with(head), "{error}"),
                (got, wanted) => panic!("{got:?}, wanted {wanted:?}"),
            },
        );
    }
    let described_lists: &[(&str, Result<(), &str>)] = &[
        (
            "M0 is the foundation. M1 adds the parser. M2 adds types.",
            Ok(()),
        ),
        (
            "M0 is the foundation. M1 adds the parser. Every other feature is a design.",
            Err("the status does not say what M2 adds, at M2"),
        ),
        (
            "M0 is the foundation. M1 adds a. M2 adds b. M3 adds c.",
            Err("the status says what M3 adds, at M2"),
        ),
        (
            "M1 adds a. M2 adds b.",
            Err("the status does not say what M0 is"),
        ),
    ];
    for (text, expected) in described_lists {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the milestones described by {text:?} at M2"),
            move || {
                let got = milestones_described(text, Milestone::M2);
                assert_eq!(got, expected.map_err(str::to_owned));
            },
        );
    }
    let m2_kinds = [(true, "syntax"), (true, "type"), (false, "borrow")];
    let bullets: &[(&str, Result<(), &str>)] = &[
        (
            "- `check` reads a file and prints each syntax error, with a fix where one is known. Types and borrows arrive at M2 and M3.",
            Err(
                "`type` errors are missing from: - `check` reads a file and prints each syntax error, with a fix where one is known",
            ),
        ),
        (
            "- `check` reads a file and prints each syntax and type error, with a fix where one is known. Borrows arrive at M3.",
            Ok(()),
        ),
        (
            "- `check` reads a file and its `.test.en` part and prints each syntax, borrow and type error, with a fix where one is known. Borrows arrive at M3.",
            Err(
                "`borrow` errors do not run, but are named in: - `check` reads a file and its `.test.en` part and prints each syntax, borrow and type error, with a fix where one is known",
            ),
        ),
        (
            "- `check` reads a file and its `.test.en` part and prints each syntax error of every file type, with a fix where one is known.",
            Err(
                "`type` errors are missing from: - `check` reads a file and its `.test.en` part and prints each syntax error of every file type, with a fix where one is known.",
            ),
        ),
        (
            "- `check` reads a file and reports its mistakes.",
            Err("no `prints each ... error` in: - `check` reads a file and reports its mistakes."),
        ),
    ];
    for (text, expected) in bullets {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the kinds of error in {text:?} at M2"),
            move || {
                assert_eq!(
                    check_reports(text, &m2_kinds),
                    expected.map_err(str::to_owned)
                );
            },
        );
    }
    // The status's first sentence at M2: types run, borrows and machine code do not.
    const M2_STEMS: [(bool, &[&str]); 3] = [
        (true, TYPE_STEMS),
        (false, BORROW_STEMS),
        (false, BUILD_STEMS),
    ];
    let heads: &[(&str, Result<(), &str>)] = &[
        (
            "Enrang can read a program and report its syntax and type errors, format it and start a project",
            Ok(()),
        ),
        (
            "Enrang can read a program, check its types and borrows, report its errors, format it and start a project",
            Err("the status's first sentence claims `borrow`"),
        ),
        (
            "Enrang can read a program and report its syntax and type errors, emit x86 machine code for it, format it and start a project",
            Err("the status's first sentence claims `machine code`"),
        ),
        (
            "Enrang Compiles a program to native code",
            Err("the status's first sentence claims `compiles`"),
        ),
    ];
    for (text, expected) in heads {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the first sentence {text:?} at M2"),
            move || match (head_claims(text, &M2_STEMS), expected) {
                (Ok(()), Ok(())) => {}
                (Err(error), Err(head)) => assert!(error.starts_with(head), "{error}"),
                (got, wanted) => panic!("{got:?}, wanted {wanted:?}"),
            },
        );
    }
    h.case(
        "readme/the status's first sentence ends before `, but nothing is`",
        || {
            let fake = "## Status\n\nA is built. It reads, but nothing is run yet.\n\nM0 is.\n";
            assert_eq!(status_head(fake), "A is built. It reads");
            assert_eq!(
                status_head("## Status\n\nIt reads.\n\nMore.\n"),
                "It reads."
            );
            assert_eq!(status_head("## Status\n"), "");
            let readme = read("README.md");
            assert!(
                status_head(status(&readme)).contains("Milestone "),
                "{readme}"
            );
        },
    );
    h.case(
        "readme/a README describing M1 fails the M2 bump's checks for M2's reason alone",
        move || {
            // While the README describes M1: it fails each check at M2 and passes it at
            // M1, so its stale entries list sentences M2 made false, not checks that
            // no README could pass. Once it is rewritten this case checks nothing.
            let readme = read("README.md");
            if described(&readme) != Milestone::M1 {
                return;
            }
            let m1_steps = [
                (false, "type-checked", &[] as &[&str]),
                (false, "borrow-checked", &[]),
                (false, "turned into machine code", &[]),
            ];
            let m1_kinds = [(true, "syntax"), (false, "type"), (false, "borrow")];
            let (status, line) = (status(&readme), bullet(&readme, "`check`"));
            assert!(compiler_sentence(status, &M2_STEPS).is_err());
            assert!(milestones_described(status, Milestone::M2).is_err());
            assert!(check_reports(line, &m2_kinds).is_err());
            assert_eq!(compiler_sentence(status, &m1_steps), Ok(()));
            assert_eq!(milestones_described(status, Milestone::M1), Ok(()));
            assert_eq!(check_reports(line, &m1_kinds), Ok(()));
        },
    );
    // The checks the M3 bump added or extended, each shown to pass on the README the
    // owner would write and to fail on the one written for M2.
    const M3_STEPS: [(bool, &str, &[&str]); 3] = [
        (true, "type-checked", &[]),
        (true, "borrow-checked", &[]),
        (false, "turned into machine code", &[]),
    ];
    let m3_compilers: &[(&str, Result<(), &str>)] = &[
        (
            "Enrang reports its syntax and type errors, but nothing is borrow-checked or turned into machine code yet.",
            Err("`borrow-checked` runs, but the status says it does not"),
        ),
        (
            "Enrang reports its syntax, type and borrow errors, but nothing is turned into machine code yet.",
            Ok(()),
        ),
        (
            "It checks borrows.",
            Err("the status does not say `nothing is ... yet.`"),
        ),
    ];
    for (text, expected) in m3_compilers {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the compiler sentence of {text:?} at M3"),
            move || match (compiler_sentence(text, &M3_STEPS), expected) {
                (Ok(()), Ok(())) => {}
                (Err(error), Err(head)) => assert!(error.starts_with(head), "{error}"),
                (got, wanted) => panic!("{got:?}, wanted {wanted:?}"),
            },
        );
    }
    let m3_described: &[(&str, Result<(), &str>)] = &[
        (
            "M0 is the foundation. M1 adds the parser. M2 adds types. M3 adds borrows.",
            Ok(()),
        ),
        (
            "M0 is the foundation. M1 adds a. M2 adds b. Every other feature is a design.",
            Err("the status does not say what M3 adds, at M3"),
        ),
        (
            "M0 is the foundation. M1 adds a. M2 adds b. M3 adds c. M4 adds d.",
            Err("the status says what M4 adds, at M3"),
        ),
    ];
    for (text, expected) in m3_described {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the milestones described by {text:?} at M3"),
            move || {
                let got = milestones_described(text, Milestone::M3);
                assert_eq!(got, expected.map_err(str::to_owned));
            },
        );
    }
    let m3_kinds = [(true, "syntax"), (true, "type"), (true, "borrow")];
    let m3_bullets: &[(&str, Result<(), &str>)] = &[
        (
            "- `check` reads a file and its `.test.en` part and prints each syntax, type and borrow error, with a fix where one is known.",
            Ok(()),
        ),
        (
            "- `check` reads a file and its `.test.en` part and prints each syntax and type error, with a fix where one is known. Borrows arrive at M3.",
            Err(
                "`borrow` errors are missing from: - `check` reads a file and its `.test.en` part and prints each syntax and type error, with a fix where one is known",
            ),
        ),
    ];
    for (text, expected) in m3_bullets {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the kinds of error in {text:?} at M3"),
            move || {
                assert_eq!(
                    check_reports(text, &m3_kinds),
                    expected.map_err(str::to_owned)
                );
            },
        );
    }
    // When types and borrows arrive, as each milestone's bullet must say it.
    let (types_at, borrows_at) = (Milestone::M2, Milestone::M3);
    let arrivals: &[(&str, bool, bool, Result<(), &str>)] = &[
        (
            "x. Types and borrows arrive at M2 and M3.",
            false,
            false,
            Ok(()),
        ),
        (
            "x. Borrows arrive at M3.",
            false,
            false,
            Err("`Types and borrows arrive at M2 and M3.` is missing from"),
        ),
        ("x. Borrows arrive at M3.", true, false, Ok(())),
        (
            "x. Types and borrows arrive at M2 and M3. Borrows arrive at M3.",
            true,
            false,
            Err("`Types and borrows arrive` is stale in"),
        ),
        ("x, with a fix where one is known.", true, true, Ok(())),
        (
            "x, with a fix where one is known. Borrows arrive at M3.",
            true,
            true,
            Err("`Borrows arrive` is stale in"),
        ),
    ];
    for (text, types, borrows, expected) in arrivals {
        let (text, types, borrows, expected) = (*text, *types, *borrows, expected.clone());
        h.case(
            format!(
                "readme/the arrival sentence of {text:?} with types {types} and borrows {borrows}"
            ),
            move || match (
                arrival(text, (types, types_at), (borrows, borrows_at)),
                expected,
            ) {
                (Ok(()), Ok(())) => {}
                (Err(error), Err(head)) => assert!(error.starts_with(head), "{error}"),
                (got, wanted) => panic!("{got:?}, wanted {wanted:?}"),
            },
        );
    }
    // The status's first sentence at M3: types and borrows run, machine code does not.
    const M3_STEMS: [(bool, &[&str]); 3] = [
        (true, TYPE_STEMS),
        (true, BORROW_STEMS),
        (false, BUILD_STEMS),
    ];
    let m3_heads: &[(&str, Result<(), &str>)] = &[
        (
            "Enrang can read a program, report its syntax, type and borrow errors, format it and start a project",
            Ok(()),
        ),
        (
            "Enrang can read a program, check its types and borrows, emit x86 machine code for it and start a project",
            Err("the status's first sentence claims `machine code`"),
        ),
    ];
    for (text, expected) in m3_heads {
        let (text, expected) = (*text, expected.clone());
        h.case(
            format!("readme/the first sentence {text:?} at M3"),
            move || match (head_claims(text, &M3_STEMS), expected) {
                (Ok(()), Ok(())) => {}
                (Err(error), Err(head)) => assert!(error.starts_with(head), "{error}"),
                (got, wanted) => panic!("{got:?}, wanted {wanted:?}"),
            },
        );
    }
    h.case(
        "readme/a README describing M2 fails the M3 bump's checks for M3's reason alone",
        move || {
            // While the README describes M2: it fails each check at M3 and passes it at
            // M2, so its stale entries list sentences M3 made false, not checks that
            // no README could pass. Once it is rewritten this case checks nothing.
            let readme = read("README.md");
            if described(&readme) != Milestone::M2 {
                return;
            }
            let m2_kinds = [(true, "syntax"), (true, "type"), (false, "borrow")];
            let (status, line) = (status(&readme), bullet(&readme, "`check`"));
            let (types, borrows) = ((true, types_at), (true, borrows_at));
            assert!(compiler_sentence(status, &M3_STEPS).is_err());
            assert!(milestones_described(status, Milestone::M3).is_err());
            assert!(check_reports(line, &m3_kinds).is_err());
            assert!(arrival(line, types, borrows).is_err());
            assert_eq!(compiler_sentence(status, &M2_STEPS), Ok(()));
            assert_eq!(milestones_described(status, Milestone::M2), Ok(()));
            assert_eq!(check_reports(line, &m2_kinds), Ok(()));
            assert_eq!(arrival(line, types, (false, borrows_at)), Ok(()));
            // And the page sentence names M2, whose codes all have pages; M3's do too.
            let pages = readme
                .lines()
                .find(|line| line.starts_with("- `explain` prints"))
                .expect("the line about explain");
            assert!(pages.contains("Every code due by M2 has one."), "{pages}");
            assert!(
                Code::ALL
                    .iter()
                    .filter(|code| code.since() <= Milestone::M3)
                    .all(|code| explain(*code).is_some())
            );
        },
    );
    let sentences: &[(&str, Option<&str>)] = &[
        (
            "It runs, but nothing is type-checked or built yet. More.",
            Some("nothing is type-checked or built yet."),
        ),
        ("Nothing is checked yet.", None),
        ("nothing is checked. More yet.", None),
        ("nothing is checked", None),
    ];
    for (text, expected) in sentences {
        let (text, expected) = (*text, *expected);
        h.case(
            format!("readme/reads what is not done yet in {text:?}"),
            move || assert_eq!(not_yet(text), expected),
        );
    }
}
