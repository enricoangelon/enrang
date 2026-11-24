//! The README claims nothing beyond what exists.
//!
//! Every claim the README makes about the compiler is checked against the command
//! line as it is, at `CURRENT_MILESTONE`: what the compiler does today and what it
//! cannot do yet, that its hello world is what `enrang init` writes and that `enrang
//! check` accepts it, the milestone it names for running programs, and that its
//! ownership example fails exactly where its comment says, with the fixes the text
//! names. Every file and page it links to must exist. The README is the owner's to
//! write, so after a bump it can be stale until the owner rewrites it. A claim known
//! to be stale then is listed in [`KNOWN_STALE`]: its case asserts that the check
//! fails, and the run says so in its skip notices (`SKIP README.md ...`, which
//! `ENRANG_REQUIRE=README.md` turns into a failure). So a stale README is never taken
//! for a true one, and once it is rewritten each listed case fails until its entry is
//! removed.

use std::fs;
use std::path::Path;
use std::process::Command;

use enrang_cli::{LATER, WORKING};
use enrang_diag::{CURRENT_MILESTONE, Code, Phase};
use enrang_testkit::{Harness, TempDir, catch_panic, skip, workspace_root};

use crate::support::{CLI, Ran, being_built, finished, read};

/// The README's claims known to be false today. Empty while the README describes the
/// current milestone; after a bump, list here each claim that is stale until the
/// README is rewritten, each with the sentence that is now false.
const KNOWN_STALE: &[&str] = &[];

/// Registers the check of one claim. A claim in [`KNOWN_STALE`] must fail its check.
fn claim(h: &mut Harness, name: &'static str, check: fn()) {
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

/// Whether some code of `phase` is reached today, so `check` reports its errors.
fn checks(phase: Phase) -> bool {
    Code::ALL
        .iter()
        .any(|code| code.phase() == phase && code.reached())
}

/// Whether `name` is a command that works today.
fn works(name: &str) -> bool {
    WORKING.iter().any(|command| command.name == name)
}

/// The README's ```ts blocks, in order.
fn ts_blocks(readme: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut current: Option<String> = None;
    for line in readme.lines() {
        match (&mut current, line.trim_end()) {
            (None, "```ts") => current = Some(String::new()),
            (Some(block), "```") => {
                blocks.push(std::mem::take(block));
                current = None;
            }
            (Some(block), _) => {
                block.push_str(line);
                block.push('\n');
            }
            (None, _) => {}
        }
    }
    blocks
}

/// The block that follows the paragraph containing `marker`.
fn block_after<'a>(readme: &str, blocks: &'a [String], marker: &str) -> &'a str {
    let at = readme
        .find(marker)
        .unwrap_or_else(|| panic!("no `{marker}`"));
    let index = readme[..at].matches("```ts\n").count();
    &blocks[index]
}

/// The relative paths the README links to, with their anchors: Markdown links and
/// the `src`/`srcset` of images, leaving out web addresses.
fn links(readme: &str) -> Vec<String> {
    let mut found = Vec::new();
    for (open, close) in [("](", ')'), ("src=\"", '"'), ("srcset=\"", '"')] {
        for piece in readme.split(open).skip(1) {
            let Some(end) = piece.find(close) else {
                continue;
            };
            let target = &piece[..end];
            if !target.contains("://") && !target.is_empty() {
                found.push(target.to_owned());
            }
        }
    }
    found
}

/// GitHub's anchor for a Markdown heading: lowercase, punctuation dropped but `-`
/// and `_`, spaces made `-`.
fn anchor(heading: &str) -> String {
    heading
        .trim()
        .to_lowercase()
        .chars()
        .filter(|c| c.is_alphanumeric() || matches!(c, '-' | '_' | ' '))
        .map(|c| if c == ' ' { '-' } else { c })
        .collect()
}

/// What is wrong with a link: a missing file, or an anchor no heading of a Markdown
/// file has.
fn broken(root: &Path, target: &str) -> Option<String> {
    let (path, fragment) = target.split_once('#').unwrap_or((target, ""));
    let file = root.join(path);
    if !file.exists() {
        return Some(format!("`{target}` links to no file"));
    }
    if fragment.is_empty() {
        return None;
    }
    let text = fs::read_to_string(&file).ok()?;
    let headings = text.lines().filter_map(|line| {
        line.trim_start_matches('#')
            .strip_prefix(' ')
            .filter(|_| line.starts_with('#'))
    });
    match headings.map(anchor).any(|a| a == fragment) {
        true => None,
        false => Some(format!("`{target}` links to no heading of {path}")),
    }
}

/// The kinds of error the IMPORTANT note says the compiler checks for, between
/// `checks programs for ` and ` errors`, split at `,` and ` and `.
fn kinds_claimed(readme: &str) -> Result<Vec<String>, String> {
    let (_, rest) = readme
        .split_once("checks programs for ")
        .ok_or("no `checks programs for ... errors`")?;
    let (list, _) = rest
        .split_once(" errors")
        .ok_or("no ` errors` after the list")?;
    Ok(list
        .split(',')
        .flat_map(|part| part.split(" and "))
        .map(|word| word.trim().to_owned())
        .filter(|word| !word.is_empty())
        .collect())
}

/// What is wrong with the kinds claimed, given which kinds run.
fn kinds_problem(claimed: &[String], runs: &[(bool, &str)]) -> Option<String> {
    if let Some((_, kind)) = runs
        .iter()
        .find(|(on, kind)| *on && !claimed.iter().any(|c| c == kind))
    {
        return Some(format!("`{kind}` errors are checked but not named"));
    }
    claimed
        .iter()
        .find(|c| !runs.iter().any(|(on, kind)| *on && kind == c))
        .map(|c| format!("`{c}` errors are named but not checked"))
}

fn kinds_running() -> [(bool, &'static str); 3] {
    [
        (checks(Phase::Syntax), "syntax"),
        (checks(Phase::Types), "type"),
        (checks(Phase::Borrows), "borrow"),
    ]
}

/// `enrang` run in `dir`.
fn cli_in(dir: &Path, args: &[&str]) -> Ran {
    finished(Command::new(CLI).args(args).current_dir(dir))
}

/// `text` as `enrang fmt` writes it.
fn formatted(dir: &Path, name: &str, text: &str) -> String {
    fs::write(dir.join(name), text).expect("a file");
    let ran = cli_in(dir, &["fmt", name]);
    assert_eq!(ran.code, 0, "{ran:?}");
    fs::read_to_string(dir.join(name)).expect("the file fmt wrote")
}

/// The comment `// error[CODE]: message` on a line of `block`: its 1-based line, the
/// code and the message.
fn error_comment(block: &str) -> Option<(usize, String, String)> {
    block.lines().enumerate().find_map(|(i, line)| {
        let (_, comment) = line.split_once("// error[")?;
        let (code, message) = comment.split_once("]: ")?;
        Some((i + 1, code.to_owned(), message.trim().to_owned()))
    })
}

pub fn register(h: &mut Harness) {
    if !KNOWN_STALE.is_empty() {
        skip(
            "README.md",
            KNOWN_STALE.len(),
            &format!("is stale at {CURRENT_MILESTONE} until the owner rewrites it"),
        );
    }
    claim(
        h,
        "readme/every file and heading it links to exists",
        || {
            let readme = read("README.md");
            let found = links(&readme);
            assert!(found.iter().any(|l| l == "docs/SPEC.md"), "{found:?}");
            let root = workspace_root();
            let problems: Vec<String> = found.iter().filter_map(|l| broken(&root, l)).collect();
            assert!(problems.is_empty(), "{problems:#?}");
        },
    );
    claim(h, "readme/it says what the compiler checks today", || {
        let readme = read("README.md");
        let claimed = kinds_claimed(&readme).unwrap_or_else(|e| panic!("{e}"));
        if let Some(problem) = kinds_problem(&claimed, &kinds_running()) {
            panic!("{problem}");
        }
    });
    claim(
        h,
        "readme/it says it cannot build or run a program while it cannot",
        || {
            let readme = read("README.md");
            let neither = !works("build") && !works("run");
            assert_eq!(
                readme.contains("Enrang can't build or run a program yet."),
                neither
            );
            assert_eq!(
                readme.contains("doesn't generate machine code yet"),
                !works("build")
            );
            assert_eq!(
                readme.contains("Enrang can't compile a program yet."),
                !works("build")
            );
        },
    );
    claim(
        h,
        "readme/its hello world is what init writes, and check accepts it",
        || {
            let readme = read("README.md");
            assert!(readme.contains("`enrang init hello` starts a project with this program and its test, and `enrang check` accepts both today."));
            let blocks = ts_blocks(&readme);
            let program = block_after(&readme, &blocks, "## Hello, world");
            let test = block_after(&readme, &blocks, "Tests sit next to the code");
            let dir = TempDir::new("meta-readme-hello");
            let ran = cli_in(dir.path(), &["init", "hello"]);
            assert_eq!(ran.code, 0, "{ran:?}");
            let src = dir.path().join("hello/src");
            let written = |name: &str| fs::read_to_string(src.join(name)).expect("init wrote it");
            assert_eq!(formatted(dir.path(), "a.en", program), written("main.en"));
            assert_eq!(
                formatted(dir.path(), "b.test.en", test),
                written("main.test.en")
            );
            let ran = cli_in(dir.path(), &["check", "hello/src/main.en"]);
            assert_eq!((ran.code, ran.stderr.as_str()), (0, ""), "{ran:?}");
            // The blocks as the README writes them, a file and its test part.
            fs::write(dir.path().join("readme.en"), program).expect("a file");
            fs::write(dir.path().join("readme.test.en"), test).expect("a file");
            let ran = cli_in(dir.path(), &["check", "readme.en"]);
            assert_eq!((ran.code, ran.stderr.as_str()), (0, ""), "{ran:?}");
        },
    );
    claim(
        h,
        "readme/running programs arrives in the milestone it names",
        || {
            let readme = read("README.md");
            assert!(readme.contains("arrives with the VM in the [next milestone]"));
            let run = LATER
                .iter()
                .find(|c| c.name == "run")
                .expect("`run` is a later command");
            assert_eq!(run.since, being_built(CURRENT_MILESTONE), "{run:?}");
        },
    );
    claim(
        h,
        "readme/its ownership example fails where its comment says, with the fixes it names",
        || {
            let readme = read("README.md");
            let blocks = ts_blocks(&readme);
            let example = block_after(&readme, &blocks, "## Ownership");
            let (line, code, message) =
                error_comment(example).expect("an `// error[..]: ..` comment");
            let dir = TempDir::new("meta-readme-ownership");
            fs::write(dir.path().join("ownership.en"), example).expect("a file");
            let ran = cli_in(dir.path(), &["check", "ownership.en"]);
            assert_eq!(ran.code, 1, "{ran:?}");
            assert!(
                ran.stderr
                    .starts_with(&format!("error[{code}]: {message}\n")),
                "{ran:?}"
            );
            assert!(
                ran.stderr.contains(&format!("--> ownership.en:{line}:")),
                "{ran:?}"
            );
            assert_eq!(
                ran.stderr.matches("\nerror[").count(),
                0,
                "one error: {ran:?}"
            );
            assert!(
                ran.stderr
                    .contains("error: aborting due to 1 previous error"),
                "{ran:?}"
            );
            for fix in [
                "change the parameter to `u: &User`",
                "`archive(ada.clone())`",
            ] {
                assert!(readme.contains(fix), "the README no longer names `{fix}`");
                assert!(
                    ran.stderr.contains(fix),
                    "`check` does not suggest `{fix}`: {ran:?}"
                );
            }
        },
    );
    h.case(
        "readme/every known stale claim is a claim of this module",
        || {
            let source = include_str!("readme.rs");
            for name in KNOWN_STALE {
                assert!(source.contains(&format!("claim(h, \"{name}\"")), "{name}");
            }
        },
    );
    h.case(
        "readme/a link to a missing file or heading is found",
        || {
            let root = workspace_root();
            assert!(broken(&root, "docs/SPEC.md").is_none());
            assert!(broken(&root, "docs/ARCHITECTURE.md#12-milestones").is_none());
            assert!(broken(&root, "docs/NOWHERE.md").is_some());
            assert!(broken(&root, "docs/ARCHITECTURE.md#13-nothing-here").is_some());
            assert_eq!(anchor("12. Milestones"), "12-milestones");
            let fake = "[a](docs/SPEC.md) <img src=\"assets/logo.svg\"> [w](https://x.org/a)";
            assert_eq!(links(fake), ["docs/SPEC.md", "assets/logo.svg"]);
        },
    );
    h.case(
        "readme/naming a kind of error that is not checked, or leaving one out, is found",
        || {
            let runs = [(true, "syntax"), (true, "type"), (false, "borrow")];
            let words = |text: &str| kinds_claimed(text).expect("a list");
            assert!(
                kinds_problem(&words("checks programs for syntax and type errors"), &runs)
                    .is_none()
            );
            assert!(
                kinds_problem(
                    &words("checks programs for syntax, type and borrow errors"),
                    &runs
                )
                .is_some()
            );
            assert!(kinds_problem(&words("checks programs for syntax errors"), &runs).is_some());
            assert!(kinds_claimed("checks nothing").is_err());
        },
    );
    h.case(
        "readme/the error comment of an example is read with its line",
        || {
            let block = "const a = 1;\nf(a); // error[EN0601]: `a` was moved\n";
            assert_eq!(
                error_comment(block),
                Some((2, "EN0601".to_owned(), "`a` was moved".to_owned()))
            );
        },
    );
}
