//! `check`, `fmt` and `init` as processes, in the golden suite `cli-project`
//! (`support::PROJECT_SUITE`). Each case runs in a fresh directory holding its files, and
//! again in this process in another such directory, which must print the same and
//! leave the same files. The exit status of each case is written here by hand, so
//! blessing never changes which outcome a command is expected to have.
//!
//! A golden is the transcript `cli` uses, with what the run read from standard input
//! after the command line, as `[stdin]`, and, for a run that writes, every file of
//! the directory it wrote to afterwards, as `[file path]`. `enrang.json` is left out
//! of that list, since `init` writes the host's target into it, and checked here.
//!
//! `initialised/` runs in a project `enrang init` made and holds neither `[stdin]` nor
//! `[file path]`, so the gating meta-test can run it again as it is; the other cases
//! need the files this module lists. A transcript that needs no file and no standard
//! input belongs to `cli` (`goldens.rs`), where every meta-test runs it.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use enrang_cli::{Env, Outcome, run_in};
use enrang_diag::{Code, Milestone};
use enrang_testkit::{
    Case, Expected, Harness, StreamSource, TempDir, extract_cases, golden, workspace_root,
};

use crate::support::{PROJECT_SUITE, Ran, enrang_fed, inproc_at, strings, transcript};

/// A program with no syntax error, in the canonical style.
const CLEAN: &str = "console.log(1);\n";

/// A program with one syntax error: G01's.
const MISSING_SEMICOLON: &str = "const x = 1\nconsole.log(x);\n";

/// A program that parses and is not in the canonical style.
const UNFORMATTED: &str = "const   x=1;\nif (x == 1) {\n      console.log(x);\n}\n";

/// SPEC 11's worked sizes for `P == 4` as compile-time asserts: they hold on a
/// 32-bit target and fail on a 64-bit one, so the target reaches phase 2.
const SIZES: &str = "assert(sizeOf<string>() == 12, \"a string is three words\");
assert(sizeOf<i64[]>() == 12, \"an array is three words\");
assert(sizeOf<i64 | null>() == 12, \"a nullable i64 has a tag\");
assert(sizeOf<Player>() == 20, \"Player\");
assert(sizeOf<Token>() == 16, \"Token\");
assert(sizeOf<GdtPointer>() == 6, \"GdtPointer\");
assert(sizeOf<{ found: bool, index: i32, last: bool }>() == 8, \"an object type\");

public final class Player {
  public name: string;
  public score: i64;
}

public enum Token {
  Num { value: i64 },
  Add,
  Bad { text: string },
}

@packed
public final class GdtPointer {
  public limit: u16;
  public base: u32;
}
";

/// A program whose summary shows a contract, a store, a borrowing class's flag
/// and its witness (A:1328-1330, A:1364).
const EMIT_SUMMARY: &str = "let data: i64[] = [1, 2];
let c = new Copier(&data);
c.step();
console.log(data, longest(\"a\", \"bb\"));

public function longest(a: &string, b: &string): &string {
  return a.length() >= b.length() ? a : b;
}

private class Copier {
  private dst: &i64[];
  public constructor(dst: &i64[]) {
    this.dst = dst;
  }
  public step(): void {
    this.dst.push(0);
  }
}
";

/// A program with two type errors, which phase 2 reports together.
const TYPE_ERRORS: &str = "const n: i64 = \"five\";\nconsole.log(totl);\n";

/// A test part with a type error of its own.
const TYPE_ERROR_IN_TEST: &str = "test(\"one\", () => {\n  const b: bool = 1;\n});\n";

/// A test part that parses and is not in the canonical style.
const UNFORMATTED_TEST: &str = "test(\"one\",() => {\n  expect(1).toBe(1);\n});\n";

/// The cases of SPEC 1, 14 and 15, read once.
pub fn spec_cases() -> &'static [Case] {
    static CASES: OnceLock<Vec<Case>> = OnceLock::new();
    CASES.get_or_init(|| {
        let spec = fs::read_to_string(workspace_root().join("docs/SPEC.md")).expect("SPEC");
        extract_cases(&spec).unwrap_or_else(|errors| panic!("{errors}"))
    })
}

pub fn spec_case(id: &str) -> &'static Case {
    spec_cases()
        .iter()
        .find(|case| case.id == id)
        .unwrap_or_else(|| panic!("SPEC has no case {id}"))
}

/// The cases of SPEC 14 whose whole output `check` reaches now that it runs phase 3
/// (M3 plan f.2): each `enrang check`, of milestone M1, M2 or M3 in
/// `tests/trace/case_since.txt`. The meta suite runs them as processes once their
/// milestone is the current one; until the bump to M3 this suite does.
const EXACT: [&str; 22] = [
    "G01", "G02", "G03", "G04", "G05", "G06", "G07", "G08", "G09", "G10", "G11", "G12", "G13",
    "G16", "G17", "G18", "G19", "G20", "G21", "G22", "G23", "G24",
];

/// Whether `check` reports `code` now: a code of phases 1 to 4 as built, every
/// code whose `since` is M3 or earlier.
fn reached_code(code: &str) -> bool {
    Code::from_name(code).is_some_and(|code| code.since() <= Milestone::M3)
}

/// The diagnostics of a rendered stderr, in order, each as its code and its text
/// with the blank line after it. Text before the first is no diagnostic (a running
/// program's own output), and the summary line ends them.
fn diagnostics(stderr: &str) -> Vec<(String, String)> {
    let mut found: Vec<(String, String)> = Vec::new();
    for line in stderr.split_inclusive('\n') {
        let code = ["error[", "warning["]
            .iter()
            .find_map(|head| line.strip_prefix(head))
            .and_then(|rest| rest.split_once(']'))
            .map(|(code, _)| code.to_owned());
        if let Some(code) = code {
            found.push((code, line.to_owned()));
        } else if line.starts_with("error: aborting") {
            break;
        } else if let Some((_, text)) = found.last_mut() {
            text.push_str(line);
        }
    }
    found
}

/// The `enrang check` of a case's files that milestone M2 can run: the file its
/// command names, with the command's `--target`, `--cpu` and `--float`; for `enrang
/// test`, the module whose `.test.en` part it names, which `check` loads with it.
fn check_of(case: &Case) -> Vec<String> {
    let words: Vec<&str> = case.cmd.split_whitespace().skip(2).collect();
    let mut args = vec!["check".to_owned()];
    args.extend(
        words
            .iter()
            .filter(|word| {
                ["--target=", "--cpu=", "--float="]
                    .iter()
                    .any(|flag| word.starts_with(flag))
            })
            .map(|word| (*word).to_owned()),
    );
    let file = words
        .iter()
        .find(|word| !word.starts_with('-'))
        .map_or_else(|| case.files[0].name.clone(), |word| (*word).to_owned());
    let file = match case.cmd.split_whitespace().nth(1) {
        Some("test") => file.replace(".test.en", ".en"),
        _ => file,
    };
    args.push(file);
    args
}

/// What [`check_of`] prints now, as its exit status and stderr: the diagnostics of
/// SPEC's expected stderr whose codes `check` reports. They must come
/// first, and be warnings when others follow them, so the text is theirs without
/// the blank line that parted them from the rest, and the status 0. A case whose
/// output cannot be cut that way is one this table cannot state: an error.
fn reached_now(case: &Case) -> Result<(i32, String), String> {
    let found = diagnostics(&case.stderr.text);
    let reached = found
        .iter()
        .take_while(|(code, _)| reached_code(code))
        .count();
    let (first, rest) = found.split_at(reached);
    if rest.iter().any(|(code, _)| reached_code(code)) {
        return Err(format!(
            "{}: a diagnostic `check` reports follows one it does not",
            case.id
        ));
    }
    if !rest.is_empty() && first.iter().any(|(_, text)| !text.starts_with("warning[")) {
        return Err(format!(
            "{}: an error `check` reports comes before one it does not",
            case.id
        ));
    }
    if rest.is_empty() && !first.is_empty() {
        return Err(format!(
            "{}: `check` reaches all of it, so it belongs in EXACT",
            case.id
        ));
    }
    let text: String = first.iter().map(|(_, text)| text.as_str()).collect();
    Ok((
        0,
        text.strip_suffix('\n').map_or(text.clone(), str::to_owned),
    ))
}

/// A case of the suite.
#[derive(Clone, Debug)]
pub struct ProjectCase {
    /// The golden's name: under `check/`, `fmt/` or `init/`, or under `initialised/`.
    pub name: String,
    pub files: Vec<(String, Vec<u8>)>,
    /// Empty directories made before the run.
    pub dirs: Vec<String>,
    pub args: Vec<String>,
    pub stdin: Option<Vec<u8>>,
    pub exit: i32,
    /// The directory, relative to the case's, whose files the golden lists after
    /// the run; `Some("")` for all of them.
    pub dump: Option<String>,
    /// Whether the directory holds the project `enrang init` makes before the
    /// case's own files are written.
    pub initialised: bool,
}

impl ProjectCase {
    fn new(name: &str, args: &[&str], exit: i32) -> ProjectCase {
        ProjectCase {
            name: format!("{name}.txt"),
            files: Vec::new(),
            dirs: Vec::new(),
            args: strings(args),
            stdin: None,
            exit,
            dump: None,
            initialised: false,
        }
    }

    fn initialised(mut self) -> ProjectCase {
        self.initialised = true;
        self
    }

    fn file(mut self, path: &str, text: &str) -> ProjectCase {
        self.files.push((path.to_owned(), text.as_bytes().to_vec()));
        self
    }

    fn bytes(mut self, path: &str, bytes: &[u8]) -> ProjectCase {
        self.files.push((path.to_owned(), bytes.to_vec()));
        self
    }

    fn dir(mut self, path: &str) -> ProjectCase {
        self.dirs.push(path.to_owned());
        self
    }

    fn stdin(mut self, text: &[u8]) -> ProjectCase {
        self.stdin = Some(text.to_vec());
        self
    }

    fn dump(mut self, dir: &str) -> ProjectCase {
        self.dump = Some(dir.to_owned());
        self
    }

    fn spec(mut self, id: &str) -> ProjectCase {
        for file in &spec_case(id).files {
            self = self.file(&file.name, &file.contents);
        }
        self
    }

    /// A fresh directory holding the case's files.
    pub fn directory(&self) -> TempDir {
        let dir = TempDir::new("project");
        if self.initialised {
            let ran = crate::support::enrang_in(dir.path(), &strings(&["init"]));
            assert_eq!(ran.code, 0, "init: {ran:?}");
        }
        for path in &self.dirs {
            fs::create_dir_all(dir.join(path)).expect("a directory");
        }
        for (path, bytes) in &self.files {
            let path = dir.join(path);
            fs::create_dir_all(path.parent().expect("a parent")).expect("its parent");
            fs::write(path, bytes).expect("a file");
        }
        dir
    }

    pub fn run(&self, dir: &Path) -> Ran {
        enrang_fed(dir, &self.args, self.stdin.as_deref().unwrap_or_default())
    }

    pub fn run_in_process(&self, dir: &Path) -> Outcome {
        let words: Vec<&str> = self.args.iter().map(String::as_str).collect();
        inproc_at(dir, &words, self.stdin.as_deref().unwrap_or_default())
    }

    /// The golden's text for a run of the case in `dir`.
    pub fn text(&self, ran: &Ran, dir: &Path) -> String {
        let mut text = transcript(&self.args, ran);
        if let Some(stdin) = &self.stdin {
            let (command, rest) = text.split_once('\n').expect("a command line");
            text = format!(
                "{command}\n[stdin]\n{}{rest}",
                String::from_utf8_lossy(stdin)
            );
        }
        if let Some(root) = &self.dump {
            text.push_str(&dump(dir, root));
        }
        text
    }
}

/// The files under `root` in `dir`, in path order, each as `[file path]` and its text.
pub fn dump(dir: &Path, root: &str) -> String {
    fn walk(dir: &Path, relative: &Path, found: &mut Vec<PathBuf>) {
        let mut entries: Vec<_> = fs::read_dir(dir.join(relative))
            .expect("a directory")
            .map(|entry| entry.expect("an entry").file_name())
            .collect();
        entries.sort();
        for name in entries {
            let path = relative.join(name);
            if dir.join(&path).is_dir() {
                walk(dir, &path, found);
            } else {
                found.push(path);
            }
        }
    }
    let mut found = Vec::new();
    walk(dir, Path::new(root), &mut found);
    let mut text = String::new();
    for path in found {
        if path.file_name().is_some_and(|name| name == "enrang.json") {
            continue;
        }
        let bytes = fs::read(dir.join(&path)).expect("a file");
        text.push_str(&format!(
            "[file {}]\n{}",
            path.display(),
            String::from_utf8_lossy(&bytes)
        ));
    }
    text
}

/// A manifest whose `key` holds a number, which only `base` may: a usage message.
fn number_for(key: &str) -> ProjectCase {
    let manifest = if key == "entry" {
        "{\"entry\": 5}\n".to_owned()
    } else {
        format!("{{\"entry\": \"main.en\", \"{key}\": 5}}\n")
    };
    ProjectCase::new(&format!("check/manifest_number_for_{key}"), &["check"], 2)
        .file("enrang.json", &manifest)
        .file("main.en", CLEAN)
}

fn check_cases() -> Vec<ProjectCase> {
    let mut cases = Vec::new();
    // SPEC 14's cases whose stderr is phase 1's and 2's, and those of phase 3
    // (M3 plan f.2): each golden is SPEC's block, which `EXACT`'s cases check too.
    for id in [
        "G01", "G02", "G03", "G04", "G07", "G08", "G09", "G10", "G11", "G16", "G18", "G21", "G23",
        "G24",
    ] {
        let file = &spec_case(id).files[0].name;
        let name = format!("check/{}", id.to_lowercase());
        cases.push(ProjectCase::new(&name, &["check", file], 1).spec(id));
    }
    // `--emit=` (M3 plan b.11, D23): the elaborated MIR of SPEC 1's ownership
    // block, a summary with a contract, a store, a flag and its witness, and
    // nothing on stdout when phase 3 reports an error.
    cases.extend([
        ProjectCase::new("check/emit_mir", &["check", "--emit=mir", "main.en"], 0)
            .file("main.en", &spec_case("ownership").files[0].contents),
        ProjectCase::new(
            "check/emit_summary",
            &["check", "--emit=summary", "main.en"],
            0,
        )
        .file("main.en", EMIT_SUMMARY),
        ProjectCase::new(
            "check/emit_mir_with_errors",
            &["check", "--emit=mir", "g08.en"],
            1,
        )
        .spec("G08"),
        // A chain that ends in another module has that module's witness
        // appended (A:1373, plan b.11), and the modules come in topological order.
        ProjectCase::new(
            "check/emit_summary_two_modules",
            &["check", "--emit=summary", "src/main.en"],
            0,
        )
        .file(
            "src/util/bag.en",
            "public function fill(xs: &i64[], n: i64): void { let i = 0; while (i < n) { grow(xs, i); i++; } }\nprivate function grow(xs: &i64[], v: i64): void { xs.push(v); }\n",
        )
        .file(
            "src/words.en",
            "import { fill } from \"./util/bag\";\npublic function extend(zs: &i64[]): void { fill(zs, 2); }\n",
        )
        .file(
            "src/main.en",
            "import { extend } from \"./words\";\nlet xs: i64[] = [];\nextend(&xs);\nconsole.log(xs);\n",
        ),
        // Two modules' MIR, one after the other, a blank line between.
        ProjectCase::new(
            "check/emit_mir_two_modules",
            &["check", "--emit=mir", "main.en"],
            0,
        )
        .file("lib.en", "public function one(): i64 { return 1; }\n")
        .file(
            "main.en",
            "import { one } from \"./lib\";\nconst n = one();\nconsole.log(n);\n",
        ),
        ProjectCase::new(
            "check/emit_summary_with_a_warning",
            &["check", "--emit=summary", "main.en"],
            0,
        )
        .file(
            "main.en",
            "let name = \" Ada \";\nname.trim();\nconsole.log(name);\n",
        ),
    ]);
    let clean = |name: &str, args: &[&str], exit: i32| {
        ProjectCase::new(name, args, exit).file("main.en", CLEAN)
    };
    let g01 = |name: &str, args: &[&str], exit: i32| ProjectCase::new(name, args, exit).spec("G01");
    cases.extend([
        clean("check/clean", &["check", "main.en"], 0),
        ProjectCase::new("check/ownership", &["check", "ownership.en"], 0)
            .spec("ownership"),
        ProjectCase::new("check/tour", &["check", "tour.en"], 0).spec("tour"),
        clean("check/test_part", &["check", "main.en"], 1)
            .file("main.test.en", "test(\"one\", () => { expect(1).toBe(1) });\n"),
        ProjectCase::new("check/both_parts", &["check", "main.en"], 1)
            .file("main.en", MISSING_SEMICOLON)
            .file("main.test.en", "const y = 2\n"),
        // A part given alone checks its module with it, whose private items it sees
        // (review 5A; M1 checked the part by itself).
        ProjectCase::new("check/test_part_alone", &["check", "main.test.en"], 0)
            .file("main.en", "private function one(): i64 {\n  return 1;\n}\n")
            .file("main.test.en", "test(\"one\", () => { expect(one()).toBe(1); });\n"),
        ProjectCase::new("check/test_part_module_error", &["check", "main.test.en"], 1)
            .file("main.en", MISSING_SEMICOLON)
            .file("main.test.en", "test(\"one\", () => { expect(1).toBe(1); });\n"),
        // G07's second help applied: the `clone` that `User` has synthesised
        // (S:639; review 5A: a false EN0303 at M2).
        ProjectCase::new("check/g07_clone_help_applied", &["check", "g07.en"], 0).file(
            "g07.en",
            &spec_case("G07").files[0]
                .contents
                .replace("archive(u);", "archive(u.clone());"),
        ),
        ProjectCase::new("check/manifest_entry", &["check"], 1)
            .file("enrang.json", "{\"name\":\"hello\",\"entry\":\"src/main.en\",\"target\":\"x86_64-linux\"}\n")
            .file("src/main.en", MISSING_SEMICOLON),
        ProjectCase::new("check/manifest_clean", &["check"], 0)
            .file("enrang.json", "{\"name\":\"hello\",\"entry\":\"src/main.en\",\"target\":\"x86_64-linux\"}\n")
            .file("src/main.en", CLEAN)
            .file("src/main.test.en", "test(\"one\", () => { expect(1).toBe(1); });\n"),
        ProjectCase::new("check/manifest_no_entry", &["check"], 2)
            .file("enrang.json", "{\"name\": \"hello\"}\n"),
        ProjectCase::new("check/manifest_target_with_a_file", &["check", "--cpu=x86-64", "other.en"], 2)
            .file("enrang.json", "{\"entry\": \"src/main.en\", \"target\": \"i386-none\"}\n")
            .file("other.en", CLEAN),
        ProjectCase::new(
            "check/manifest_target_overridden",
            &["check", "--target=x86_64-linux", "--cpu=x86-64"],
            0,
        )
        .file("enrang.json", "{\"entry\": \"main.en\", \"target\": \"i386-none\"}\n")
        .file("main.en", CLEAN),
        ProjectCase::new("check/manifest_cpu_and_float", &["check"], 0)
            .file(
                "enrang.json",
                "{\"entry\": \"main.en\", \"target\": \"i386-linux\", \"cpu\": \"k6\", \"float\": \"soft\", \"base\": 65536}\n",
            )
            .file("main.en", CLEAN),
        ProjectCase::new("check/manifest_float_rejected", &["check"], 2)
            .file("enrang.json", "{\"entry\": \"main.en\", \"float\": \"x87\"}\n")
            .file("main.en", CLEAN),
        ProjectCase::new("check/manifest_invalid_json", &["check", "main.en"], 2)
            .file("enrang.json", "{\n  \"entry\": \"main.en\",\n}\n")
            .file("main.en", CLEAN),
        ProjectCase::new("check/manifest_invalid_utf8", &["check"], 2)
            .bytes("enrang.json", b"{\"entry\": \"m\xffain.en\"}\n"),
        ProjectCase::new("check/manifest_not_an_object", &["check"], 2)
            .file("enrang.json", "[\"main.en\"]\n"),
        ProjectCase::new("check/manifest_wrong_type", &["check"], 2)
            .file("enrang.json", "{\"entry\": [\"main.en\"]}\n"),
        ProjectCase::new("check/manifest_base_wrong_type", &["check"], 2)
            .file("enrang.json", "{\"entry\": \"main.en\", \"base\": true}\n"),
        ProjectCase::new("check/manifest_duplicate_key", &["check"], 0)
            .file("enrang.json", "{\"entry\": \"missing.en\", \"entry\": \"main.en\"}\n")
            .file("main.en", CLEAN),
        number_for("name"),
        number_for("entry"),
        number_for("target"),
        number_for("cpu"),
        number_for("float"),
        ProjectCase::new("check/manifest_unknown_key", &["check"], 2)
            .file("enrang.json", "{\"entry\": \"main.en\", \"targte\": \"i386-none\"}\n"),
        ProjectCase::new("check/manifest_unreadable", &["check", "main.en"], 2)
            .dir("enrang.json")
            .file("main.en", CLEAN),
        ProjectCase::new("check/directory", &["check", "src"], 2).dir("src"),
        ProjectCase::new("check/invalid_utf8", &["check", "bad.en"], 1)
            .bytes("bad.en", b"const s = \"caf\xe9\";\n"),
        g01("check/json", &["check", "--error-format=json", "g01.en"], 1),
        g01("check/json_human", &["check", "--error-format=human", "g01.en"], 1),
        clean(
            "check/json_note",
            &["check", "--error-format=json", "--target=i386-linux", "--cpu=k6", "main.en"],
            0,
        ),
        clean("check/json_clean", &["check", "--error-format=json", "main.en"], 0),
        g01("check/color_never", &["check", "--color=never", "g01.en"], 1),
        g01("check/color_auto", &["check", "--color=auto", "g01.en"], 1),
        clean("check/target_unknown", &["check", "--target=bogus", "main.en"], 2),
        clean("check/target_misspelt", &["check", "--target=i386-linx", "main.en"], 2),
        clean("check/target_windows_32", &["check", "--target=i386-windows", "main.en"], 2),
        clean("check/target_vm", &["check", "--target=vm32", "main.en"], 2),
        clean("check/target_each_flag", &["check", "--target=i386-none", "--cpu=i486", "--float=x87", "main.en"], 0),
        clean("check/cpu_native", &["check", "--cpu=native", "main.en"], 2),
        clean("check/cpu_unknown", &["check", "--target=i386-linux", "--cpu=pentium5", "main.en"], 2),
        clean("check/cpu_not_on_target", &["check", "--target=x86_64-linux", "--cpu=i386", "main.en"], 2),
        clean("check/cpu_long_mode_on_32", &["check", "--target=i386-linux", "--cpu=x86-64", "main.en"], 2),
        clean("check/cpu_alias", &["check", "--target=i386-linux", "--cpu=k6", "main.en"], 0),
        clean("check/cpu_alias_64_bit_models", &["check", "--target=x86_64-linux", "--cpu=p4", "main.en"], 0),
        clean("check/cpu_alias_no_long_mode", &["check", "--target=x86_64-linux", "--cpu=core-duo", "main.en"], 2),
        clean("check/float_not_on_target", &["check", "--target=x86_64-linux", "--float=soft", "main.en"], 2),
        clean("check/float_needs_level", &["check", "--target=i386-linux", "--cpu=i686", "--float=sse2", "main.en"], 2),
        clean("check/float_unknown", &["check", "--float=quad", "main.en"], 2),
        clean("check/debug_info", &["check", "--debug-info=dwarf", "main.en"], 2),
        clean("check/multiboot", &["check", "--multiboot", "main.en"], 2),
        clean("check/coverage", &["check", "--coverage", "main.en"], 2),
        clean("check/multiboot_and_coverage", &["check", "--coverage", "--multiboot", "main.en"], 2),
        g01("check/phase_0_stops_phase_1", &["check", "--cpu=native", "g01.en"], 2),
        g01("check/alias_note_and_syntax_error", &["check", "--target=i386-linux", "--cpu=k6", "g01.en"], 1),
        ProjectCase::new("check/sizes_32_bit", &["check", "--target=i386-linux", "sizes.en"], 0)
            .file("sizes.en", SIZES),
        ProjectCase::new("check/sizes_64_bit", &["check", "--target=x86_64-linux", "sizes.en"], 1)
            .file("sizes.en", SIZES),
        ProjectCase::new("check/phase_2_error", &["check", "main.en"], 1)
            .file("main.en", TYPE_ERRORS)
            .file("main.test.en", TYPE_ERROR_IN_TEST),
        ProjectCase::new("check/phase_2_json", &["check", "--error-format=json", "main.en"], 1)
            .file("main.en", TYPE_ERRORS)
            .file("main.test.en", TYPE_ERROR_IN_TEST),
        ProjectCase::new("check/phase_2_import", &["check", "main.en"], 1)
            .file("main.en", "import { twice } from \"./util\";\n\nconst s: string = twice(2);\n")
            .file("util.en", "public function twice(x: i64): i64 {\n  return x * 2;\n}\n"),
        // The internal `--library` the compile-fixture runners pass for a fixture
        // headed `//! library` (G50): the entry is a library module, so `extend`
        // meets EN0439's rule rather than EN0806's.
        ProjectCase::new("check/library_module", &["check", "--library", "lib.en"], 1).file(
            "lib.en",
            "public type Point = { x: f64, y: f64 };\nextend Point {\n  public length(): f64;\n}\n",
        ),
        ProjectCase::new("check/imports_clean", &["check", "main.en"], 0)
            .file("main.en", "import { twice } from \"./util\";\n\nconsole.log(twice(2));\n")
            .file("util.en", "public function twice(x: i64): i64 {\n  return x * 2;\n}\n"),
    ]);
    cases
}

/// A tree with something of every kind for `fmt`.
fn tree(case: ProjectCase) -> ProjectCase {
    case.file("src/a.en", UNFORMATTED)
        .file("src/b.en", CLEAN)
        .file("src/bad.en", MISSING_SEMICOLON)
        .file("src/notes.txt", "  not   source\n")
        .file("src/sub/c.en", "f( 1,2 );\n")
        .file("src/sub/c.test.en", UNFORMATTED_TEST)
        .file("src/sub/snippet.fail.en", UNFORMATTED)
        .file("top.en", UNFORMATTED)
}

fn fmt_cases() -> Vec<ProjectCase> {
    let formatted = |case: ProjectCase| {
        case.file("src/a.en", "const x = 1;\n")
            .file("src/b.en", CLEAN)
            .file(
                "src/sub/c.test.en",
                "test(\"one\", () => { expect(1).toBe(1); });\n",
            )
    };
    vec![
        tree(ProjectCase::new("fmt/tree", &["fmt", "src"], 1)).dump(""),
        tree(ProjectCase::new(
            "fmt/tree_check",
            &["fmt", "--check", "src"],
            1,
        ))
        .dump(""),
        formatted(ProjectCase::new(
            "fmt/formatted_check",
            &["fmt", "--check", "src"],
            0,
        )),
        formatted(ProjectCase::new("fmt/formatted", &["fmt", "src"], 0)).dump(""),
        tree(ProjectCase::new("fmt/file", &["fmt", "top.en"], 0)).dump(""),
        tree(ProjectCase::new(
            "fmt/file_check",
            &["fmt", "--check", "top.en"],
            1,
        )),
        tree(ProjectCase::new(
            "fmt/paths_in_order",
            &["fmt", "--check", "top.en", "src/sub", "src/a.en"],
            1,
        )),
        tree(ProjectCase::new(
            "fmt/a_file_once",
            &["fmt", "--check", "src/a.en", "src/a.en"],
            1,
        )),
        tree(ProjectCase::new(
            "fmt/fail_file_named",
            &["fmt", "src/sub/snippet.fail.en"],
            0,
        ))
        .dump("src/sub"),
        tree(ProjectCase::new(
            "fmt/missing",
            &["fmt", "top.en", "missing.en"],
            2,
        ))
        .dump(""),
        tree(ProjectCase::new(
            "fmt/syntax_error_only",
            &["fmt", "src/bad.en"],
            1,
        ))
        .dump("src"),
        ProjectCase::new("fmt/ignore_file", &["fmt", "--check", "f.en"], 0)
            .file("f.en", "// enrang-fmt-ignore-file\nconst   x=1;\n"),
        ProjectCase::new("fmt/not_dot_en_named", &["fmt", "--check", "script"], 1)
            .file("script", UNFORMATTED),
        ProjectCase::new("fmt/empty_directory", &["fmt", "--check", "empty"], 0).dir("empty"),
        ProjectCase::new("fmt/only_fail_en_is_skipped", &["fmt", "--check", "src"], 1)
            .file("src/fail.en", UNFORMATTED)
            .file("src/x.failure.en", UNFORMATTED)
            .file("src/x.fail.en", UNFORMATTED)
            .file("src/x.fail.en.txt", UNFORMATTED),
        ProjectCase::new("fmt/stdin", &["fmt"], 0).stdin(UNFORMATTED.as_bytes()),
        ProjectCase::new("fmt/stdin_dash", &["fmt", "-"], 0).stdin(UNFORMATTED.as_bytes()),
        ProjectCase::new("fmt/stdin_formatted", &["fmt"], 0).stdin(CLEAN.as_bytes()),
        ProjectCase::new("fmt/stdin_check", &["fmt", "--check"], 1).stdin(UNFORMATTED.as_bytes()),
        ProjectCase::new("fmt/stdin_check_no_final_newline", &["fmt", "--check"], 1)
            .stdin(b"const x = 1;"),
        ProjectCase::new(
            "fmt/stdin_check_blank_lines_at_the_end",
            &["fmt", "--check"],
            1,
        )
        .stdin(b"const x = 1;\n\n\n"),
        ProjectCase::new("fmt/stdin_check_formatted", &["fmt", "--check", "-"], 0)
            .stdin(CLEAN.as_bytes()),
        ProjectCase::new("fmt/stdin_syntax_error", &["fmt"], 1).stdin(MISSING_SEMICOLON.as_bytes()),
        ProjectCase::new("fmt/stdin_check_syntax_error", &["fmt", "--check"], 1)
            .stdin(MISSING_SEMICOLON.as_bytes()),
        // Standard input is no file of a module, so an editor can pipe a test part
        // through `fmt` as it pipes any other file.
        ProjectCase::new("fmt/stdin_test_part", &["fmt"], 0).stdin(UNFORMATTED_TEST.as_bytes()),
        ProjectCase::new("fmt/stdin_check_test_part", &["fmt", "--check"], 1)
            .stdin(UNFORMATTED_TEST.as_bytes()),
    ]
}

fn init_cases() -> Vec<ProjectCase> {
    let existing = |case: ProjectCase| {
        case.file("enrang.json", "{}\n")
            .file("src/main.en", CLEAN)
            .file("src/main.test.en", "\n")
            .file(".gitignore", "target/\n")
    };
    vec![
        ProjectCase::new("init/name", &["init", "hello"], 0).dump(""),
        ProjectCase::new("init/here", &["init"], 0).dump(""),
        ProjectCase::new("init/nested_name", &["init", "apps/hello"], 0).dump(""),
        ProjectCase::new("init/into_an_existing_directory", &["init", "hello"], 0)
            .file("hello/README.md", "# hello\n")
            .dump(""),
        ProjectCase::new("init/overwrite_manifest", &["init"], 2)
            .file("enrang.json", "{}\n")
            .dump(""),
        ProjectCase::new("init/overwrite_named", &["init", "hello"], 2)
            .file("hello/src/main.test.en", "\n")
            .dump(""),
        existing(ProjectCase::new("init/overwrite_all", &["init"], 2)).dump(""),
        ProjectCase::new("init/name_is_a_file", &["init", "hello"], 2)
            .file("hello", "a file\n")
            .dump(""),
        ProjectCase::new("init/src_is_a_file", &["init"], 2)
            .file("src", "a file\n")
            .dump(""),
        ProjectCase::new("init/parent_is_a_file", &["init", "hello/inner"], 2)
            .file("hello", "a file\n")
            .dump(""),
        ProjectCase::new(
            "init/inner_part_is_a_file",
            &["init", "apps/hello/inner"],
            2,
        )
        .file("apps/hello", "a file\n")
        .dump(""),
    ]
}

/// Cases in a fresh project, as an explain page's transcript runs.
fn initialised_cases() -> Vec<ProjectCase> {
    vec![
        ProjectCase::new("initialised/init/again", &["init"], 2).initialised(),
        ProjectCase::new("initialised/check/clean", &["check"], 0).initialised(),
        ProjectCase::new("initialised/fmt/check", &["fmt", "--check", "src"], 0).initialised(),
    ]
}

/// Every case of the suite.
pub fn cases() -> Vec<ProjectCase> {
    let mut cases = check_cases();
    cases.extend(crate::emit::cases());
    cases.extend(fmt_cases());
    cases.extend(init_cases());
    cases.extend(initialised_cases());
    cases
}

/// What `init` writes into `enrang.json` for a project of this name.
fn manifest_text(name: &str) -> String {
    format!(
        "{{\n  \"name\": \"{name}\",\n  \"entry\": \"src/main.en\",\n  \"target\": \"{}\"\n}}\n",
        enrang_target::host_target()
    )
}

pub fn register(h: &mut Harness) {
    for case in cases() {
        let name = case.name.clone();
        h.case(format!("golden/{PROJECT_SUITE}/{name}"), move || {
            let dir = case.directory();
            let ran = case.run(dir.path());
            assert_eq!(
                ran.code, case.exit,
                "exit status of {:?}: {ran:?}",
                case.args
            );
            let text = case.text(&ran, dir.path());

            let twin = case.directory();
            let outcome = case.run_in_process(twin.path());
            assert_eq!(outcome.stdout, ran.stdout, "{:?} in-process", case.args);
            assert_eq!(outcome.stderr, ran.stderr, "{:?} in-process", case.args);
            assert_eq!(
                i32::from(outcome.code),
                ran.code,
                "{:?} in-process",
                case.args
            );
            if let Some(root) = &case.dump {
                assert_eq!(dump(twin.path(), root), dump(dir.path(), root), "{name}");
            }
            golden(PROJECT_SUITE, &name, &text)
        });
    }

    for id in EXACT {
        h.case(
            format!("project/{id} is SPEC 14 byte for byte, as a process"),
            move || {
                let spec = spec_case(id);
                let case =
                    ProjectCase::new(id, &["check", &spec.files[0].name], spec.exit).spec(id);
                assert_eq!(spec.cmd, format!("enrang check {}", spec.files[0].name));
                let dir = case.directory();
                let ran = case.run(dir.path());
                assert_eq!(ran.code, spec.exit, "{ran:?}");
                assert_eq!(ran.stdout, spec.stdout.text);
                assert_eq!(ran.stderr, spec.stderr.text);
            },
        );
    }
    for spec in spec_cases() {
        if EXACT.contains(&spec.id.as_str()) {
            continue;
        }
        let id = spec.id.clone();
        h.case(
            format!("project/{id}: check prints what phases 1 to 4 reach of SPEC's output"),
            move || {
                let spec = spec_case(&id);
                let args = check_of(spec);
                let words: Vec<&str> = args.iter().map(String::as_str).collect();
                let (exit, stderr) = reached_now(spec).unwrap_or_else(|error| panic!("{error}"));
                let case = ProjectCase::new(&id, &words, exit).spec(&id);
                let dir = case.directory();
                let ran = case.run(dir.path());
                assert_eq!(
                    (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                    (exit, "", stderr.as_str()),
                    "{args:?}"
                );
            },
        );
    }
    h.case(
        "project/what check reaches of a case is cut where SPEC's output is",
        || {
            let case = |cmd: &str, exit: i32, stderr: &str| Case {
                id: "X".to_owned(),
                line: 1,
                files: Vec::new(),
                cmd: cmd.to_owned(),
                exit,
                stdout: Expected {
                    source: StreamSource::Unnamed,
                    text: String::new(),
                },
                stderr: Expected {
                    source: StreamSource::Block,
                    text: stderr.to_owned(),
                },
                serial: Expected {
                    source: StreamSource::Unnamed,
                    text: String::new(),
                },
            };
            let warning = "warning[EN0453]: w\n --> x.en:1:1\n";
            let borrow = "error[EN0310]: b\n --> x.en:2:1\n";
            let summary = "error: aborting due to 1 previous error; 1 warning emitted\n";
            let g23 = format!("{warning}\n{borrow}\n{summary}");
            assert_eq!(
                reached_now(&case("enrang check x.en", 1, &g23)),
                Ok((0, warning.to_owned()))
            );
            let borrow_only = format!("{borrow}\n{summary}");
            assert_eq!(
                reached_now(&case("enrang check x.en", 1, &borrow_only)),
                Ok((0, String::new()))
            );
            let panic = "panic: index 3\nstack:\n";
            assert_eq!(
                reached_now(&case("enrang run x.en", 101, panic)),
                Ok((0, String::new()))
            );
            let typed = "error[EN0401]: t\n --> x.en:1:1\n";
            let both = format!("{typed}\n{borrow}\n{summary}");
            assert!(reached_now(&case("enrang check x.en", 1, &both)).is_err());
            let after = format!("{borrow}\n{warning}\n{summary}");
            assert!(reached_now(&case("enrang check x.en", 1, &after)).is_err());
            let whole = format!("{typed}\nerror: aborting due to 1 previous error\n");
            assert!(reached_now(&case("enrang check x.en", 1, &whole)).is_err());
            assert_eq!(
                check_of(&case("enrang test --ci src/math.test.en", 0, "")),
                strings(&["check", "src/math.en"])
            );
            assert_eq!(
                check_of(&case(
                    "enrang build --target=i386-none --cpu=i386 --image=floppy k.en",
                    0,
                    ""
                )),
                strings(&["check", "--target=i386-none", "--cpu=i386", "k.en"])
            );
        },
    );
    h.case(
        "project/the ownership block passes check, as SPEC 1 says",
        || {
            let spec = spec_case("ownership");
            let case =
                ProjectCase::new("ownership", &["check", "ownership.en"], 0).spec("ownership");
            assert_eq!(spec.cmd, "enrang check ownership.en");
            let dir = case.directory();
            let ran = case.run(dir.path());
            assert_eq!(
                (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                (spec.exit, "", "")
            );
        },
    );

    for (name, dir) in [("hello", "hello"), ("hello", "apps/hello")] {
        h.case(
            format!("project/init {dir} writes the manifest of `{name}`"),
            move || {
                let root = TempDir::new("init");
                let ran = crate::support::enrang_in(root.path(), &strings(&["init", dir]));
                assert_eq!(ran.code, 0, "{ran:?}");
                let manifest =
                    fs::read_to_string(root.join(dir).join("enrang.json")).expect("written");
                assert_eq!(manifest, manifest_text(name));
            },
        );
    }
    h.case(
        "project/init with no name is named after its directory",
        || {
            let root = TempDir::new("init-here");
            let ran = crate::support::enrang_in(root.path(), &strings(&["init"]));
            assert_eq!(ran.code, 0, "{ran:?}");
            let name = root
                .path()
                .file_name()
                .expect("a name")
                .to_string_lossy()
                .into_owned();
            let manifest = fs::read_to_string(root.join("enrang.json")).expect("written");
            assert_eq!(manifest, manifest_text(&name));
        },
    );
    h.case("project/init names `.` after the directory it is", || {
        let root = TempDir::new("init-dot");
        let ran = crate::support::enrang_in(root.path(), &strings(&["init", "."]));
        assert_eq!(ran.code, 0, "{ran:?}");
        let name = root
            .path()
            .file_name()
            .expect("a name")
            .to_string_lossy()
            .into_owned();
        let manifest = fs::read_to_string(root.join("enrang.json")).expect("written");
        assert_eq!(manifest, manifest_text(&name));
    });
    h.case(
        "project/a name is written to the manifest as a JSON string",
        || {
            let root = TempDir::new("init-quote");
            let ran = crate::support::enrang_in(root.path(), &strings(&["init", "a\"b\\c"]));
            assert_eq!(ran.code, 0, "{ran:?}");
            let manifest = fs::read_to_string(root.join("a\"b\\c/enrang.json")).expect("written");
            assert!(
                manifest.contains("\"name\": \"a\\\"b\\\\c\","),
                "{manifest}"
            );
        },
    );
    h.case(
        "project/a new project checks, is formatted, and checks again in place",
        || {
            let root = TempDir::new("init-check");
            assert_eq!(
                crate::support::enrang_in(root.path(), &strings(&["init", "hello"])).code,
                0
            );
            let project = root.join("hello");
            let check = crate::support::enrang_in(&project, &strings(&["check"]));
            assert_eq!((check.code, check.stderr.as_str()), (0, ""), "{check:?}");
            let fmt = crate::support::enrang_in(&project, &strings(&["fmt", "--check", "src"]));
            assert_eq!(
                (fmt.code, fmt.stdout.as_str(), fmt.stderr.as_str()),
                (0, "", ""),
                "{fmt:?}"
            );
            let again = crate::support::enrang_in(&project, &strings(&["init"]));
            assert_eq!(again.code, 2);
            assert_eq!(
                again.stderr.matches("error[EN1307]").count(),
                4,
                "{}",
                again.stderr
            );
        },
    );
    h.case("project/fmt rewrites only the files that change", || {
        let case = tree(ProjectCase::new("tree", &["fmt", "src"], 1));
        let dir = case.directory();
        let kept = dir.join("src/b.en");
        let before = fs::metadata(&kept)
            .and_then(|meta| meta.modified())
            .expect("a time");
        std::thread::sleep(std::time::Duration::from_millis(20));
        let ran = case.run(dir.path());
        assert_eq!(ran.code, 1, "{ran:?}");
        let after = fs::metadata(&kept)
            .and_then(|meta| meta.modified())
            .expect("a time");
        assert_eq!(before, after, "an unchanged file is not written");
    });
    h.case("project/fmt --check changes nothing at all", || {
        let case = tree(ProjectCase::new(
            "tree",
            &["fmt", "--check", "src", "top.en"],
            1,
        ));
        let dir = case.directory();
        let before = dump(dir.path(), "");
        let ran = case.run(dir.path());
        assert_eq!(ran.code, 1, "{ran:?}");
        assert_eq!(dump(dir.path(), ""), before);
        assert!(
            ran.stdout.ends_with("4 of 6 files would change\n"),
            "{}",
            ran.stdout
        );
    });
    h.case(
        "project/fmt after fmt changes nothing, and --check agrees",
        || {
            let case = tree(ProjectCase::new("tree", &["fmt", "src", "top.en"], 1));
            let dir = case.directory();
            assert_eq!(case.run(dir.path()).code, 1);
            let once = dump(dir.path(), "");
            assert_eq!(
                case.run(dir.path()).code,
                1,
                "only the file that does not parse fails"
            );
            assert_eq!(dump(dir.path(), ""), once);
            let ran = crate::support::enrang_in(
                dir.path(),
                &strings(&["fmt", "--check", "src/a.en", "src/sub", "top.en"]),
            );
            assert_eq!((ran.code, ran.stdout.as_str()), (0, ""), "{ran:?}");
        },
    );
    #[cfg(unix)]
    h.case(
        "project/a symbolic link inside a tree is not followed",
        || {
            let dir = TempDir::new("links");
            dir.write("src/a.en", UNFORMATTED);
            let target = dir.join("src");
            std::os::unix::fs::symlink(&target, dir.join("src/loop")).expect("a link");
            std::os::unix::fs::symlink(dir.join("src/a.en"), dir.join("src/link.en"))
                .expect("a link");
            let ran = crate::support::enrang_in(dir.path(), &strings(&["fmt", "--check", "src"]));
            assert_eq!(ran.code, 1, "{ran:?}");
            assert_eq!(
                ran.stdout,
                "src/a.en would be reformatted\n1 of 1 file would change\n"
            );
        },
    );
    #[cfg(unix)]
    h.case(
        "project/init stops at a dangling link where it would write or needs a directory",
        || {
            for (link, args, at) in [
                (".gitignore", &["init"][..], ".gitignore"),
                ("src", &["init"][..], "src"),
                ("hello", &["init", "hello"][..], "hello"),
            ] {
                let dir = TempDir::new("dangling");
                std::os::unix::fs::symlink("nowhere", dir.join(link)).expect("a link");
                let ran = crate::support::enrang_in(dir.path(), &strings(args));
                assert_eq!((ran.code, ran.stdout.as_str()), (2, ""), "{ran:?}");
                assert_eq!(ran.stderr.matches("error[EN1307]").count(), 1, "{ran:?}");
                assert!(
                    ran.stderr.starts_with(&format!(
                        "error[EN1307]: `enrang init` would overwrite `{at}`\n"
                    )),
                    "{ran:?}"
                );
                let left: Vec<_> = fs::read_dir(dir.path())
                    .expect("a directory")
                    .map(|entry| entry.expect("an entry").file_name())
                    .collect();
                assert_eq!(left, [link], "nothing is written");
            }
        },
    );
    h.case("project/init paints EN1307 when colour is on", || {
        let dir = TempDir::new("init-colour");
        dir.write("enrang.json", "{}\n");
        let run = |color: bool| {
            run_in(
                &strings(&["init"]),
                color,
                &mut Env {
                    dir: dir.path(),
                    stdin: &mut std::io::Cursor::new(Vec::new()),
                },
            )
        };
        let (painted, plain) = (run(true), run(false));
        assert_eq!(painted.code, plain.code);
        assert!(painted.stderr.contains('\x1b'), "{painted:?}");
        assert!(!plain.stderr.contains('\x1b'), "{plain:?}");
        assert_eq!(
            crate::streams::without_escapes(&painted.stderr),
            plain.stderr
        );
    });
    modes::register(h);
    h.case(
        "project/check --color=always paints what --color=never does not",
        || {
            let case =
                ProjectCase::new("color", &["check", "--color=always", "g01.en"], 1).spec("G01");
            let dir = case.directory();
            let painted = case.run(dir.path());
            assert!(painted.stderr.contains('\x1b'), "{painted:?}");
            let never = crate::support::enrang_in(
                dir.path(),
                &strings(&["check", "--color=never", "g01.en"]),
            );
            assert!(!never.stderr.contains('\x1b'));
            assert_eq!(
                crate::streams::without_escapes(&painted.stderr),
                never.stderr
            );
        },
    );
    interfaces::register(h);
}

/// Module interface files (M3 plan b.9): `check` writes one per user module inside a
/// project, under `out/interfaces/`, and nothing for a lone file; the bytes depend on
/// the program alone, not on the directory, the entry or the order of imports; a
/// write that fails is skipped. The goldens above never list `out/`.
mod interfaces {
    use std::fs;
    use std::path::Path;

    use enrang_testkit::{Harness, TempDir};

    use crate::support::{Ran, enrang_in, strings};

    const MAIN: &str = "import { area } from \"./shapes\";
import { greet } from \"./words\";
console.log(area(3), greet(\"Ada\"));
";
    const SHAPES: &str = "public function area(r: i64): i64 {
  return r * r * 3;
}
public final class Box2 {
  public w: i64 = 0;
  public h: i64 = 0;
}
";
    const WORDS: &str = "import { area } from \"./shapes\";
public function greet(name: &string): string {
  return `hi ${name} ${area(1)}`;
}
public function first(a: &string, b: &string): &string {
  return a;
}
";
    const MANIFEST: &str = "{\"entry\": \"main.en\"}\n";

    /// A project of three modules in a fresh directory, with `extra` files.
    fn project(extra: &[(&str, &str)]) -> TempDir {
        let dir = TempDir::new("interfaces");
        dir.write("enrang.json", MANIFEST);
        dir.write("main.en", MAIN);
        dir.write("shapes.en", SHAPES);
        dir.write("words.en", WORDS);
        for (name, text) in extra {
            dir.write(name, text);
        }
        dir
    }

    fn check(dir: &Path, args: &[&str]) -> Ran {
        let ran = enrang_in(dir, &strings(args));
        assert_eq!(ran.code, 0, "{ran:?}");
        ran
    }

    fn read(dir: &Path, module: &str) -> String {
        fs::read_to_string(dir.join(format!("out/interfaces/{module}.eni")))
            .unwrap_or_else(|e| panic!("{module}.eni: {e}"))
    }

    /// FNV-1a 64 of `text`, as 16 lowercase hex digits.
    fn fnv1a(text: &str) -> String {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for b in text.bytes() {
            h ^= u64::from(b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        format!("{h:016x}")
    }

    /// The header line that starts with `key `.
    fn header<'a>(text: &'a str, key: &str) -> Vec<&'a str> {
        text.lines()
            .take_while(|l| !l.is_empty())
            .filter(|l| l.starts_with(&format!("{key} ")))
            .collect()
    }

    pub fn register(h: &mut Harness) {
        h.case(
            "interfaces/a project's check writes one file per user module",
            || {
                let dir = project(&[]);
                check(dir.path(), &["check"]);
                let mut names: Vec<String> = fs::read_dir(dir.join("out/interfaces"))
                    .expect("written")
                    .map(|e| {
                        e.expect("an entry")
                            .file_name()
                            .to_string_lossy()
                            .into_owned()
                    })
                    .collect();
                names.sort();
                assert_eq!(names, ["main.eni", "shapes.eni", "words.eni"]);
                for m in ["main", "shapes", "words"] {
                    let text = read(dir.path(), m);
                    assert!(
                        text.starts_with("enrang-interface 1\ncompiler enrang "),
                        "{text}"
                    );
                    for section in ["\n[api]\n", "\n[bodies]\n", "\n[witnesses]\n"] {
                        assert!(text.contains(section), "{m}: {text}");
                    }
                }
            },
        );
        h.case(
            "interfaces/the bytes are the same on a second run and in another directory",
            || {
                let a = project(&[]);
                check(a.path(), &["check"]);
                let first: Vec<String> = ["main", "shapes", "words"]
                    .map(|m| read(a.path(), m))
                    .into();
                check(a.path(), &["check"]);
                let b = project(&[]);
                check(b.path(), &["check", "main.en"]);
                for (i, m) in ["main", "shapes", "words"].iter().enumerate() {
                    assert_eq!(read(a.path(), m), first[i], "{m}: second run");
                    assert_eq!(read(b.path(), m), first[i], "{m}: another directory");
                }
            },
        );
        h.case(
            "interfaces/a module's file does not depend on the entry or the import order",
            || {
                let a = project(&[]);
                check(a.path(), &["check", "main.en"]);
                let b = project(&[(
                    "other.en",
                    "import { greet } from \"./words\";\nimport { area } from \"./shapes\";\nconsole.log(greet(\"x\"), area(2));\n",
                )]);
                check(b.path(), &["check", "other.en"]);
                for m in ["shapes", "words"] {
                    assert_eq!(read(a.path(), m), read(b.path(), m), "{m}");
                }
            },
        );
        h.case(
            "interfaces/the header names each direct user import with its API hash",
            || {
                let dir = project(&[]);
                check(dir.path(), &["check"]);
                let (main, shapes, words) = (
                    read(dir.path(), "main"),
                    read(dir.path(), "shapes"),
                    read(dir.path(), "words"),
                );
                let api = |t: &str| header(t, "api")[0]["api ".len()..].to_owned();
                assert_eq!(
                    header(&main, "import"),
                    [
                        format!("import \"shapes\" {}", api(&shapes)),
                        format!("import \"words\" {}", api(&words)),
                    ]
                );
                assert_eq!(
                    header(&words, "import"),
                    [format!("import \"shapes\" {}", api(&shapes))]
                );
                assert!(header(&shapes, "import").is_empty());
                for key in ["target", "source", "used", "api", "content"] {
                    assert_eq!(header(&main, key).len(), 1, "{key}: {main}");
                }
                // Each hash is 16 lowercase hex digits.
                for line in header(&main, "content") {
                    let hash = &line["content ".len()..];
                    assert!(
                        hash.len() == 16
                            && hash
                                .chars()
                                .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
                    );
                }
            },
        );
        h.case(
            "interfaces/a module's contracts and bodies are in its file, its test part is not",
            || {
                let dir = project(&[(
                    "words.test.en",
                    "test(\"first\", () => { expect(pick(\"a\", \"b\") == \"a\").toBe(true); });\n\nprivate function pick(a: &string, b: &string): &string { return first(a, b); }\n",
                )]);
                check(dir.path(), &["check", "words.en"]);
                let words = read(dir.path(), "words");
                assert!(words.contains("fn first(_1: &string, _2: &string) -> &string"), "{words}");
                assert!(words.contains("sources(0)"), "{words}");
                assert!(words.contains("bodyHash "), "{words}");
                assert!(!words.contains("test ") && !words.contains("pick"), "{words}");
                let shapes = read(dir.path(), "shapes");
                assert!(shapes.contains("layout Box2 size 16 align 8 offsets(0, 8)"), "{shapes}");
            },
        );
        h.case("interfaces/a lone file writes none", || {
            let dir = TempDir::new("interfaces");
            dir.write("main.en", "console.log(1);\n");
            check(dir.path(), &["check", "main.en"]);
            assert!(!dir.join("out").exists());
        });
        h.case("interfaces/a check with errors writes none", || {
            let dir = project(&[]);
            dir.write("main.en", "const xs: i64[] = [];\nxs.push(1);\n");
            let ran = enrang_in(dir.path(), &strings(&["check"]));
            assert_eq!(ran.code, 1, "{ran:?}");
            assert!(!dir.join("out").exists());
        });
        h.case(
            "interfaces/a check that fails in phase 4 writes none",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", MANIFEST);
                dir.write(
                    "main.en",
                    "const cells: u8[3000000000] = [0; 3000000000];\nconsole.log(cells[0]);\n",
                );
                let ran = enrang_in(dir.path(), &strings(&["check"]));
                assert_eq!(ran.code, 1, "{ran:?}");
                assert!(ran.stderr.contains("EN0435"), "{ran:?}");
                assert!(!dir.join("out").exists());
            },
        );
        h.case(
            "interfaces/the header hashes are FNV-1a of the source, the contents and each body",
            || {
                // FNV-1a 64 (plan b.9), pinned by its known vectors.
                assert_eq!(fnv1a(""), "cbf29ce484222325");
                assert_eq!(fnv1a("a"), "af63dc4c8601ec8c");
                let dir = project(&[]);
                check(dir.path(), &["check"]);
                for (m, source) in [("main", MAIN), ("shapes", SHAPES), ("words", WORDS)] {
                    let text = read(dir.path(), m);
                    assert_eq!(
                        header(&text, "source"),
                        [format!("source {}", fnv1a(source))]
                    );
                    let (head, rest) = text.split_once("\n\n").expect("a header");
                    let content = head.lines().last().expect("the content line");
                    assert_eq!(content, format!("content {}", fnv1a(&format!("\n{rest}"))));
                    let bodies = rest
                        .split_once("[bodies]\n")
                        .and_then(|(_, b)| b.split_once("\n[witnesses]\n"))
                        .expect("a [bodies] section")
                        .0;
                    let mut body = String::new();
                    let mut seen = 0;
                    for line in bodies.split_inclusive('\n') {
                        match line.strip_prefix("bodyHash ") {
                            Some(h) => {
                                assert_eq!(h.trim_end(), fnv1a(&body), "{m}: {body}");
                                body.clear();
                                seen += 1;
                            }
                            None => body.push_str(line),
                        }
                    }
                    assert!(seen > 0, "{m}: {text}");
                }
            },
        );
        h.case(
            "interfaces/an import's API reaches the importer's api; its contract never reaches used",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", MANIFEST);
                dir.write(
                    "main.en",
                    "import { put } from \"./lib\";\nlet xs: i64[] = [];\nput(&xs);\nconsole.log(xs.length());\n",
                );
                let lib = "public function put(xs: &i64[]): void { xs.push(1); }\n";
                dir.write("lib.en", lib);
                check(dir.path(), &["check"]);
                let before = read(dir.path(), "main");
                // Only `put`'s contract (and its moves-or-writes bit) changes.
                dir.write(
                    "lib.en",
                    "public function put(xs: &i64[]): void { console.log(xs.length()); }\n",
                );
                check(dir.path(), &["check"]);
                let reading = read(dir.path(), "main");
                assert_eq!(header(&reading, "used"), header(&before, "used"));
                assert_ne!(reading, before, "the contract is in the file");
                // A new public item changes `lib`'s API, hence `main`'s.
                dir.write(
                    "lib.en",
                    &format!("{lib}public function other(): i64 {{ return 1; }}\n"),
                );
                check(dir.path(), &["check"]);
                let grown = read(dir.path(), "main");
                assert_ne!(header(&grown, "api"), header(&before, "api"));
                assert_eq!(header(&grown, "used"), header(&before, "used"));
            },
        );
        h.case(
            "interfaces/the used hash leaves out an import's moves bit",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", MANIFEST);
                dir.write(
                    "main.en",
                    "import { take } from \"./lib\";\ntake(\"a\".toString());\n",
                );
                dir.write(
                    "lib.en",
                    "public function take(x: string): void { console.log(x); }\n",
                );
                check(dir.path(), &["check"]);
                let before = read(dir.path(), "main");
                dir.write(
                    "lib.en",
                    "public function take(x: string): void { const y = x; console.log(y); }\n",
                );
                check(dir.path(), &["check"]);
                let after = read(dir.path(), "main");
                assert!(
                    before.contains("moves(0)") && after.contains("moves(1)"),
                    "{after}"
                );
                assert_eq!(header(&after, "used"), header(&before, "used"));
            },
        );
        h.case(
            "interfaces/imports are in path order, a folder import's modules included",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", MANIFEST);
                dir.write(
                    "main.en",
                    "import { zed } from \"./zeta\";\nimport { alp } from \"./alpha\";\nimport { serial } from \"./drivers\";\nconsole.log(zed() + alp() + serial.speed());\n",
                );
                dir.write("zeta.en", "public function zed(): i64 { return 1; }\n");
                dir.write("alpha.en", "public function alp(): i64 { return 2; }\n");
                dir.write("drivers/serial.en", "public function speed(): i64 { return 9600; }\n");
                check(dir.path(), &["check"]);
                let main = read(dir.path(), "main");
                let names: Vec<&str> = header(&main, "import")
                    .iter()
                    .map(|l| l.split('"').nth(1).expect("a path"))
                    .collect();
                assert_eq!(names, ["alpha", "drivers/serial", "zeta"], "{main}");
            },
        );
        h.case(
            "interfaces/a module's witnesses are its own, with no other module's appended",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", "{\"entry\": \"main.en\"}\n");
                dir.write(
                    "bag.en",
                    "public function fill(xs: &i64[]): void { grow(xs); }\nprivate function grow(xs: &i64[]): void { xs.push(1); }\n",
                );
                dir.write(
                    "main.en",
                    "import { fill } from \"./bag\";\nlet xs: i64[] = [];\nextend(&xs);\nconsole.log(xs);\n\nfunction extend(zs: &i64[]): void { fill(zs); }\n",
                );
                check(dir.path(), &["check"]);
                let main = read(dir.path(), "main");
                let witnesses = main.split_once("\n[witnesses]\n").expect("witnesses").1;
                assert!(witnesses.contains("passes it to `fill` from `bag`, which changes it"), "{main}");
                assert!(!witnesses.contains("`grow`"), "{main}");
                assert!(!witnesses.contains("module \"bag\""), "{main}");
            },
        );
        h.case("interfaces/bodies are in path order, the statements first", || {
            let dir = TempDir::new("interfaces");
            dir.write("enrang.json", MANIFEST);
            dir.write(
                "main.en",
                "console.log(bee() + ant());\nprivate function bee(): i64 { return 1; }\nprivate function ant(): i64 { return 2; }\n",
            );
            check(dir.path(), &["check"]);
            let main = read(dir.path(), "main");
            let bodies = main.split_once("[bodies]\n").expect("bodies").1;
            let at = |what: &str| bodies.find(what).unwrap_or_else(|| panic!("{what}: {main}"));
            assert!(at("statements (") < at("fn ant(") && at("fn ant(") < at("fn bee("), "{main}");
        });
        h.case(
            "interfaces/a test part's arrows and classes are never stored",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", MANIFEST);
                dir.write(
                    "main.en",
                    "console.log(twice(2));\n\nprivate function twice(x: i64): i64 { return x * 2; }\n",
                );
                dir.write(
                    "main.test.en",
                    "test(\"maps\", () => { const xs: i64[] = [1, 2]; expect(xs.map(x => twice(x)).length()).toBe(2); });\nprivate class Peek { private r: &i64[]; public constructor(r: &i64[]) { this.r = r; } public poke(): void { this.r.push(1); } }\n",
                );
                check(dir.path(), &["check", "main.en"]);
                let main = read(dir.path(), "main");
                assert!(!main.contains("arrow"), "{main}");
                assert!(!main.contains("Peek"), "{main}");
            },
        );
        h.case(
            "interfaces/a borrowing class's layout is deferred, a generic class has none",
            || {
                let dir = TempDir::new("interfaces");
                dir.write("enrang.json", MANIFEST);
                dir.write(
                    "main.en",
                    "let xs: i64[] = [1];\nlet w = new Worker(&xs);\nw.poke();\nlet st = new Stack<i64>();\nst.push(1);\nconsole.log(xs.length(), st.size());\n\nprivate class Worker { private r: &i64[]; public constructor(r: &i64[]) { this.r = r; } public poke(): void { this.r.push(1); } }\nprivate class Stack<T> { private items: T[] = []; public push(x: T): void { this.items.push(x); } public size(): isize { return this.items.length(); } }\n",
                );
                check(dir.path(), &["check"]);
                let main = read(dir.path(), "main");
                assert!(main.contains("\nlayout Worker deferred\n"), "{main}");
                assert!(!main.contains("layout Stack"), "{main}");
            },
        );
        h.case(
            "interfaces/an entry outside the project writes nothing outside out/interfaces",
            || {
                let top = TempDir::new("interfaces");
                top.write("proj/enrang.json", MANIFEST);
                top.write("proj/main.en", "console.log(1);\n");
                top.write("elsewhere/x.en", "console.log(2);\n");
                let proj = top.join("proj");
                let abs = top.join("elsewhere/x.en");
                let abs = abs.to_str().expect("a UTF-8 path");
                check(&proj, &["check", abs]);
                check(&proj, &["check", "../elsewhere/x.en"]);
                assert!(!top.join("elsewhere/x.eni").exists());
                assert!(!proj.join("out/elsewhere").exists());
                assert!(!proj.join("out/interfaces/elsewhere").exists());
                let written: Vec<String> = match fs::read_dir(proj.join("out/interfaces")) {
                    Ok(dir) => dir
                        .map(|e| {
                            e.expect("an entry")
                                .file_name()
                                .to_string_lossy()
                                .into_owned()
                        })
                        .collect(),
                    Err(_) => Vec::new(),
                };
                assert!(written.iter().all(|n| n != "x.eni"), "{written:?}");
            },
        );
        h.case(
            "interfaces/a write that fails is skipped, and the check still passes",
            || {
                let dir = project(&[]);
                dir.write("out", "a file where the directory would go\n");
                let ran = check(dir.path(), &["check"]);
                assert_eq!((ran.stdout.as_str(), ran.stderr.as_str()), ("", ""));
            },
        );
    }
}

/// What `fmt`, `init` and `check` do with a file or directory that its mode keeps
/// them from reading or writing. File modes exist only on unix, and bind nobody who
/// runs as root, so each case is skipped with a notice where they cannot be set.
mod modes {
    use enrang_testkit::Harness;

    /// The cases this module registers, for the skip notice.
    const CASES: usize = 6;

    #[cfg(not(unix))]
    pub fn register(_: &mut Harness) {
        enrang_testkit::skip("file modes", CASES, "exist only on unix");
    }

    #[cfg(unix)]
    pub fn register(h: &mut Harness) {
        if bound() {
            unix::register(h);
        } else {
            enrang_testkit::skip("file modes", CASES, "do not bind this user");
        }
    }

    /// Whether a file with no permissions is unreadable here, as it is for anyone but
    /// root.
    #[cfg(unix)]
    fn bound() -> bool {
        let dir = enrang_testkit::TempDir::new("modes");
        let probe = dir.write("probe", "x");
        unix::set_mode(&probe, 0o000);
        let bound = std::fs::read(&probe).is_err();
        unix::set_mode(&probe, 0o644);
        bound
    }

    #[cfg(unix)]
    mod unix {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;
        use std::path::Path;

        use enrang_testkit::{Harness, TempDir};

        use super::super::{CLEAN, UNFORMATTED};
        use crate::support::{Ran, enrang_in, strings};

        /// What `fmt` writes for `UNFORMATTED`.
        const FORMATTED: &str = "const x = 1;\nif (x == 1) { console.log(x); }\n";

        pub fn set_mode(path: &Path, mode: u32) {
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).expect("a mode");
        }

        /// Runs `args` in `dir` with `locked` set to `mode`, then gives it back the
        /// mode it had, so the directory can be removed and read.
        fn run_locked(dir: &TempDir, locked: &str, mode: u32, args: &[&str]) -> Ran {
            let path = dir.join(locked);
            let before = fs::metadata(&path).expect("it exists").permissions();
            set_mode(&path, mode);
            let ran = enrang_in(dir.path(), &strings(args));
            fs::set_permissions(&path, before).expect("its mode back");
            ran
        }

        fn en1305(message: &str) -> String {
            format!(
                "error[EN1305]: {message}\n  = explain: run `enrang explain EN1305`\n\nerror: aborting due to 1 previous error\n"
            )
        }

        fn text(dir: &TempDir, path: &str) -> String {
            fs::read_to_string(dir.join(path)).expect("a file")
        }

        pub fn register(h: &mut Harness) {
            h.case(
                "project/fmt reads every file before it writes one, and an unreadable file stops it",
                || {
                    let dir = TempDir::new("fmt-unreadable");
                    dir.write("src/a.en", UNFORMATTED);
                    dir.write("src/b.en", UNFORMATTED);
                    let ran = run_locked(&dir, "src/b.en", 0o000, &["fmt", "src"]);
                    assert_eq!(
                        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                        (2, "", en1305("cannot read `src/b.en`: permission denied").as_str())
                    );
                    assert_eq!(text(&dir, "src/a.en"), UNFORMATTED, "nothing is written");
                },
            );
            h.case(
                "project/fmt given an unreadable file writes no other",
                || {
                    let dir = TempDir::new("fmt-unreadable-named");
                    dir.write("a.en", UNFORMATTED);
                    dir.write("b.en", UNFORMATTED);
                    let ran = run_locked(&dir, "b.en", 0o000, &["fmt", "a.en", "b.en"]);
                    assert_eq!(
                        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                        (
                            2,
                            "",
                            en1305("cannot read `b.en`: permission denied").as_str()
                        )
                    );
                    assert_eq!(text(&dir, "a.en"), UNFORMATTED, "nothing is written");
                },
            );
            h.case("project/fmt stops at a directory it cannot list", || {
                let dir = TempDir::new("fmt-unlisted");
                dir.write("src/a.en", UNFORMATTED);
                dir.write("src/locked/c.en", UNFORMATTED);
                let ran = run_locked(&dir, "src/locked", 0o000, &["fmt", "src"]);
                assert_eq!(
                    (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                    (
                        2,
                        "",
                        en1305("cannot read `src/locked`: permission denied").as_str()
                    )
                );
                assert_eq!(text(&dir, "src/a.en"), UNFORMATTED, "nothing is written");
            });
            h.case(
                "project/fmt reports a file it cannot write, writes the others, and exits 1",
                || {
                    let dir = TempDir::new("fmt-read-only");
                    dir.write("a.en", UNFORMATTED);
                    dir.write("b.en", UNFORMATTED);
                    let ran = run_locked(&dir, "a.en", 0o444, &["fmt", "a.en", "b.en"]);
                    assert_eq!(
                        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                        (1, "", "error: cannot write to a.en: permission denied\n")
                    );
                    assert_eq!(text(&dir, "a.en"), UNFORMATTED);
                    assert_eq!(text(&dir, "b.en"), FORMATTED);
                },
            );
            h.case(
                "project/init reports a directory it cannot make, and exits 1",
                || {
                    let dir = TempDir::new("init-read-only");
                    fs::create_dir(dir.join("locked")).expect("a directory");
                    let ran = run_locked(&dir, "locked", 0o555, &["init", "locked/hello"]);
                    assert_eq!(
                        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                        (
                            1,
                            "",
                            "error: cannot write to locked/hello/src: permission denied\n"
                        )
                    );
                    assert_eq!(
                        fs::read_dir(dir.join("locked")).expect("it lists").count(),
                        0
                    );
                },
            );
            h.case(
                "project/check reports an unreadable test part, which it never skips",
                || {
                    let dir = TempDir::new("check-unreadable-part");
                    dir.write("m.en", CLEAN);
                    dir.write(
                        "m.test.en",
                        "test(\"one\", () => { expect(1).toBe(1); });\n",
                    );
                    let ran = run_locked(&dir, "m.test.en", 0o000, &["check", "m.en"]);
                    assert_eq!(
                        (ran.code, ran.stdout.as_str(), ran.stderr.as_str()),
                        (
                            2,
                            "",
                            en1305("cannot read `m.test.en`: permission denied").as_str()
                        )
                    );
                },
            );
        }
    }
}
