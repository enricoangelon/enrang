//! What the suite shares: the documents and their tables, and short ways to call
//! `resolve`. Expected values come from the documents wherever they state a table,
//! so the code and the documents cannot drift apart.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::sync::OnceLock;

use enrang_base::SourceMap;
use enrang_diag::{Diagnostic, EntryKind, RenderOpts, render_text};
use enrang_target::{
    Arch, CpuLevel, Feature, FeatureSet, FloatStrategy, TargetOpts, TargetSpec, resolve,
};
use enrang_testkit::workspace_root;

pub const I386_TARGETS: [&str; 2] = ["i386-linux", "i386-none"];
pub const X86_64_TARGETS: [&str; 3] = ["x86_64-linux", "x86_64-windows", "x86_64-none"];
pub const VM_TARGETS: [&str; 2] = ["vm64", "vm32"];
pub const NATIVE_TARGETS: [&str; 5] = [
    "x86_64-linux",
    "x86_64-windows",
    "i386-linux",
    "i386-none",
    "x86_64-none",
];
pub const TARGETS: [&str; 7] = [
    "x86_64-linux",
    "x86_64-windows",
    "i386-linux",
    "i386-none",
    "x86_64-none",
    "vm64",
    "vm32",
];

/// A whole document, read once.
pub fn doc(name: &str) -> &'static str {
    static DOCS: OnceLock<BTreeMap<&'static str, String>> = OnceLock::new();
    let docs = DOCS.get_or_init(|| {
        ["SPEC.md", "ARCHITECTURE.md", "DEV_RUNTIME.md", "TESTING.md"]
            .into_iter()
            .map(|name| {
                let path = workspace_root().join("docs").join(name);
                let text = fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("cannot read docs/{name}: {error}"));
                (name, text)
            })
            .collect()
    });
    docs.get(name)
        .unwrap_or_else(|| panic!("docs/{name} is not known to the suite"))
}

/// The depth of a Markdown heading line, 0 for any other line.
fn heading_depth(line: &str) -> usize {
    let hashes = line.bytes().take_while(|b| *b == b'#').count();
    if hashes > 0 && line.as_bytes().get(hashes) == Some(&b' ') {
        hashes
    } else {
        0
    }
}

/// A section by its exact heading line, through to the next heading that is not
/// nested in it. Headings inside code fences do not count.
pub fn section(document: &str, heading: &str) -> &'static str {
    let text = doc(document);
    let depth = heading_depth(heading);
    assert!(depth > 0, "`{heading}` is not a heading");
    let mut start = None;
    let mut offset = 0;
    let mut fenced = false;
    for line in text.split_inclusive('\n') {
        let bare = line.trim_end();
        if bare.starts_with("```") {
            fenced = !fenced;
        }
        if !fenced {
            match start {
                None if bare == heading => start = Some(offset),
                Some(start) if (1..=depth).contains(&heading_depth(bare)) => {
                    return &text[start..offset];
                }
                _ => {}
            }
        }
        offset += line.len();
    }
    match start {
        Some(start) => &text[start..],
        None => panic!("docs/{document} has no heading `{heading}`"),
    }
}

/// A Markdown table, cells trimmed and `\|` unescaped.
#[derive(Clone, Debug)]
pub struct Table {
    pub header: Vec<String>,
    pub rows: Vec<Vec<String>>,
}

impl Table {
    pub fn col(&self, header: &str) -> usize {
        self.header
            .iter()
            .position(|cell| cell == header)
            .unwrap_or_else(|| panic!("no column `{header}` in {:?}", self.header))
    }

    pub fn row(&self, first: &str) -> &[String] {
        self.rows
            .iter()
            .find(|row| row[0] == first)
            .unwrap_or_else(|| panic!("no row `{first}` in a table with {:?}", self.header))
    }

    pub fn get(&self, first: &str, header: &str) -> &str {
        &self.row(first)[self.col(header)]
    }
}

fn cells(line: &str) -> Vec<String> {
    let inner = line.trim().trim_start_matches('|').trim_end_matches('|');
    let mut out = vec![String::new()];
    let mut chars = inner.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'|') => {
                chars.next();
                out.last_mut().unwrap().push('|');
            }
            '|' => out.push(String::new()),
            other => out.last_mut().unwrap().push(other),
        }
    }
    out.iter().map(|cell| cell.trim().to_owned()).collect()
}

/// Every table in `text`, in order.
pub fn tables(text: &str) -> Vec<Table> {
    let mut found = Vec::new();
    let mut current: Vec<&str> = Vec::new();
    for line in text.lines().chain([""]) {
        if line.trim_start().starts_with('|') {
            current.push(line);
        } else if !current.is_empty() {
            assert!(current.len() >= 2, "a table with no rule: {current:?}");
            found.push(Table {
                header: cells(current[0]),
                rows: current[2..].iter().map(|row| cells(row)).collect(),
            });
            current.clear();
        }
    }
    found
}

/// The one table in `text` whose header is `header`.
pub fn table(text: &str, header: &[&str]) -> Table {
    let mut matching = tables(text)
        .into_iter()
        .filter(|table| table.header == header);
    let found = matching
        .next()
        .unwrap_or_else(|| panic!("no table with header {header:?}"));
    assert!(matching.next().is_none(), "two tables with {header:?}");
    found
}

/// The `` `quoted` `` pieces of `text`.
pub fn backticked(text: &str) -> Vec<&str> {
    text.split('`').skip(1).step_by(2).collect()
}

/// The only line of `text` that starts with `prefix`.
pub fn line_starting<'a>(text: &'a str, prefix: &str) -> &'a str {
    let mut lines = text.lines().filter(|line| line.starts_with(prefix));
    let found = lines
        .next()
        .unwrap_or_else(|| panic!("no line starting `{prefix}`"));
    assert!(lines.next().is_none(), "two lines starting `{prefix}`");
    found
}

/// A number as the documents write one, in decimal or `0x` hex with `_` allowed.
pub fn number(text: &str) -> u64 {
    let digits = text.replace('_', "");
    let parsed = match digits.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => digits.parse(),
    };
    parsed.unwrap_or_else(|error| panic!("`{text}` is not a number: {error}"))
}

pub fn level(name: &str) -> CpuLevel {
    CpuLevel::from_name(name).unwrap_or_else(|| panic!("no level `{name}`"))
}

pub fn feature(name: &str) -> Feature {
    Feature::from_name(name).unwrap_or_else(|| panic!("no feature `{name}`"))
}

pub fn features(names: &[&str]) -> FeatureSet {
    let list: Vec<Feature> = names.iter().map(|name| feature(name)).collect();
    FeatureSet::of(&list)
}

/// The rungs of the level table in ARCHITECTURE 8.2, each with its whole set of
/// feature names. A cell starting with `+` adds to the row above.
pub fn arch_levels() -> &'static Vec<(String, BTreeSet<String>)> {
    static LEVELS: OnceLock<Vec<(String, BTreeSet<String>)>> = OnceLock::new();
    LEVELS.get_or_init(|| {
        let table = table(
            section("ARCHITECTURE.md", "### 8.2 The `--cpu` ladder"),
            &[
                "Level",
                "`FeatureSet`",
                "Codegen uses",
                "Startup check (floor code)",
            ],
        );
        let mut rows: Vec<(String, BTreeSet<String>)> = Vec::new();
        for row in &table.rows {
            let name = row[0].trim_matches('`').to_owned();
            let cell = &row[1];
            let quoted = backticked(cell);
            assert_eq!(quoted.len(), 1, "one list of features in `{cell}`");
            let mut set = if cell.starts_with('+') {
                rows.last().expect("a row above").1.clone()
            } else {
                BTreeSet::new()
            };
            set.extend(quoted[0].split_whitespace().map(str::to_owned));
            rows.push((name, set));
        }
        assert_eq!(rows.len(), CpuLevel::ALL.len());
        rows
    })
}

/// The whole set ARCHITECTURE 8.2 gives `level`.
pub fn arch_level_set(level: CpuLevel) -> &'static BTreeSet<String> {
    let found = arch_levels()
        .iter()
        .find(|(name, _)| name == level.name())
        .unwrap_or_else(|| panic!("no row for `{}` in 8.2", level.name()));
    &found.1
}

/// Which architecture's ladder a target's `--cpu` climbs, read from the table's
/// `i386-*` and `x86_64-*` families.
pub fn arch_of(target: &str) -> Arch {
    if target.starts_with("i386-") {
        Arch::I386
    } else if target.starts_with("x86_64-") {
        Arch::X86_64
    } else {
        assert!(target.starts_with("vm"), "`{target}` is in no family");
        Arch::Mir
    }
}

/// The float strategy a build gets with no `--float` (SPEC 9.3 and 10.1, ARCHITECTURE
/// 2.7): on `i386-*`, `soft` at `i386` and `i486`, `x87` at `i586` and `i686`, `sse2`
/// at `sse2`; `sse2` on `x86_64-*`; the host's floats in the VM.
pub fn default_float(arch: Arch, level: CpuLevel) -> FloatStrategy {
    match (arch, level) {
        (Arch::Mir, _) => FloatStrategy::Host,
        (_, CpuLevel::I386 | CpuLevel::I486) => FloatStrategy::Soft,
        (_, CpuLevel::I586 | CpuLevel::I686) => FloatStrategy::X87,
        (_, CpuLevel::Sse2 | CpuLevel::X86_64) => FloatStrategy::Sse2,
    }
}

/// SPEC 10.1's sentence naming the default float of each level, as `(strategy,
/// levels)` pairs in its order.
pub fn spec_default_floats() -> Vec<(String, Vec<String>)> {
    let text = section("SPEC.md", "### 10.1 The option");
    let lead = "The default float strategy follows the level (section 9.3): ";
    let (_, rest) = text
        .split_once(lead)
        .unwrap_or_else(|| panic!("SPEC 10.1 no longer says `{lead}`"));
    let (list, _) = rest.split_once('.').expect("the sentence ends");
    list.split(", ")
        .map(|clause| {
            let (strategy, levels) = clause
                .split_once(" at ")
                .unwrap_or_else(|| panic!("`{clause}` is not `strategy at levels`"));
            let levels = backticked(levels).into_iter().map(str::to_owned).collect();
            (strategy.trim_matches('`').to_owned(), levels)
        })
        .collect()
}

pub fn opts_with(cpu: Option<&str>, float: Option<&str>) -> TargetOpts {
    TargetOpts {
        cpu: cpu.map(str::to_owned),
        float: float.map(str::to_owned),
        ..TargetOpts::default()
    }
}

pub fn cpu(level: &str) -> TargetOpts {
    opts_with(Some(level), None)
}

pub fn float(strategy: &str) -> TargetOpts {
    opts_with(None, Some(strategy))
}

/// The result of a resolve that must succeed.
pub fn ok(target: &str, opts: &TargetOpts) -> (TargetSpec, Vec<Diagnostic>) {
    resolve(target, opts).unwrap_or_else(|diag| {
        panic!(
            "resolve({target}, {opts:?}) failed:\n{}",
            render(std::slice::from_ref(&diag))
        )
    })
}

pub fn spec(target: &str, opts: &TargetOpts) -> TargetSpec {
    ok(target, opts).0
}

pub fn default_spec(target: &str) -> TargetSpec {
    spec(target, &TargetOpts::default())
}

/// The error of a resolve that must fail.
pub fn err(target: &str, opts: &TargetOpts) -> Diagnostic {
    match resolve(target, opts) {
        Ok((spec, _)) => panic!("resolve({target}, {opts:?}) succeeded: {spec:#?}"),
        Err(diag) => diag,
    }
}

pub fn render(diags: &[Diagnostic]) -> String {
    render_text(diags, &SourceMap::new(), &RenderOpts::default())
}

/// The texts of a diagnostic's `= note:` entries.
pub fn notes(diag: &Diagnostic) -> Vec<&str> {
    diag.entries
        .iter()
        .filter(|entry| entry.kind == EntryKind::Note)
        .map(|entry| entry.text.as_str())
        .collect()
}

/// Everything a diagnostic says, to search for words a reader must see.
pub fn all_text(diag: &Diagnostic) -> String {
    render(std::slice::from_ref(diag))
}

/// Asserts `diag` says each of `words`.
pub fn says(diag: &Diagnostic, words: &[&str]) {
    let text = all_text(diag);
    for word in words {
        assert!(text.contains(word), "`{word}` is not in:\n{text}");
    }
}

/// The feature a word in SPEC 10.1's `Code may assume` column stands for. `None`
/// for words naming what no [`Feature`] tracks.
pub fn spec_word(word: &str) -> Vec<Feature> {
    let names: &[&str] = match word.trim() {
        "FPU" => &["fpu"],
        "SSE" => &["sse"],
        "CPUID" => &["cpuid"],
        "CR4" => &["cr4"],
        "CMOV" => &["cmov"],
        "BSWAP" => &["bswap"],
        "CMPXCHG" => &["cmpxchg"],
        "XADD" => &["xadd"],
        "RDTSC" => &["rdtsc"],
        "multi-byte NOP" => &["nopl"],
        "INVLPG" => &["invlpg"],
        "CMPXCHG8B" => &["cmpxchg8b"],
        "MSRs" => &["msr"],
        "FCOMI family" => &["fcomi"],
        "SSE2 scalar" | "SSE2" => &["sse2"],
        "FXSAVE" => &["fxsave"],
        "NOPL in long mode" => &["nopl"],
        "POPCNT" => &["popcnt"],
        "SSE3+" => &["sse3", "ssse3", "sse4.1", "sse4.2"],
        "`--float=sse2` allowed" | "CMPXCHG16B" | "long-mode LAHF/SAHF" => &[],
        other => panic!("SPEC 10.1 uses a word the suite cannot read: `{other}`"),
    };
    names.iter().map(|name| feature(name)).collect()
}

/// What one row of SPEC 10.1 says about features.
#[derive(Debug, Default, Clone)]
pub struct SpecRow {
    /// Features this row adds (`+ ...`) or lists as assumed.
    pub adds: BTreeSet<Feature>,
    /// Features this row says code must not assume.
    pub denies: BTreeSet<Feature>,
    /// The row starts from the one above it.
    pub cumulative: bool,
}

/// The rows of SPEC 10.1's level table, by level name in table order.
pub fn spec_levels() -> &'static Vec<(String, SpecRow)> {
    static LEVELS: OnceLock<Vec<(String, SpecRow)>> = OnceLock::new();
    LEVELS.get_or_init(|| {
        let table = table(
            section("SPEC.md", "### 10.1 The option"),
            &["Level", "Code may assume", "Covers", "Startup check"],
        );
        let mut rows = Vec::new();
        for row in &table.rows {
            let name = row[0].trim_matches('`').to_owned();
            let cell = row[1].as_str();
            let mut parsed = SpecRow::default();
            if let Some(added) = cell.strip_prefix("+ ") {
                parsed.cumulative = true;
                parsed.adds.extend(added.split(", ").flat_map(spec_word));
            } else if let Some((_, denied)) = cell.split_once("; no ") {
                parsed.denies.extend(denied.split(", ").flat_map(spec_word));
            } else if let Some((assumed, denied)) = cell.split_once(". **Not** ") {
                parsed.adds.extend(assumed.split(", ").flat_map(spec_word));
                parsed.denies.extend(denied.split(", ").flat_map(spec_word));
            } else {
                panic!("SPEC 10.1 row `{name}` has a shape the suite cannot read: `{cell}`");
            }
            rows.push((name, parsed));
        }
        assert_eq!(rows.len(), CpuLevel::ALL.len());
        rows
    })
}

/// One alias as SPEC 10.1 states it.
#[derive(Clone, Debug)]
pub struct SpecAlias {
    pub name: String,
    pub level32: String,
    pub on_64: SpecOn64,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SpecOn64 {
    /// Named as resolving to `x86-64`.
    Whole,
    /// Named as resolving to `x86-64`, with a note about its 64-bit models.
    SomeModels,
    /// Named as EN0912, because those chips have no long mode.
    NoLongMode,
    /// Not named: it resolves to an `i386`-family level, so it is EN0912 too.
    Family,
}

/// Every alias of SPEC 10.1, in its order, read from its two sentences.
pub fn spec_aliases() -> &'static Vec<SpecAlias> {
    static ALIASES: OnceLock<Vec<SpecAlias>> = OnceLock::new();
    ALIASES.get_or_init(|| {
        let line = line_starting(
            section("SPEC.md", "### 10.1 The option"),
            "Aliases print a note",
        );
        let (_, rest) = line.split_once("resolved level: ").expect("the alias list");
        let (list32, rest) = rest
            .split_once(" on 32-bit targets. On 64-bit targets ")
            .expect("the 32-bit list and the 64-bit sentence");
        let (list64, _) = rest.split_once(". `native`").expect("the 64-bit sentence");

        let clauses: Vec<&str> = list64.split("; ").collect();
        assert_eq!(clauses.len(), 3, "three 64-bit clauses in `{list64}`");
        let whole = backticked(clauses[0]);
        assert!(clauses[0].contains("resolve to `x86-64`"), "{}", clauses[0]);
        let some = backticked(clauses[1]);
        assert!(
            clauses[1].contains("only their 64-bit models"),
            "{}",
            clauses[1]
        );
        let none = backticked(clauses[2]);
        assert!(clauses[2].contains("EN0912"), "{}", clauses[2]);
        assert!(clauses[2].contains("no long mode"), "{}", clauses[2]);

        let mut aliases = Vec::new();
        for clause in list32.split("; ") {
            let (names, target) = clause.rsplit_once(" to ").expect("`names to level`");
            let target = target.trim_matches('`');
            for name in backticked(names) {
                let on_64 = if whole.contains(&name) {
                    SpecOn64::Whole
                } else if some.contains(&name) {
                    SpecOn64::SomeModels
                } else if none.contains(&name) {
                    SpecOn64::NoLongMode
                } else {
                    SpecOn64::Family
                };
                aliases.push(SpecAlias {
                    name: name.to_owned(),
                    level32: target.to_owned(),
                    on_64,
                });
            }
        }
        assert_eq!(aliases.len(), 21, "SPEC 10.1 lists 21 aliases");
        aliases
    })
}
