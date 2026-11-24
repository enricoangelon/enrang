//! Explain pages (SPEC 13.1), one source file per code family under `explain/`.
//!
//! A family file is a list of pages:
//!
//! ```text
//! === EN1301
//! --- rule
//! The rule, in prose.
//! --- failing
//! A failing example, or a transcript for a code that no source can trigger.
//! --- fixed
//! The fixed example or transcript.
//! --- typescript
//! The TypeScript perspective; this section is optional.
//! ```
//!
//! A malformed file panics on first use, and the suite reads every page.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::OnceLock;

use crate::codes::Code;

/// Each family and its text. A code's page goes in the file of its family, which
/// is the code without its last two digits.
const FAMILIES: &[(&str, &str)] = &[
    ("EN00", include_str!("../explain/EN00.txt")),
    ("EN01", include_str!("../explain/EN01.txt")),
    ("EN02", include_str!("../explain/EN02.txt")),
    ("EN03", include_str!("../explain/EN03.txt")),
    ("EN04", include_str!("../explain/EN04.txt")),
    ("EN05", include_str!("../explain/EN05.txt")),
    ("EN06", include_str!("../explain/EN06.txt")),
    ("EN07", include_str!("../explain/EN07.txt")),
    ("EN08", include_str!("../explain/EN08.txt")),
    ("EN09", include_str!("../explain/EN09.txt")),
    ("EN10", include_str!("../explain/EN10.txt")),
    ("EN13", include_str!("../explain/EN13.txt")),
];

/// What `enrang explain <code>` prints for a code whose page has arrived.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct ExplainPage {
    pub code: Code,
    pub rule: &'static str,
    /// A failing example: source for a `Compile` code, otherwise a transcript.
    pub failing: &'static str,
    /// The same, fixed.
    pub fixed: &'static str,
    /// The TypeScript perspective, where one is relevant.
    pub typescript: Option<&'static str>,
}

impl fmt::Display for ExplainPage {
    /// The page as the reader sees it, ending in a newline.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}: {}", self.code, self.code.title())?;
        writeln!(f, "\n{}", self.rule)?;
        writeln!(f, "\nFailing:\n\n{}", indented(self.failing))?;
        writeln!(f, "\nFixed:\n\n{}", indented(self.fixed))?;
        if let Some(typescript) = self.typescript {
            writeln!(f, "\nFrom TypeScript:\n\n{typescript}")?;
        }
        Ok(())
    }
}

fn indented(block: &str) -> String {
    let lines: Vec<String> = block
        .split('\n')
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                format!("    {line}")
            }
        })
        .collect();
    lines.join("\n")
}

/// The page of `code`. `None` means it has not arrived: every row must have one by
/// its `since` milestone (TESTING 18), and until then its registry title stands in.
pub fn explain(code: Code) -> Option<&'static ExplainPage> {
    static PAGES: OnceLock<BTreeMap<Code, ExplainPage>> = OnceLock::new();
    PAGES
        .get_or_init(|| {
            let mut pages = BTreeMap::new();
            for &(family, text) in FAMILIES {
                parse_family(family, text)
                    .and_then(|parsed| merge_pages(&mut pages, parsed))
                    .unwrap_or_else(|error| panic!("explain/{family}.txt: {error}"));
            }
            pages
        })
        .get(&code)
}

/// Adds `parsed` to `pages`, refusing a code that has a page already: replacing the
/// first page in silence would lose it.
fn merge_pages(
    pages: &mut BTreeMap<Code, ExplainPage>,
    parsed: Vec<ExplainPage>,
) -> Result<(), String> {
    for page in parsed {
        let code = page.code;
        if pages.insert(code, page).is_some() {
            return Err(format!("{code} has two pages"));
        }
    }
    Ok(())
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Section {
    Rule,
    Failing,
    Fixed,
    TypeScript,
}

fn parse_section(name: &str) -> Option<Section> {
    match name {
        "rule" => Some(Section::Rule),
        "failing" => Some(Section::Failing),
        "fixed" => Some(Section::Fixed),
        "typescript" => Some(Section::TypeScript),
        _ => None,
    }
}

/// A page being read, with sections in the order the format fixes.
struct Draft {
    code: Code,
    line: usize,
    rule: Option<&'static str>,
    failing: Option<&'static str>,
    fixed: Option<&'static str>,
    typescript: Option<&'static str>,
}

impl Draft {
    fn slot(&mut self, section: Section) -> &mut Option<&'static str> {
        match section {
            Section::Rule => &mut self.rule,
            Section::Failing => &mut self.failing,
            Section::Fixed => &mut self.fixed,
            Section::TypeScript => &mut self.typescript,
        }
    }

    fn finish(self) -> Result<ExplainPage, String> {
        let required = |name: &str, value: Option<&'static str>| {
            value.ok_or_else(|| {
                format!(
                    "line {}: the page of {} has no `{name}` section",
                    self.line, self.code
                )
            })
        };
        Ok(ExplainPage {
            code: self.code,
            rule: required("rule", self.rule)?,
            failing: required("failing", self.failing)?,
            fixed: required("fixed", self.fixed)?,
            typescript: self.typescript,
        })
    }
}

/// Parses a family file. Sections keep their text exactly, but for the white space
/// around it, and may not be empty.
fn parse_family(family: &str, text: &'static str) -> Result<Vec<ExplainPage>, String> {
    let mut pages = Vec::new();
    let mut draft: Option<Draft> = None;
    let mut open: Option<(Section, usize, usize)> = None;
    let mut next_start = 0;
    for (index, raw_line) in text.split_inclusive('\n').enumerate() {
        let number = index + 1;
        let start = next_start;
        next_start += raw_line.len();
        let line = raw_line.trim_end_matches('\n');
        let page_head = line.strip_prefix("=== ");
        let section_head = line.strip_prefix("--- ");
        if page_head.is_none() && section_head.is_none() {
            if open.is_none() && !line.trim().is_empty() {
                return Err(format!("line {number}: text outside a section"));
            }
            continue;
        }
        if let (Some(page), Some((section, from, opened_at))) = (draft.as_mut(), open.take()) {
            close_section(page, section, &text[from..start], opened_at)?;
        }
        if let Some(name) = page_head {
            let code = Code::from_name(name)
                .ok_or_else(|| format!("line {number}: `{name}` is not a code"))?;
            if !name.starts_with(family) || name.len() != family.len() + 2 {
                return Err(format!("line {number}: {name} is not in family {family}"));
            }
            if let Some(done) = draft.take() {
                pages.push(done.finish()?);
            }
            draft = Some(Draft {
                code,
                line: number,
                rule: None,
                failing: None,
                fixed: None,
                typescript: None,
            });
        } else if let Some(name) = section_head {
            let section = parse_section(name)
                .ok_or_else(|| format!("line {number}: unknown section `{name}`"))?;
            let page = draft
                .as_mut()
                .ok_or_else(|| format!("line {number}: a section before any page"))?;
            if page.slot(section).is_some() {
                return Err(format!("line {number}: section `{name}` is repeated"));
            }
            open = Some((section, next_start, number));
        }
    }
    if let (Some(page), Some((section, from, opened_at))) = (draft.as_mut(), open.take()) {
        close_section(page, section, &text[from..], opened_at)?;
    }
    if let Some(done) = draft.take() {
        pages.push(done.finish()?);
    }
    Ok(pages)
}

fn close_section(
    page: &mut Draft,
    section: Section,
    body: &'static str,
    opened_at: usize,
) -> Result<(), String> {
    let body = body.trim();
    if body.is_empty() {
        return Err(format!("line {opened_at}: an empty section"));
    }
    *page.slot(section) = Some(body);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const GOOD: &str = "\
=== EN1301
--- rule
The rule.
--- failing
$ enrang fmt
--- fixed
$ enrang check
--- typescript
The view.

=== EN1302
--- rule
Another rule.
--- failing
$ enrang tsc
--- fixed
$ enrang check
";

    #[test]
    fn parses_two_pages_with_their_sections() {
        let pages = parse_family("EN13", GOOD).unwrap();
        assert_eq!(pages.len(), 2);
        assert_eq!(pages[0].code, Code::EN1301);
        assert_eq!(pages[0].rule, "The rule.");
        assert_eq!(pages[0].failing, "$ enrang fmt");
        assert_eq!(pages[0].fixed, "$ enrang check");
        assert_eq!(pages[0].typescript, Some("The view."));
        assert_eq!(pages[1].code, Code::EN1302);
        assert_eq!(pages[1].typescript, None);
    }

    #[test]
    fn keeps_blank_lines_inside_a_section() {
        let text = "=== EN1301\n--- rule\na\n\nb\n--- failing\nc\n--- fixed\nd\n";
        let pages = parse_family("EN13", text).unwrap();
        assert_eq!(pages[0].rule, "a\n\nb");
    }

    #[test]
    fn rejects_malformed_files() {
        let table: &[(&str, &str, &str)] = &[
            ("EN13", "stray\n", "line 1: text outside a section"),
            ("EN13", "--- rule\nx\n", "line 1: a section before any page"),
            ("EN13", "=== EN9999\n", "line 1: `EN9999` is not a code"),
            ("EN13", "=== EN0704\n", "line 1: `EN0704` is not a code"),
            (
                "EN06",
                "=== EN1301\n",
                "line 1: EN1301 is not in family EN06",
            ),
            // Right start, and too short to be the family without its last two digits.
            ("EN1", "=== EN1301\n", "line 1: EN1301 is not in family EN1"),
            (
                "EN13",
                "=== EN1301\n--- bogus\nx\n",
                "line 2: unknown section `bogus`",
            ),
            (
                "EN13",
                "=== EN1301\n--- rule\nx\n--- rule\ny\n",
                "line 4: section `rule` is repeated",
            ),
            (
                "EN13",
                "=== EN1301\n--- rule\n\n--- failing\nx\n",
                "line 2: an empty section",
            ),
            (
                "EN13",
                "=== EN1301\n--- failing\nx\n--- fixed\ny\n",
                "line 1: the page of EN1301 has no `rule` section",
            ),
            (
                "EN13",
                "=== EN1301\n--- rule\nx\n--- fixed\ny\n",
                "line 1: the page of EN1301 has no `failing` section",
            ),
            (
                "EN13",
                "=== EN1301\n--- rule\nx\n--- failing\ny\n",
                "line 1: the page of EN1301 has no `fixed` section",
            ),
            (
                "EN13",
                "=== EN1301\ntext before a section\n",
                "line 2: text outside a section",
            ),
        ];
        for &(family, text, expected) in table {
            let error = parse_family(family, text).expect_err(text);
            assert_eq!(error, expected, "for {text:?}");
        }
    }

    #[test]
    fn merging_two_pages_of_one_code_is_an_error() {
        let once = parse_family("EN13", GOOD).unwrap();
        let again = parse_family(
            "EN13",
            "=== EN1301\n--- rule\nr\n--- failing\nf\n--- fixed\nx\n",
        );
        let mut pages = BTreeMap::new();
        assert_eq!(merge_pages(&mut pages, once), Ok(()));
        assert_eq!(pages.len(), 2);
        assert_eq!(
            merge_pages(&mut pages, again.unwrap()),
            Err("EN1301 has two pages".to_owned())
        );
    }

    #[test]
    fn merging_keeps_each_family_s_pages() {
        let mut pages = BTreeMap::new();
        let first = parse_family(
            "EN13",
            "=== EN1301\n--- rule\nr\n--- failing\nf\n--- fixed\nx\n",
        );
        let second = parse_family(
            "EN13",
            "=== EN1302\n--- rule\ns\n--- failing\ng\n--- fixed\ny\n",
        );
        assert_eq!(merge_pages(&mut pages, first.unwrap()), Ok(()));
        assert_eq!(merge_pages(&mut pages, second.unwrap()), Ok(()));
        assert_eq!(pages[&Code::EN1301].rule, "r");
        assert_eq!(pages[&Code::EN1302].rule, "s");
    }

    #[test]
    fn a_family_may_hold_no_page() {
        assert_eq!(parse_family("EN13", "\n\n").unwrap(), Vec::new());
    }

    #[test]
    fn a_blank_line_between_pages_is_not_text_outside_a_section() {
        assert_eq!(parse_family("EN13", GOOD).unwrap().len(), 2);
    }
}
