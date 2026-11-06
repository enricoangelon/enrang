//! The Markdown row-ID extractor, over the real documents and synthetic tables.

use enrang_testkit::{
    DocRow, Harness, ROW_FAMILIES, RowForm, numbered_row_ids, parse_covers, row_ids, workspace_root,
};

use crate::support::read_doc;

fn ids(rows: &[DocRow]) -> Vec<&str> {
    rows.iter().map(|row| row.id.as_str()).collect()
}

const TABLE: &str = "\
Prose that mentions C99 and | a pipe.

| ID | Meaning |
|---|---|
| C01 | first |
| C02 | `T \\| null` |
| Copy | not an ID |
| H01 | another family |

After the table, C98 in prose.
";

pub fn register(h: &mut Harness) {
    // Prefix, the rows, the first and last ID.
    let families: &[(&str, usize, &str, &str)] = &[
        ("C", 17, "C01", "C17"),
        ("H", 26, "H01", "H26"),
        ("MIG-", 14, "MIG-01", "MIG-14"),
        ("REF-", 12, "REF-01", "REF-12"),
        ("FAIL-", 13, "FAIL-01", "FAIL-13"),
        ("ADV-", 52, "ADV-1", "ADV-52"),
    ];
    for &(prefix, count, first, last) in families {
        h.case(format!("rows::real::{prefix}"), move || {
            let family = ROW_FAMILIES
                .iter()
                .find(|family| family.prefix == prefix)
                .expect("TESTING 18 names the family");
            let text = std::fs::read_to_string(workspace_root().join(family.doc))
                .expect("the family's document exists");
            let rows = family.extract(&text).expect("the document parses");
            let found = ids(&rows);
            assert_eq!(found.len(), count, "{found:?}");
            assert_eq!(found.first().copied(), Some(first));
            assert_eq!(found.last().copied(), Some(last));

            // Numbered without a hole, in document order, each on a real table line.
            let width = first.len() - prefix.len();
            for (index, id) in found.iter().enumerate() {
                let number = index + 1;
                let wanted = if prefix == "ADV-" {
                    format!("{prefix}{number}")
                } else {
                    format!("{prefix}{number:0width$}")
                };
                assert_eq!(*id, wanted);
            }
            let lines: Vec<&str> = text.split('\n').collect();
            for row in &rows {
                let line = lines[row.line - 1];
                assert!(line.starts_with("| "), "line {} is {line:?}", row.line);
                let number = row.id.strip_prefix("ADV-").unwrap_or(&row.id);
                assert!(line.starts_with(&format!("| {number} |")), "{line:?}");
            }
        });
    }
    let family_count = families.len();
    h.case("rows::real::every_family_is_checked_above", move || {
        assert_eq!(ROW_FAMILIES.len(), family_count);
    });
    h.case("rows::real::families_are_in_the_named_documents", || {
        for family in ROW_FAMILIES {
            let in_spec = family.doc == "docs/SPEC.md";
            assert_eq!(in_spec, matches!(family.prefix, "C" | "H"), "{family:?}");
        }
        let numbered: Vec<&str> = ROW_FAMILIES
            .iter()
            .filter(|family| matches!(family.form, RowForm::Numbered { .. }))
            .map(|family| family.prefix)
            .collect();
        assert_eq!(numbered, ["ADV-"]);
    });
    h.case("rows::real::prose_mentions_add_nothing", || {
        // SPEC line 730 and others mention these IDs in prose: only tables count.
        let spec = read_doc("SPEC.md");
        assert!(
            spec.lines()
                .any(|line| line.contains("C08") && !line.starts_with('|'))
        );
        assert_eq!(row_ids(&spec, "C").unwrap().len(), 17);
    });
    h.case(
        "rows::real::the_dev_runtime_covers_mention_is_not_a_row",
        || {
            let dev = read_doc("DEV_RUNTIME.md");
            assert!(dev.contains("`//! covers: MIG-07`"));
            let found = row_ids(&dev, "MIG-").unwrap();
            assert_eq!(found.iter().filter(|row| row.id == "MIG-07").count(), 1);
        },
    );

    h.case("rows::table::finds_only_data_rows_of_the_family", || {
        assert_eq!(ids(&row_ids(TABLE, "C").unwrap()), ["C01", "C02"]);
        assert_eq!(ids(&row_ids(TABLE, "H").unwrap()), ["H01"]);
    });
    h.case("rows::table::reports_each_rows_line", || {
        let lines: Vec<usize> = row_ids(TABLE, "C")
            .unwrap()
            .iter()
            .map(|row| row.line)
            .collect();
        assert_eq!(lines, [5, 6]);
    });
    // A document and the IDs of family `C`.
    let tables: &[(&str, &str, &[&str])] = &[
        ("empty_document", "", &[]),
        ("no_tables", "C01 in prose\n", &[]),
        ("no_delimiter_row", "| C01 | a |\n| C02 | b |\n", &[]),
        (
            "no_delimiter_among_many",
            "| C01 |\n| C02 |\n| C03 |\n| C04 |\n",
            &[],
        ),
        (
            "empty_cells_are_no_delimiter",
            "| a |\n|  |\n| C01 |\n",
            &[],
        ),
        ("header_is_not_a_row", "| C01 | a |\n|---|---|\n", &[]),
        (
            "delimiter_with_alignment",
            "| ID | a |\n|:---|---:|\n| C01 | b |\n",
            &["C01"],
        ),
        (
            "spaced_delimiter",
            "| ID | a |\n| --- | --- |\n| C01 | b |\n",
            &["C01"],
        ),
        (
            "two_tables",
            "| ID |\n|---|\n| C01 |\n\ntext\n\n| ID |\n|---|\n| C02 |\n",
            &["C01", "C02"],
        ),
        (
            "no_closing_pipe",
            "| ID | a\n|---|---\n| C01 | b\n",
            &["C01"],
        ),
        ("tight_cell", "|ID|a|\n|---|---|\n|C01|b|\n", &["C01"]),
        ("spaces_in_cell", "| ID |\n|---|\n|    C01    |\n", &["C01"]),
        ("indented_table", "  | ID |\n  |---|\n  | C01 |\n", &["C01"]),
        (
            "only_the_first_cell",
            "| ID | x |\n|---|---|\n| y | C01 |\n",
            &[],
        ),
        ("backticks_are_not_an_id", "| ID |\n|---|\n| `C01` |\n", &[]),
        ("in_a_fence", "```text\n| ID |\n|---|\n| C01 |\n```\n", &[]),
        (
            "after_a_fence",
            "```\ncode\n```\n| ID |\n|---|\n| C01 |\n",
            &["C01"],
        ),
        (
            "broken_by_a_line",
            "| ID |\n|---|\n| C01 |\nprose\n| C02 |\n",
            &["C01"],
        ),
        (
            "word_prefix",
            "| ID |\n|---|\n| Cat |\n| C |\n| C-1 |\n",
            &[],
        ),
        ("one_digit", "| ID |\n|---|\n| C1 |\n", &["C1"]),
        (
            "escaped_pipe_later",
            "| ID | a |\n|---|---|\n| C01 | x \\| y |\n",
            &["C01"],
        ),
    ];
    for &(name, doc, expected) in tables {
        h.case(format!("rows::table::{name}"), move || {
            let found = row_ids(doc, "C").unwrap_or_else(|error| panic!("{error}"));
            assert_eq!(ids(&found), expected);
        });
    }
    // Errors: a document, the expected line, and what the message must say.
    let errors: &[(&str, &str, &str, usize, &str)] = &[
        (
            "garbage_after_digits",
            "| ID |\n|---|\n| C01x |\n",
            "C",
            3,
            "`C01x` is not a `C` row ID",
        ),
        (
            "escaped_pipe_in_the_id_cell",
            "| ID | a |\n|---|---|\n| C01 \\| y | z |\n",
            "C",
            3,
            "`C01 \\| y` is not a `C` row ID",
        ),
        (
            "digits_then_dash",
            "| ID |\n|---|\n| C1-2 |\n",
            "C",
            3,
            "`C1-2` is not a `C` row ID",
        ),
        (
            "duplicate",
            "| ID |\n|---|\n| C01 |\n| C02 |\n| C01 |\n",
            "C",
            5,
            "`C01` is used twice",
        ),
        (
            "duplicate_across_tables",
            "| ID |\n|---|\n| C01 |\n\n| ID |\n|---|\n| C01 |\n",
            "C",
            7,
            "`C01` is used twice",
        ),
        (
            "unterminated_fence",
            "text\n```text\n| ID |\n",
            "C",
            2,
            "never closed",
        ),
        (
            "dashed_family",
            "| ID |\n|---|\n| MIG-1a |\n",
            "MIG-",
            3,
            "`MIG-1a`",
        ),
    ];
    for &(name, doc, prefix, line, message) in errors {
        h.case(format!("rows::error::{name}"), move || {
            let error = row_ids(doc, prefix).expect_err("it must be refused");
            assert_eq!(error.line, line, "{error}");
            assert!(error.message.contains(message), "{error}");
            assert!(
                error.to_string().starts_with(&format!("line {line}: ")),
                "{error}"
            );
        });
    }
    h.case("rows::prefix::a_dashed_family_needs_its_dash", || {
        let doc = "| ID |\n|---|\n| MIG-01 |\n| MIG02 |\n| REF-01 |\n";
        assert_eq!(ids(&row_ids(doc, "MIG-").unwrap()), ["MIG-01"]);
        assert_eq!(ids(&row_ids(doc, "REF-").unwrap()), ["REF-01"]);
        assert_eq!(ids(&row_ids(doc, "ADV-").unwrap()), Vec::<&str>::new());
    });
    register_numbered(h);
    register_families(h);
    register_covers(h);
}

const NUMBERED: &str = "\
## 11. Before

| # | Not this |
|---|---|
| 1 | earlier section |

## 12. Attacks

Prose.

| # | Attack |
|---|---|
| 1 | first |
| 2 | second |

### 12.1 Subsection

| # | More |
|---|---|
| 3 | third |

| Name | Other |
|---|---|
| x | no `#` column |

## 13. After

| # | Not this |
|---|---|
| 9 | later section |
";

fn register_numbered(h: &mut Harness) {
    h.case("rows::numbered::makes_ids_from_the_section_only", || {
        let rows = numbered_row_ids(NUMBERED, "## 12. Attacks", "ADV-").unwrap();
        assert_eq!(ids(&rows), ["ADV-1", "ADV-2", "ADV-3"]);
    });
    h.case("rows::numbered::keeps_lines", || {
        let rows = numbered_row_ids(NUMBERED, "## 12. Attacks", "ADV-").unwrap();
        let lines: Vec<usize> = rows.iter().map(|row| row.line).collect();
        assert_eq!(lines, [13, 14, 20]);
    });
    h.case("rows::numbered::a_subsection_ends_at_its_own_level", || {
        let rows = numbered_row_ids(NUMBERED, "### 12.1 Subsection", "X").unwrap();
        assert_eq!(ids(&rows), ["X3"]);
    });
    let errors: &[(&str, &str, &str, &str)] = &[
        ("no_heading", "text\n", "## 12. Attacks", "no heading"),
        (
            "not_a_heading",
            "12 Attacks\n",
            "12 Attacks",
            "is not a heading",
        ),
        (
            "not_a_number",
            "## H\n\n| # |\n|---|\n| 1a |\n",
            "## H",
            "`1a` in a `#` column",
        ),
        (
            "empty_cell",
            "## H\n\n| # |\n|---|\n|  |\n",
            "## H",
            "`` in a `#` column",
        ),
        (
            "duplicate",
            "## H\n\n| # |\n|---|\n| 1 |\n| 1 |\n",
            "## H",
            "`ADV-1` is used twice",
        ),
        ("unterminated_fence", "## H\n```\n", "## H", "never closed"),
    ];
    for &(name, doc, heading, message) in errors {
        h.case(format!("rows::numbered::error::{name}"), move || {
            let error = numbered_row_ids(doc, heading, "ADV-").expect_err("it must be refused");
            assert!(error.message.contains(message), "{error}");
        });
    }
    h.case("rows::numbered::a_section_without_a_table_is_empty", || {
        assert_eq!(
            numbered_row_ids("## H\n\nProse.\n", "## H", "A").unwrap(),
            []
        );
    });
    h.case(
        "rows::numbered::a_heading_in_a_fence_is_not_the_section",
        || {
            let error = numbered_row_ids("```\n## H\n```\n", "## H", "A").unwrap_err();
            assert!(error.message.contains("no heading"), "{error}");
        },
    );
}

fn register_families(h: &mut Harness) {
    for family in ROW_FAMILIES {
        h.case(
            format!("rows::family::refuses_an_empty_result::{}", family.prefix),
            move || {
                let doc = "## 12. Adversarial scenarios\n\nNo table.\n";
                let error = family.extract(doc).expect_err("no rows must be an error");
                assert!(error.message.contains(family.prefix), "{error}");
            },
        );
    }
}

fn register_covers(h: &mut Harness) {
    let table: &[(&str, &str, &[&str])] = &[
        ("empty", "", &[]),
        ("no_claims", "function main(): void {}\n", &[]),
        ("one", "//! covers: MIG-07\n", &["MIG-07"]),
        (
            "two_lines",
            "//! covers: MIG-07\n//! covers: REF-01\n",
            &["MIG-07", "REF-01"],
        ),
        (
            "comma_list",
            "//! covers: C01, C02,C03\n",
            &["C01", "C02", "C03"],
        ),
        ("indented", "    //! covers: H01\n", &["H01"]),
        (
            "after_code",
            "fn f() {}\n//! covers: H01\nfn g() {}\n",
            &["H01"],
        ),
        ("not_at_line_start", "x //! covers: H01\n", &[]),
        ("plain_comment", "// covers: H01\n", &[]),
        ("no_colon", "//! covers H01\n", &[]),
        ("other_key", "//! covered: H01\n", &[]),
        ("empty_claim", "//! covers:\n//! covers: ,\n", &[]),
        ("crlf", "//! covers: H01\r\n", &["H01"]),
    ];
    for &(name, fixture, expected) in table {
        h.case(format!("rows::covers::{name}"), move || {
            assert_eq!(parse_covers(fixture), expected);
        });
    }
}
