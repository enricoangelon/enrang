//! Document row IDs (TESTING 18).
//!
//! Prose tables have no macro, so their rows carry stable IDs in the first cell,
//! and a retired ID is never reused. Fixtures claim the IDs with
//! `//! covers: MIG-07`. An uncovered ID and an orphan `covers` both fail, which
//! [`crate::gate_covers`] decides from these lists.

use std::collections::BTreeSet;
use std::fmt;

use crate::markdown::{self, Item, heading_level};

/// A table row with a stable ID.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct DocRow {
    pub id: String,
    /// The row's line in the document.
    pub line: usize,
}

/// A problem in a document's tables, at a 1-based line.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct RowError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for RowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for RowError {}

/// How a family's rows spell their IDs.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum RowForm {
    /// The first cell is the whole ID: `C01`, `MIG-07`.
    Literal,
    /// The first cell is a bare number in the `#` column of the tables under a
    /// heading, and the ID is the family's prefix plus that number: `ADV-7`.
    Numbered { heading: &'static str },
}

/// One family of row IDs.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct RowFamily {
    /// The document, relative to the workspace root.
    pub doc: &'static str,
    pub prefix: &'static str,
    pub form: RowForm,
    /// IDs the document retired. They are never reused, so the family's numbers
    /// have a hole where they were.
    pub retired: &'static [&'static str],
}

impl RowFamily {
    /// The family's rows in `doc`. A family with no rows is an error: it would
    /// make the coverage gate over it pass while checking nothing. So is a row
    /// that reuses a retired ID.
    pub fn extract(&self, doc: &str) -> Result<Vec<DocRow>, RowError> {
        let rows = match self.form {
            RowForm::Literal => row_ids(doc, self.prefix)?,
            RowForm::Numbered { heading } => numbered_row_ids(doc, heading, self.prefix)?,
        };
        if let Some(row) = rows
            .iter()
            .find(|row| self.retired.contains(&row.id.as_str()))
        {
            return Err(RowError {
                line: row.line,
                message: format!("row ID `{}` is retired and never reused", row.id),
            });
        }
        if rows.is_empty() {
            return Err(RowError {
                line: 1,
                message: format!("no `{}` rows in {}", self.prefix, self.doc),
            });
        }
        Ok(rows)
    }
}

/// The families TESTING 18 names: `C` (SPEC 4.5, which retires C01-C03), `H`
/// (SPEC 5.8), and `MIG`, `REF`, `FAIL` and `ADV` (`DEV_RUNTIME.md` sections 7, 8,
/// 10 and 12).
pub const ROW_FAMILIES: [RowFamily; 6] = [
    RowFamily {
        doc: "docs/SPEC.md",
        prefix: "C",
        form: RowForm::Literal,
        retired: &["C01", "C02", "C03"],
    },
    RowFamily {
        doc: "docs/SPEC.md",
        prefix: "H",
        form: RowForm::Literal,
        retired: &[],
    },
    RowFamily {
        doc: "docs/DEV_RUNTIME.md",
        prefix: "MIG-",
        form: RowForm::Literal,
        retired: &[],
    },
    RowFamily {
        doc: "docs/DEV_RUNTIME.md",
        prefix: "REF-",
        form: RowForm::Literal,
        retired: &[],
    },
    RowFamily {
        doc: "docs/DEV_RUNTIME.md",
        prefix: "FAIL-",
        form: RowForm::Literal,
        retired: &[],
    },
    RowFamily {
        doc: "docs/DEV_RUNTIME.md",
        prefix: "ADV-",
        form: RowForm::Numbered {
            heading: "## 12. Adversarial scenarios",
        },
        retired: &[],
    },
];

/// The rows whose first cell is `prefix` and then digits, in document order.
pub fn row_ids(doc: &str, prefix: &str) -> Result<Vec<DocRow>, RowError> {
    let items = scan(doc)?;
    let mut rows = Vec::new();
    for table in tables(&items) {
        for &(line, first_cell) in &table.rows {
            let Some(rest) = first_cell.strip_prefix(prefix) else {
                continue;
            };
            if !rest.starts_with(|c: char| c.is_ascii_digit()) {
                continue;
            }
            if !rest.bytes().all(|b| b.is_ascii_digit()) {
                return Err(RowError {
                    line,
                    message: format!("`{first_cell}` is not a `{prefix}` row ID"),
                });
            }
            rows.push(DocRow {
                id: first_cell.to_owned(),
                line,
            });
        }
    }
    reject_duplicates(rows)
}

/// The rows of the `#` tables under the heading whose whole line is `heading`,
/// with IDs made from `prefix` and the number in the first cell.
pub fn numbered_row_ids(doc: &str, heading: &str, prefix: &str) -> Result<Vec<DocRow>, RowError> {
    let items = scan(doc)?;
    let start = items
        .iter()
        .position(|item| matches!(item, Item::Line { text, .. } if *text == heading))
        .ok_or_else(|| RowError {
            line: 1,
            message: format!("no heading `{heading}`"),
        })?;
    let level = heading_level(heading).ok_or_else(|| RowError {
        line: 1,
        message: format!("`{heading}` is not a heading"),
    })?;
    let end = items[start + 1..]
        .iter()
        .position(|item| {
            matches!(item, Item::Line { text, .. }
                if heading_level(text).is_some_and(|other| other <= level))
        })
        .map_or(items.len(), |offset| start + 1 + offset);

    let mut rows = Vec::new();
    for table in tables(&items) {
        if table.first_item < start || table.first_item >= end || table.header != "#" {
            continue;
        }
        for &(line, first_cell) in &table.rows {
            let numeric = !first_cell.is_empty() && first_cell.bytes().all(|b| b.is_ascii_digit());
            if !numeric {
                return Err(RowError {
                    line,
                    message: format!("`{first_cell}` in a `#` column is not a number"),
                });
            }
            rows.push(DocRow {
                id: format!("{prefix}{first_cell}"),
                line,
            });
        }
    }
    reject_duplicates(rows)
}

/// The IDs a fixture claims with `//! covers: MIG-07` lines. One line may list
/// several, separated by commas.
pub fn parse_covers(fixture: &str) -> Vec<String> {
    fixture
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("//! covers:"))
        .flat_map(|ids| ids.split(','))
        .map(str::trim)
        .filter(|id| !id.is_empty())
        .map(str::to_owned)
        .collect()
}

fn scan(doc: &str) -> Result<Vec<Item<'_>>, RowError> {
    markdown::scan(doc).map_err(|fence| RowError {
        line: fence.line,
        message: "this code fence is never closed".to_owned(),
    })
}

fn reject_duplicates(rows: Vec<DocRow>) -> Result<Vec<DocRow>, RowError> {
    let mut seen = BTreeSet::new();
    for row in &rows {
        if !seen.insert(row.id.as_str()) {
            return Err(RowError {
                line: row.line,
                message: format!("row ID `{}` is used twice", row.id),
            });
        }
    }
    Ok(rows)
}

struct Table<'a> {
    /// The index in the scanned items of the header row.
    first_item: usize,
    /// The header's first cell.
    header: &'a str,
    /// The line and first cell of each data row.
    rows: Vec<(usize, &'a str)>,
}

/// The tables of a document: a header row, a delimiter row, then data rows until
/// the first line that is not a row. A lone line of pipes is not a table.
fn tables<'a>(items: &[Item<'a>]) -> Vec<Table<'a>> {
    let mut tables = Vec::new();
    let mut index = 0;
    while index + 1 < items.len() {
        let (Some((_, header)), Some((_, delimiter))) =
            (table_line(&items[index]), table_line(&items[index + 1]))
        else {
            index += 1;
            continue;
        };
        if !is_delimiter(delimiter) {
            index += 1;
            continue;
        }
        let mut table = Table {
            first_item: index,
            header: first_cell(header),
            rows: Vec::new(),
        };
        index += 2;
        while let Some((line, text)) = items.get(index).and_then(table_line) {
            table.rows.push((line, first_cell(text)));
            index += 1;
        }
        tables.push(table);
    }
    tables
}

fn table_line<'a>(item: &Item<'a>) -> Option<(usize, &'a str)> {
    match item {
        Item::Line { line, text } if text.trim_start().starts_with('|') => Some((*line, *text)),
        _ => None,
    }
}

fn is_delimiter(text: &str) -> bool {
    let trimmed = text.trim();
    trimmed.contains('-') && trimmed.chars().all(|c| matches!(c, '|' | '-' | ':' | ' '))
}

/// The text between the first two unescaped pipes. A row's other cells may hold
/// `\|`, and the first cell is trimmed.
fn first_cell(row: &str) -> &str {
    let after_pipe = row.trim_start().strip_prefix('|').unwrap_or(row);
    let mut escaped = false;
    for (at, c) in after_pipe.char_indices() {
        match c {
            '\\' => escaped = !escaped,
            '|' if !escaped => return after_pipe[..at].trim(),
            _ => escaped = false,
        }
    }
    after_pipe.trim()
}
