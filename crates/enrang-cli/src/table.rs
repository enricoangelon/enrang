//! Plain text tables.

/// Left-aligned columns two spaces apart, each row a line with nothing trailing.
pub(crate) fn table(rows: &[Vec<String>]) -> String {
    let mut widths: Vec<usize> = Vec::new();
    for row in rows {
        for (column, cell) in row.iter().enumerate() {
            let width = cell.chars().count();
            match widths.get_mut(column) {
                Some(known) => *known = (*known).max(width),
                None => widths.push(width),
            }
        }
    }
    let mut out = String::new();
    for row in rows {
        let mut line = String::new();
        for (cell, width) in row.iter().zip(&widths) {
            line.push_str(&format!("{cell:<width$}  "));
        }
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::table;

    fn rows(cells: &[&[&str]]) -> Vec<Vec<String>> {
        cells
            .iter()
            .map(|row| row.iter().map(|cell| (*cell).to_owned()).collect())
            .collect()
    }

    #[test]
    fn columns_are_two_spaces_apart_with_nothing_trailing() {
        let text = table(&rows(&[&["a", "b"], &["ccc", "d"]]));
        assert_eq!(text, "a    b\nccc  d\n");
    }

    #[test]
    fn a_cell_is_as_wide_as_its_characters_not_its_bytes() {
        // `éé` is four bytes and two columns: measured in bytes it would pad `ab` to four.
        let text = table(&rows(&[&["éé", "x"], &["ab", "y"]]));
        assert_eq!(text, "éé  x\nab  y\n");
    }
}
