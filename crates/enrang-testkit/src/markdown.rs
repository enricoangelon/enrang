//! The little of Markdown the extractors need: fenced blocks, headings and the
//! lines between them, numbered as an editor numbers them.

/// A fenced code block.
pub(crate) struct Block<'a> {
    /// The line of the opening fence.
    pub(crate) line: usize,
    /// The first word of the info string, such as `ts`, or empty.
    pub(crate) lang: &'a str,
    /// The lines between the fences, each ending in a newline.
    pub(crate) contents: String,
}

pub(crate) enum Item<'a> {
    Line { line: usize, text: &'a str },
    Block(Block<'a>),
}

/// A fence that the document never closes, at its opening line.
pub(crate) struct UnterminatedFence {
    pub(crate) line: usize,
}

/// Splits a document into blocks and the lines outside them. What is inside a
/// block is data, so a heading or marker in one is not seen as a line.
pub(crate) fn scan(doc: &str) -> Result<Vec<Item<'_>>, UnterminatedFence> {
    let mut items = Vec::new();
    let mut lines = doc.split('\n').enumerate();
    while let Some((index, text)) = lines.next() {
        let line = index + 1;
        let Some(fence) = Fence::opening(text) else {
            items.push(Item::Line { line, text });
            continue;
        };
        let mut contents = String::new();
        let mut closed = false;
        for (_, inner) in lines.by_ref() {
            if fence.closes(inner) {
                closed = true;
                break;
            }
            contents.push_str(fence.strip_indent(inner));
            contents.push('\n');
        }
        if !closed {
            return Err(UnterminatedFence { line });
        }
        items.push(Item::Block(Block {
            line,
            lang: fence.lang,
            contents,
        }));
    }
    Ok(items)
}

/// The level of a heading line, or `None` for any other line.
pub(crate) fn heading_level(text: &str) -> Option<usize> {
    let rest = text.strip_prefix(indent_of(text))?;
    let level = rest.len() - rest.trim_start_matches('#').len();
    let after = &rest[level..];
    ((1..=6).contains(&level) && (after.is_empty() || after.starts_with(' '))).then_some(level)
}

/// The leading spaces of a line, when they are few enough for it to still be a
/// block-level construct.
fn indent_of(text: &str) -> &str {
    let width = text.len() - text.trim_start_matches(' ').len();
    &text[..width.min(3)]
}

struct Fence<'a> {
    mark: char,
    run: usize,
    indent: usize,
    lang: &'a str,
}

impl<'a> Fence<'a> {
    fn opening(text: &'a str) -> Option<Fence<'a>> {
        let indent = text.len() - text.trim_start_matches(' ').len();
        if indent > 3 {
            return None;
        }
        let rest = &text[indent..];
        let mark = rest.chars().next().filter(|c| matches!(c, '`' | '~'))?;
        let run = rest.len() - rest.trim_start_matches(mark).len();
        let info = rest[run..].trim();
        if run < 3 || (mark == '`' && info.contains('`')) {
            return None;
        }
        Some(Fence {
            mark,
            run,
            indent,
            lang: info.split_whitespace().next().unwrap_or(""),
        })
    }

    fn closes(&self, text: &str) -> bool {
        let indent = text.len() - text.trim_start_matches(' ').len();
        let rest = &text[indent..];
        let run = rest.len() - rest.trim_start_matches(self.mark).len();
        indent <= 3 && run >= self.run && rest[run..].trim().is_empty()
    }

    fn strip_indent<'t>(&self, text: &'t str) -> &'t str {
        let spaces = text.len() - text.trim_start_matches(' ').len();
        &text[spaces.min(self.indent)..]
    }
}
