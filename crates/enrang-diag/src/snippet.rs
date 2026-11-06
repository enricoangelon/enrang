//! Turns a help's edits into the lines of its suggestion snippet (SPEC 13.1).
//!
//! Only changed lines are shown, with no gaps between them. Line numbers are the
//! ones each change would occupy if it were the only edit of the block.

use std::collections::BTreeMap;

use enrang_base::{BytePos, FileId, SourceFile, SourceMap};

use crate::diagnostic::{Edit, Help};
use crate::text::display_text;

/// What stands where a snippet line has its `|`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum GutterMark {
    Bar,
    Inserted,
    Replaced,
}

/// One line of a suggestion snippet.
#[derive(Clone, Debug)]
pub(crate) struct HelpLine {
    /// `None` for a command, which is not a line of any file.
    pub(crate) number: Option<u32>,
    pub(crate) gutter: GutterMark,
    pub(crate) text: String,
    /// The `+` and `~` line under `text`, empty if it has none.
    pub(crate) marks: String,
    /// One edit replaced the whole line. In a multi-line edit it then shows `~` in
    /// the gutter and no marks, and on its own it reads like any other replacement.
    whole: bool,
}

/// Consecutive snippet lines, and where they are if not the diagnostic's own file.
#[derive(Clone, Debug)]
pub(crate) struct HelpSection {
    pub(crate) location: Option<BytePos>,
    pub(crate) lines: Vec<HelpLine>,
}

/// Plans a help's snippet. The diagnostic's file comes first and has no location
/// line, since the diagnostic's own location line already names it.
pub(crate) fn plan_help(help: &Help, map: &SourceMap, home: Option<FileId>) -> Vec<HelpSection> {
    let mut sections = Vec::new();
    let mut by_file: BTreeMap<FileId, Vec<&Edit>> = BTreeMap::new();
    let mut commands = Vec::new();
    for edit in &help.edits {
        if edit.span.is_dummy() {
            commands.extend(edit.replacement.split('\n').map(command_line));
        } else {
            let file = map.file_of(edit.span.lo).id;
            by_file.entry(file).or_default().push(edit);
        }
    }
    if !commands.is_empty() {
        sections.push(HelpSection {
            location: None,
            lines: commands,
        });
    }
    if let Some(file) = home
        && let Some(edits) = by_file.remove(&file)
    {
        sections.push(HelpSection {
            location: None,
            lines: plan_file(file, map, &edits),
        });
    }
    for (file, edits) in by_file {
        sections.push(HelpSection {
            location: edits.iter().map(|edit| edit.span.lo).min(),
            lines: plan_file(file, map, &edits),
        });
    }

    let shown: usize = sections.iter().map(|section| section.lines.len()).sum();
    if shown > 1 {
        for line in sections.iter_mut().flat_map(|section| &mut section.lines) {
            if line.whole {
                line.gutter = GutterMark::Replaced;
                line.marks.clear();
            }
        }
    }
    sections
}

fn command_line(text: &str) -> HelpLine {
    HelpLine {
        number: None,
        gutter: GutterMark::Bar,
        text: display_text(text),
        marks: String::new(),
        whole: false,
    }
}

/// An edit in file-relative offsets, with a terminator it replaces by another
/// terminator taken out, so that it no longer reaches the next line.
#[derive(Copy, Clone, Debug)]
struct Change<'e> {
    lo: usize,
    hi: usize,
    text: &'e str,
    /// It removes a whole line, terminator included.
    removes_line: bool,
}

/// A place in the snippet: lines inserted before a line, then that line's changes,
/// then lines inserted after it.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
enum Slot {
    Before,
    Changed,
    After,
}

fn plan_file(file: FileId, map: &SourceMap, edits: &[&Edit]) -> Vec<HelpLine> {
    let view = FileView {
        file: map.file(file),
        map,
    };
    let mut ordered: Vec<&Edit> = edits.to_vec();
    ordered.sort_by_key(|edit| (edit.span.lo, edit.span.hi));

    let mut planned: Vec<Planned> = Vec::new();
    let mut group: Vec<Change<'_>> = Vec::new();
    let mut group_lines = (0, 0);
    for edit in ordered {
        let change = view.change(edit);
        if let Some(inserted) = view.inserted_lines(&change) {
            planned.push(inserted);
            continue;
        }
        let (first, last) = view.lines_of(&change);
        if !group.is_empty() && first > group_lines.1 {
            planned.push(view.plan_group(&group, group_lines));
            group.clear();
        }
        group_lines = if group.is_empty() {
            (first, last)
        } else {
            (group_lines.0, group_lines.1.max(last))
        };
        group.push(change);
    }
    if !group.is_empty() {
        planned.push(view.plan_group(&group, group_lines));
    }
    planned.sort_by_key(|&(key, _)| key);
    planned.into_iter().flat_map(|(_, lines)| lines).collect()
}

/// Snippet lines and the place they sort at.
type Planned = ((u32, Slot), Vec<HelpLine>);

struct FileView<'a> {
    file: &'a SourceFile,
    map: &'a SourceMap,
}

impl FileView<'_> {
    fn line_of(&self, offset: usize) -> u32 {
        let starts = &self.file.line_starts;
        starts
            .partition_point(|&start| start as usize <= offset)
            .max(1) as u32
    }

    fn line_start(&self, line: u32) -> usize {
        self.file.line_starts[line as usize - 1] as usize
    }

    fn line_text(&self, line: u32) -> &str {
        self.map.line_text(self.file.id, line)
    }

    /// The offset just past a line's text, before its terminator.
    fn line_end(&self, line: u32) -> usize {
        self.line_start(line) + self.line_text(line).len()
    }

    fn change<'e>(&self, edit: &'e Edit) -> Change<'e> {
        let start = self.file.start.0;
        let len = self.file.text.len();
        let lo = (edit.span.lo.0.saturating_sub(start) as usize).min(len);
        let hi = (edit.span.hi.0.saturating_sub(start) as usize).clamp(lo, len);
        let text = edit.replacement.as_str();
        let plain = Change {
            lo,
            hi,
            text,
            removes_line: false,
        };
        let hi_line = self.line_of(hi);
        if lo == hi || self.line_start(hi_line) != hi || hi_line == self.line_of(lo) {
            return plain;
        }
        let end = self.line_end(hi_line - 1);
        if let Some(text) = text.strip_suffix('\n') {
            let text = text.strip_suffix('\r').unwrap_or(text);
            Change {
                hi: end,
                text,
                ..plain
            }
        } else if text.is_empty() && lo == self.line_start(self.line_of(lo)) {
            Change {
                hi: end,
                removes_line: true,
                ..plain
            }
        } else {
            plain
        }
    }

    /// The old lines a change reaches.
    fn lines_of(&self, change: &Change<'_>) -> (u32, u32) {
        (self.line_of(change.lo), self.line_of(change.hi))
    }

    /// Plans a change that only adds whole lines, if it is one.
    fn inserted_lines(&self, change: &Change<'_>) -> Option<Planned> {
        if change.lo != change.hi {
            return None;
        }
        let line = self.line_of(change.lo);
        let (slot, first, text) = if change.lo == self.line_start(line)
            && let Some(text) = change.text.strip_suffix('\n')
        {
            (Slot::Before, line, text)
        } else if change.lo == self.line_end(line)
            && let Some(text) = strip_leading_newline(change.text)
        {
            (Slot::After, line + 1, text)
        } else {
            return None;
        };
        let lines = text
            .split('\n')
            .enumerate()
            .map(|(index, text)| HelpLine {
                number: Some(first + index as u32),
                gutter: GutterMark::Inserted,
                text: display_text(text.strip_suffix('\r').unwrap_or(text)),
                marks: String::new(),
                whole: false,
            })
            .collect();
        Some(((line, slot), lines))
    }

    /// Plans changes that share their old lines.
    fn plan_group(&self, group: &[Change<'_>], (first, last): (u32, u32)) -> Planned {
        let start = self.line_start(first);
        let end = self.line_end(last);
        let text = &self.file.text;
        let mut new_text = String::new();
        let mut marks = String::new();
        let mut cursor = start;
        for change in group {
            let lo = text.floor_char_boundary(change.lo.clamp(cursor, end));
            new_text.push_str(&text[cursor..lo]);
            let column = new_text.chars().count();
            let width = change.text.chars().count();
            let replaces = change.hi > change.lo;
            // A pure deletion leaves nothing to underline, so it marks its place.
            let (mark, width) = if replaces {
                ('~', width.max(1))
            } else {
                ('+', width)
            };
            if width > 0 && marks.len() <= column {
                marks.extend(std::iter::repeat_n(' ', column - marks.len()));
                marks.extend(std::iter::repeat_n(mark, width));
            }
            new_text.push_str(change.text);
            cursor = text.ceil_char_boundary(change.hi.clamp(lo, end));
        }
        new_text.push_str(&text[cursor..end]);

        let key = (first, Slot::Changed);
        let removes_line = group.iter().any(|change| change.removes_line);
        if first != last || removes_line || new_text.contains('\n') {
            let lines = new_text
                .split('\n')
                .enumerate()
                .map(|(index, text)| HelpLine {
                    number: Some(first + index as u32),
                    gutter: GutterMark::Replaced,
                    text: display_text(text.strip_suffix('\r').unwrap_or(text)),
                    marks: String::new(),
                    whole: false,
                })
                .collect();
            return (key, lines);
        }
        let whole = matches!(group, [change] if self.replaces_whole_line(change, first));
        let line = HelpLine {
            number: Some(first),
            gutter: GutterMark::Bar,
            text: display_text(&new_text),
            marks,
            whole,
        };
        (key, vec![line])
    }

    /// Whether a change replaces all of a line but perhaps its outer white space.
    fn replaces_whole_line(&self, change: &Change<'_>, line: u32) -> bool {
        let start = self.line_start(line);
        let text = self.line_text(line);
        let indent = text.len() - text.trim_start().len();
        change.hi > change.lo
            && change.lo <= start + indent
            && change.hi >= start + text.trim_end().len()
    }
}

fn strip_leading_newline(text: &str) -> Option<&str> {
    text.strip_prefix('\n')
        .or_else(|| text.strip_prefix("\r\n"))
}
