//! The human renderer: SPEC 13.1, byte for byte.

use std::collections::BTreeMap;

use enrang_base::{BytePos, FileId, SourceMap, Span};

use crate::diagnostic::{Diagnostic, Entry, Severity};
use crate::snippet::{GutterMark, HelpLine, HelpSection, plan_help};

/// The most unlabelled lines printed between two labelled ones. More become `...`.
const MAX_GAP: u32 = 2;

/// How to render. The default is what golden tests and pipes see.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Default)]
pub struct RenderOpts {
    /// Paint with ANSI colour. With the escape sequences removed the bytes are
    /// those of the colourless output.
    pub color: bool,
}

/// Renders diagnostics, in the given order, and the final `aborting` line when any
/// is an error. Warnings alone abort nothing and test verdicts report through the
/// test runner, so neither gets that line, and that line never counts a note.
///
/// A message, label, entry, help and path can quote anything the user gave, so each
/// goes through [`shown`]. A label or an entry keeps its line breaks, which render as
/// continuation lines; anywhere else a line break is written as an escape.
///
/// Panics if a span lies in no file of `map`, which is a compiler bug.
pub fn render_text(diags: &[Diagnostic], map: &SourceMap, opts: &RenderOpts) -> String {
    let paint = Paint { on: opts.color };
    let mut out = String::new();
    for (index, diag) in diags.iter().enumerate() {
        if index > 0 {
            out.push('\n');
        }
        render_one(diag, map, paint, &mut out);
    }
    let count = |severity| diags.iter().filter(|d| d.severity == severity).count();
    let errors = count(Severity::Error);
    if errors > 0 {
        out.push('\n');
        paint.push(Style::Error, "error", &mut out);
        out.push_str(": aborting due to ");
        out.push_str(&counted(errors, "previous error"));
        let warnings = count(Severity::Warning);
        if warnings > 0 {
            out.push_str("; ");
            out.push_str(&counted(warnings, "warning"));
            out.push_str(" emitted");
        }
        out.push('\n');
    }
    out
}

fn counted(count: usize, noun: &str) -> String {
    let plural = if count == 1 { "" } else { "s" };
    format!("{count} {noun}{plural}")
}

/// Whether a character, printed as it is, could act on the terminal or break the
/// layout: a control character, a bidirectional control (the `Bidi_Control` property),
/// which reorders what follows it on screen, or a line or paragraph separator.
fn disturbs_terminal(c: char) -> bool {
    c.is_control()
        || matches!(
            c,
            '\u{61c}'
                | '\u{200e}'
                | '\u{200f}'
                | '\u{202a}'..='\u{202e}'
                | '\u{2066}'..='\u{2069}'
                | '\u{2028}'
                | '\u{2029}'
        )
}

/// Text that did not come from a source file, as it may reach a terminal: a character
/// that could disturb it is written as an escape. A message can quote any argument
/// or path the user gave, so the renderer passes all of them through this.
pub fn shown(text: &str) -> String {
    text.chars()
        .map(|c| {
            if disturbs_terminal(c) {
                c.escape_default().to_string()
            } else {
                c.to_string()
            }
        })
        .collect()
}

/// Source text as it is shown. Each scalar keeps one column: a tab renders as one
/// space, and so does anything else that could disturb the terminal.
pub(crate) fn display_text(text: &str) -> String {
    text.chars()
        .map(|c| if disturbs_terminal(c) { ' ' } else { c })
        .collect()
}

#[derive(Copy, Clone, Debug)]
enum Style {
    Error,
    Warning,
    Fail,
    Note,
    Bold,
    Gutter,
    Secondary,
    Help,
    Inserted,
    Replaced,
}

impl Style {
    fn code(self) -> &'static str {
        match self {
            Style::Error => "1;31",
            Style::Warning => "1;33",
            Style::Fail => "1;35",
            Style::Note | Style::Bold => "1",
            Style::Gutter | Style::Secondary => "1;34",
            Style::Help => "1;36",
            Style::Inserted => "32",
            Style::Replaced => "33",
        }
    }

    fn of(severity: Severity) -> Style {
        match severity {
            Severity::Error => Style::Error,
            Severity::Warning => Style::Warning,
            Severity::Fail => Style::Fail,
            Severity::Note => Style::Note,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Paint {
    on: bool,
}

impl Paint {
    fn push(self, style: Style, text: &str, out: &mut String) {
        if self.on && !text.is_empty() {
            out.push_str("\x1b[");
            out.push_str(style.code());
            out.push('m');
            out.push_str(text);
            out.push_str("\x1b[0m");
        } else {
            out.push_str(text);
        }
    }
}

/// A label placed on its line, in columns counted from 0.
struct Annotation<'d> {
    primary: bool,
    column: usize,
    width: usize,
    text: &'d str,
}

/// A diagnostic's labels in one file.
struct LabelBlock<'d> {
    file: FileId,
    /// What the location line points at.
    location: BytePos,
    has_primary: bool,
    lines: BTreeMap<u32, Vec<Annotation<'d>>>,
}

/// The primary's file first, then the others in file order.
fn label_blocks<'d>(diag: &'d Diagnostic, map: &SourceMap) -> Vec<LabelBlock<'d>> {
    let mut blocks: Vec<LabelBlock<'d>> = Vec::new();
    let primary = std::iter::once((&diag.primary, true));
    let secondary = diag.secondary.iter().map(|label| (label, false));
    for (label, is_primary) in primary.chain(secondary) {
        if label.span.is_dummy() {
            continue;
        }
        let place = locate(map, label.span);
        let at = blocks.iter().position(|block| block.file == place.file);
        let block = match at {
            Some(index) => &mut blocks[index],
            None => {
                blocks.push(LabelBlock {
                    file: place.file,
                    location: label.span.lo,
                    has_primary: is_primary,
                    lines: BTreeMap::new(),
                });
                blocks.last_mut().expect("just pushed")
            }
        };
        if !block.has_primary {
            block.location = block.location.min(label.span.lo);
        }
        block.lines.entry(place.line).or_default().push(Annotation {
            primary: is_primary,
            column: place.column,
            width: place.width,
            text: &label.text,
        });
    }
    let others = usize::from(blocks.first().is_some_and(|block| block.has_primary));
    blocks[others..].sort_by_key(|block| block.file);
    for annotations in blocks.iter_mut().flat_map(|block| block.lines.values_mut()) {
        annotations.sort_by_key(|a| (!a.primary, a.column, a.width));
    }
    blocks
}

struct Place {
    file: FileId,
    line: u32,
    column: usize,
    width: usize,
}

/// Where a span's marks go. The marks stay on the line the span starts on and stop
/// at its end, and even a zero-width span gets one.
fn locate(map: &SourceMap, span: Span) -> Place {
    let loc = map.loc(span.lo);
    let file = map.file(loc.file);
    let line_start = file.line_starts[loc.line as usize - 1] as usize;
    let line_end = line_start + map.line_text(loc.file, loc.line).len();
    let lo = ((span.lo.0 - file.start.0) as usize).clamp(line_start, line_end);
    let hi = (span.hi.0.saturating_sub(file.start.0) as usize).clamp(lo, line_end);
    let text = &file.text;
    let width = text[text.floor_char_boundary(lo)..text.ceil_char_boundary(hi)]
        .chars()
        .count();
    Place {
        file: loc.file,
        line: loc.line,
        column: loc.col as usize - 1,
        width: width.max(1),
    }
}

fn digits(number: u32) -> usize {
    number.to_string().len()
}

/// The digit count of the largest line number shown anywhere in a diagnostic. With
/// no numbers, `=` still takes the place it has under one-digit numbers.
fn gutter_width(blocks: &[LabelBlock<'_>], helps: &[Vec<HelpSection>]) -> usize {
    let labelled = blocks.iter().flat_map(|block| block.lines.keys().copied());
    let suggested = helps
        .iter()
        .flatten()
        .flat_map(|section| &section.lines)
        .filter_map(|line| line.number);
    labelled.chain(suggested).max().map_or(1, digits)
}

/// Writes the lines of one diagnostic.
struct Writer<'a> {
    paint: Paint,
    width: usize,
    map: &'a SourceMap,
    out: &'a mut String,
}

impl Writer<'_> {
    /// `|`, or the `+` or `~` standing in for it, after a line number or its blank.
    fn gutter(&mut self, number: Option<u32>, gutter: GutterMark) {
        let number = number.map_or(String::new(), |number| number.to_string());
        let head = format!("{number:>width$} ", width = self.width);
        self.paint.push(Style::Gutter, &head, self.out);
        match gutter {
            GutterMark::Bar => self.paint.push(Style::Gutter, "|", self.out),
            GutterMark::Inserted => self.paint.push(Style::Inserted, "+", self.out),
            GutterMark::Replaced => self.paint.push(Style::Replaced, "~", self.out),
        }
    }

    fn bare_gutter(&mut self) {
        self.gutter(None, GutterMark::Bar);
        self.out.push('\n');
    }

    /// A gutter and text, with no space after the gutter if there is no text.
    fn text_line(&mut self, number: Option<u32>, gutter: GutterMark, text: &str) {
        self.gutter(number, gutter);
        if !text.is_empty() {
            self.out.push(' ');
            self.out.push_str(text);
        }
        self.out.push('\n');
    }

    fn location(&mut self, at: BytePos) {
        let loc = self.map.loc(at);
        let path = shown(&self.map.file(loc.file).path.to_string_lossy());
        let pad = " ".repeat(self.width);
        self.out.push_str(&pad);
        self.paint.push(Style::Gutter, "-->", self.out);
        self.out
            .push_str(&format!(" {path}:{}:{}\n", loc.line, loc.col));
    }

    fn source_line(&mut self, file: FileId, line: u32) {
        let text = display_text(self.map.line_text(file, line));
        self.text_line(Some(line), GutterMark::Bar, &text);
    }

    fn annotation(&mut self, annotation: &Annotation<'_>, severity: Severity) {
        let style = if annotation.primary {
            Style::of(severity)
        } else {
            Style::Secondary
        };
        let mark = if annotation.primary { "^" } else { "-" };
        self.gutter(None, GutterMark::Bar);
        self.out.push(' ');
        self.out.push_str(&" ".repeat(annotation.column));
        self.paint
            .push(style, &mark.repeat(annotation.width), self.out);
        let mut lines = annotation.text.split('\n');
        if let Some(first) = lines.next()
            && !first.is_empty()
        {
            self.out.push(' ');
            self.paint.push(style, &shown(first), self.out);
        }
        self.out.push('\n');
        for line in lines {
            self.gutter(None, GutterMark::Bar);
            if !line.is_empty() {
                self.out
                    .push_str(&" ".repeat(annotation.column + annotation.width + 2));
                self.paint.push(style, &shown(line), self.out);
            }
            self.out.push('\n');
        }
    }

    fn label_block(&mut self, block: &LabelBlock<'_>, severity: Severity) {
        self.location(block.location);
        self.bare_gutter();
        let mut previous: Option<u32> = None;
        for (&line, annotations) in &block.lines {
            if let Some(previous) = previous {
                let gap = line - previous - 1;
                if gap > MAX_GAP {
                    self.paint.push(Style::Gutter, "...", self.out);
                    self.out.push('\n');
                } else {
                    for unlabelled in previous + 1..line {
                        self.source_line(block.file, unlabelled);
                    }
                }
            }
            self.source_line(block.file, line);
            for annotation in annotations {
                self.annotation(annotation, severity);
            }
            previous = Some(line);
        }
    }

    fn entry(&mut self, entry: &Entry) {
        let pad = " ".repeat(self.width + 1);
        let head = format!("= {}:", entry.kind.name());
        let continuation = " ".repeat(self.width + 1 + head.len() + 1);
        let mut lines = entry.text.split('\n');
        self.out.push_str(&pad);
        self.paint.push(Style::Bold, &head, self.out);
        if let Some(first) = lines.next()
            && !first.is_empty()
        {
            self.out.push(' ');
            self.out.push_str(&shown(first));
        }
        self.out.push('\n');
        for line in lines {
            if !line.is_empty() {
                self.out.push_str(&continuation);
                self.out.push_str(&shown(line));
            }
            self.out.push('\n');
        }
    }

    fn help_line(&mut self, line: &HelpLine) {
        self.text_line(line.number, line.gutter, &line.text);
        if !line.marks.is_empty() {
            self.gutter(None, GutterMark::Bar);
            self.out.push(' ');
            self.painted_marks(&line.marks);
            self.out.push('\n');
        }
    }

    /// Marks in runs, since `+` and `~` have different colours.
    fn painted_marks(&mut self, marks: &str) {
        let mut rest = marks;
        while let Some(first) = rest.chars().next() {
            let run = rest.find(|c| c != first).unwrap_or(rest.len());
            let style = match first {
                '+' => Style::Inserted,
                _ => Style::Replaced,
            };
            if first == ' ' {
                self.out.push_str(&rest[..run]);
            } else {
                self.paint.push(style, &rest[..run], self.out);
            }
            rest = &rest[run..];
        }
    }

    fn help(&mut self, message: &str, sections: &[HelpSection]) {
        self.paint.push(Style::Help, "help", self.out);
        self.out.push_str(": ");
        self.out.push_str(&shown(message));
        self.out.push('\n');
        for section in sections {
            if let Some(at) = section.location {
                self.location(at);
            }
            self.bare_gutter();
            for line in &section.lines {
                self.help_line(line);
            }
        }
    }

    fn explain(&mut self, command: &str) {
        let pad = " ".repeat(self.width + 1);
        self.out.push_str(&pad);
        self.paint.push(Style::Bold, "= explain:", self.out);
        self.out.push_str(&format!(" run `{command}`\n"));
    }
}

fn render_one(diag: &Diagnostic, map: &SourceMap, paint: Paint, out: &mut String) {
    let blocks = label_blocks(diag, map);
    let home = blocks
        .first()
        .filter(|block| block.has_primary)
        .map(|block| block.file);
    let helps: Vec<Vec<HelpSection>> = diag
        .helps
        .iter()
        .map(|help| plan_help(help, map, home))
        .collect();
    let explain = diag.explain_command();

    let head = match diag.severity {
        Severity::Note => diag.severity.to_string(),
        _ => format!("{}[{}]", diag.severity, diag.code),
    };
    paint.push(Style::of(diag.severity), &head, out);
    out.push_str(": ");
    paint.push(Style::Bold, &shown(&diag.message), out);
    out.push('\n');

    let width = gutter_width(&blocks, &helps);
    let mut writer = Writer {
        paint,
        width,
        map,
        out,
    };
    for block in &blocks {
        writer.label_block(block, diag.severity);
    }
    let more_follows = !diag.entries.is_empty() || !helps.is_empty() || explain.is_some();
    if !blocks.is_empty() && more_follows {
        writer.bare_gutter();
    }
    for entry in &diag.entries {
        writer.entry(entry);
    }
    for (help, sections) in diag.helps.iter().zip(&helps) {
        writer.help(&help.message, sections);
    }
    if let Some(command) = &explain {
        writer.explain(command);
    }
}
