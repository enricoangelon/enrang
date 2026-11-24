//! Comments and blank lines, read from the source between token spans: their text
//! and order never change, `//` comments move to the code's indentation, trailing
//! comments get two spaces, `*` block comments are re-indented, blank lines are kept
//! at most one in a row, and `// enrang-fmt-ignore` keeps a statement or declaration
//! as written (SPEC 12.5 Comments, Blank lines, Opting out).
//!
//! Comments are printed in source order, each once: a sequence (a block, a body, a
//! file) places those before an element on lines of their own, makes those after an
//! element on its line its trailing comments, and keeps a block comment that comes
//! before code on its line inline before that code; anywhere else a comment goes
//! before the next node that has a span. Every choice depends only on what shares a
//! line with the comment, which the output keeps, so a second run makes the same.

use enrang_base::Span;

use crate::token::Token;

use super::Printer;
use super::doc::{
    Doc, GroupId, break_parent, concat, group_with, hardline, if_break, indent, line, line_suffix,
    nil, text, verbatim,
};

/// SPEC 12.5 "Opting out": keeps the next statement or declaration as written.
const IGNORE: &str = "// enrang-fmt-ignore";

/// A comment of the source, by its global positions.
#[derive(Copy, Clone, Debug)]
pub(crate) struct Comment {
    pub lo: u32,
    pub hi: u32,
    /// `/* */`, against `//`.
    pub block: bool,
}

/// Every comment of `text`, whose first byte is at global position `start`, found in
/// the gaps between `tokens`. A gap of a file that lexes cleanly holds only white
/// space and comments.
pub(crate) fn scan(text: &str, start: u32, tokens: &[Token]) -> Vec<Comment> {
    let mut found = Vec::new();
    let mut gap_lo = 0usize;
    for token in tokens {
        let gap_hi = (token.span.lo.0.saturating_sub(start) as usize).min(text.len());
        scan_gap(text, gap_lo, gap_hi, start, &mut found);
        gap_lo = gap_lo.max((token.span.hi.0.saturating_sub(start) as usize).min(text.len()));
    }
    scan_gap(text, gap_lo, text.len(), start, &mut found);
    found
}

fn scan_gap(text: &str, lo: usize, hi: usize, start: u32, found: &mut Vec<Comment>) {
    let Some(gap) = text.get(lo..hi) else {
        return;
    };
    let mut at = 0;
    while at < gap.len() {
        let rest = &gap[at..];
        let (len, block) = if rest.starts_with("//") {
            (rest.find('\n').unwrap_or(rest.len()), false)
        } else if let Some(body) = rest.strip_prefix("/*") {
            (body.find("*/").map_or(rest.len(), |len| len + 4), true)
        } else {
            at += rest.chars().next().map_or(1, char::len_utf8);
            continue;
        };
        let global = |offset: usize| start + u32::try_from(lo + offset).unwrap_or(u32::MAX);
        found.push(Comment {
            lo: global(at),
            hi: global(at + len),
            block,
        });
        at += len;
    }
}

/// What separates the next piece of a sequence from the last one.
#[derive(Copy, Clone, Eq, PartialEq)]
enum Gap {
    /// Nothing printed yet.
    Start,
    /// A line break, and a blank line when the source had one.
    Line,
    /// A space: the last piece was a block comment followed by code on its line.
    Space,
}

/// One element of a sequence: its span (decorators included), and its kind.
pub(crate) struct SeqEl<K> {
    pub span: Span,
    /// Where to look for a blank line before it, when that is not `span.lo`: the
    /// place an import had before sorting.
    pub blank_at: Option<u32>,
    /// A statement or declaration, which `// enrang-fmt-ignore` keeps as written; an
    /// enum case or a `match` arm is one element of a table, never the unit.
    pub ignorable: bool,
    pub kind: K,
}

impl<K> SeqEl<K> {
    pub(crate) fn new(span: Span, kind: K) -> SeqEl<K> {
        SeqEl {
            span,
            blank_at: None,
            ignorable: true,
            kind,
        }
    }

    /// An element of a table, which `// enrang-fmt-ignore` does not apply to.
    pub(crate) fn row(span: Span, kind: K) -> SeqEl<K> {
        SeqEl {
            ignorable: false,
            ..SeqEl::new(span, kind)
        }
    }
}

/// A printed sequence, without its braces.
pub(crate) struct Seq {
    /// The elements and comments, one per line, with no line break before the first
    /// or after the last.
    pub doc: Doc,
    /// The trailing comment of the opening brace's line.
    pub after_open: Doc,
    /// How many elements it holds.
    pub count: usize,
    /// The group of the braces around it, which [`Printer::braces`] makes.
    pub id: GroupId,
}

impl Printer<'_> {
    /// The text of a comment as printed: a `//` comment loses its trailing spaces, a
    /// block comment whose every later line starts with `*` puts each at the code's
    /// indentation plus one space, and any other block comment is as written.
    pub(super) fn comment_doc(&self, comment: &Comment) -> Doc {
        let raw = self.slice(comment.lo, comment.hi);
        if !comment.block {
            return text(raw.trim_end());
        }
        if !raw.contains('\n') {
            return text(raw);
        }
        let mut lines = raw.split('\n');
        let first = lines.next().unwrap_or("");
        let rest: Vec<&str> = lines.collect();
        if rest.iter().all(|line| line.trim_start().starts_with('*')) {
            let mut parts = vec![text(first.trim_end())];
            for line in rest {
                parts.push(hardline());
                parts.push(text(format!(" {}", line.trim())));
            }
            return concat(parts);
        }
        verbatim(raw)
    }

    fn next(&self) -> Option<Comment> {
        self.comments.get(self.next_comment).copied()
    }

    /// The comments not yet printed that start before `pos`.
    pub(super) fn take_before(&mut self, pos: u32) -> Vec<Comment> {
        let mut taken = Vec::new();
        while let Some(comment) = self.next().filter(|comment| comment.lo < pos) {
            taken.push(comment);
            self.next_comment += 1;
        }
        taken
    }

    /// Drops the comments inside text printed as written, which carries them.
    pub(super) fn skip_until(&mut self, pos: u32) {
        while self.next().is_some_and(|comment| comment.lo < pos) {
            self.next_comment += 1;
        }
    }

    /// Whether a comment not yet printed starts in `lo..hi`.
    pub(super) fn has_comment_in(&self, lo: u32, hi: u32) -> bool {
        self.comments[self.next_comment..]
            .iter()
            .any(|comment| comment.lo >= lo && comment.lo < hi)
    }

    /// Whether only spaces lie between the start of `comment`'s line and it.
    pub(super) fn own_line(&self, comment: &Comment) -> bool {
        let before = self.slice(self.start, comment.lo);
        before
            .trim_end_matches([' ', '\t', '\r'])
            .chars()
            .next_back()
            .is_none_or(|c| c == '\n')
    }

    /// Whether only spaces lie between `comment` and the end of its line.
    pub(super) fn ends_line(&self, comment: &Comment) -> bool {
        !comment.block || self.newline_after(comment.hi)
    }

    /// Whether the next character after `pos` that is not a space ends a line, or
    /// there is none.
    pub(super) fn newline_after(&self, pos: u32) -> bool {
        let after = self.slice(pos, self.start + self.src.len() as u32);
        after
            .trim_start_matches([' ', '\t', '\r'])
            .chars()
            .next()
            .is_none_or(|c| c == '\n')
    }

    /// Whether white space holding a blank line comes right before `pos`.
    pub(super) fn blank_before(&self, pos: u32) -> bool {
        if pos == 0 {
            return false;
        }
        let before = self.slice(self.start, pos);
        let space = before.len() - before.trim_end().len();
        before[before.len() - space..].matches('\n').count() >= 2
    }

    /// Whether every comment not yet printed before `pos` is a block comment with
    /// code after it on its line, so that all of them stay on the line of `pos`.
    pub(super) fn inline_before(&self, pos: u32) -> bool {
        self.comments[self.next_comment..]
            .iter()
            .take_while(|comment| comment.lo < pos)
            .all(|comment| !self.ends_line(comment))
    }

    /// The comments before `pos`, printed before the node there: a block comment
    /// followed by code on its line stays on that line, any other ends its line.
    pub(super) fn leading(&mut self, pos: u32) -> Doc {
        let mut parts = Vec::new();
        for comment in self.take_before(pos) {
            parts.push(self.comment_doc(&comment));
            if self.ends_line(&comment) {
                parts.push(hardline());
            } else {
                parts.push(text(" "));
            }
        }
        concat(parts)
    }

    /// The comment before `pos` when it follows code on its line and ends that line,
    /// as `// c` does in `const x = // c`: it is that code's trailing comment, two
    /// spaces after it, and what is at `pos` goes on the next line (SPEC 12.5
    /// Comments). `None` when the next comment is no such comment; the node at `pos`
    /// then takes its comments as leading ones.
    pub(super) fn code_comment(&mut self, pos: u32) -> Option<Doc> {
        if !self.real || pos == 0 {
            return None;
        }
        let comment = self.next().filter(|comment| comment.lo < pos)?;
        if self.own_line(&comment) || !self.ends_line(&comment) {
            return None;
        }
        self.next_comment += 1;
        Some(self.trailing_doc(&[comment]))
    }

    /// `head`, then `node` at `pos` after `sep`; or, when a comment follows `head`'s
    /// code on its line ([`Printer::code_comment`]), `head`, that comment, and `node`
    /// on the next line, indented 2 more as a continuation.
    pub(super) fn then_node(
        &mut self,
        head: Doc,
        sep: &str,
        pos: u32,
        node: impl FnOnce(&mut Self) -> Doc,
    ) -> Doc {
        match self.code_comment(pos) {
            Some(trailing) => {
                let node = node(self);
                concat(vec![head, trailing, indent(concat(vec![hardline(), node]))])
            }
            None => {
                let node = node(self);
                concat(vec![head, text(sep), node])
            }
        }
    }

    /// The comments on `after`'s line, after it and an optional `,` or `;`, when the
    /// last of them ends the line: the trailing comments of what ends at `after`.
    pub(super) fn take_trailing(&mut self, after: u32, allow_sep: bool) -> Vec<Comment> {
        if after == 0 {
            return Vec::new();
        }
        let mut taken = Vec::new();
        let mut cursor = after;
        let mut at = self.next_comment;
        while let Some(&comment) = self.comments.get(at) {
            if comment.lo < cursor {
                break;
            }
            let gap = self.slice(cursor, comment.lo).trim_matches([' ', '\t']);
            let sep_ok = allow_sep && taken.is_empty() && (gap == "," || gap == ";");
            if !gap.is_empty() && !sep_ok {
                break;
            }
            taken.push(comment);
            cursor = comment.hi;
            at += 1;
            if !comment.block {
                break;
            }
        }
        match taken.last() {
            Some(last) if self.ends_line(last) => {
                self.next_comment = at;
                taken
            }
            _ => Vec::new(),
        }
    }

    /// Trailing comments: two spaces after the code, then the comments, which never
    /// count toward the width, and a line break after them.
    pub(super) fn trailing_doc(&self, comments: &[Comment]) -> Doc {
        if comments.is_empty() {
            return nil();
        }
        concat(vec![self.trailing_suffix(comments), break_parent()])
    }

    /// [`Printer::trailing_doc`] without the break it forces, for a layout that
    /// already ends the line.
    fn trailing_suffix(&self, comments: &[Comment]) -> Doc {
        let mut parts = vec![text(" ")];
        for comment in comments {
            parts.push(text(" "));
            parts.push(self.comment_doc(comment));
        }
        line_suffix(concat(parts))
    }

    /// The comments before the closer of a list at `close`, one document each, to go
    /// after a line break or a space; a `//` comment breaks the list.
    pub(super) fn dangling(&mut self, close: u32) -> Vec<Doc> {
        let mut docs = Vec::new();
        for comment in self.take_before(close) {
            let doc = self.comment_doc(&comment);
            if comment.block {
                docs.push(doc);
            } else {
                docs.push(concat(vec![doc, break_parent()]));
            }
        }
        docs
    }

    pub(super) fn is_ignore(&self, comment: &Comment) -> bool {
        !comment.block && self.slice(comment.lo, comment.hi).trim_end() == IGNORE
    }

    /// What the parser left after an error, which `fmt` never meets in a file that
    /// parses: its source as written, comments included, or nothing.
    pub(super) fn error_text(&mut self, span: Span) -> Doc {
        if self.has_place(span) {
            self.as_written(span)
        } else {
            nil()
        }
    }

    /// The source of `span` as written, with the comments inside it.
    pub(super) fn as_written(&mut self, span: Span) -> Doc {
        self.skip_until(span.hi.0);
        verbatim(self.slice(span.lo.0, span.hi.0))
    }

    /// The elements of a sequence one per line, with the comments before, between and
    /// after them, a blank line wherever the source had one except before the first,
    /// and elements after `// enrang-fmt-ignore` as written. `open` is the position
    /// after the opening brace and `close` that of the closing one, when known.
    pub(super) fn seq<K>(
        &mut self,
        open: Option<u32>,
        close: Option<u32>,
        els: &[SeqEl<K>],
        allow_sep: bool,
        mut build: impl FnMut(&mut Self, &K) -> Doc,
    ) -> Seq {
        let id = self.group_id();
        let after_open = match open {
            Some(pos) if self.real => {
                let found = self.take_trailing(pos, false);
                self.trailing_doc(&found)
            }
            _ => nil(),
        };
        let mut parts = Vec::new();
        let mut gap = Gap::Start;
        for el in els {
            let place = self.has_place(el.span);
            let mut ignore = false;
            if place {
                let comments = self.take_before(el.span.lo.0);
                ignore = el.ignorable && comments.iter().any(|comment| self.is_ignore(comment));
                self.comment_run(&mut parts, &mut gap, &comments, None);
            }
            let blank_at = if place {
                el.blank_at.unwrap_or(el.span.lo.0)
            } else {
                0
            };
            self.separate(&mut parts, gap, blank_at);
            let doc = if ignore {
                self.as_written(el.span)
            } else {
                build(self, &el.kind)
            };
            parts.push(doc);
            if place {
                let found = self.take_trailing(el.span.hi.0, allow_sep);
                parts.push(self.trailing_doc(&found));
            }
            gap = Gap::Line;
        }
        if let Some(close) = close.filter(|_| self.real) {
            let comments = self.take_before(close);
            let braces = open.is_some().then_some(id);
            self.comment_run(&mut parts, &mut gap, &comments, braces);
        }
        Seq {
            doc: concat(parts),
            after_open,
            count: els.len(),
            id,
        }
    }

    /// The comments between two elements of a sequence, or between the last one and
    /// the closer. Those on the line where the last element ends are its trailing
    /// comments, two spaces after it, wherever the source had them on that line;
    /// before a closing brace on their line, block comments stay inline when the
    /// braces' group `braces` stays on one line, so either layout prints back to
    /// itself. The others go on lines of their own.
    fn comment_run(
        &mut self,
        parts: &mut Vec<Doc>,
        gap: &mut Gap,
        comments: &[Comment],
        braces: Option<GroupId>,
    ) {
        let mut rest = comments;
        if *gap == Gap::Line {
            let late = comments
                .iter()
                .take_while(|comment| !self.own_line(comment))
                .count();
            // A `//` comment runs to the end of its line, so only the comments up to
            // the first one share the line; any after it go on lines of their own,
            // or the next print would read them as part of it.
            let late = comments[..late]
                .iter()
                .position(|comment| !comment.block)
                .map_or(late, |first| first + 1);
            let (line, after) = comments.split_at(late);
            rest = after;
            match line.last() {
                None => {}
                Some(last) if braces.is_some() && !self.ends_line(last) => {
                    let mut inline = Vec::with_capacity(line.len() * 2);
                    for comment in line {
                        inline.push(text(" "));
                        inline.push(self.comment_doc(comment));
                    }
                    let suffix = self.trailing_suffix(line);
                    parts.push(if_break(braces, suffix, concat(inline)));
                }
                Some(_) => parts.push(self.trailing_doc(line)),
            }
        }
        for comment in rest {
            self.separate(parts, *gap, comment.lo);
            parts.push(self.comment_doc(comment));
            *gap = if self.ends_line(comment) {
                Gap::Line
            } else {
                Gap::Space
            };
        }
    }

    fn separate(&self, parts: &mut Vec<Doc>, gap: Gap, pos: u32) {
        match gap {
            Gap::Start => {}
            Gap::Space => parts.push(text(" ")),
            Gap::Line => {
                parts.push(hardline());
                if self.blank_before(pos) {
                    parts.push(hardline());
                }
            }
        }
    }

    /// A sequence in braces: `{}` when empty, one element per line, or on one line
    /// when `one_line` allows it and it fits (SPEC 12.5 Bodies, Spaces). Returns the
    /// id of the braces' group.
    pub(super) fn braces(&mut self, seq: Seq, one_line: bool) -> (Doc, GroupId) {
        let id = seq.id;
        if seq.count == 0 && seq.doc.is_nil() && seq.after_open.is_nil() {
            return (text("{}"), id);
        }
        let flat_ok = one_line && seq.count == 1;
        let doc = group_with(
            id,
            !flat_ok,
            concat(vec![
                text("{"),
                seq.after_open,
                indent(concat(vec![line(), seq.doc])),
                line(),
                text("}"),
            ]),
        );
        (doc, id)
    }
}
