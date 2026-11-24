//! The tree printer, which is `enrang fmt` (SPEC 12.5, ARCHITECTURE 2.3): it lays out
//! a tree in the canonical style, at 100 columns, with the comments and blank lines
//! of the source it came from, and the spelling of each literal that the style keeps.
//!
//! - `doc`: the document IR and its layout.
//! - `comments`: comments and blank lines from the source between token spans, the
//!   sequence printer of blocks and bodies, and `// enrang-fmt-ignore`.
//! - `items`, `stmts`, `exprs`, `types`: the tree, by SPEC 3's sections.
//!
//! A tree whose file span is `Span::DUMMY`, as a generated one is, prints without its
//! source: no comments, no blank lines, and each string from its value.

mod comments;
mod doc;
mod exprs;
mod items;
mod stmts;
mod types;

use enrang_base::{BytePos, SourceFile, Span};
use enrang_diag::DiagCtx;

use crate::ast::File;
use crate::token::{Punct, Token, TokenKind};

use comments::Comment;
use doc::{
    Doc, GroupId, concat, conditional, fill, group_with, hardline, if_break, indent, join, line,
    nil, softline, text,
};

/// SPEC 12.5: "100 columns, a rule rather than a default".
const WIDTH: usize = 100;

/// SPEC 12.5 "Opting out": on line 1, the whole file stays as written.
const IGNORE_FILE: &str = "// enrang-fmt-ignore-file";

pub(crate) fn print_file(source: &SourceFile, file: &File) -> String {
    let body = source.text.strip_prefix('\u{FEFF}').unwrap_or(&source.text);
    let first_line = body.split('\n').next().unwrap_or("");
    if first_line.trim_end() == IGNORE_FILE {
        return source.text.to_string();
    }
    let real = !file.span.is_dummy();
    let mut printer = Printer::new(source, real);
    let doc = printer.file(file);
    let out = doc::layout(&doc, WIDTH);
    let out = out.trim_end_matches([' ', '\t', '\n']);
    if out.trim().is_empty() {
        return String::new();
    }
    format!("{out}\n")
}

/// The state of one print: the source, its tokens and comments, and the next comment
/// still to print. Comments are printed in source order as the tree is walked in
/// source order: before a node, every comment that starts before it.
pub(crate) struct Printer<'a> {
    src: &'a str,
    start: u32,
    /// Whether the tree's spans point into `src`.
    real: bool,
    tokens: Vec<Token>,
    comments: Vec<Comment>,
    next_comment: usize,
    next_group: GroupId,
    /// The token printed just before the next expression is `&` or `<`, where a
    /// single-quoted string could lex as a lifetime (SPEC 12.5 Quotes).
    after_amp_lt: bool,
}

impl<'a> Printer<'a> {
    fn new(source: &'a SourceFile, real: bool) -> Printer<'a> {
        let (tokens, comments) = if real {
            let tokens = crate::lexer::lex(source, &mut DiagCtx::new());
            let comments = comments::scan(&source.text, source.start.0, &tokens);
            (tokens, comments)
        } else {
            (Vec::new(), Vec::new())
        };
        Printer {
            src: &source.text,
            start: source.start.0,
            real,
            tokens,
            comments,
            next_comment: 0,
            next_group: 0,
            after_amp_lt: false,
        }
    }

    /// A printer with no source, as for a generated tree.
    fn bare() -> Printer<'static> {
        Printer {
            src: "",
            start: 0,
            real: false,
            tokens: Vec::new(),
            comments: Vec::new(),
            next_comment: 0,
            next_group: 0,
            after_amp_lt: false,
        }
    }

    fn group_id(&mut self) -> GroupId {
        self.next_group += 1;
        self.next_group
    }

    /// Whether `span` points into the source.
    fn has_place(&self, span: Span) -> bool {
        self.real && !span.is_dummy()
    }

    /// The source text between two positions, or `""` when they are not in it.
    fn slice(&self, lo: u32, hi: u32) -> &'a str {
        let lo = lo.saturating_sub(self.start) as usize;
        let hi = hi.saturating_sub(self.start) as usize;
        self.src.get(lo..hi).unwrap_or("")
    }

    fn span_text(&self, span: Span) -> &'a str {
        if self.has_place(span) {
            self.slice(span.lo.0, span.hi.0)
        } else {
            ""
        }
    }

    /// The index of the first token starting at or after `pos`.
    fn token_at(&self, pos: u32) -> usize {
        self.tokens.partition_point(|token| token.span.lo.0 < pos)
    }

    /// The first `punct` token at or after `pos`.
    fn find_punct(&self, pos: u32, punct: Punct) -> Option<usize> {
        let at = self.token_at(pos);
        self.tokens[at..]
            .iter()
            .position(|token| token.is(punct))
            .map(|offset| at + offset)
    }

    /// The `}` that closes the `{` at token `open`.
    fn matching_brace(&self, open: usize) -> Option<usize> {
        let mut depth = 0usize;
        for (at, token) in self.tokens.iter().enumerate().skip(open) {
            if token.is(Punct::LBrace) {
                depth += 1;
            } else if token.is(Punct::RBrace) {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(at);
                }
            }
        }
        None
    }

    /// The positions just after the `{` and at the `}` of the braces whose `{` is the
    /// first one at or after `pos`.
    fn braces_after(&self, pos: u32) -> (Option<u32>, Option<u32>) {
        if !self.real || pos == 0 {
            return (None, None);
        }
        let Some(open) = self.find_punct(pos, Punct::LBrace) else {
            return (None, None);
        };
        let close = self
            .matching_brace(open)
            .map(|at| self.tokens[at].span.lo.0);
        (Some(self.tokens[open].span.hi.0), close)
    }

    /// Where the closing bracket of a list ends its items: the first token after
    /// `after` that is not a `,`, when it is `close`.
    fn closer_after(&self, after: u32, close: Punct) -> Option<u32> {
        if !self.real || after == 0 {
            return None;
        }
        let at = self.token_at(after);
        let token = self.tokens[at..]
            .iter()
            .find(|token| !token.is(Punct::Comma))?;
        let fits = token.is(close)
            || matches!(
                (close, token.kind),
                (
                    Punct::Gt,
                    TokenKind::Punct(Punct::Shr | Punct::Shr3 | Punct::Ge | Punct::ShrEq)
                )
            );
        fits.then_some(token.span.lo.0)
    }

    /// A comma list in brackets (SPEC 12.5 Lists, Rows): flat when it fits, else one
    /// item per line with a trailing comma, or filled when every item is short; a last
    /// item that hugs stays on the opening line. Comments before and after each item,
    /// and before the closer, keep their places.
    fn list<T>(
        &mut self,
        items: &[T],
        span: impl Fn(&T) -> Span,
        build: impl FnMut(&mut Self, &T) -> ListItem,
        opts: ListOpts,
    ) -> Listed {
        self.list_then(items, span, build, opts, |_| nil())
    }

    /// [`Printer::list`], then `suffix`, built after the list's comments and printed
    /// after its closer inside its group: the `): Ret` of a signature, which breaks
    /// the parameters when it does not fit (SPEC 12.5 Signatures). Everything is
    /// built in source order, since comments are taken in that order.
    fn list_then<T>(
        &mut self,
        items: &[T],
        span: impl Fn(&T) -> Span,
        mut build: impl FnMut(&mut Self, &T) -> ListItem,
        opts: ListOpts,
        suffix: impl FnOnce(&mut Self) -> Doc,
    ) -> Listed {
        let id = self.group_id();
        // SPEC 12.5 Comments: "a comment right after `{` stays on that line".
        let after_open = match items.first().map(&span) {
            Some(first) if opts.pad && self.has_place(first) => {
                let at = self.token_at(first.lo.0);
                match at.checked_sub(1).map(|before| self.tokens[before]) {
                    Some(open) if open.is(Punct::LBrace) => {
                        let found = self.take_trailing(open.span.hi.0, false);
                        self.trailing_doc(&found)
                    }
                    _ => nil(),
                }
            }
            _ => nil(),
        };
        let mut built = Vec::with_capacity(items.len());
        let mut commented = !after_open.is_nil();
        // SPEC 12.5 Blank lines: "Elsewhere 0 or 1 is kept as written"; a list
        // that keeps one goes one item per line.
        let mut blank = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            let at = span(item);
            let place = self.has_place(at);
            blank.push(index > 0 && place && self.blank_before_item(at.lo.0));
            let lead = if place { self.leading(at.lo.0) } else { nil() };
            let item = build(self, item);
            let trail = if place {
                let found = self.take_trailing(at.hi.0, true);
                self.trailing_doc(&found)
            } else {
                nil()
            };
            commented |= !lead.is_nil() || !trail.is_nil();
            built.push((lead, item, trail));
        }
        let blanks = blank.contains(&true);
        let dangling = match opts.close_at {
            Some(pos) if self.real => self.dangling(pos),
            _ => Vec::new(),
        };
        commented |= !dangling.is_empty();
        let suffix = suffix(self);
        let open = text(opts.open);
        let close = text(opts.close);
        let edge = if opts.pad { line() } else { softline() };
        if built.is_empty() {
            if dangling.is_empty() {
                let doc = concat(vec![open, close, suffix]);
                return Listed { doc, id };
            }
            let doc = group_with(
                id,
                false,
                concat(vec![
                    open,
                    indent(concat(vec![edge.clone(), join(&line(), dangling)])),
                    edge,
                    close,
                    suffix,
                ]),
            );
            return Listed { doc, id };
        }
        let count = built.len();
        let early_breaks = built
            .iter()
            .take(count - 1)
            .any(|(_, item, _)| item.doc.breaks());
        let hug = opts.hug && !commented && !opts.force && !early_breaks && !blanks;
        let hug_target = built.last().and_then(|(_, item, _)| item.hug);
        let trailing = |last: bool| {
            if !last {
                text(",")
            } else if opts.trailing_comma {
                if_break(Some(id), text(","), nil())
            } else {
                nil()
            }
        };
        let short = opts.fill
            && !opts.force
            && !commented
            && !blanks
            && count >= 2
            && built.iter().all(|(_, item, _)| {
                item.doc
                    .flat_width()
                    .is_some_and(|width| width <= opts.short)
            });
        let full: Vec<Doc> = built
            .iter()
            .enumerate()
            .map(|(at, (lead, item, trail))| {
                concat(vec![
                    lead.clone(),
                    item.doc.clone(),
                    trailing(at + 1 == count),
                    trail.clone(),
                ])
            })
            .collect();
        let body = if short {
            let mut parts = Vec::with_capacity(count * 2);
            for (at, doc) in full.into_iter().enumerate() {
                if at > 0 {
                    parts.push(line());
                }
                parts.push(doc);
            }
            fill(parts)
        } else {
            let mut parts = Vec::with_capacity(count * 3);
            for (at, doc) in full.into_iter().enumerate() {
                if at > 0 {
                    parts.push(line());
                    if blank[at] {
                        parts.push(hardline());
                    }
                }
                parts.push(doc);
            }
            concat(parts)
        };
        let mut inner = vec![body];
        for comment in dangling {
            inner.push(line());
            inner.push(comment);
        }
        let broken = concat(vec![
            open.clone(),
            after_open,
            indent(concat(vec![edge.clone(), concat(inner)])),
            edge,
            close.clone(),
            suffix.clone(),
        ]);
        match hug_target {
            Some(target) if hug => {
                let docs: Vec<Doc> = built.iter().map(|(_, item, _)| item.doc.clone()).collect();
                let last = docs[count - 1].clone();
                let hugged_last = last.with_broken(target).unwrap_or_else(|| last.clone());
                let mut hugged_docs = docs.clone();
                hugged_docs[count - 1] = hugged_last;
                let flat = concat(vec![
                    open.clone(),
                    join(&text(", "), docs),
                    close.clone(),
                    suffix.clone(),
                ]);
                let hugged = concat(vec![open, join(&text(", "), hugged_docs), close, suffix]);
                let expanded = group_with(id, true, broken);
                let parent = if last.breaks() {
                    doc::break_parent()
                } else {
                    nil()
                };
                let doc = concat(vec![parent, conditional(flat, vec![hugged, expanded])]);
                Listed { doc, id }
            }
            _ => Listed {
                doc: group_with(id, opts.force, broken),
                id,
            },
        }
    }
}

impl Printer<'_> {
    /// Whether the source has a blank line between the item at `pos` and the `,`
    /// or comments before it.
    fn blank_before_item(&self, pos: u32) -> bool {
        let at = self.token_at(pos);
        let Some(before) = at.checked_sub(1).map(|before| self.tokens[before]) else {
            return false;
        };
        let lines: Vec<&str> = self.slice(before.span.hi.0, pos).split('\n').collect();
        lines.len() > 2
            && lines[1..lines.len() - 1]
                .iter()
                .any(|line| line.trim().is_empty())
    }
}

/// One item of a [`Printer::list`]: its document, and the group it breaks when it is
/// the last item and hugs the opening line.
pub(crate) struct ListItem {
    doc: Doc,
    hug: Option<GroupId>,
}

impl ListItem {
    fn plain(doc: Doc) -> ListItem {
        ListItem { doc, hug: None }
    }
}

/// A printed list and the id of its group.
pub(crate) struct Listed {
    doc: Doc,
    id: GroupId,
}

pub(crate) struct ListOpts {
    open: &'static str,
    close: &'static str,
    /// A brace list: one space inside each brace when flat (SPEC 12.5 Spaces).
    pad: bool,
    /// A last item that is a block-bodied arrow or an object literal may stay on the
    /// opening line (SPEC 12.5 Lists): arguments only.
    hug: bool,
    /// Items this short or shorter all fill lines instead (SPEC 12.5 Lists).
    fill: bool,
    short: usize,
    /// One item per line even when the list fits (SPEC 12.5 Rows).
    force: bool,
    trailing_comma: bool,
    /// Where the closer is, so comments before it stay inside.
    close_at: Option<u32>,
}

impl ListOpts {
    fn new(open: &'static str, close: &'static str) -> ListOpts {
        ListOpts {
            open,
            close,
            pad: false,
            hug: false,
            fill: true,
            short: 10,
            force: false,
            trailing_comma: true,
            close_at: None,
        }
    }

    /// Parameters: one per line when they do not fit, never filled (SPEC 12.5
    /// Signatures).
    fn params() -> ListOpts {
        ListOpts {
            fill: false,
            ..ListOpts::new("(", ")")
        }
    }

    fn braces() -> ListOpts {
        ListOpts {
            pad: true,
            ..ListOpts::new("{", "}")
        }
    }

    fn close_at(self, close_at: Option<u32>) -> ListOpts {
        ListOpts { close_at, ..self }
    }
}

/// A position as the `u32` comments are compared with.
fn pos(at: BytePos) -> u32 {
    at.0
}
