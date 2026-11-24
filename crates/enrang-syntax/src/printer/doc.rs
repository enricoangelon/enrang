//! The document IR the printer builds and the layout that turns it into text, after
//! Wadler's "prettier printer" and the printer of Prettier: text, line breaks that a
//! group takes all or none of, indentation, fills for lists of short items,
//! conditional groups that try layouts in turn, and line suffixes for trailing
//! comments, which never count toward the width.
//!
//! A group breaks when it holds a hard line, a `BreakParent` or a broken group;
//! [`Doc`] works that out when the group is built, so a document is immutable and its
//! parts are shared, not copied, between the layouts a conditional group tries.

use std::collections::BTreeMap;
use std::rc::Rc;

/// Names a group, so that an `IfBreak` or `IndentIfBreak` elsewhere can follow it.
pub(crate) type GroupId = u32;

/// An immutable, cheaply cloned document.
#[derive(Clone, Debug)]
pub(crate) struct Doc(Rc<Inner>);

#[derive(Debug)]
struct Inner {
    node: Node,
    /// Whether this document forces the group around it to break.
    breaks: bool,
}

#[derive(Debug)]
pub(crate) enum Node {
    Nil,
    /// Text with no line break.
    Text(String),
    /// Text kept exactly as written, line breaks included: a multi-line template, a
    /// block comment printed as written, a node under `// enrang-fmt-ignore`. Lines
    /// after the first are not indented.
    Verbatim(String),
    Concat(Vec<Doc>),
    Indent(Doc),
    Group(Group),
    /// Content and separator in turn: as many contents on a line as fit.
    Fill(Vec<Doc>),
    /// `broken` when the group (`None`: the enclosing one) is broken, else `flat`.
    IfBreak {
        group: Option<GroupId>,
        broken: Doc,
        flat: Doc,
    },
    /// `contents`, indented when group `group` broke.
    IndentIfBreak {
        group: GroupId,
        contents: Doc,
    },
    Line(LineKind),
    /// Printed before the next line break: a trailing comment.
    LineSuffix(Doc),
    /// Breaks the enclosing group.
    BreakParent,
}

#[derive(Debug)]
pub(crate) struct Group {
    id: Option<GroupId>,
    brk: bool,
    contents: Doc,
    /// For a conditional group, the layouts after `contents`, tried in turn when
    /// `contents` does not fit flat; the last one is used broken if none fits.
    alts: Vec<Doc>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum LineKind {
    /// A space when flat.
    Normal,
    /// Nothing when flat.
    Soft,
    /// Always a line break.
    Hard,
}

impl Doc {
    fn new(node: Node) -> Doc {
        let breaks = match &node {
            Node::Nil | Node::Text(_) | Node::Line(LineKind::Normal | LineKind::Soft) => false,
            Node::Verbatim(text) => text.contains('\n'),
            Node::Concat(parts) | Node::Fill(parts) => parts.iter().any(Doc::breaks),
            Node::Indent(doc) | Node::LineSuffix(doc) => doc.breaks(),
            Node::IndentIfBreak { contents, .. } => contents.breaks(),
            Node::IfBreak { broken, flat, .. } => broken.breaks() || flat.breaks(),
            Node::Group(group) => group.brk,
            Node::Line(LineKind::Hard) | Node::BreakParent => true,
        };
        Doc(Rc::new(Inner { node, breaks }))
    }

    pub(crate) fn node(&self) -> &Node {
        &self.0.node
    }

    /// Whether this document forces the group around it to break.
    pub(crate) fn breaks(&self) -> bool {
        self.0.breaks
    }

    pub(crate) fn is_nil(&self) -> bool {
        matches!(self.node(), Node::Nil)
    }

    /// This document with group `id`, wherever it is, broken; `None` when the
    /// document holds no such group. A conditional group's layouts are not searched.
    pub(crate) fn with_broken(&self, id: GroupId) -> Option<Doc> {
        match self.node() {
            Node::Group(group) if group.id == Some(id) => Some(Doc::new(Node::Group(Group {
                id: group.id,
                brk: true,
                contents: group.contents.clone(),
                alts: group.alts.clone(),
            }))),
            Node::Group(group) if group.alts.is_empty() => {
                let contents = group.contents.with_broken(id)?;
                Some(group_doc(group.id, true, contents, Vec::new()))
            }
            Node::Concat(parts) => {
                let (at, changed) = parts
                    .iter()
                    .enumerate()
                    .find_map(|(at, part)| part.with_broken(id).map(|doc| (at, doc)))?;
                let mut parts = parts.clone();
                parts[at] = changed;
                Some(concat(parts))
            }
            Node::Indent(doc) => doc.with_broken(id).map(indent),
            _ => None,
        }
    }

    /// The width of this document printed flat, or `None` when it cannot be flat.
    pub(crate) fn flat_width(&self) -> Option<usize> {
        if self.breaks() {
            return None;
        }
        match self.node() {
            Node::Nil | Node::Line(LineKind::Soft) | Node::BreakParent => Some(0),
            Node::LineSuffix(_) => Some(0),
            Node::Text(text) | Node::Verbatim(text) => Some(width(text)),
            Node::Line(LineKind::Normal) => Some(1),
            Node::Line(LineKind::Hard) => None,
            Node::Concat(parts) | Node::Fill(parts) => parts
                .iter()
                .try_fold(0, |sum, part| Some(sum + part.flat_width()?)),
            Node::Indent(doc) => doc.flat_width(),
            Node::IndentIfBreak { contents, .. } => contents.flat_width(),
            Node::IfBreak { flat, .. } => flat.flat_width(),
            Node::Group(group) => group.contents.flat_width(),
        }
    }
}

/// The width of `text` in columns: SPEC 2 counts Unicode scalar values.
pub(crate) fn width(text: &str) -> usize {
    text.chars().count()
}

pub(crate) fn nil() -> Doc {
    Doc::new(Node::Nil)
}

pub(crate) fn text(text: impl Into<String>) -> Doc {
    let text = text.into();
    if text.contains('\n') {
        Doc::new(Node::Verbatim(text))
    } else {
        Doc::new(Node::Text(text))
    }
}

pub(crate) fn verbatim(text: impl Into<String>) -> Doc {
    Doc::new(Node::Verbatim(text.into()))
}

pub(crate) fn concat(parts: Vec<Doc>) -> Doc {
    let parts: Vec<Doc> = parts.into_iter().filter(|part| !part.is_nil()).collect();
    match parts.len() {
        0 => nil(),
        1 => parts.into_iter().next().unwrap_or_else(nil),
        _ => Doc::new(Node::Concat(parts)),
    }
}

pub(crate) fn indent(doc: Doc) -> Doc {
    Doc::new(Node::Indent(doc))
}

fn group_doc(id: Option<GroupId>, brk: bool, contents: Doc, alts: Vec<Doc>) -> Doc {
    let brk = brk || (alts.is_empty() && contents.breaks());
    Doc::new(Node::Group(Group {
        id,
        brk,
        contents,
        alts,
    }))
}

pub(crate) fn group(contents: Doc) -> Doc {
    group_doc(None, false, contents, Vec::new())
}

/// A group that `IfBreak` and `IndentIfBreak` can name, broken from the start when
/// `brk` is set.
pub(crate) fn group_with(id: GroupId, brk: bool, contents: Doc) -> Doc {
    group_doc(Some(id), brk, contents, Vec::new())
}

/// Tries `first` flat, then each of `alts` in turn, and prints the last one broken
/// when nothing fits. Breaks in the layouts do not break the groups around it; the
/// caller adds a `BreakParent` beside it when they must.
pub(crate) fn conditional(first: Doc, alts: Vec<Doc>) -> Doc {
    group_doc(None, false, first, alts)
}

pub(crate) fn fill(parts: Vec<Doc>) -> Doc {
    Doc::new(Node::Fill(parts))
}

pub(crate) fn if_break(group: Option<GroupId>, broken: Doc, flat: Doc) -> Doc {
    Doc::new(Node::IfBreak {
        group,
        broken,
        flat,
    })
}

pub(crate) fn indent_if_break(group: GroupId, contents: Doc) -> Doc {
    Doc::new(Node::IndentIfBreak { group, contents })
}

pub(crate) fn line() -> Doc {
    Doc::new(Node::Line(LineKind::Normal))
}

pub(crate) fn softline() -> Doc {
    Doc::new(Node::Line(LineKind::Soft))
}

pub(crate) fn hardline() -> Doc {
    Doc::new(Node::Line(LineKind::Hard))
}

pub(crate) fn line_suffix(doc: Doc) -> Doc {
    Doc::new(Node::LineSuffix(doc))
}

pub(crate) fn break_parent() -> Doc {
    Doc::new(Node::BreakParent)
}

/// `parts` with `sep` between each two.
pub(crate) fn join(sep: &Doc, parts: Vec<Doc>) -> Doc {
    let mut out = Vec::with_capacity(parts.len() * 2);
    for (at, part) in parts.into_iter().enumerate() {
        if at > 0 {
            out.push(sep.clone());
        }
        out.push(part);
    }
    concat(out)
}

// ---------------------------------------------------------------------------------
// Layout.

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Mode {
    Flat,
    Break,
}

#[derive(Copy, Clone)]
enum Item<'a> {
    Doc(&'a Doc),
    /// The parts of a fill from some index on.
    Fill(&'a [Doc]),
}

#[derive(Copy, Clone)]
struct Cmd<'a> {
    ind: usize,
    mode: Mode,
    item: Item<'a>,
}

/// `doc` laid out at `width` columns. Spaces before a line break the layout makes are
/// removed; text kept verbatim keeps its own.
pub(crate) fn layout(doc: &Doc, width_limit: usize) -> String {
    let mut printer = Layout {
        width: width_limit as isize,
        out: String::new(),
        pos: 0,
        floor: 0,
        modes: BTreeMap::new(),
        remeasure: false,
    };
    printer.run(doc);
    printer.out
}

struct Layout {
    width: isize,
    out: String,
    /// Columns used on the current line.
    pos: usize,
    /// Trailing spaces before this byte of `out` are verbatim text and stay.
    floor: usize,
    modes: BTreeMap<GroupId, Mode>,
    /// A hard line was printed in flat mode, so the next group is measured again.
    remeasure: bool,
}

impl Layout {
    fn run(&mut self, doc: &Doc) {
        let mut cmds: Vec<Cmd<'_>> = vec![Cmd {
            ind: 0,
            mode: Mode::Break,
            item: Item::Doc(doc),
        }];
        let mut suffixes: Vec<Cmd<'_>> = Vec::new();
        while let Some(cmd) = cmds.pop() {
            match cmd.item {
                Item::Fill(parts) => self.fill(cmd, parts, &mut cmds),
                Item::Doc(doc) => self.doc(cmd, doc, &mut cmds, &mut suffixes),
            }
            if cmds.is_empty() && !suffixes.is_empty() {
                cmds.extend(suffixes.drain(..).rev());
            }
        }
    }

    fn doc<'a>(
        &mut self,
        cmd: Cmd<'a>,
        doc: &'a Doc,
        cmds: &mut Vec<Cmd<'a>>,
        suffixes: &mut Vec<Cmd<'a>>,
    ) {
        let Cmd { ind, mode, .. } = cmd;
        match doc.node() {
            Node::Nil | Node::BreakParent => {}
            Node::Text(text) => {
                self.out.push_str(text);
                self.pos += width(text);
            }
            Node::Verbatim(text) => {
                self.out.push_str(text);
                match text.rfind('\n') {
                    Some(at) => self.pos = width(&text[at + 1..]),
                    None => self.pos += width(text),
                }
                self.floor = self.out.len();
            }
            Node::Concat(parts) => {
                for part in parts.iter().rev() {
                    cmds.push(Cmd {
                        ind,
                        mode,
                        item: Item::Doc(part),
                    });
                }
            }
            Node::Indent(inner) => cmds.push(Cmd {
                ind: ind + 2,
                mode,
                item: Item::Doc(inner),
            }),
            Node::IndentIfBreak { group, contents } => {
                let broken = self.modes.get(group) == Some(&Mode::Break);
                cmds.push(Cmd {
                    ind: if broken { ind + 2 } else { ind },
                    mode,
                    item: Item::Doc(contents),
                });
            }
            Node::IfBreak {
                group,
                broken,
                flat,
            } => {
                let group_mode = match group {
                    Some(id) => self.modes.get(id).copied().unwrap_or(Mode::Flat),
                    None => mode,
                };
                let chosen = if group_mode == Mode::Break {
                    broken
                } else {
                    flat
                };
                cmds.push(Cmd {
                    ind,
                    mode,
                    item: Item::Doc(chosen),
                });
            }
            Node::LineSuffix(inner) => suffixes.push(Cmd {
                ind,
                mode,
                item: Item::Doc(inner),
            }),
            Node::Fill(parts) => cmds.push(Cmd {
                ind,
                mode,
                item: Item::Fill(parts),
            }),
            Node::Group(group) => {
                let chosen = if mode == Mode::Flat && !self.remeasure {
                    Cmd {
                        ind,
                        mode: if group.brk { Mode::Break } else { Mode::Flat },
                        item: Item::Doc(&group.contents),
                    }
                } else {
                    self.remeasure = false;
                    self.choose(ind, group, cmds)
                };
                if let Some(id) = group.id {
                    self.modes.insert(id, chosen.mode);
                }
                cmds.push(chosen);
            }
            Node::Line(kind) => {
                if mode == Mode::Flat && *kind != LineKind::Hard {
                    if *kind == LineKind::Normal {
                        self.out.push(' ');
                        self.pos += 1;
                    }
                    return;
                }
                if mode == Mode::Flat {
                    self.remeasure = true;
                }
                if !suffixes.is_empty() {
                    cmds.push(cmd);
                    cmds.extend(suffixes.drain(..).rev());
                    return;
                }
                self.newline(ind);
            }
        }
    }

    /// The layout of a group met in break mode.
    fn choose<'a>(&self, ind: usize, group: &'a Group, cmds: &[Cmd<'a>]) -> Cmd<'a> {
        let rem = self.width - self.pos as isize;
        let flat = Cmd {
            ind,
            mode: Mode::Flat,
            item: Item::Doc(&group.contents),
        };
        if !group.brk && self.fits(vec![flat], cmds, rem, false) {
            return flat;
        }
        if group.alts.is_empty() {
            return Cmd {
                mode: Mode::Break,
                ..flat
            };
        }
        let last = group.alts.last().unwrap_or(&group.contents);
        if !group.brk {
            for alt in &group.alts {
                let cmd = Cmd {
                    ind,
                    mode: Mode::Flat,
                    item: Item::Doc(alt),
                };
                if self.fits(vec![cmd], cmds, rem, false) {
                    return cmd;
                }
            }
        }
        Cmd {
            ind,
            mode: Mode::Break,
            item: Item::Doc(last),
        }
    }

    /// Prettier's fill: each content flat if it fits, each separator flat if the
    /// next content then fits too.
    fn fill<'a>(&mut self, cmd: Cmd<'a>, parts: &'a [Doc], cmds: &mut Vec<Cmd<'a>>) {
        let Some(content) = parts.first() else {
            return;
        };
        let ind = cmd.ind;
        let rem = self.width - self.pos as isize;
        let at = |mode, doc| Cmd {
            ind,
            mode,
            item: Item::Doc(doc),
        };
        let content_fits = self.fits(vec![at(Mode::Flat, content)], &[], rem, true);
        let content_mode = if content_fits {
            Mode::Flat
        } else {
            Mode::Break
        };
        let Some(sep) = parts.get(1) else {
            cmds.push(at(content_mode, content));
            return;
        };
        let Some(second) = parts.get(2) else {
            cmds.push(at(content_mode, sep));
            cmds.push(at(content_mode, content));
            return;
        };
        let both = vec![
            at(Mode::Flat, content),
            at(Mode::Flat, sep),
            at(Mode::Flat, second),
        ];
        let both_fit = self.fits(both, &[], rem, true);
        cmds.push(Cmd {
            ind,
            mode: cmd.mode,
            item: Item::Fill(&parts[2..]),
        });
        let sep_mode = if both_fit { Mode::Flat } else { Mode::Break };
        cmds.push(at(sep_mode, sep));
        cmds.push(at(content_mode, content));
    }

    /// Whether `next`, then the commands still to print, fit in `rem` columns up to
    /// the first line break.
    fn fits<'a>(
        &self,
        next: Vec<Cmd<'a>>,
        rest: &[Cmd<'a>],
        mut rem: isize,
        must_be_flat: bool,
    ) -> bool {
        let mut stack: Vec<(Mode, Item<'a>)> =
            next.iter().rev().map(|cmd| (cmd.mode, cmd.item)).collect();
        let mut rest_at = rest.len();
        loop {
            if rem < 0 {
                return false;
            }
            let (mode, item) = match stack.pop() {
                Some(top) => top,
                None => {
                    if rest_at == 0 {
                        return true;
                    }
                    rest_at -= 1;
                    (rest[rest_at].mode, rest[rest_at].item)
                }
            };
            let doc = match item {
                Item::Fill(parts) => {
                    for part in parts.iter().rev() {
                        stack.push((mode, Item::Doc(part)));
                    }
                    continue;
                }
                Item::Doc(doc) => doc,
            };
            match doc.node() {
                Node::Nil | Node::BreakParent => {}
                Node::Text(text) => rem -= width(text) as isize,
                Node::Verbatim(text) => match text.find('\n') {
                    Some(at) => {
                        rem -= width(&text[..at]) as isize;
                        return rem >= 0;
                    }
                    None => rem -= width(text) as isize,
                },
                Node::Concat(parts) | Node::Fill(parts) => {
                    for part in parts.iter().rev() {
                        stack.push((mode, Item::Doc(part)));
                    }
                }
                Node::Indent(inner) => stack.push((mode, Item::Doc(inner))),
                Node::IndentIfBreak { contents, .. } => stack.push((mode, Item::Doc(contents))),
                Node::IfBreak {
                    group,
                    broken,
                    flat,
                } => {
                    let group_mode = match group {
                        Some(id) => self.modes.get(id).copied().unwrap_or(Mode::Flat),
                        None => mode,
                    };
                    let chosen = if group_mode == Mode::Break {
                        broken
                    } else {
                        flat
                    };
                    stack.push((mode, Item::Doc(chosen)));
                }
                Node::LineSuffix(_) => {}
                Node::Group(group) => {
                    if must_be_flat && group.brk {
                        return false;
                    }
                    let group_mode = if group.brk { Mode::Break } else { mode };
                    let contents = if group_mode == Mode::Break {
                        group.alts.last().unwrap_or(&group.contents)
                    } else {
                        &group.contents
                    };
                    stack.push((group_mode, Item::Doc(contents)));
                }
                Node::Line(kind) => {
                    if mode == Mode::Break || *kind == LineKind::Hard {
                        return true;
                    }
                    if *kind == LineKind::Normal {
                        rem -= 1;
                    }
                }
            }
        }
    }

    fn newline(&mut self, ind: usize) {
        let keep = self.out[self.floor..].trim_end_matches([' ', '\t']).len();
        self.out.truncate(self.floor + keep);
        self.out.push('\n');
        self.out.extend(std::iter::repeat_n(' ', ind));
        self.pos = ind;
    }
}
