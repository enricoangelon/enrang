//! The wording of phase 3's diagnostics (A:1301-1314; M3 plan d.13, e; owner 3):
//! each code's message, labels, notes, helps and fix-its, as SPEC 13-14, ARCH 6.5
//! and the plan give them, SPEC 14's G cases byte for byte.
//!
//! The analyses hand over what they found (a conflict, a move, a mark, a misfit);
//! the words are read back from the MIR and the source. A path prints as the user
//! wrote it (`this.owner`, `found.name`), else as its source text. A fix-it is
//! offered only where applying it compiles (A:1314): the `[...q]` and `q.clone()`
//! edits of a loop only when the hold is shared, the element type is `Clone` and
//! the body never derefs the binding by hand; G07's `&` only when the callee is in
//! user code and its contract says it neither moves nor writes the parameter (K2).
//! Where the docs give no wording, the head is plan e's (choice), in the style of
//! the goldens.

use std::collections::{BTreeSet, VecDeque};

use enrang_base::{BytePos, SourceMap, Span};
use enrang_diag::{Code, Diagnostic, Edit, Help};
use enrang_hir::{DefId, DefKind, FieldIdx, ParamEnv, Perm, ResultPerm, Tcx, Ty, TyKind};
use enrang_mir::{
    Body, BodyOwner, BorrowOrigin, Callee, FormCall, Local, LocalKind, LoopSource, Operand, Place,
    PlaceTy, Point, Proj, Rvalue, StatementKind, TerminatorKind,
};

use crate::access::{AccessKind, BorrowConflict};
use crate::cx::BodyCx;
use crate::fit::FitError;
use crate::held::{HeldResults, StoreError, StoreErrorKind};
use crate::loans::{LoanId, LoanKind};
use crate::marks::{MarkError, MarkOrigin};
use crate::movepaths::MovePathIdx;
use crate::moves::MoveError;

const RULE_BORROWS: &str = "a value has many shared borrows or one exclusive borrow, never both.";

// ---------------------------------------------------------------------------------
// Reading the source and the MIR back.

/// The text of `span`, or `""` for a span in no file.
fn text(map: &SourceMap, span: Span) -> &str {
    if span.lo == Span::DUMMY.lo || span.lo > span.hi {
        return "";
    }
    map.text(span)
}

/// The first whole-word occurrence of `word` inside `span`.
pub(crate) fn word_in(map: &SourceMap, span: Span, word: &str) -> Option<Span> {
    if word.is_empty() {
        return None;
    }
    let t = text(map, span);
    let ident = |c: char| c.is_alphanumeric() || c == '_' || c == '$';
    let mut from = 0;
    while let Some(i) = t[from..].find(word).map(|i| i + from) {
        let before = t[..i].chars().next_back();
        let after = t[i + word.len()..].chars().next();
        let first_ident = word.chars().next().is_some_and(ident);
        let last_ident = word.chars().next_back().is_some_and(ident);
        if !(first_ident && before.is_some_and(ident)) && !(last_ident && after.is_some_and(ident))
        {
            let lo = span.lo + i as u32;
            return Some(Span {
                lo,
                hi: lo + word.len() as u32,
            });
        }
        from = i + word.len();
    }
    None
}

/// The whole line holding `pos`, without its terminator; `DUMMY` for the position
/// of no file.
fn line_of(map: &SourceMap, pos: BytePos) -> Span {
    if pos == Span::DUMMY.lo {
        return Span::DUMMY;
    }
    let file = map.file_of(pos);
    let offset = pos.0 - file.start.0;
    let line = file.line_starts.partition_point(|&s| s <= offset).max(1);
    let start = file.line_starts[line - 1];
    let rest = &file.text[start as usize..];
    let len = rest.find(['\n', '\r']).unwrap_or(rest.len());
    let lo = file.start + start;
    Span {
        lo,
        hi: lo + len as u32,
    }
}

/// `span` with the `;` right after it, when there is one.
fn with_semicolon(map: &SourceMap, span: Span) -> Span {
    let line = line_of(map, span.hi);
    let rest = text(
        map,
        Span {
            lo: span.hi,
            hi: line.hi,
        },
    );
    match rest.starts_with(';') {
        true => Span {
            hi: span.hi + 1,
            ..span
        },
        false => span,
    }
}

/// The whitespace a line starts with.
fn indent_of(map: &SourceMap, pos: BytePos) -> String {
    let t = text(map, line_of(map, pos));
    t.chars().take_while(|c| *c == ' ' || *c == '\t').collect()
}

/// The keyword written right before `span` on its line (`const` of `const xs`).
fn keyword_before(map: &SourceMap, span: Span, kw: &str) -> Option<Span> {
    let line = line_of(map, span.lo);
    let before = text(
        map,
        Span {
            lo: line.lo,
            hi: span.lo,
        },
    );
    let trimmed = before.trim_end();
    let start = trimmed.strip_suffix(kw)?.len();
    let lo = line.lo + start as u32;
    Some(Span {
        lo,
        hi: lo + kw.len() as u32,
    })
}

/// The `let` or `const` statement on one line that declares the name at `span`,
/// up to its `;`.
fn statement_text(map: &SourceMap, span: Span) -> Option<String> {
    let line = line_of(map, span.lo);
    let t = text(map, line);
    let at = (span.lo.0 - line.lo.0) as usize;
    let start = ["let ", "const "]
        .iter()
        .filter_map(|kw| t[..at].rfind(kw))
        .max()?;
    let end = t[at..].find(';')? + at + 1;
    Some(t[start..end].to_owned())
}

/// The position after `name`, an optional `?` and the `:` that follows it from
/// `from`: where a parameter's type starts.
fn type_after_colon(map: &SourceMap, from: BytePos) -> Option<BytePos> {
    let line = line_of(map, from);
    let t = text(
        map,
        Span {
            lo: from,
            hi: line.hi,
        },
    );
    let colon = t.find(':')?;
    let skip = t[colon + 1..].len() - t[colon + 1..].trim_start().len();
    Some(from + (colon + 1 + skip) as u32)
}

/// The written return type `written` of a definition: after the `:` that follows
/// its parameter list's closing `)`, before the body's `{`; a parameter's own type
/// is never it.
fn written_ret(map: &SourceMap, data: &enrang_hir::DefData, written: &str) -> Option<Span> {
    let head = Span {
        lo: data.name_span.hi,
        hi: data.span.hi,
    };
    let t = text(map, head);
    let open = t.find('(')?;
    let mut depth = 0usize;
    let mut close = None;
    for (i, c) in t[open..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(open + i + 1);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close?;
    let body = t[close..].find('{').map_or(t.len(), |i| close + i);
    word_in(
        map,
        Span {
            lo: head.lo + close as u32,
            hi: head.lo + body as u32,
        },
        written,
    )
}

fn sym(s: impl ToString) -> String {
    s.to_string()
}

/// The definition a body belongs to.
fn owner_def(b: &Body) -> Option<DefId> {
    match b.owner {
        BodyOwner::Fn(d) | BodyOwner::Test(d) => Some(d),
        BodyOwner::Arrow(enrang_hir::BodyOwner::Fn(d), _) => Some(d),
        _ => None,
    }
}

/// A definition's own name (`inc`, `Counter`); a constructor as its call is
/// written, `new Wrap`.
fn name_of(tcx: &Tcx, d: DefId) -> String {
    let data = tcx.def(d);
    match (data.kind, data.parent) {
        (DefKind::Ctor, Some(p)) => format!("new {}", name_of(tcx, p)),
        _ => data.name().map_or_else(String::new, sym),
    }
}

/// A method's name with its class (`Words.next`), a function's own name.
fn qualified(tcx: &Tcx, d: DefId) -> String {
    let data = tcx.def(d);
    match data.parent.filter(|p| tcx.adt_of(*p).is_some()) {
        Some(p) => format!("{}.{}", name_of(tcx, p), name_of(tcx, d)),
        None => name_of(tcx, d),
    }
}

/// The class, interface or enum a member belongs to, by name.
fn parent_name(tcx: &Tcx, d: DefId) -> String {
    tcx.def(d)
        .parent
        .map_or_else(|| name_of(tcx, d), |p| name_of(tcx, p))
}

/// Whether `l` is a body's `this`: `_1` of a definition that takes it.
fn is_this(tcx: &Tcx, b: &Body, l: Local) -> bool {
    l == Local(1)
        && matches!(b.owner, BodyOwner::Fn(d) if tcx.takes_this(d))
        && b.locals[l].kind == LocalKind::Arg
}

/// A local as the user wrote it: its name, or `this`.
fn local_name(tcx: &Tcx, b: &Body, l: Local) -> Option<String> {
    if is_this(tcx, b, l) {
        return Some("this".to_owned());
    }
    b.locals[l].name.map(sym)
}

/// The value a temporary of `b` is made from: the place a reborrow `&*x` goes
/// through, or a copied, moved or converted operand's place.
fn temp_source(b: &Body, t: Local) -> Option<Place> {
    b.blocks
        .iter()
        .flat_map(|blk| &blk.stmts)
        .find_map(|s| match &s.kind {
            StatementKind::Assign { dest, value } if *dest == Place::local(t) => match value {
                // A reborrow through the reference, a narrowed payload's
                // included: `&*(a as Present).0`.
                Rvalue::Ref { place, .. } if b.projs(*place).contains(&Proj::Deref) => Some(*place),
                Rvalue::Use(o) | Rvalue::Convert(_, o) => o.place(),
                _ => None,
            },
            _ => None,
        })
}

/// What the source calls the holder of a loan: its name, or for a temporary the
/// named local whose reference it copies or reborrows (`&*r` holds what `r`
/// held); `None` when no named local stands behind it.
fn holder_name(cx: &BodyCx, h: Local) -> Option<String> {
    let (tcx, b) = (cx.tcx, cx.body);
    let mut l = h;
    for _ in 0..b.locals.len() {
        if let Some(n) = local_name(tcx, b, l) {
            return Some(n);
        }
        if b.locals[l].kind != LocalKind::Temp {
            return None;
        }
        l = temp_source(b, l)?.local;
    }
    None
}

/// The first write through a reference that holds loan `l`, from its site on:
/// a statement writing through it, or a call passing it to a Write parameter;
/// the holders are the site's destination and every temporary that copies or
/// reborrows one of them.
fn first_write(cx: &BodyCx, l: LoanId) -> Option<Span> {
    let b = cx.body;
    let loan = &cx.loans.table[l];
    let Some(StatementKind::Assign { dest, .. }) = b.stmt_at(loan.site).map(|s| &s.kind) else {
        return None;
    };
    let mut rel = BTreeSet::from([dest.local]);
    loop {
        let more: Vec<Local> = (b.locals.indices())
            .filter(|t| !rel.contains(t) && b.locals[*t].kind == LocalKind::Temp)
            .filter(|t| temp_source(b, *t).is_some_and(|p| rel.contains(&p.local)))
            .collect();
        if more.is_empty() {
            break;
        }
        rel.extend(more);
    }
    after(b, loan.site)
        .into_iter()
        .find_map(|p| match b.stmt_at(p) {
            Some(st) => match &st.kind {
                StatementKind::Assign { dest, .. }
                    if rel.contains(&dest.local)
                        && b.projs(*dest).first() == Some(&Proj::Deref) =>
                {
                    Some(st.span)
                }
                _ => None,
            },
            None => {
                let TerminatorKind::Call { callee, args, .. } = &b.blocks[p.block].term.kind else {
                    return None;
                };
                let info = crate::cx::call_info(cx, callee, args);
                let writes = (info.perms.iter().enumerate())
                    .filter(|(_, perm)| **perm == Perm::Write)
                    .filter_map(|(i, _)| args.get(*info.args_map.get(i)?))
                    .any(|a| a.place().is_some_and(|q| rel.contains(&q.local)));
                writes.then_some(b.blocks[p.block].term.span)
            }
        })
}

/// The name of field `f` of a place of type `pt`.
fn field_name(tcx: &Tcx, pt: PlaceTy, f: FieldIdx) -> Option<String> {
    match tcx.kind(pt.ty) {
        TyKind::Adt(adt, _) => Some(sym(tcx.field_def(adt, pt.variant, f).name)),
        TyKind::Tuple(_) => Some(enrang_base::Idx::index(f).to_string()),
        TyKind::Object(s) => (tcx.shape(s).fields)
            .get(enrang_base::Idx::index(f))
            .map(|(n, _)| sym(n)),
        // A type parameter's field, read through its object type (an implicit
        // one) or its bounding class.
        TyKind::Param(p) => {
            let param = tcx.param(p);
            let bound = match param.implicit {
                Some(enrang_hir::Implicit::Shape(s)) => {
                    tcx.mk_object_shape((*tcx.shape(s)).clone())
                }
                _ => param.bounds.iter().find_map(|&b| match tcx.bound(b) {
                    enrang_hir::Bound::Class { adt, args } => {
                        Some(tcx.mk_adt(*adt, &tcx.list(*args)))
                    }
                    enrang_hir::Bound::Iface { .. } => None,
                })?,
            };
            field_name(tcx, PlaceTy::of(bound), f)
        }
        _ => None,
    }
}

/// A place as the user wrote it (`this.owner`, `found.name`, `*r`, `xs[i]`), or
/// `None` when part of it has no name.
fn place_text(tcx: &Tcx, b: &Body, p: Place) -> Option<String> {
    projs_text(tcx, b, p.local, b.projs(p))
}

/// [`place_text`] of `local` with `projs` applied.
fn projs_text(tcx: &Tcx, b: &Body, local: Local, projs: &[Proj]) -> Option<String> {
    let out = local_name(tcx, b, local)?;
    let pt = PlaceTy::of(b.locals[local].ty);
    projs_text_from(tcx, b, out, pt, projs, is_this(tcx, b, local))
}

/// `projs` applied to the text `out` of a place of type `pt`; a first `Deref`
/// prints nothing when `silent` (`this`, or a capture read through its
/// reference).
fn projs_text_from(
    tcx: &Tcx,
    b: &Body,
    mut out: String,
    mut pt: PlaceTy,
    projs: &[Proj],
    silent: bool,
) -> Option<String> {
    let mut pending_deref = false;
    for (i, &proj) in projs.iter().enumerate() {
        match proj {
            Proj::Deref => pending_deref = !(i == 0 && silent),
            Proj::Field(f) => {
                pending_deref = false;
                // A nullable's or a case's payload tuple prints as the value.
                let name = field_name(tcx, pt, f)?;
                let tuple = pt.variant.is_none() && matches!(tcx.kind(pt.ty), TyKind::Tuple(_));
                if tuple {
                    // A tuple part as the source indexes it, `t[0]`.
                    out = format!("{out}[{name}]");
                } else if !(pt.variant.is_some() && name == "0") {
                    out = format!("{out}.{name}");
                }
            }
            Proj::Variant(_) => {}
            // A loop's own element, `xs[#i]`, is the source as written (`xs`).
            Proj::Index(l) if matches!(b.locals[l].kind, LocalKind::HiddenLoop(_)) => {
                return Some(out);
            }
            Proj::Index(l) => {
                pending_deref = false;
                out = format!("{out}[{}]", index_text(tcx, b, l));
            }
            Proj::ConstIndex(n) => {
                pending_deref = false;
                out = format!("{out}[{n}]");
            }
        }
        pt = pt.project(tcx, proj)?;
    }
    if pending_deref {
        out = format!("*{out}");
    }
    Some(out)
}

/// An index local as written: its name, the constant or named local a
/// temporary holds, else `i`.
fn index_text(tcx: &Tcx, b: &Body, l: Local) -> String {
    if let Some(n) = local_name(tcx, b, l) {
        return n;
    }
    let defs: Vec<&Rvalue> = (b.blocks.iter())
        .flat_map(|blk| &blk.stmts)
        .filter_map(|s| match &s.kind {
            StatementKind::Assign { dest, value } if *dest == Place::local(l) => Some(value),
            _ => None,
        })
        .collect();
    match defs.as_slice() {
        [Rvalue::Use(Operand::Const(c))] => match &c.kind {
            enrang_mir::ConstKind::Value(enrang_hir::ConstValue::Int(n, _)) => n.to_string(),
            _ => "i".to_owned(),
        },
        [Rvalue::Use(Operand::Copy(p))] if p.is_local() => {
            local_name(tcx, b, p.local).unwrap_or_else(|| "i".to_owned())
        }
        _ => "i".to_owned(),
    }
}

/// The type of `local` with `projs` applied.
fn projs_ty(tcx: &Tcx, b: &Body, local: Local, projs: &[Proj]) -> Option<Ty> {
    let mut pt = PlaceTy::of(b.locals[local].ty);
    for &x in projs {
        pt = pt.project(tcx, x)?;
    }
    Some(pt.ty)
}

/// The place a move path names exactly.
fn path_place(cx: &BodyCx, n: MovePathIdx) -> Option<Place> {
    let b = cx.body;
    (cx.moves.lookup.iter())
        .filter(|(_, v)| **v == (n, true))
        .map(|(p, _)| *p)
        .min_by_key(|p| b.projs(*p).len())
}

/// A move path as the user wrote it: its place, or for a constructor's field,
/// which has no place of its own, `this.f`.
fn path_text(cx: &BodyCx, n: MovePathIdx) -> Option<String> {
    if let Some(p) = path_place(cx, n) {
        return place_text(cx.tcx, cx.body, p);
    }
    let tcx = cx.tcx;
    let (f, ..) = cx.moves.ctor_fields.iter().flatten().find(|f| f.1 == n)?;
    let adt = tcx.adt_of(tcx.def(owner_def(cx.body)?).parent?)?;
    Some(format!("this.{}", tcx.field_def(adt, None, *f).name))
}

/// The place a move at `m.at` takes: the operand whose path is `m.path`, else the
/// first moved operand there.
fn moved_place(cx: &BodyCx, m: &MoveError) -> Option<Place> {
    let ops = crate::init::point_operands(cx.body, m.at);
    let moved = || {
        ops.iter().filter_map(|o| match o {
            Operand::Move(p) => Some(*p),
            _ => None,
        })
    };
    moved()
        .find(|p| cx.moves.lookup.get(p).map(|x| x.0) == Some(m.path))
        .or_else(|| moved().next())
}

/// The indexed expression `xs[...]` of `root` inside `span`, as written.
fn indexed_text(map: &SourceMap, span: Span, root: &str) -> Option<String> {
    let at = word_in(map, span, root)?;
    let rest = text(
        map,
        Span {
            lo: at.lo,
            hi: span.hi,
        },
    );
    let open = rest.find('[')?;
    let mut depth = 0;
    for (i, c) in rest.char_indices().skip(open) {
        match c {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(rest[..=i].to_owned());
                }
            }
            _ => {}
        }
    }
    None
}

/// The span of the statement or terminator at `p`.
fn span_at(b: &Body, p: Point) -> Span {
    b.stmt_at(p).map_or(b.blocks[p.block].term.span, |s| s.span)
}

/// The call that ends `p`'s block.
fn call_of(b: &Body, p: Point) -> Option<(&Callee, &[Operand], Span)> {
    let t = &b.blocks[p.block].term;
    match &t.kind {
        TerminatorKind::Call { callee, args, .. } => Some((callee, args.as_slice(), t.span)),
        _ => None,
    }
}

/// A named callee's definition.
fn callee_def(c: &Callee) -> Option<DefId> {
    match c {
        Callee::Fn(f) | Callee::Virtual { method: f, .. } => Some(f.def),
        _ => None,
    }
}

/// The type of a place, or `None`.
fn place_ty(cx: &BodyCx, p: Place) -> Option<Ty> {
    cx.body.place_ty(cx.tcx, p).map(|pt| pt.ty)
}

/// The text of a local's declaration (`u` of `const u = ...`).
fn decl_span(b: &Body, l: Local) -> Span {
    b.locals[l].span
}

fn is_clone(tcx: &Tcx, t: Ty) -> bool {
    tcx.is_clone(t, &ParamEnv::empty())
}

fn is_copy(tcx: &Tcx, t: Ty) -> bool {
    tcx.is_copy(t, &ParamEnv::empty())
}

/// The element type of an array, a fixed array or a slice.
fn element_of(tcx: &Tcx, t: Ty) -> Option<Ty> {
    match tcx.kind(t) {
        TyKind::Array(e) | TyKind::Slice(e) | TyKind::Fixed(e, _) => Some(e),
        TyKind::Ref(inner) => element_of(tcx, inner),
        _ => None,
    }
}

/// The places a statement or terminator mentions, operands, destinations and
/// borrowed places alike.
fn mentions(b: &Body, p: Point) -> Vec<Place> {
    match b.stmt_at(p) {
        Some(s) => enrang_mir::statement_places(&s.kind),
        None => {
            let mut v = enrang_mir::terminator_places(&b.blocks[p.block].term.kind);
            if let TerminatorKind::Call {
                callee: Callee::ClosureLocal(l),
                ..
            } = &b.blocks[p.block].term.kind
            {
                v.push(Place::local(*l));
            }
            v
        }
    }
}

/// Every point of the body.
fn points(b: &Body) -> impl Iterator<Item = Point> + '_ {
    b.blocks
        .iter_enumerated()
        .flat_map(|(blk, data)| (0..=data.stmts.len()).map(move |i| Point::new(blk, i)))
}

/// Points reachable from just after `at`, in breadth-first order.
fn after(b: &Body, at: Point) -> Vec<Point> {
    let mut out = Vec::new();
    let mut queue = VecDeque::from([(at.block, at.index as usize + 1)]);
    let mut seen = BTreeSet::new();
    while let Some((block, from)) = queue.pop_front() {
        for i in from..=b.blocks[block].stmts.len() {
            out.push(Point::new(block, i));
        }
        for s in b.blocks[block].term.kind.successors() {
            if seen.insert(s) {
                queue.push_back((s, 0));
            }
        }
    }
    out
}

/// A loop source's span with the `&` written before it (`&queue`).
fn with_amp(map: &SourceMap, span: Span) -> Span {
    let line = line_of(map, span.lo);
    let before = text(
        map,
        Span {
            lo: line.lo,
            hi: span.lo,
        },
    );
    match before.ends_with('&') {
        true => Span {
            lo: BytePos(span.lo.0 - 1),
            ..span
        },
        false => span,
    }
}

/// A loan's site as written: the `&s` of `r = &s`, else the loan's own span.
fn site_span(cx: &BodyCx, l: LoanId) -> Span {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let loan = &cx.loans.table[l];
    if let LoanKind::Hold(id) | LoanKind::HoldCrossing(id) = loan.kind
        && let Some(lp) = b.meta.loops.iter().find(|x| x.id == id)
    {
        return with_amp(map, lp.span);
    }
    if text(map, loan.span).starts_with('&') {
        return loan.span;
    }
    match b.stmt_at(loan.site).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            value:
                Rvalue::Ref {
                    place,
                    origin: BorrowOrigin::Explicit,
                },
            ..
        }) => place_text(tcx, b, *place)
            .and_then(|t| word_in(map, loan.span, &format!("&{t}")))
            .unwrap_or(loan.span),
        _ => loan.span,
    }
}

// ---------------------------------------------------------------------------------
// Conflicts (EN0706-EN0712, EN0715, EN0718).

pub fn report_conflict(cx: &BodyCx, c: &BorrowConflict) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let loan = &cx.loans.table[c.loan];
    let site = site_span(cx, c.loan);
    let root = loan.path.root;
    let root_name = local_name(tcx, b, root);
    let place = place_text(tcx, b, c.access.place)
        .or_else(|| root_name.clone())
        .unwrap_or_else(|| text(map, c.access.span).to_owned());
    // A receiver is named as the call writes it, `a` of `a.push(1)` on a
    // reference `a`, not `*a`.
    let place = match (c.access.method, place.strip_prefix('*')) {
        (Some(_), Some(inner)) => inner.to_owned(),
        _ => place,
    };
    // A holder the source names, else none (never the place itself).
    let holder =
        (c.holder.and_then(|h| holder_name(cx, h))).filter(|h| Some(h) != root_name.as_ref());
    // A receiver's borrow is the call it is for, whose span holds it (G08, G23).
    let primary = match (c.access.method, call_of(b, c.at)) {
        (Some(_), Some((_, _, span)))
            if b.stmt_at(c.at).is_some()
                && span.lo <= c.access.span.lo
                && c.access.span.hi <= span.hi =>
        {
            span
        }
        // A loop's source is its `&q` as written (T:676).
        _ if b.meta.loops.iter().any(|l| l.span == c.access.span) => with_amp(map, c.access.span),
        _ => c.access.span,
    };
    let method = c.access.method.map(sym);
    let hold = matches!(loan.kind, LoanKind::Hold(_) | LoanKind::HoldCrossing(_))
        || (loan.origin == BorrowOrigin::ForOfHidden && loan.kind == LoanKind::Site);
    let later = |d: Diagnostic, label: &str| match c.later_use {
        Some((l, span)) => {
            let name = local_name(tcx, b, l);
            // A use with no text of its own, as the drop at a scope's end is, is
            // shown at the first statement after the conflict that names the
            // holder (H05: `moved[1]`), never past the end of a line.
            let blank = text(map, span).trim().is_empty();
            let named = |s: Span| name.as_deref().and_then(|n| word_in(map, s, n));
            let next = || {
                after(b, c.at).into_iter().find_map(|p| {
                    (mentions(b, p).iter().any(|pl| pl.local == l))
                        .then(|| named(span_at(b, p)))
                        .flatten()
                })
            };
            match (named(span), blank) {
                (Some(at), _) => d.with_secondary(at, label),
                (None, false) => d.with_secondary(span, label),
                // No such statement: the label would point past the code.
                (None, true) => match next() {
                    Some(at) => d.with_secondary(at, label),
                    None => d,
                },
            }
        }
        None => d,
    };
    let held_by = |what: &str| match &holder {
        Some(h) if c.holder != Some(Local::RETURN) => format!("{what}, held by `{h}`"),
        _ => what.to_owned(),
    };
    match c.code {
        Code::EN0706 | Code::EN0707 if hold => hold_change(cx, c, primary, &place),
        Code::EN0706 if view_of(cx, c).is_some() => {
            view_change(cx, c, primary, view_of(cx, c).expect("a view"))
        }
        Code::EN0706 => {
            let label = match &method {
                Some(m) => format!("`{m}` changes `{place}`, so it needs exclusive access to it"),
                None => format!("`{place}` changes here"),
            };
            let kind = borrow_kind(cx, c);
            let src = root_name.clone().unwrap_or_else(|| place.clone());
            let message = match &holder {
                Some(h) => format!("`{place}` cannot change while `{h}` still points into it"),
                None => format!("`{place}` cannot change while a borrow of it is still used"),
            };
            let d = Diagnostic::new(c.code, message, primary, label).with_secondary(
                site,
                held_by(&format!("{kind} borrow of `{src}` starts here")),
            );
            let again = match &holder {
                Some(h) => format!("`{h}` is used again here"),
                None => "the borrow is used again here".to_owned(),
            };
            let d = later(d, &again).rule(RULE_BORROWS);
            match copy_instead(cx, c) {
                Some(help) => d.with_help(help),
                None => d,
            }
        }
        Code::EN0707 => {
            if loan.origin == BorrowOrigin::CompoundTarget {
                return reserved(cx, c, primary, &place);
            }
            let label = match c.access.kind {
                AccessKind::ExclusiveBorrow => "second exclusive borrow".to_owned(),
                _ => format!("`{place}` changes here"),
            };
            let in_call = holder_in_call(cx, c);
            let first = match in_call {
                true => "first exclusive borrow, still live until the call returns".to_owned(),
                false => held_by("first exclusive borrow"),
            };
            let message = match c.access.kind {
                AccessKind::ExclusiveBorrow => {
                    format!("cannot borrow `{place}` as exclusive twice at the same time")
                }
                _ => match &holder {
                    Some(h) => format!("cannot change `{place}` while `{h}` may write into it"),
                    None => format!("cannot change `{place}` while it is borrowed"),
                },
            };
            let d = Diagnostic::new(c.code, message, primary, label).with_secondary(site, first);
            let d = match in_call {
                true => d,
                false => later(
                    d,
                    &format!(
                        "`{}` is used again here",
                        holder.as_deref().unwrap_or("the borrow")
                    ),
                ),
            };
            let d = d.rule(RULE_BORROWS);
            let array = place_ty(cx, c.access.place).and_then(|t| element_of(tcx, t));
            match (in_call, array) {
                (true, Some(_)) => d.with_help(Help::text(format!(
                    "to exchange two elements of one array, use `{place}.swap(i, j)`"
                ))),
                _ => d,
            }
        }
        Code::EN0708 => read_while_written(cx, c, primary, &place),
        Code::EN0709 => {
            let message = match hold {
                true => format!("cannot move `{place}` while iterating over it"),
                false => format!("cannot move `{place}` while it is borrowed"),
            };
            let kind = borrow_kind(cx, c);
            let d = Diagnostic::new(c.code, message, primary, format!("`{place}` moves here"));
            let d = match hold {
                true => d.with_secondary(site, format!("`{place}` is borrowed here")),
                false => {
                    let d = d.with_secondary(
                        site,
                        held_by(&format!("{kind} borrow of `{place}` starts here")),
                    );
                    later(d, "the borrow is still in use here")
                }
            };
            // A copy only of a value that has one (`Clone`).
            let clone = place_ty(cx, c.access.place).is_some_and(|t| is_clone(tcx, t));
            let copy = match clone {
                true => format!(", or move a copy: `{}`", clone_call(&place)),
                false => String::new(),
            };
            d.with_help(Help::text(match hold {
                true => format!("move `{place}` after the loop{copy}"),
                false => format!("move `{place}` after its last borrow{copy}"),
            }))
        }
        Code::EN0710 => returned_local(cx, c),
        Code::EN0711 => {
            let s = root_name.clone().unwrap_or_else(|| place.clone());
            let message = match &holder {
                Some(h) if c.holder != Some(Local::RETURN) => {
                    format!("`{s}` is dropped while `{h}` still borrows it")
                }
                _ => format!("`{s}` is dropped while it is still borrowed"),
            };
            let kind = borrow_kind(cx, c);
            // An explicit `dispose(q)` ends `q` there, not at its block's end.
            let disposed = text(map, primary).trim_start().starts_with("dispose(");
            let mut d = Diagnostic::new(c.code, message, primary, format!("`{s}` is dropped here"));
            if b.locals[root].kind == LocalKind::User && !disposed {
                d = d.with_secondary(
                    decl_span(b, root),
                    format!("`{s}` lives until the end of this block"),
                );
            }
            let d = d.with_secondary(
                site,
                held_by(&format!("{kind} borrow of `{s}` starts here")),
            );
            let d = later(d, "the borrow is still in use here");
            match &holder {
                Some(h) if c.holder != Some(Local::RETURN) && disposed => d.with_help(Help::text(
                    format!("dispose of `{s}` after the last use of `{h}`"),
                )),
                Some(h) if c.holder != Some(Local::RETURN) => d.with_help(Help::text(format!(
                    "declare `{s}` outside the block so it lives as long as `{h}`"
                ))),
                _ => d,
            }
        }
        Code::EN0712 => {
            let message = match &holder {
                Some(h) if c.holder != Some(Local::RETURN) => {
                    format!("the temporary is dropped while `{h}` still borrows it")
                }
                _ => "the temporary is dropped while it is still borrowed".to_owned(),
            };
            let d = Diagnostic::new(c.code, message, primary, "the temporary is dropped here")
                .with_secondary(site, "borrow of the temporary starts here");
            // S:951's help is for an argument; a receiver or a borrow written as
            // the whole value is bound to a local too, by its own words.
            let in_call = call_of(b, loan.site).filter(|(_, _, call)| {
                call.lo <= site.lo && site.hi <= call.hi && text(map, *call).ends_with(')')
            });
            let made = match b.stmt_at(loan.site).map(|s| &s.kind) {
                Some(StatementKind::Assign { dest, .. }) => Some(*dest),
                _ => None,
            };
            let receiver = in_call.is_some_and(|(callee, args, _)| {
                callee_def(callee).is_some_and(|f| tcx.takes_this(f))
                    && made.is_some()
                    && args.first().and_then(Operand::place) == made
            });
            let help = match (loan.origin, receiver, in_call.is_some()) {
                (BorrowOrigin::AutoBorrow, ..) | (_, true, _) => {
                    "bind the receiver to a local first"
                }
                (_, false, true) => "bind the argument first",
                (_, false, false) => "bind the value to a local first, then borrow the local",
            };
            later(d, "the borrow is still in use here").with_help(Help::text(help))
        }
        Code::EN0715 => {
            let captured = root_name.clone().unwrap_or_else(|| place.clone());
            // A closure with no name, an arrow passed as it is written, is "the
            // arrow", in plain words.
            let closure = holder
                .as_ref()
                .map_or_else(|| "the arrow".to_owned(), |h| format!("`{h}`"));
            // The live loan is the capture, or the access is: `grow` capturing
            // `xs` while `e`, a plain reference, still points into it.
            let captures = loan.origin == BorrowOrigin::ClosureCapture;
            if !captures {
                let by = capturing_closure(b, c.at)
                    .and_then(|l| local_name(tcx, b, l))
                    .map_or_else(|| "the arrow".to_owned(), |n| format!("`{n}`"));
                let at = format!("{by} captures `{captured}` here");
                // The live loan is an argument's, passed to a call still running.
                let callee = call_of(b, loan.site)
                    .filter(|_| holder.is_none())
                    .and_then(|(f, _, _)| callee_def(f))
                    .map(|f| name_of(tcx, f));
                if let Some(f) = callee {
                    let d = Diagnostic::new(
                        c.code,
                        format!("`{captured}` is locked while `{f}` will still use it"),
                        primary,
                        at,
                    )
                    .with_secondary(site, format!("`{captured}` is passed to `{f}` here"));
                    return later(d, &format!("`{f}` is still running here")).with_help(
                        Help::text(format!(
                            "use `{captured}` after `{f}` returns, or pass it to the closure as a parameter"
                        )),
                    );
                }
                let d = Diagnostic::new(
                    c.code,
                    format!("`{captured}` is locked while {closure} will still be used"),
                    primary,
                    at,
                )
                .with_secondary(site, format!("{closure} borrows `{captured}` here"));
                return later(d, &format!("{closure} is used again here")).with_help(Help::text(
                    format!(
                        "use `{captured}` after the last use of {closure}, or pass it to the closure as a parameter"
                    ),
                ));
            }
            let d = Diagnostic::new(
                c.code,
                format!("`{captured}` is locked while {closure} will still be used"),
                primary,
                format!("`{captured}` is used here"),
            )
            .with_secondary(site, format!("{closure} captures `{captured}` here"));
            later(d, &format!("{closure} is used again here")).with_help(Help::text(format!(
                "use `{captured}` after the last use of {closure}, or pass it to the closure as a parameter"
            )))
        }
        Code::EN0718 => {
            let d = Diagnostic::new(
                c.code,
                format!("`{place}` is used twice at once"),
                primary,
                "second use",
            )
            .with_secondary(site, "first use, still live here");
            // S:976: every closure value is used exclusively, whatever it does
            // with its captures.
            later(d, "the first use ends here").note(
                "a closure value is used exclusively, so it can't be called, forwarded or captured again while another use of it is live",
            )
        }
        _ => Diagnostic::new(c.code, c.code.title(), primary, ""),
    }
}

/// What a holder points into through a call that hands out a part of its
/// receiver: a `slice` view of an array or a string (S:1436), or the result of a
/// virtual call that locks the object only because an override may return a
/// reference into it (S:931).
struct ViewOf {
    /// The call as written, `list.slice(0, 1)`.
    call: Span,
    /// The result's referent type.
    ty: Ty,
    /// A `slice` of an array, whose copy is `[...v]`.
    array: bool,
}

fn view_of(cx: &BodyCx, c: &BorrowConflict) -> Option<ViewOf> {
    let (tcx, b) = (cx.tcx, cx.body);
    let h = c.holder?;
    if b.locals[h].kind != LocalKind::User {
        return None;
    }
    // The call whose result `h` is, directly or through a moved temporary.
    let made = |l: Local| {
        points(b).find_map(|p| match &b.blocks[p.block].term.kind {
            TerminatorKind::Call {
                callee, args, dest, ..
            } if b.stmt_at(p).is_none() && *dest == Place::local(l) => {
                Some((callee, args, b.blocks[p.block].term.span))
            }
            _ => None,
        })
    };
    let (callee, args, span) = made(h).or_else(|| {
        points(b).find_map(|p| match b.stmt_at(p).map(|s| &s.kind) {
            Some(StatementKind::Assign {
                dest,
                value: Rvalue::Use(Operand::Move(t) | Operand::Copy(t)),
            }) if *dest == Place::local(h)
                && t.is_local()
                && b.locals[t.local].kind == LocalKind::Temp =>
            {
                made(t.local)
            }
            _ => None,
        })
    })?;
    let ty = match tcx.kind(b.locals[h].ty) {
        TyKind::Ref(t) => t,
        _ => return None,
    };
    let f = callee_def(callee)?;
    let library = tcx.module(tcx.def(f).module).library;
    let slice = library && name_of(tcx, f) == "slice";
    let override_only = matches!(callee, Callee::Virtual { .. })
        && !matches!(&crate::contract(tcx, f).sources, enrang_hir::RetSources::Params(s) if s.contains(&0));
    if !(slice || override_only) || args.is_empty() {
        return None;
    }
    let array = slice && matches!(tcx.kind(ty), TyKind::Slice(_));
    Some(ViewOf {
        call: span,
        ty,
        array,
    })
}

/// A library method that grows an array or a string (S:1436's `grows here`).
fn grows(method: &str) -> bool {
    matches!(
        method,
        "push" | "insert" | "extend" | "extendCloned" | "pushByte" | "pushCodePoint"
    ) || method.starts_with("push")
}

/// EN0706 against a view or an override's result (S:1436, S:931): `` `list`
/// can't change while `head` points into it ``, with its three labels and the
/// help to keep a copy.
fn view_change(cx: &BodyCx, c: &BorrowConflict, primary: Span, v: ViewOf) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let loan = &cx.loans.table[c.loan];
    let h = c.holder.expect("a holder");
    let holder = local_name(tcx, b, h).unwrap_or_default();
    let src = local_name(tcx, b, loan.path.root).unwrap_or_else(|| text(map, v.call).to_owned());
    // Plan d.13: only an array view's source `grows here`, for a growing change.
    let grown = v.array && c.access.method.is_some_and(|m| grows(&sym(m)));
    let change = match grown {
        true => format!("`{src}` grows here"),
        false => format!("`{src}` changes here"),
    };
    let d = Diagnostic::new(
        c.code,
        format!("`{src}` can't change while `{holder}` points into it"),
        primary,
        change,
    )
    .with_secondary(v.call, format!("`{holder}` points into `{src}` from here"))
    .rule(RULE_BORROWS);
    let d = match c.later_use {
        Some((l, span)) => {
            let at = local_name(tcx, b, l)
                .and_then(|n| word_in(map, span, &n))
                .unwrap_or(span);
            d.with_secondary(at, format!("`{holder}` is still used here"))
        }
        None => d,
    };
    let call = text(map, v.call);
    let copy = match (v.array, tcx.kind(v.ty)) {
        (true, _) => Some(format!("[...{call}]")),
        (false, TyKind::Str) => Some(format!("{call}.toString()")),
        (false, _) if is_clone(tcx, v.ty) => Some(format!("{call}.clone()")),
        _ => None,
    };
    let decl = decl_span(b, h);
    let kw = ["const", "let"]
        .into_iter()
        .find(|kw| keyword_before(map, decl, kw).is_some());
    match (copy, kw) {
        (Some(copy), Some(kw)) => {
            d.with_help(Help::text(format!("keep a copy: {kw} {holder} = {copy};")))
        }
        _ => d,
    }
}

/// Whether the capture made at `at` is of a variable its arrow assigns whole:
/// the arrow's environment field `k` that holds it is written through, as
/// `*(*_1).k = v`.
fn capture_reassigns(cx: &BodyCx, at: Point) -> bool {
    let b = cx.body;
    let Some(StatementKind::Assign {
        dest: cap,
        value:
            Rvalue::Ref {
                origin: BorrowOrigin::ClosureCapture,
                ..
            },
    }) = b.stmt_at(at).map(|s| &s.kind)
    else {
        return false;
    };
    let env = points(b).find_map(|p| match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            dest,
            value: Rvalue::Aggregate(enrang_mir::AggregateKind::ClosureEnv, ops),
        }) => (ops.iter().position(|o| o.place() == Some(*cap))).map(|k| (*dest, k)),
        _ => None,
    });
    let Some((env, k)) = env else {
        return false;
    };
    let arrow = points(b).find_map(|p| match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            value:
                Rvalue::ClosureValue {
                    func: enrang_mir::ClosureFn::Arrow(a),
                    env: e,
                },
            ..
        }) if *e == env => Some(*a),
        _ => None,
    });
    let parent = match b.owner {
        BodyOwner::Fn(d) => enrang_hir::BodyOwner::Fn(d),
        BodyOwner::Test(d) => enrang_hir::BodyOwner::Test(d),
        BodyOwner::Statements(m) => enrang_hir::BodyOwner::Statements(m),
        BodyOwner::Arrow(p, _) => p,
        BodyOwner::Shim(_) => return false,
    };
    let Some(ab) = arrow.and_then(|a| cx.bodies.get(&BodyOwner::Arrow(parent, a))) else {
        return false;
    };
    let field = enrang_hir::FieldIdx(k as u32);
    let whole = [Proj::Deref, Proj::Field(field), Proj::Deref];
    points(ab).any(|p| {
        matches!(ab.stmt_at(p).map(|s| &s.kind),
            Some(StatementKind::Assign { dest, .. })
                if dest.local == Local(1) && ab.projs(*dest) == whole)
    })
}

/// The closure local that the capture made at `at` goes into: the destination
/// of the `closure(...)` whose environment holds the capture's temporary.
fn capturing_closure(b: &Body, at: Point) -> Option<Local> {
    let Some(StatementKind::Assign { dest: cap, value }) = b.stmt_at(at).map(|s| &s.kind) else {
        return None;
    };
    if !matches!(
        value,
        Rvalue::Ref {
            origin: BorrowOrigin::ClosureCapture,
            ..
        }
    ) {
        return None;
    }
    let env = points(b).find_map(|p| match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            dest,
            value: Rvalue::Aggregate(_, ops),
        }) if ops.iter().any(|o| o.place() == Some(*cap)) => Some(*dest),
        _ => None,
    })?;
    points(b).find_map(|p| match b.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            dest,
            value: Rvalue::ClosureValue { env: e, .. },
        }) if *e == env && dest.is_local() => Some(dest.local),
        _ => None,
    })
}

/// Whether the conflict's loan is shared or exclusive, as the modes say.
fn borrow_kind(cx: &BodyCx, c: &BorrowConflict) -> &'static str {
    let held = HeldResults::run(cx, false);
    match crate::wlive::compute_modes(cx, &held).exclusive(c.loan) {
        true => "exclusive",
        false => "shared",
    }
}

/// G09's "still live until the call returns": the loan's holder is a temporary
/// that the call ending the access's block takes as an argument.
fn holder_in_call(cx: &BodyCx, c: &BorrowConflict) -> bool {
    let b = cx.body;
    let Some(h) = c.holder else { return false };
    b.locals[h].kind == LocalKind::Temp
        && call_of(b, c.at).is_some_and(|(_, args, _)| {
            args.iter()
                .any(|a| a.place().is_some_and(|p| p == Place::local(h)))
        })
}

/// A change of a loop's held source (G08, G21; A:1310-1314).
fn hold_change(cx: &BodyCx, c: &BorrowConflict, primary: Span, place: &str) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let loan = &cx.loans.table[c.loan];
    let lp = match loan.kind {
        LoanKind::Hold(l) | LoanKind::HoldCrossing(l) => b.meta.loops.iter().find(|x| x.id == l),
        _ => None,
    };
    let source = with_amp(map, lp.map_or(loan.span, |l| l.span));
    let src_text = text(map, source);
    // Only a write of the whole source, or of a path it goes through, is a
    // reassignment (G21): `xs = []`, and `this.view = other` in a loop over
    // `this.view` (`LTK-5`), as is an arrow's capture of a variable the arrow
    // assigns (`run(() => { xs = []; })`); an exclusive borrow of it, or a local
    // function's hidden argument, changes it (G08).
    let through = |pl: Place| match lp.map(|l| &l.source) {
        Some(LoopSource::Path(src)) => {
            pl.local == src.local && b.projs(*src).starts_with(b.projs(pl))
        }
        _ => false,
    };
    let reassign = ((c.access.place.is_local() || through(c.access.place))
        && matches!(c.access.kind, AccessKind::Reassign | AccessKind::Write)
        && c.access.method.is_none())
        || capture_reassigns(cx, c.at);
    let shared = !crate::wlive::compute_modes(cx, &HeldResults::run(cx, false)).exclusive(c.loan);
    // A loop over a copy frees the access from this loop's own loans only, its
    // hold, crossing loans and binding's: another the access meets too, an outer
    // loop's hold or `xs.first()`'s, stays (A:1314).
    let own = |id: &LoanId| {
        let other = &cx.loans.table[*id];
        lp.is_some_and(|l| match other.kind {
            LoanKind::Hold(x) | LoanKind::HoldCrossing(x) => x == l.id,
            LoanKind::Site => other.site == l.bind,
            _ => false,
        })
    };
    let fixable = shared
        && c.others.iter().all(own)
        && lp.is_some_and(|l| !derefs_by_hand(b, l.binding) && reads_as_value(cx, l.binding));
    let src_ty = lp.and_then(|l| match &l.source {
        LoopSource::Path(p) => place_ty(cx, *p),
        LoopSource::Once(x) => Some(b.locals[*x].ty),
    });
    let elem_clone = src_ty
        .and_then(|t| element_of(tcx, t))
        .is_some_and(|e| is_clone(tcx, e));
    if reassign {
        let d = Diagnostic::new(
            c.code,
            format!("cannot reassign `{place}` during iteration"),
            primary,
            "cannot reassign while borrowed",
        )
        .with_secondary(source, format!("`{place}` is borrowed here"));
        return match (fixable && elem_clone, src_text.strip_prefix('&')) {
            (true, Some(inner)) => d.with_help(Help::suggest(
                format!(
                    "iterate over `{}` if reassignment is intentional",
                    clone_call(inner)
                ),
                vec![Edit::replace(source, clone_call(inner))],
            )),
            _ => d,
        };
    }
    let begins = match shared {
        true => "immutable borrow begins here",
        false => "mutable borrow begins here",
    };
    let structural = c.access.method.is_some();
    let mut d = Diagnostic::new(
        c.code,
        format!("cannot mutate `{place}` while iterating over it"),
        primary,
        "conflicting mutable access",
    )
    .with_secondary(source, begins);
    if structural {
        d = d.note("structural mutations may invalidate the iterator");
    }
    // G08's "collect new jobs separately" fits a change that adds elements; any
    // other change, as `pop()` or a method of the holder, loops over a copy.
    let adds = c.access.method.is_some_and(|m| grows(&sym(m)));
    match (fixable && elem_clone, src_text.starts_with('&')) {
        (true, true) => d.with_help(Help::suggest(
            match structural && adds {
                true => "collect new jobs separately, or loop over a copy",
                false => "loop over a copy",
            },
            vec![
                Edit::replace(
                    Span {
                        lo: source.lo,
                        hi: source.lo + 1,
                    },
                    "[...",
                ),
                Edit::insert(source.hi, "]"),
            ],
        )),
        _ => d,
    }
}

/// Whether every use of a loop's binding `x` reads as well from the value a loop
/// over a copy binds as from the reference it is (A:1314): a place through it
/// (`x.n`), or its reborrow `&*x` as a method's receiver (`x.length()`,
/// `x == "a"`) or an argument of `console.log`, `console.error` or a template;
/// never `x` kept or passed where a reference is due (`saved = x`, `add(x)`).
fn reads_as_value(cx: &BodyCx, x: Local) -> bool {
    let (tcx, b) = (cx.tcx, cx.body);
    points(b).all(|p| {
        let through: Vec<Place> = (mentions(b, p).into_iter())
            .filter(|pl| pl.local == x)
            .collect();
        if through.is_empty() {
            return true;
        }
        match b.stmt_at(p).map(|s| &s.kind) {
            Some(StatementKind::StorageLive(_) | StatementKind::StorageDead(_)) => true,
            Some(StatementKind::Assign { dest, .. }) if *dest == Place::local(x) => true,
            Some(StatementKind::Assign {
                dest,
                value:
                    Rvalue::Ref {
                        place,
                        origin: BorrowOrigin::Reborrow,
                    },
            }) if place.local == x && b.projs(*place) == [Proj::Deref] && dest.is_local() => {
                let arg = |a: &Operand| a.place() == Some(*dest);
                match call_of(b, p) {
                    Some((callee, args, _)) if prints(callee) => args.iter().any(arg),
                    Some((callee, args, _)) => {
                        args.first().is_some_and(arg)
                            && callee_def(callee)
                                .and_then(|d| tcx.sig_opt(d))
                                .is_some_and(|s| s.receiver.is_some())
                    }
                    None => false,
                }
            }
            _ => through
                .iter()
                .all(|pl| b.projs(*pl).len() > 1 && b.projs(*pl)[0] == Proj::Deref),
        }
    })
}

/// Whether the body derefs `x` by hand (`*x`), which a loop over a copy, whose
/// binding is a value, would reject; an auto-deref (`x.f`, a reborrow for a call)
/// is not one.
fn derefs_by_hand(b: &Body, x: Local) -> bool {
    points(b).any(|p| {
        let reborrow = matches!(
            b.stmt_at(p).map(|s| &s.kind),
            Some(StatementKind::Assign {
                value: Rvalue::Ref {
                    origin: BorrowOrigin::Reborrow,
                    ..
                },
                ..
            })
        );
        !reborrow
            && mentions(b, p)
                .iter()
                .any(|pl| pl.local == x && b.projs(*pl) == [Proj::Deref])
    })
}

/// G23's fix-it: `&queue[0]` becomes `queue[0].clone()` when the holder is a
/// `const` local the borrow initialises, of a `Clone` referent, used only where a
/// value reads as well: shown (`console.log`, templates) or compared.
fn copy_instead(cx: &BodyCx, c: &BorrowConflict) -> Option<Help> {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let loan = &cx.loans.table[c.loan];
    let h = c.holder?;
    let decl = &b.locals[h];
    if loan.origin != BorrowOrigin::Explicit
        || decl.kind != LocalKind::User
        || decl.mutable
        || !matches!(
            b.stmt_at(loan.site).map(|s| &s.kind),
            Some(StatementKind::Assign { dest, .. }) if *dest == Place::local(h)
        )
    {
        return None;
    }
    let TyKind::Ref(referent) = tcx.kind(decl.ty) else {
        return None;
    };
    if !is_clone(tcx, referent) || !only_shown(b, h, loan.site) {
        return None;
    }
    let site = site_span(cx, c.loan);
    let inner = text(map, site).strip_prefix('&')?;
    Some(Help::suggest(
        "keep a copy instead of a reference",
        vec![Edit::replace(site, format!("{inner}.clone()"))],
    ))
}

/// Whether every use of `h` but its initialisation at `init` is a reborrow or a
/// copy passed straight to `console.log`, `console.error` or a template.
fn only_shown(b: &Body, h: Local, init: Point) -> bool {
    points(b).filter(|p| *p != init).all(|p| {
        let uses = mentions(b, p).iter().any(|pl| pl.local == h);
        if !uses {
            return true;
        }
        match b.stmt_at(p).map(|s| &s.kind) {
            Some(StatementKind::StorageLive(_) | StatementKind::StorageDead(_)) => true,
            Some(StatementKind::Assign { dest, value }) => {
                // The holder itself, or its auto-reborrow; never a deref by hand,
                // `*h`, which a value would not take (A:1314).
                let reads = matches!(
                    value,
                    Rvalue::Ref { place, origin }
                        if place.local == h && match b.projs(*place) {
                            [] => true,
                            [Proj::Deref] => *origin == BorrowOrigin::Reborrow,
                            _ => false,
                        }
                ) || matches!(value, Rvalue::Use(Operand::Copy(pl)) if *pl == Place::local(h));
                reads
                    && dest.is_local()
                    && matches!(
                        call_of(b, p),
                        Some((callee, args, _))
                            if prints(callee) && args.iter().any(|a| a.place() == Some(*dest))
                    )
            }
            Some(_) => false,
            None => matches!(call_of(b, p), Some((callee, _, _)) if prints(callee)),
        }
    })
}

/// EN0707 against a compound target's reservation (O6): the right side borrows
/// the place for writing while the store waits.
fn reserved(cx: &BodyCx, c: &BorrowConflict, primary: Span, place: &str) -> Diagnostic {
    let map = cx.tcx.map();
    // The assignment as written, from its span, never its line's text, which may
    // hold a comment or another statement.
    let stmt = text(map, site_span(cx, c.loan)).trim();
    let d = Diagnostic::new(
        c.code,
        format!("`{place}` can't be borrowed for writing while the assignment to it waits"),
        primary,
        "exclusive borrow while the assignment waits to store",
    )
    .with_secondary(
        site_span(cx, c.loan),
        format!("the assignment reserves `{place}` here"),
    );
    match stmt.split_once(" += ") {
        Some((lhs, rhs)) => {
            let rhs = rhs.trim_end_matches(';').trim();
            d.with_help(Help::text(format!(
                "run the right side first: `const r = {rhs}; {lhs} += r;`"
            )))
        }
        None => d,
    }
}

/// EN0708: a read against a live exclusive loan (S:941), or a compound target's
/// store against a read the append still uses (O6).
fn read_while_written(cx: &BodyCx, c: &BorrowConflict, primary: Span, place: &str) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let line = |s: Span| map.loc(s.lo).line;
    if let Some((Callee::Form(FormCall::Append), _, stmt)) = call_of(b, c.at) {
        // The store's conflict, reported at the read whose loan it meets: the
        // call a receiver's borrow is for (`s.slice(0, 1)`), or the borrow. The
        // help copies the assignment as written, from its span (`stmt`), never its
        // line's text, which may hold a comment or another statement.
        let read = receiver_call(cx, c.loan).unwrap_or(primary);
        let st = text(map, stmt);
        let at = read.hi.0.checked_sub(stmt.lo.0).map(|n| n as usize);
        let d = Diagnostic::new(
            c.code,
            format!("`{place}` can't be read here while the assignment appends to it"),
            read,
            "read here, and still used when the assignment stores",
        );
        let string_read = loan_ty_is_str(cx, c);
        return match (
            at.filter(|&at| at <= st.len() && st.is_char_boundary(at)),
            string_read,
        ) {
            (Some(at), true) => d.with_help(Help::text(format!(
                "append a copy: `{}.toString(){};`",
                st[..at].trim_start(),
                st[at..].trim_end().trim_end_matches(';')
            ))),
            _ => d,
        };
    }
    let root = local_name(tcx, b, cx.loans.table[c.loan].path.root);
    let holder = (c.holder.and_then(|h| holder_name(cx, h))).filter(|h| Some(h) != root.as_ref());
    // The place read as written where it is a path, `t[0]` of `const b = t[0];`
    // (H39), not the local the copy initialises.
    let written = text(map, primary);
    let path_like = !written.is_empty()
        && written
            .chars()
            .all(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '$' | '.' | '[' | ']'));
    let place = match path_like && !written.starts_with(place) {
        true => written,
        false => place,
    };
    // The write that makes the loan exclusive, which the later use may be.
    let write = first_write(cx, c.loan);
    let writer = holder
        .as_deref()
        .map_or_else(|| "it".to_owned(), |h| format!("`{h}`"));
    let site = match write.or(c.later_use.map(|u| u.1)) {
        Some(span) => format!(
            "borrowed for writing here, because {writer} writes on line {}",
            line(span)
        ),
        None => "borrowed for writing here".to_owned(),
    };
    let message = match &holder {
        Some(h) => format!("`{place}` can't be read while `{h}` may write into it"),
        None => format!("`{place}` can't be read while a borrow of it may write into it"),
    };
    let mut d = Diagnostic::new(c.code, message, primary, "read here")
        .with_secondary(site_span(cx, c.loan), site);
    if let Some((l, span)) = c.later_use {
        let at = holder_name(cx, l)
            .and_then(|n| word_in(map, span, &n))
            .unwrap_or(span);
        let is_write = write.is_some_and(|w| w.lo <= span.lo && span.hi <= w.hi)
            || write.is_some_and(|w| span.lo <= w.lo && w.hi <= span.hi);
        match (is_write, write) {
            (false, Some(w)) => {
                d = d.with_secondary(w, "the write");
                d = d.with_secondary(at, "still used here");
            }
            _ => d = d.with_secondary(at, "the write"),
        }
        // After the write too, when it comes after the later use.
        let to = write.map_or(line(span), |w| line(w).max(line(span)));
        let from = line(site_span(cx, c.loan));
        d = d.with_help(Help::text(match from == to {
            true => format!("read `{place}` into a local before this statement"),
            false => format!("read `{place}` before line {from} or after line {to}"),
        }));
    }
    d.rule(RULE_BORROWS)
}

/// The call a receiver's borrow at a loan's site is for, when its span holds the
/// borrow's (`s.slice(0, 1)` for the `&s` of `slice`).
fn receiver_call(cx: &BodyCx, l: LoanId) -> Option<Span> {
    let b = cx.body;
    let loan = &cx.loans.table[l];
    let Some(StatementKind::Assign {
        dest,
        value: Rvalue::Ref { .. },
    }) = b.stmt_at(loan.site).map(|s| &s.kind)
    else {
        return None;
    };
    let (_, args, span) = call_of(b, loan.site)?;
    (args.first().and_then(|a| a.place()) == Some(*dest)
        && span.lo <= loan.span.lo
        && loan.span.hi <= span.hi)
        .then_some(span)
}

/// Whether the loan of a conflict borrows a `string`, which `.toString()` copies.
fn loan_ty_is_str(cx: &BodyCx, c: &BorrowConflict) -> bool {
    let loan = &cx.loans.table[c.loan];
    let tcx = cx.tcx;
    match cx.body.stmt_at(loan.site).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => place_ty(cx, *dest)
            .is_some_and(|t| matches!(tcx.kind(t), TyKind::Ref(i) if tcx.kind(i) == TyKind::Str)),
        _ => false,
    }
}

/// EN0710: a returned reference to a local (G10), or into the object an Own `this`
/// consumes (S:929).
fn returned_local(cx: &BodyCx, c: &BorrowConflict) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let loan = &cx.loans.table[c.loan];
    let root = loan.path.root;
    let def = owner_def(b);
    let f = def.map_or_else(|| "the function".to_owned(), |d| name_of(tcx, d));
    let site = site_span(cx, c.loan);
    if is_this(tcx, b, root) {
        return Diagnostic::new(
            c.code,
            format!("`{f}` returns a reference into the object it consumes"),
            site,
            "this reference would point at the consumed object",
        )
        .note("a `move` method gives up its object, which is disposed of when the method ends")
        .with_help(Help::text(
            "return the value itself, or take `this` by reference",
        ));
    }
    let s = local_name(tcx, b, root).unwrap_or_else(|| text(map, site).to_owned());
    let message = match b.locals[root].kind == LocalKind::Temp {
        true => format!("cannot return a reference to a temporary, `{s}`"),
        false => format!("cannot return a reference to local `{s}`"),
    };
    // A borrow made before the `return` whose value holds it is reported at that
    // `return`, the borrow a secondary span, as `rustc`'s E0515 does: `return
    // p.intoLexer();` after `new Lexer(&tmp)` (`D20-core-3`).
    let ret = return_at(cx, c.at).filter(|r| !(r.lo <= site.lo && site.hi <= r.hi));
    let mut d = match ret {
        Some(r) => Diagnostic::new(
            c.code,
            message,
            r,
            format!("the returned value still points into `{s}`"),
        )
        .with_secondary(site, format!("`{s}` is borrowed here")),
        None => Diagnostic::new(
            c.code,
            message,
            site,
            "this reference would point at freed memory",
        ),
    };
    if b.locals[root].kind == LocalKind::User {
        d = d.with_secondary(
            decl_span(b, root),
            format!("`{s}` is dropped when `{f}` returns"),
        );
    }
    let refs: Vec<String> = def
        .and_then(|d| tcx.sig_opt(d))
        .map(|sig| {
            sig.params
                .iter()
                .filter(|p| matches!(tcx.kind(p.ty), TyKind::Ref(_)))
                .map(|p| format!("`{}`", p.name))
                .collect()
        })
        .unwrap_or_default();
    let d = match refs.is_empty() {
        true => d.rule(format!(
            "a returned reference must borrow from a parameter, and `{f}` has no reference parameters."
        )),
        false => d.rule(format!(
            "a returned reference must borrow from a parameter: {}.",
            refs.join(" or ")
        )),
    };
    match owned_instead(cx, def, root, site).or_else(|| view_copy(cx, def, root, site)) {
        Some(help) => d.with_help(help),
        None => d,
    }
}

/// The statement that filled the return place on the way to `at`, the earliest
/// in source order when several paths fill it: the `return` whose value holds a
/// loan that `at`, a drop before the `Return`, meets.
fn return_at(cx: &BodyCx, at: Point) -> Option<Span> {
    let b = cx.body;
    let cfg = enrang_mir::Cfg::new(b);
    let fills = |q: Point| match b.stmt_at(q).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => dest.local == Local::RETURN,
        Some(_) => false,
        None => matches!(&b.blocks[q.block].term.kind,
            TerminatorKind::Call { dest, .. } if dest.local == Local::RETURN),
    };
    let mut found: Option<Span> = None;
    let mut seen = BTreeSet::new();
    let mut work = vec![(at.block, at.index as usize)];
    while let Some((bb, end)) = work.pop() {
        let hit = (0..end)
            .rev()
            .map(|i| Point::new(bb, i))
            .find(|&q| fills(q));
        match hit {
            Some(q) => {
                let s = span_at(b, q);
                found = Some(found.map_or(s, |f| if s.lo < f.lo { s } else { f }));
            }
            None => {
                for &pr in &cfg.preds[bb] {
                    if seen.insert(pr) {
                        work.push((pr, b.blocks[pr].stmts.len() + 1));
                    }
                }
            }
        }
    }
    found
}

/// S:1436's help for a returned part of a local, `return xs.slice(0, 2);`: keep a
/// copy, `[...xs.slice(0, 2)]` of an array's part or `.toString()` of a string's,
/// and return it by value, the return type made owned.
fn view_copy(cx: &BodyCx, def: Option<DefId>, root: Local, site: Span) -> Option<Help> {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let d = def?;
    let sig = tcx.sig_opt(d)?;
    let TyKind::Ref(inner) = tcx.kind(sig.ret) else {
        return None;
    };
    let name = local_name(tcx, b, root)?;
    // The returned expression: `return <name>.slice(...);` on one line.
    let line = line_of(map, site.lo);
    let t = text(map, line);
    let at = (site.lo.0 - line.lo.0) as usize;
    let start = t[..at].rfind("return ")? + "return ".len();
    let end = at + t[at..].find(';')?;
    let expr = t[start..end].trim_end();
    if !(expr.starts_with(&format!("{name}.slice(")) && expr.ends_with(')')) || start != at {
        return None;
    }
    let (owned, copy) = match tcx.kind(inner) {
        TyKind::Slice(e) => (format!("{}[]", tcx.ty_string(e)), format!("[...{expr}]")),
        TyKind::Str => ("string".to_owned(), format!("{expr}.toString()")),
        _ => return None,
    };
    if sig.ret_readonly {
        return None;
    }
    let message = format!("keep a copy: return {copy};");
    // The edit changes the return type, so only a body with no other `return`.
    if !one_return(b) {
        return Some(Help::text(message));
    }
    let ret = written_ret(map, tcx.def(d), &tcx.ty_string(sig.ret))?;
    let expr_span = Span {
        lo: line.lo + start as u32,
        hi: line.lo + (start + expr.len()) as u32,
    };
    Some(Help::suggest(
        message,
        vec![Edit::replace(ret, owned), Edit::replace(expr_span, copy)],
    ))
}

/// G10's fix-it: return the local itself when the result is `&T` of the local's
/// type and the borrow is `&s` of the whole local, written as the whole returned
/// expression (`return first(&s);` returns no `s`).
fn owned_instead(cx: &BodyCx, def: Option<DefId>, root: Local, site: Span) -> Option<Help> {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let d = def?;
    let sig = tcx.sig_opt(d)?;
    let TyKind::Ref(inner) = tcx.kind(sig.ret) else {
        return None;
    };
    let name = local_name(tcx, b, root)?;
    if inner != b.locals[root].ty || text(map, site) != format!("&{name}") || sig.ret_readonly {
        return None;
    }
    let rest = text(
        map,
        Span {
            lo: site.hi,
            hi: line_of(map, site.hi).hi,
        },
    );
    if keyword_before(map, site, "return").is_none()
        || !rest.trim_start().starts_with(';')
        || !one_return(b)
    {
        return None;
    }
    let ret = written_ret(map, tcx.def(d), &tcx.ty_string(sig.ret))?;
    Some(Help::suggest(
        "return the owned value instead",
        vec![
            Edit::replace(ret, tcx.ty_string(inner)),
            Edit::replace(site, name),
        ],
    ))
}

// ---------------------------------------------------------------------------------
// Moves and init (EN0601-EN0621 of the moves module).

pub fn report_move(cx: &BodyCx, m: &MoveError) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let moving = matches!(
        m.code,
        Code::EN0603 | Code::EN0604 | Code::EN0605 | Code::EN0607 | Code::EN0617
    );
    let moved = moved_place(cx, m).filter(|_| moving);
    let what = match (moved, m.code) {
        (Some(p), Code::EN0604) => local_name(tcx, b, p.local)
            .and_then(|root| indexed_text(map, m.span, &root))
            .or_else(|| place_text(tcx, b, p)),
        (Some(p), _) => place_text(tcx, b, p),
        (None, _) => path_text(cx, m.path),
    };
    let shown = what.clone().unwrap_or_else(|| text(map, m.span).to_owned());
    // The use, narrowed to the path where the statement names it (G07).
    let narrow = |span: Span| {
        what.as_deref()
            .and_then(|w| word_in(map, span, w))
            .unwrap_or(span)
    };
    match m.code {
        Code::EN0601 => used_after_move(cx, m, &shown, narrow(m.span)),
        Code::EN0602 => {
            // The local that was never assigned, not the part of it read: `g` of
            // `return g.name;` (A:994).
            let root = path_place(cx, m.path)
                .filter(|p| !p.is_local() && b.locals[p.local].kind == LocalKind::User)
                .map(|p| Place::local(p.local));
            let (shown, narrow) = match root.and_then(|p| place_text(tcx, b, p)) {
                Some(name) => {
                    let at = word_in(map, m.span, &name).unwrap_or(m.span);
                    (name, at)
                }
                None => (shown.clone(), narrow(m.span)),
            };
            let place = root.or_else(|| path_place(cx, m.path));
            let ty = place
                .and_then(|p| place_ty(cx, p))
                .map_or_else(|| "this type".to_owned(), |t| tcx.ty_string(t));
            let mut d = Diagnostic::new(
                m.code,
                format!("`{shown}` is used before it has a value"),
                narrow,
                format!("a `{ty}` has no default value"),
            );
            if let Some(p) = place.filter(|p| p.is_local()) {
                d = d.with_secondary(
                    decl_span(b, p.local),
                    format!("`{shown}` is declared here with no value"),
                );
            }
            d.with_help(Help::text(format!(
                "give `{shown}` a value where it is declared, or on every path before this use"
            )))
        }
        Code::EN0603 => move_out_of_ref(cx, m, &shown),
        Code::EN0604 => {
            let at = m.span;
            let d = Diagnostic::new(
                m.code,
                format!("cannot move out of `{shown}`"),
                narrow(at),
                "an element of an array can't be moved out",
            )
            .with_help(Help::text(format!("borrow it: `&{shown}`")));
            let elem_clone = moved
                .or_else(|| path_place(cx, m.path))
                .and_then(|p| place_ty(cx, p))
                .is_some_and(|t| is_clone(tcx, t));
            let d = match elem_clone {
                true => d.with_help(Help::text(format!("or copy it: `{shown}.clone()`"))),
                false => d,
            };
            // `.remove(i)` (O2) only where the array can shrink: a growable
            // `T[]`, not a fixed array or a `Slice`.
            let growable = moved.or_else(|| path_place(cx, m.path)).is_some_and(|p| {
                let projs = b.projs(p);
                let at = projs
                    .iter()
                    .rposition(|x| matches!(x, Proj::Index(_) | Proj::ConstIndex(_)));
                at.and_then(|i| projs_ty(tcx, b, p.local, &projs[..i]))
                    .is_some_and(|t| matches!(tcx.kind(t), TyKind::Array(_)))
            });
            let (arr, idx) = match shown.split_once('[') {
                Some((a, i)) => (a.to_owned(), i.trim_end_matches(']').to_owned()),
                None => (shown.clone(), "i".to_owned()),
            };
            match growable {
                true => d.with_help(Help::text(format!(
                    "or take it out of the array: `{arr}.remove({idx})`"
                ))),
                false => d,
            }
        }
        Code::EN0605 => {
            // The box is the place before the last `Box` deref: `*b` itself, or
            // a part of its contents, `b.name`, which `b.unbox().name` takes.
            let boxed = moved.or_else(|| path_place(cx, m.path)).and_then(|p| {
                let projs = b.projs(p);
                let at = (0..projs.len()).rev().find(|&i| {
                    projs[i] == Proj::Deref
                        && projs_ty(tcx, b, p.local, &projs[..i])
                            .is_some_and(|t| matches!(tcx.kind(t), TyKind::Boxed(_)))
                })?;
                let inner = projs_text(tcx, b, p.local, &projs[..at])?;
                let rest = match at + 1 == projs.len() {
                    true => String::new(),
                    false => shown.strip_prefix(inner.as_str())?.to_owned(),
                };
                Some((inner, rest))
            });
            let (head, help) = match boxed {
                Some((inner, rest)) if rest.is_empty() => (
                    format!("cannot move out of `*{inner}`"),
                    format!("take the value with `{inner}.unbox()`"),
                ),
                Some((inner, rest)) => (
                    format!("cannot move out of `{shown}`"),
                    format!("take the value with `{inner}.unbox()` first: `{inner}.unbox(){rest}`"),
                ),
                None => {
                    let inner = shown.strip_prefix('*').unwrap_or(&shown).to_owned();
                    (
                        format!("cannot move out of `*{inner}`"),
                        format!("take the value with `{inner}.unbox()`"),
                    )
                }
            };
            Diagnostic::new(
                m.code,
                head,
                narrow(m.span),
                "the contents of a `Box` can't be moved out",
            )
            .with_help(Help::text(help))
        }
        Code::EN0607 => {
            let p = moved.or_else(|| path_place(cx, m.path));
            let (owner, class, may) = p
                .and_then(|p| dtor_prefix(cx, p))
                .unwrap_or_else(|| (shown.clone(), "its class".to_owned(), false));
            let d = match may {
                false => Diagnostic::new(
                    m.code,
                    format!(
                        "cannot move `{shown}` out of `{owner}`, because `{class}` has a \
                         destructor"
                    ),
                    narrow(m.span),
                    format!("`{class}`'s destructor needs every field when it runs"),
                ),
                true => Diagnostic::new(
                    m.code,
                    format!(
                        "cannot move `{shown}` out of `{owner}`, because `{class}` may have a \
                         destructor"
                    ),
                    narrow(m.span),
                    format!(
                        "a `{class}` may be a class whose destructor needs every field, or one \
                         with fields `{class}` does not list"
                    ),
                ),
            };
            match p
                .and_then(|p| place_ty(cx, p))
                .is_some_and(|t| is_clone(tcx, t))
            {
                true => d.with_help(Help::text(format!("copy it: `{shown}.clone()`"))),
                false => d,
            }
        }
        Code::EN0610 => this_unset(cx, m, &shown),
        Code::EN0611 => {
            // Primary the move, secondary the first read it reaches in a later
            // turn (A:1007).
            let primary = narrow(m.span);
            let read = narrow(span_at(b, m.at));
            let d = Diagnostic::new(
                m.code,
                format!("`{shown}` was moved in an earlier turn"),
                primary,
                "moved here, in an earlier turn",
            );
            let d = match read != primary {
                true => d.with_secondary(read, "read here in the next turn"),
                false => d,
            };
            d.with_help(Help::text(format!(
                "borrow it instead (`&{shown}`), or move a copy each turn: `{shown}.clone()`"
            )))
        }
        Code::EN0613 => assign_const(cx, m, &shown),
        Code::EN0617 => {
            // The captured variable as the parent names it, with the part of it
            // moved (`u.name`), not the move's text (fix3).
            let place = moved.or_else(|| path_place(cx, m.path));
            let name = place
                .and_then(|p| captured_text(cx, p))
                .unwrap_or_else(|| shown.clone());
            let at = word_in(map, m.span, &name).unwrap_or(m.span);
            // A local function is named; an arrow is "the arrow".
            let (whose, who) = match (b.owner, owner_def(b)) {
                (BodyOwner::Fn(_), Some(d)) => {
                    let f = name_of(tcx, d);
                    (format!("`{f}`'s capture"), format!("`{f}`"))
                }
                _ => ("the arrow's capture".to_owned(), "the arrow".to_owned()),
            };
            let d = Diagnostic::new(
                m.code,
                format!("cannot move `{name}` out of {whose}"),
                at,
                format!("`{name}` is captured, so {who} can't give it away"),
            )
            .note("an arrow or a local function may run more than once, so what it captures stays where it is");
            match place
                .and_then(|p| place_ty(cx, p))
                .is_some_and(|t| is_clone(tcx, t))
            {
                true => d.with_help(Help::text(format!("move a copy instead: `{name}.clone()`"))),
                false => d,
            }
        }
        // S:1155: `` `report()` reads `count` before it is declared ``, labelled
        // with the declaration's line, and the help names its statement.
        Code::EN0618 => {
            let callee = call_of(b, m.at)
                .and_then(|(c, _, _)| callee_def(c))
                .map_or_else(|| "the function".to_owned(), |d| name_of(tcx, d));
            let decl = path_place(cx, m.path)
                .map(|p| decl_span(b, p.local))
                .filter(|s| s.lo != Span::DUMMY.lo);
            let label = match decl {
                Some(d) => format!("`{shown}` is declared on line {}", map.loc(d.lo).line),
                None => format!("`{shown}` is declared after this call"),
            };
            let d = Diagnostic::new(
                m.code,
                format!("`{callee}()` reads `{shown}` before it is declared"),
                m.span,
                label,
            );
            match decl.and_then(|d| statement_text(map, d)) {
                Some(stmt) => d.with_help(Help::text(format!("move this call below `{stmt}`"))),
                None => d.with_help(Help::text(format!(
                    "move this call below the declaration of `{shown}`"
                ))),
            }
        }
        Code::EN0619 => super_once(cx, m),
        Code::EN0621 => kept_assignment(cx, m, &shown),
        _ => Diagnostic::new(m.code, m.code.title(), m.span, ""),
    }
}

/// Whether `callee` prints its arguments: `console.log`, `console.error` or a
/// template, its arguments flattened or not.
fn prints(callee: &Callee) -> bool {
    matches!(
        callee.form(),
        Some(FormCall::Log | FormCall::Error | FormCall::Template)
    )
}

/// `text` without one pair of parentheses around all of it: `s += "?"` of
/// `(s += "?")`, but `f(a)` and `(a)(b)` unchanged.
fn unparenthesised(text: &str) -> &str {
    let t = text.trim();
    let Some(inner) = t.strip_prefix('(').and_then(|r| r.strip_suffix(')')) else {
        return t;
    };
    let mut depth = 0i32;
    for c in inner.chars() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        if depth < 0 {
            return t;
        }
    }
    inner.trim()
}

/// EN0621 (A:942, S:520, T:878): the assignment whose value would be kept, the
/// place that still owns it, and the help: assign one at a time for a chain, else
/// assign first, then copy, into the binding the value was kept in.
fn kept_assignment(cx: &BodyCx, m: &MoveError, shown: &str) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let place = moved_place(cx, m).or_else(|| path_place(cx, m.path));
    let target = place
        .and_then(|p| place_text(tcx, b, p).or_else(|| captured_text(cx, p)))
        .unwrap_or_else(|| shown.to_owned());
    // The assignment itself: the store into the place right before the kept use
    // in its block (`b = "xx".toString()` of `a = b = "xx".toString()`), else the
    // use's own span, which a compound assignment's is.
    let stored = place.and_then(|pl| {
        let stmts = &b.blocks[m.at.block].stmts;
        stmts[..(m.at.index as usize).min(stmts.len())]
            .iter()
            .rev()
            .find_map(|s| match &s.kind {
                StatementKind::Assign { dest, .. } if *dest == pl => Some(s.span),
                _ => None,
            })
    });
    let at = stored
        .filter(|s| s.lo >= m.span.lo && s.hi <= m.span.hi)
        .unwrap_or(m.span);
    let expr = unparenthesised(text(map, at)).to_owned();
    // A chain: the use is the right side of another assignment, `a = <at>`.
    let outer = text(
        map,
        Span {
            lo: m.span.lo,
            hi: at.lo,
        },
    )
    .trim_end()
    .trim_end_matches('(')
    .trim_end();
    let chain = (at.lo > m.span.lo)
        .then(|| outer.strip_suffix('='))
        .flatten()
        .filter(|lhs| !lhs.ends_with(['=', '!', '<', '>', '+', '-', '*', '/', '%', '&', '|', '^']))
        .map(|lhs| unparenthesised(lhs).to_owned())
        .filter(|lhs| !lhs.is_empty());
    // A binding the value would initialise, `const t = (s += "?");`.
    let binding = match b.stmt_at(m.at).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. })
            if dest.is_local() && b.locals[dest.local].kind == LocalKind::User =>
        {
            let name = local_name(tcx, b, dest.local);
            let decl = decl_span(b, dest.local);
            let kw = ["const", "let"]
                .into_iter()
                .find(|kw| keyword_before(map, decl, kw).is_some());
            name.zip(kw)
        }
        _ => None,
    };
    let help = match (chain, binding) {
        (Some(lhs), _) => {
            format!("assign one at a time: `{expr}; {lhs} = {target}.clone();`")
        }
        (None, Some((name, kw))) => {
            format!("assign first, then copy: `{expr}; {kw} {name} = {target}.clone();`")
        }
        (None, None) => format!(
            "assign first, then copy: `{expr};`, then write `{target}.clone()` in its place"
        ),
    };
    Diagnostic::new(
        m.code,
        "an assignment's value can't be kept",
        at,
        format!("`{expr}` is still owned by `{target}`"),
    )
    .with_help(Help::text(help))
}

/// The nearest prefix of `p` whose type has a destructor, and its class.
fn dtor_prefix(cx: &BodyCx, p: Place) -> Option<(String, String, bool)> {
    let (tcx, b) = (cx.tcx, cx.body);
    let projs = b.projs(p);
    for n in (0..projs.len()).rev() {
        let ty = projs_ty(tcx, b, p.local, &projs[..n])?;
        match tcx.kind(ty) {
            TyKind::Adt(adt, args) if tcx.class_dtor(adt, args).is_some() => {
                let owner = projs_text(tcx, b, p.local, &projs[..n])?;
                return Some((owner, name_of(tcx, tcx.adt(adt).def), false));
            }
            TyKind::Param(_) => {
                let owner = projs_text(tcx, b, p.local, &projs[..n])?;
                return Some((owner, tcx.ty_string(ty), true));
            }
            _ => {}
        }
    }
    None
}

/// Where a move path was moved, and how: the call it was passed to, the method it
/// was the receiver of, the loop that took it, or the place it went into.
enum MovedBy {
    Arg {
        callee: DefId,
        index: usize,
        site: Span,
    },
    Receiver {
        method: DefId,
    },
    Loop,
    Into(String),
    Other,
}

/// How `path` was moved at `site`, and the place the move took: the path itself,
/// a prefix of it (`e.open()` uses up `e.inside`), or a part of it (`p.first`
/// moved out of a `p` used whole).
fn moved_by(cx: &BodyCx, path: MovePathIdx, site: Span) -> (MovedBy, Option<Place>) {
    let (tcx, b) = (cx.tcx, cx.body);
    let md = &cx.moves;
    // `n` is `a` or one of its prefixes.
    let above = |a: MovePathIdx, n: MovePathIdx| {
        let mut cur = Some(a);
        while let Some(c) = cur {
            if c == n {
                return true;
            }
            cur = md.paths[c].parent;
        }
        false
    };
    let moved_of = |op: &Operand| match op {
        Operand::Move(p) => md
            .lookup
            .get(p)
            .is_some_and(|(n, _)| above(path, *n) || above(*n, path))
            .then_some(*p),
        _ => None,
    };
    // A user place a temporary moves into later: `t.owner` of `_6 = move u;
    // t.owner = move _6;`.
    let into_place = |t: Local| {
        points(b).find_map(|q| match b.stmt_at(q).map(|s| &s.kind) {
            Some(StatementKind::Assign {
                dest,
                value: Rvalue::Use(Operand::Move(src)),
            }) if *src == Place::local(t) && b.locals[dest.local].kind == LocalKind::User => {
                place_text(tcx, b, *dest)
            }
            _ => None,
        })
    };
    for p in points(b) {
        if span_at(b, p) != site {
            continue;
        }
        match b.stmt_at(p).map(|s| &s.kind) {
            None => {
                let Some((callee, args, _)) = call_of(b, p) else {
                    continue;
                };
                let Some((i, moved)) = args
                    .iter()
                    .enumerate()
                    .find_map(|(i, a)| Some((i, moved_of(a)?)))
                else {
                    continue;
                };
                let Some(def) = callee_def(callee) else {
                    return (MovedBy::Other, Some(moved));
                };
                let first = usize::from(tcx.takes_this(def));
                if i < first {
                    return (MovedBy::Receiver { method: def }, Some(moved));
                }
                let by = MovedBy::Arg {
                    callee: def,
                    index: i - first,
                    site,
                };
                return (by, Some(moved));
            }
            Some(StatementKind::Assign { dest, value }) => {
                let moved = match value {
                    Rvalue::Use(op) | Rvalue::Convert(_, op) => moved_of(op),
                    Rvalue::Aggregate(_, ops) => ops.iter().find_map(moved_of),
                    _ => None,
                };
                let Some(moved) = moved else {
                    continue;
                };
                let kind = b.locals[dest.local].kind;
                if dest.is_local() && matches!(kind, LocalKind::HiddenLoop(_)) {
                    return (MovedBy::Loop, Some(moved));
                }
                let into = match kind {
                    LocalKind::User => place_text(tcx, b, *dest),
                    LocalKind::Temp if dest.is_local() => into_place(dest.local),
                    _ => None,
                };
                return match into {
                    Some(n) => (MovedBy::Into(n), Some(moved)),
                    None => (MovedBy::Other, Some(moved)),
                };
            }
            _ => {}
        }
    }
    (MovedBy::Other, None)
}

/// Whether every use of the local `x` but the stores into it reads it through a
/// borrow or a projection (`x.length()`, `console.log(x)`, `x.n`): never a copy
/// or move of the whole value, nor a move of a part, which a reference in its
/// place would not type or would move out of (A:1314).
fn only_borrowed(b: &Body, x: Local) -> bool {
    points(b).all(|p| {
        if let Some(StatementKind::Assign { dest, .. }) = b.stmt_at(p).map(|s| &s.kind)
            && dest.local == x
        {
            return true;
        }
        crate::init::point_operands(b, p).iter().all(|o| match o {
            Operand::Copy(pl) => *pl != Place::local(x),
            Operand::Move(pl) => pl.local != x,
            Operand::Const(_) => true,
        })
    })
}

/// Whether the body sets its result once, one `return` with a value, so a
/// fix-it that changes its return type changes no other `return` (A:1314).
fn one_return(b: &Body) -> bool {
    let sets = points(b).filter(|p| {
        matches!(
            b.stmt_at(*p).map(|s| &s.kind),
            Some(StatementKind::Assign { dest, .. }) if dest.local == Local::RETURN
        ) || matches!(
            &b.blocks[p.block].term.kind,
            TerminatorKind::Call { dest, .. } if b.stmt_at(*p).is_none() && dest.local == Local::RETURN
        )
    });
    sets.count() == 1
}

/// The pattern of a destructuring declaration whose source is at `src`, on one
/// line: `{ name, age }` of `const { name, age } = ada;`.
fn pattern_before(map: &SourceMap, src: Span) -> Option<Span> {
    let line = line_of(map, src.lo);
    let before = text(
        map,
        Span {
            lo: line.lo,
            hi: src.lo,
        },
    );
    let head = before.trim_end().strip_suffix('=')?.trim_end();
    let open = head.find(['{', '['])?;
    let kw = head[..open].trim();
    if !(kw.ends_with("const") || kw.ends_with("let")) || !head.ends_with(['}', ']']) {
        return None;
    }
    let lo = line.lo + open as u32;
    Some(Span {
        lo,
        hi: line.lo + head.len() as u32,
    })
}

/// The first `subject` in `site`, after the `=` of an assignment when the site
/// is one: the moved `name` of `u.name = name`, not the field.
fn moved_in(map: &SourceMap, site: Span, subject: &str) -> Option<Span> {
    let t = text(map, site);
    let eq = t.char_indices().find(|&(i, c)| {
        c == '='
            && !t[i + 1..].starts_with('=')
            && !t[..i].ends_with(['=', '!', '<', '>'])
            && !t[i + 1..].starts_with('>')
    });
    if let Some((i, _)) = eq {
        let rhs = Span {
            lo: site.lo + (i + 1) as u32,
            hi: site.hi,
        };
        if let Some(at) = word_in(map, rhs, subject) {
            return Some(at);
        }
    }
    word_in(map, site, subject)
}

/// EN0601 (G07, S:869, S:996, S:1000, S:1046): the head names the path the move
/// took and where it went; the labels and helps follow the form of the move.
fn used_after_move(cx: &BodyCx, m: &MoveError, shown: &str, primary: Span) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let site = m.moved_at.first().copied();
    let (by, moved) = site.map_or((MovedBy::Other, None), |s| moved_by(cx, m.path, s));
    let place = path_place(cx, m.path);
    let ty = place.and_then(|p| place_ty(cx, p));
    // The path the move took, as the move wrote it.
    let subject = moved
        .and_then(|p| place_text(tcx, b, p))
        .unwrap_or_else(|| shown.to_owned());
    let site_at = site.map(|s| moved_in(map, s, &subject).unwrap_or(s));
    let pattern = match (&by, site_at) {
        (MovedBy::Into(_), Some(at)) => pattern_before(map, at),
        _ => None,
    };
    let message = match &by {
        MovedBy::Arg { callee, .. } => {
            format!("`{subject}` was moved into `{}`", name_of(tcx, *callee))
        }
        MovedBy::Receiver { method } => {
            format!("`{subject}` was used up by `{}`", name_of(tcx, *method))
        }
        MovedBy::Loop => format!("`{subject}` was used up by the loop"),
        MovedBy::Into(n) => format!("`{subject}` was moved into `{n}`"),
        MovedBy::Other => format!("`{subject}` was moved"),
    };
    let label = match (&by, pattern) {
        (MovedBy::Loop, _) => "used here afterwards",
        (_, Some(_)) => "used after the move",
        _ => "used here, after the move",
    };
    let mut d = Diagnostic::new(m.code, message, primary, label);
    // Why it moved: what it owns, then the move itself.
    if let (Some(p), Some(t)) = (place, ty)
        && p.is_local()
        && b.locals[p.local].kind == LocalKind::User
    {
        let why = not_copy_because(tcx, t);
        d = d.with_secondary(
            decl_span(b, p.local),
            format!(
                "`{shown}` owns this `{}`, which is not Copy{why}",
                tcx.ty_string(t)
            ),
        );
    }
    // The type of what moved, `p` of `take(p); p.n`, not of the part used.
    let ty = moved.and_then(|p| place_ty(cx, p)).or(ty);
    match (&by, site_at, pattern) {
        (MovedBy::Arg { callee, .. }, Some(at), _) => {
            let t = ty.map_or_else(String::new, |t| tcx.ty_string(t));
            d = d.with_secondary(
                at,
                format!(
                    "`{subject}` moves here, because `{}` takes `{t}`, not `&{t}`",
                    name_of(tcx, *callee)
                ),
            );
        }
        (MovedBy::Loop, Some(at), _) => {
            d = d.with_secondary(
                at,
                format!("the loop takes `{subject}`, because there is no `&`"),
            );
        }
        (_, Some(_), Some(pat)) => {
            d = d.with_secondary(pat, format!("`{subject}` moved here"));
        }
        (_, Some(at), None) => d = d.with_secondary(at, format!("`{subject}` moves here")),
        _ => {}
    }
    match &by {
        MovedBy::Arg {
            callee,
            index,
            site,
        } => {
            d = d.from_typescript(format!(
                "both names would share one object. In Enrang a value has one owner, so passing `{subject}` hands it over."
            ));
            // A move and a use at one point, `both(s, s)`: a borrow in either
            // operand still meets the other's move, so only the copy is offered.
            let same_point = m.moved_at.first() == Some(&span_at(b, m.at));
            if !same_point
                && let Some(help) = borrow_param_instead(cx, *callee, *index, *site, &subject, ty)
            {
                d = d.with_help(help);
            }
            if ty.is_some_and(|t| is_clone(tcx, t))
                && let Some(at) = site_at
            {
                let call = text(map, *site);
                let off = (at.hi.0 - site.lo.0) as usize;
                if off <= call.len() {
                    d = d.with_help(Help::suggest(
                        format!(
                            "to keep your own, pass a copy: `{}.clone(){}`",
                            &call[..off],
                            &call[off..]
                        ),
                        vec![Edit::insert(at.hi, ".clone()")],
                    ));
                }
            }
        }
        // S:1000: the loop's head as written, borrowing its source.
        MovedBy::Loop => {
            let head = site_at.and_then(|at| {
                let line = line_of(map, at.lo);
                let before = text(
                    map,
                    Span {
                        lo: line.lo,
                        hi: at.lo,
                    },
                );
                let start = before.rfind("for")?;
                Some(format!("{}&{subject})", &before[start..]))
            });
            let message = match head {
                Some(h) => format!("to keep `{subject}`, borrow it: `{h}`"),
                None => format!("to keep `{subject}`, borrow it: `&{subject}`"),
            };
            // The edit makes the binding a reference: only where the body
            // uses it through a borrow (A:1314).
            // The bindings: the user locals the head declares before its source.
            let bound_borrowed = |at: Span| {
                let head = Span {
                    lo: line_of(map, at.lo).lo,
                    hi: at.lo,
                };
                (b.locals.indices())
                    .filter(|l| b.locals[*l].kind == LocalKind::User)
                    .filter(|l| {
                        let s = b.locals[*l].span;
                        head.lo <= s.lo && s.hi <= head.hi
                    })
                    .all(|l| only_borrowed(b, l))
            };
            // A use inside the loop's body would meet the hold the borrowed source
            // takes, as a change of it does (EN0706): the edit is offered only for
            // a use outside every loop the move runs before (A:1314).
            let in_loop = || {
                let Some(mp) = site.and_then(|s| {
                    points(b).find(|p| b.stmt_at(*p).is_some() && span_at(b, *p) == s)
                }) else {
                    return false;
                };
                (enrang_mir::Cfg::new(b).loops(b).iter())
                    .any(|l| l.blocks.contains(m.at.block) && !l.blocks.contains(mp.block))
            };
            d = match site_at
                .filter(|at| text(map, *at) == subject && bound_borrowed(*at) && !in_loop())
            {
                Some(at) => d.with_help(Help::suggest(message, vec![Edit::insert(at.lo, "&")])),
                None => d.with_help(Help::text(message)),
            };
        }
        // S:996: destructure a reference, which keeps the source whole.
        MovedBy::Into(_) if pattern.is_some() => {
            let root = moved
                .and_then(|p| local_name(tcx, b, p.local))
                .unwrap_or_else(|| subject.clone());
            // The edit makes each binding a reference: only where the body uses
            // every one of them through a borrow (A:1314).
            let bound_borrowed = pattern.is_some_and(|pat| {
                (b.locals.indices())
                    .filter(|l| b.locals[*l].kind == LocalKind::User)
                    .filter(|l| {
                        let s = b.locals[*l].span;
                        pat.lo <= s.lo && s.hi <= pat.hi
                    })
                    .all(|l| only_borrowed(b, l))
            });
            let src = site_at
                .filter(|at| text(map, *at).starts_with(root.as_str()))
                .filter(|_| bound_borrowed);
            let message = format!("destructure a reference to keep `{root}` whole");
            d = match src {
                Some(at) => d.with_help(Help::suggest(message, vec![Edit::insert(at.lo, "&")])),
                None => d.with_help(Help::text(message)),
            };
        }
        _ => {}
    }
    d
}

/// ", because it has a `string` field" for a class with a field that is not Copy.
fn not_copy_because(tcx: &Tcx, t: Ty) -> String {
    let TyKind::Adt(adt, args) = tcx.kind(t) else {
        return String::new();
    };
    let Some(class) = tcx.adt(adt).as_class() else {
        return String::new();
    };
    for i in 0..class.fields.len() {
        let ft = tcx.field_ty(adt, None, <FieldIdx as enrang_base::Idx>::new(i), args);
        if !is_copy(tcx, ft) {
            return format!(" because it has a `{}` field", tcx.ty_string(ft));
        }
    }
    String::new()
}

/// G07's first help: the callee is in user code, its parameter has the moved
/// value's type, and its contract says it neither moves nor writes it (K2).
fn borrow_param_instead(
    cx: &BodyCx,
    callee: DefId,
    index: usize,
    site: Span,
    shown: &str,
    ty: Option<Ty>,
) -> Option<Help> {
    let tcx = cx.tcx;
    let map = tcx.map();
    let module = tcx.def(callee).module;
    if tcx.module(module).library {
        return None;
    }
    let sig = tcx.sig_opt(callee)?;
    let param = sig.params.get(index)?;
    if Some(param.ty) != ty || matches!(tcx.kind(param.ty), TyKind::Ref(_) | TyKind::Param(_)) {
        return None;
    }
    let by_value = sig.params[..index]
        .iter()
        .filter(|p| !matches!(tcx.kind(p.ty), TyKind::Ref(_)))
        .count();
    let contract = crate::contract(tcx, callee);
    if contract
        .moves_or_writes
        .get(by_value)
        .copied()
        .unwrap_or(true)
    {
        return None;
    }
    let at_type = type_after_colon(map, param.span.lo)?;
    let arg = word_in(map, site, shown)?;
    let t = tcx.ty_string(param.ty);
    Some(Help::suggest(
        format!(
            "if `{}` only needs to look at it, change the parameter to `{}: &{t}`",
            name_of(tcx, callee),
            param.name
        ),
        vec![Edit::insert(at_type, "&"), Edit::insert(arg.lo, "&")],
    ))
}

/// EN0603: a move out of `this` outside a `move` method (S:1044), out of a
/// reference, or out of a raw pointer.
fn move_out_of_ref(cx: &BodyCx, m: &MoveError, shown: &str) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let place = moved_place(cx, m).or_else(|| path_place(cx, m.path));
    let primary = word_in(map, m.span, shown).unwrap_or(m.span);
    let ty = place.and_then(|p| place_ty(cx, p));
    let t = ty.map_or_else(String::new, |t| tcx.ty_string(t));
    let through_this = place.is_some_and(|p| is_this(tcx, b, p.local));
    let ctor = owner_def(b).is_some_and(|d| matches!(tcx.def(d).kind, DefKind::Ctor));
    let returned = points(b).any(|p| {
        span_at(b, p) == m.span
            && matches!(
                b.stmt_at(p).map(|s| &s.kind),
                Some(StatementKind::Assign { dest, .. }) if dest.local == Local::RETURN
            )
    });
    // A `for...of` source written without `&` (S:998, T:624): the move fills the
    // loop's hidden source local.
    let loop_source = matches!(
        b.stmt_at(m.at).map(|s| &s.kind),
        Some(StatementKind::Assign { dest, .. })
            if dest.is_local() && matches!(b.locals[dest.local].kind, LocalKind::HiddenLoop(_))
    )
    .then_some(());
    if through_this {
        // `*this`, the whole object, is named as written, with its `*`.
        let whole = place.is_some_and(|p| b.projs(p).len() == 1)
            && text(map, m.span).trim_start().starts_with('*');
        let (shown, primary) = match whole {
            true => ("*this", m.span),
            false => (shown, primary),
        };
        let label = match returned {
            true => format!("`{t}` gives the caller its own value"),
            false => format!("`{shown}` moves here"),
        };
        let mut d = Diagnostic::new(
            m.code,
            format!("cannot move `{shown}` out of `this`"),
            primary,
            label,
        );
        if loop_source.is_some() {
            return d.with_help(Help::suggest(
                format!("to loop over the elements in place, write `&{shown}`"),
                vec![Edit::insert(primary.lo, "&")],
            ));
        }
        if returned {
            let same = match whole {
                true => "object",
                false => "field",
            };
            d = d.with_help(Help::text(format!(
                "to return a reference to the same {same}, write `&{t}`"
            )));
        }
        if ty.is_some_and(|t| is_clone(tcx, t)) {
            // `*this.clone()` would parse as `*(this.clone())`: the copy of the
            // whole object replaces `*this` (A:1314).
            let (copy, edit) = match whole {
                true => (
                    "this.clone()".to_owned(),
                    Edit::replace(primary, "this.clone()"),
                ),
                false => (
                    format!("{shown}.clone()"),
                    Edit::insert(primary.hi, ".clone()"),
                ),
            };
            d = d.with_help(Help::suggest(
                match returned {
                    true => format!("to return a copy, write `{copy}`"),
                    false => format!("to pass a copy, write `{copy}`"),
                },
                vec![edit],
            ));
        }
        if !ctor {
            d = d.with_help(Help::text(
                "or mark the method `move` to give up the object",
            ));
        }
        return d;
    }
    let raw = place.is_some_and(|p| {
        let projs = b.projs(p);
        (0..projs.len()).any(|i| {
            projs[i] == Proj::Deref
                && projs_ty(tcx, b, p.local, &projs[..i])
                    .is_some_and(|t| matches!(tcx.kind(t), TyKind::Raw(_)))
        })
    });
    let what = match raw {
        true => "a raw pointer",
        false => "a reference",
    };
    let d = Diagnostic::new(
        m.code,
        format!("cannot move `{shown}` out of {what}"),
        primary,
        format!("`{shown}` is behind {what}"),
    );
    if loop_source.is_some() {
        return d.with_help(Help::suggest(
            format!("to loop over the elements in place, write `&{shown}`"),
            vec![Edit::insert(primary.lo, "&")],
        ));
    }
    // An explicit deref `*r` copies as `r.clone()`: `*r.clone()` would parse as
    // `*(r.clone())` (A:1314, every fix-it compiles).
    let written = text(tcx.map(), primary).to_owned();
    // A `move` method's receiver moved out of a reference: the copy goes after
    // the receiver, `r.clone().taken()`, since `.clone()` after the call would
    // still move `*r`.
    let moving = call_of(b, m.at)
        .and_then(|(c, _, _)| callee_def(c))
        .filter(|&d| {
            tcx.sig_opt(d)
                .is_some_and(|s| s.receiver == Some(enrang_hir::Receiver::Move))
        })
        .and_then(|d| tcx.def(d).name())
        .and_then(|name| written.rfind(&format!(".{name}(")));
    if let (Some(at), true) = (moving, ty.is_some_and(|t| is_clone(tcx, t))) {
        let copy = format!("{}.clone(){}", &written[..at], &written[at..]);
        return d.with_help(Help::suggest(
            format!("to take a copy, write `{copy}`"),
            vec![Edit::insert(primary.lo + at as u32, ".clone()")],
        ));
    }
    match (
        ty.is_some_and(|t| is_clone(tcx, t)),
        written.strip_prefix('*'),
    ) {
        (true, Some(inner)) => {
            let copy = clone_call(inner);
            d.with_help(Help::suggest(
                format!("to take a copy, write `{copy}`"),
                vec![Edit::replace(primary, copy.clone())],
            ))
        }
        (true, None) => d.with_help(Help::suggest(
            format!("to take a copy, write `{shown}.clone()`"),
            vec![Edit::insert(primary.hi, ".clone()")],
        )),
        (false, _) => d,
    }
}

/// `x.clone()` of the expression `x` as written, parenthesised when it starts
/// with a deref, which binds looser than the call: `(*b).clone()`.
fn clone_call(x: &str) -> String {
    match x.starts_with('*') {
        true => format!("({x}).clone()"),
        false => format!("{x}.clone()"),
    }
}

/// EN0613: an assignment to a by-value parameter not marked `let` (S:772), or to
/// a `const` that may have a value.
fn assign_const(cx: &BodyCx, m: &MoveError, shown: &str) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let place = path_place(cx, m.path);
    let local = place.map(|p| p.local);
    let param = local.is_some_and(|l| b.locals[l].kind == LocalKind::Arg);
    if param && let Some(l) = local {
        let t = tcx.ty_string(b.locals[l].ty);
        let mut d = Diagnostic::new(
            m.code,
            format!("cannot assign to parameter `{shown}`"),
            m.span,
            "assigned here",
        );
        let name = decl_span(b, l);
        d = match word_in(map, name, shown) {
            Some(at) => d.with_help(Help::machine(
                format!("mark it `let {shown}`"),
                vec![Edit::insert(at.lo, "let ")],
            )),
            None => d.with_help(Help::text(format!("mark it `let {shown}`"))),
        };
        return d.with_help(Help::text(format!(
            "take `{shown}: &{t}` and write `*{shown}`"
        )));
    }
    let mut d = Diagnostic::new(
        m.code,
        format!("cannot assign to `{shown}`, because it is `const`"),
        m.span,
        "assigned here",
    );
    if let Some(l) = local.filter(|l| b.locals[*l].kind == LocalKind::User) {
        let name = decl_span(b, l);
        d = d.with_secondary(name, format!("`{shown}` is declared `const` here"));
        if let Some(kw) = keyword_before(map, name, "const") {
            d = d.with_help(Help::machine(
                "make the binding mutable",
                vec![Edit::replace(kw, "let")],
            ));
        }
    }
    d
}

/// The class a constructor body builds, and its base's name.
fn ctor_classes(cx: &BodyCx) -> Option<(String, Option<String>)> {
    let tcx = cx.tcx;
    let d = owner_def(cx.body)?;
    let adt = tcx.adt_of(tcx.def(d).parent?)?;
    let class = tcx.adt(adt).as_class()?;
    let base = class.base.and_then(|t| match tcx.kind(t) {
        TyKind::Adt(a, _) => Some(name_of(tcx, tcx.adt(a).def)),
        _ => None,
    });
    Some((name_of(tcx, tcx.adt(adt).def), base))
}

/// EN0610: a field unset where `this` is used, at `super(...)` (G24) or at an exit
/// (S:587, A:998).
fn this_unset(cx: &BodyCx, m: &MoveError, shown: &str) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let md = &cx.moves;
    let (class, base) = ctor_classes(cx).unwrap_or_else(|| (String::new(), None));
    if Some(m.path) == md.super_path {
        return Diagnostic::new(
            m.code,
            "`this` can't be used before `super(...)` runs",
            m.span,
            "`this` is used here, before the base part is built",
        )
        .with_help(Help::text(
            "before `super(...)`, a constructor may only assign its own fields",
        ));
    }
    if md.supers.contains(&m.at) {
        let call = text(map, m.span).to_owned();
        let base = base.unwrap_or_else(|| "the base".to_owned());
        let mut d = Diagnostic::new(
            m.code,
            format!("`{shown}` is not set when `{call}` runs"),
            m.span,
            format!("`{base}`'s constructor runs here, before `{shown}` is set"),
        );
        let set = later_store(cx, m.at, m.path);
        if let Some(s) = set {
            d = d.with_secondary(
                with_semicolon(map, s),
                format!("`{shown}` is set only here"),
            );
        }
        d = d.from_typescript(
            "TypeScript requires `super(...)` before any use of `this` (TS17009). Enrang sets a subclass's own fields first, so a base constructor that calls an override finds them set.",
        );
        let message = format!(
            "set `{shown}` before `{call}`, because `{base}`'s constructor may call `{class}`'s methods"
        );
        return match set.and_then(|s| swap_fix(map, m.span, s)) {
            Some(edit) => d.with_help(Help::machine(message, vec![edit])),
            None => d.with_help(Help::text(message)),
        };
    }
    let field = shown.strip_prefix("this.").unwrap_or(shown);
    let inherited = md
        .ctor_fields
        .iter()
        .flatten()
        .any(|f| f.1 == m.path && !f.2);
    // An inherited field assigned before `super(...)` runs (A:998: only an own
    // field may be): the store itself is the use.
    let stores_it = matches!(
        b.stmt_at(m.at).map(|s| &s.kind),
        Some(StatementKind::Assign { dest, .. })
            if is_this(tcx, b, dest.local)
                && cx.moves.lookup.get(dest).map(|x| x.0) == Some(m.path)
    );
    if inherited
        && stores_it
        && let Some(sup) = md.supers.iter().next()
        && md.supers.iter().all(|p| *p > m.at)
    {
        let call = text(map, span_at(b, *sup)).to_owned();
        let base = base.unwrap_or_else(|| "the base".to_owned());
        return Diagnostic::new(
            m.code,
            format!("`{field}` is not set until `{call}` runs"),
            m.span,
            format!(
                "`{field}` is inherited from `{base}`, so it can be assigned only after `{call}`"
            ),
        )
        .with_help(Help::text(format!("assign this.{field} after {call}")));
    }
    let label = match b.stmt_at(m.at) {
        None if matches!(b.blocks[m.at.block].term.kind, TerminatorKind::Return) => {
            "the constructor returns here".to_owned()
        }
        _ => "`this` is used here".to_owned(),
    };
    let d = Diagnostic::new(m.code, format!("`{field}` is not set"), m.span, label);
    match inherited {
        true => d.with_help(Help::text(format!("assign this.{field} after super()"))),
        false => d.with_help(Help::text(format!(
            "assign this.{field} before `this` is used, or give `{field}` a default"
        ))),
    }
}

/// The first store into the path `n` after `at`.
fn later_store(cx: &BodyCx, at: Point, n: MovePathIdx) -> Option<Span> {
    let b = cx.body;
    let md = &cx.moves;
    after(b, at).into_iter().find_map(|p| {
        let dest = match b.stmt_at(p).map(|s| &s.kind) {
            Some(StatementKind::Assign { dest, .. }) => *dest,
            Some(StatementKind::FieldInit { field, .. }) => *field,
            _ => return None,
        };
        (md.lookup.get(&dest) == Some(&(n, true))).then(|| span_at(b, p))
    })
}

/// G24's fix-it: when the field's assignment follows `super(...)` directly, swap
/// the two statements.
fn swap_fix(map: &SourceMap, call: Span, set: Span) -> Option<Edit> {
    let call_stmt = with_semicolon(map, call);
    let set_stmt = with_semicolon(map, set);
    let between = text(
        map,
        Span {
            lo: call_stmt.hi,
            hi: set_stmt.lo,
        },
    );
    let set_text = text(map, set_stmt);
    if set_stmt.lo < call_stmt.hi
        || !between.trim().is_empty()
        || set_text.contains("this.") && {
            let value = set_text.split_once('=').map_or("", |(_, v)| v);
            value.contains("this")
        }
    {
        return None;
    }
    let indent = indent_of(map, call.lo);
    Some(Edit::replace(
        Span {
            lo: call_stmt.lo,
            hi: set_stmt.hi,
        },
        format!("{set_text}\n{indent}{}", text(map, call_stmt)),
    ))
}

/// EN0619: `super(...)` not run exactly once on every path (S:587), or misplaced.
fn super_once(cx: &BodyCx, m: &MoveError) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let md = &cx.moves;
    let in_ctor = md.ctor_fields.is_some() && md.super_path.is_some();
    if !in_ctor {
        return Diagnostic::new(
            m.code,
            "`super(...)` must be a statement of the constructor's own body",
            m.span,
            "not in a constructor's own body",
        )
        .note("`super(...)` runs only in a constructor of a class with a base, never in an arrow or a local function");
    }
    let call = md.supers.iter().next().map_or_else(
        || "super(...)".to_owned(),
        |p| text(map, span_at(b, *p)).to_owned(),
    );
    if md.supers.contains(&m.at) {
        let here = text(map, m.span).to_owned();
        return Diagnostic::new(
            m.code,
            format!("`{here}` may already have run here"),
            m.span,
            "a second `super(...)` on this path",
        )
        .note(
            "every constructor of a class with a base runs `super(...)` exactly once on every path",
        );
    }
    let d = Diagnostic::new(
        m.code,
        format!("`{call}` isn't called on every path before the constructor returns"),
        m.span,
        format!("the constructor may return here without `{call}`"),
    );
    match skipping_branch(cx, m.at.block) {
        Some(when) => d.note(when),
        None => d.note(
            "every constructor of a class with a base runs `super(...)` exactly once on every path",
        ),
    }
}

/// The branch that skips `super(...)` on a path to the exit `exit` (A:1003):
/// `` when `quiet` is true `` for `if (!quiet) { super(name); }`, from the last
/// two-way `switch` on that path where the other way can still reach a
/// `super(...)`.
fn skipping_branch(cx: &BodyCx, exit: enrang_mir::BlockId) -> Option<String> {
    let (b, md) = (cx.body, &cx.moves);
    let map = cx.tcx.map();
    let n = b.blocks.len();
    let idx = |x: enrang_mir::BlockId| enrang_base::Idx::index(x);
    let with_super: Vec<bool> = (0..n)
        .map(|i| md.supers.iter().any(|p| idx(p.block) == i))
        .collect();
    let succs = |i: usize| -> Vec<enrang_mir::BlockId> {
        b.blocks[<enrang_mir::BlockId as enrang_base::Idx>::new(i)]
            .term
            .kind
            .successors()
    };
    // The blocks from which a `super(...)` can still be reached.
    let mut reaches = with_super.clone();
    let mut changed = true;
    while changed {
        changed = false;
        for i in 0..n {
            if !reaches[i] && succs(i).iter().any(|s| reaches[idx(*s)]) {
                reaches[i] = true;
                changed = true;
            }
        }
    }
    // A path from the entry to `exit` through no `super(...)`.
    let mut parent: Vec<Option<usize>> = vec![None; n];
    let mut seen = vec![false; n];
    let mut queue = VecDeque::from([0usize]);
    seen[0] = true;
    while let Some(i) = queue.pop_front() {
        if i == idx(exit) {
            break;
        }
        for s in succs(i) {
            let j = idx(s);
            if !seen[j] && !with_super[j] {
                seen[j] = true;
                parent[j] = Some(i);
                queue.push_back(j);
            }
        }
    }
    let mut at = idx(exit);
    if !seen[at] {
        return None;
    }
    while let Some(from) = parent[at] {
        let term = &b.blocks[<enrang_mir::BlockId as enrang_base::Idx>::new(from)].term;
        if let TerminatorKind::Switch {
            arms, otherwise, ..
        } = &term.kind
            && arms.len() == 1
            && let Some(other) = otherwise
            && arms[0].0 == 0
        {
            let taken_false = idx(arms[0].1) == at;
            let away = match taken_false {
                true => idx(*other),
                false => idx(arms[0].1),
            };
            if away != at && reaches[away] {
                let cond = condition_text(map, term.span)?;
                let (cond, value) = match cond.strip_prefix('!') {
                    Some(inner) if !inner.contains(' ') => (inner.to_owned(), taken_false),
                    _ => (cond, !taken_false),
                };
                return Some(format!("when `{cond}` is {value}"));
            }
        }
        at = from;
    }
    None
}

/// The condition of a branch as written: the text in the parentheses of the `if`
/// or `while` a `switch` spans, else the span's own text.
fn condition_text(map: &SourceMap, span: Span) -> Option<String> {
    let t = text(map, span).trim();
    let rest = ["if", "while"]
        .iter()
        .find_map(|kw| t.strip_prefix(kw))
        .map(str::trim_start);
    let cond = match rest.and_then(|r| r.strip_prefix('(')) {
        Some(r) => {
            let mut depth = 1i32;
            let end = r.char_indices().find_map(|(i, c)| {
                match c {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                (depth == 0).then_some(i)
            })?;
            r[..end].trim().to_owned()
        }
        None => unparenthesised(t).to_owned(),
    };
    (!cond.is_empty() && !cond.contains('\n')).then_some(cond)
}

// ---------------------------------------------------------------------------------
// Read-only marks (EN0608, EN0609, EN0614, EN0616).

pub fn report_mark(cx: &BodyCx, m: &MarkError) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let call = call_of(b, m.at).filter(|_| b.stmt_at(m.at).is_none() || m.code == Code::EN0614);
    let method = call
        .and_then(|(c, _, _)| callee_def(c))
        .map(|d| name_of(tcx, d));
    // The marked argument as written, `"a"` of `grow("a")`, which is the
    // primary span (T:816, T:833, T:837), and the place it names.
    let marked_arg = m
        .arg
        .zip(call_of(b, m.at))
        .and_then(|(i, (callee, _, span))| {
            let first = match callee_def(callee) {
                Some(d) => {
                    usize::from(tcx.takes_this(d) || matches!(tcx.def(d).kind, DefKind::Ctor))
                }
                None => 0,
            };
            let k = i.checked_sub(first)?;
            arg_span(map, span, k).filter(|a| a.lo >= m.span.lo && a.hi <= m.span.hi)
        });
    let m = &MarkError {
        span: marked_arg.unwrap_or(m.span),
        ..m.clone()
    };
    let arg_text = marked_arg.map(|a| text(map, a).trim_start_matches('&').trim().to_owned());
    // The written place: the statement's destination, or the call's receiver.
    let written = match b.stmt_at(m.at).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => place_text(tcx, b, *dest),
        _ => None,
    };
    let receiver = call
        .filter(|_| marked_arg.is_none())
        .and_then(|(_, args, _)| {
            let first = args.first()?.place()?;
            receiver_text(cx, m.at, first)
        });
    let target = receiver
        .clone()
        .or(arg_text)
        .or(written.clone())
        .unwrap_or_else(|| text(map, m.span).trim_start_matches('&').to_owned());
    match (m.code, m.origin) {
        (Code::EN0614, origin) => {
            let method = method.unwrap_or_else(|| "this method".to_owned());
            let mut d = match origin {
                MarkOrigin::ReadOnlyResult(f) => {
                    let (why, declared) = readonly_reason(tcx, f);
                    let d = Diagnostic::new(
                        m.code,
                        format!("{why}, so `{method}` cannot change it"),
                        m.span,
                        format!("`{method}` changes it"),
                    );
                    match declared {
                        true => d.with_help(Help::text(format!(
                            "to allow this, remove `readonly` from the return type of `{}`",
                            name_of(tcx, f)
                        ))),
                        false => d,
                    }
                }
                MarkOrigin::ConstRoot(l) | MarkOrigin::ByValueParam(l) => {
                    let root = local_name(tcx, b, l).unwrap_or_else(|| target.clone());
                    let param = matches!(origin, MarkOrigin::ByValueParam(_));
                    let what = match param {
                        true => "a parameter not marked `let`".to_owned(),
                        false => "`const`".to_owned(),
                    };
                    let d = Diagnostic::new(
                        m.code,
                        format!("`{root}` is {what}, so `{method}` cannot change it"),
                        m.span,
                        format!("`{method}` changes `{target}`"),
                    );
                    let name = decl_span(b, l);
                    // S:1135, T:815: a method that writes `this` only because
                    // its body contains `unsafe` (N12) may be marked `const`.
                    let d = match call
                        .and_then(|(c, _, _)| callee_def(c))
                        .and_then(|f| const_method_help(cx, f))
                    {
                        Some(help) => d.with_help(help),
                        None => d,
                    };
                    match param {
                        false => {
                            let d = d
                                .with_secondary(
                                    name,
                                    "declared `const` here: immutable all the way down",
                                )
                                .from_typescript(
                                    "a TS `const` only freezes the binding. In Enrang values have no shared identity, so `const` freezes the value.",
                                );
                            match keyword_before(map, name, "const") {
                                Some(kw) => d.with_help(Help::machine(
                                    "make the binding mutable",
                                    vec![Edit::replace(kw, "let")],
                                )),
                                None => d,
                            }
                        }
                        true => match word_in(map, name, &root) {
                            Some(at) => d.with_help(Help::machine(
                                format!("mark it `let {root}`"),
                                vec![Edit::insert(at.lo, "let ")],
                            )),
                            None => d,
                        },
                    }
                }
                _ => Diagnostic::new(
                    m.code,
                    format!("`{target}` is read-only here, so `{method}` cannot change it"),
                    m.span,
                    format!("`{method}` changes `{target}`"),
                )
                .note(origin_note(tcx, b, origin)),
            };
            if let Some(mark) = origin_secondary(cx, origin) {
                d = d.with_secondary(mark.0, mark.1);
            }
            d
        }
        (_, origin) => {
            let call_name = call.and_then(|(c, _, _)| callee_def(c));
            let d = mark_write(cx, m, origin, &target, call_name);
            match origin_secondary(cx, origin) {
                Some((span, label)) => d.with_secondary(span, label),
                None => d,
            }
        }
    }
}

/// The receiver of the call at `at` as written: the place its `&` borrows, or
/// the reference place it copies (`this.src` of `this.src.push(1)`), without
/// the deref the call adds.
fn receiver_text(cx: &BodyCx, at: Point, arg: Place) -> Option<String> {
    let b = cx.body;
    let block = &b.blocks[at.block];
    let end = (at.index as usize).min(block.stmts.len());
    let shown = block.stmts[..end].iter().rev().find_map(|s| match &s.kind {
        StatementKind::Assign { dest, value } if *dest == arg => match value {
            Rvalue::Ref { place, .. } => Some(place_text(cx.tcx, b, *place)),
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(place_text(cx.tcx, b, *p)),
            _ => Some(None),
        },
        _ => None,
    });
    let shown = match shown {
        Some(s) => s,
        None if b.locals[arg.local].kind != LocalKind::Temp => place_text(cx.tcx, b, arg),
        None => None,
    }?;
    Some(shown.strip_prefix('*').unwrap_or(&shown).to_owned())
}

/// The span of argument `k` of the call written at `call`, by the last
/// parenthesised list it ends with: `"a"` of `grow("a")`, `GREETING` of
/// `l.log(GREETING)`.
fn arg_span(map: &SourceMap, call: Span, k: usize) -> Option<Span> {
    let t = text(map, call);
    if !t.ends_with(')') {
        return None;
    }
    // The `(` that matches the final `)`, outside string literals.
    let bytes = t.as_bytes();
    let mut depth = 0i32;
    let mut open = None;
    let mut quote: Option<u8> = None;
    for i in (0..bytes.len()).rev() {
        let c = bytes[i];
        if let Some(q) = quote {
            if c == q && (i == 0 || bytes[i - 1] != b'\\') {
                quote = None;
            }
            continue;
        }
        match c {
            b'"' | b'\'' | b'`' => quote = Some(c),
            b')' | b']' | b'}' => depth += 1,
            b'(' | b'[' | b'{' => {
                depth -= 1;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let open = open?;
    let inner = &t[open + 1..t.len() - 1];
    let mut start = 0;
    let mut pieces = Vec::new();
    let (mut depth, mut quote) = (0i32, None::<char>);
    for (i, c) in inner.char_indices() {
        if let Some(q) = quote {
            if c == q {
                quote = None;
            }
            continue;
        }
        match c {
            '"' | '\'' | '`' => quote = Some(c),
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                pieces.push((start, i));
                start = i + 1;
            }
            _ => {}
        }
    }
    pieces.push((start, inner.len()));
    let (lo, hi) = *pieces.get(k)?;
    let piece = &inner[lo..hi];
    let lead = piece.len() - piece.trim_start().len();
    let len = piece.trim().len();
    if len == 0 {
        return None;
    }
    let at = call.lo + (open + 1 + lo + lead) as u32;
    Some(Span {
        lo: at,
        hi: at + len as u32,
    })
}

/// S:1135's help for a call of a user method not marked `const` whose body
/// contains `unsafe`, which N12 makes write `this`: `` if `log` doesn't change
/// the logger, mark it `const` ``, the class named in lower-case words.
fn const_method_help(cx: &BodyCx, f: DefId) -> Option<Help> {
    let tcx = cx.tcx;
    let sig = tcx.sig_opt(f)?;
    if tcx.module(tcx.def(f).module).library
        || sig.receiver != Some(enrang_hir::Receiver::Ref(enrang_hir::Mark::None))
    {
        return None;
    }
    let body = cx
        .bodies
        .values()
        .find(|x| matches!(x.owner, BodyOwner::Fn(d) if d == f))?;
    if !crate::r3::is_unsafe(tcx, body) {
        return None;
    }
    let class = parent_name(tcx, f);
    let mut words = String::new();
    for (i, c) in class.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            words.push(' ');
        }
        words.extend(c.to_lowercase());
    }
    Some(Help::text(format!(
        "if `{}` doesn't change the {words}, mark it `const`",
        name_of(tcx, f)
    )))
}

/// A secondary label at a mark's origin, where it has a place in the source.
fn origin_secondary(cx: &BodyCx, origin: MarkOrigin) -> Option<(Span, String)> {
    let tcx = cx.tcx;
    match origin {
        MarkOrigin::ReadonlyField(adt, f) | MarkOrigin::ReadonlyRef(adt, f) => {
            let fd = tcx.field_def(adt, None, f);
            let what = match origin {
                MarkOrigin::ReadonlyRef(..) if fd.readonly_refs.contains(&Vec::new()) => {
                    "declared `readonly &`"
                }
                MarkOrigin::ReadonlyRef(..) => "declared with a `readonly &` part",
                _ => "declared `readonly`",
            };
            Some((fd.span, format!("`{}` is {what} here", fd.name)))
        }
        MarkOrigin::TopConst(d) => Some((tcx.def(d).name_span, "declared `const` here".to_owned())),
        _ => None,
    }
}

fn origin_note(tcx: &Tcx, b: &Body, origin: MarkOrigin) -> String {
    match origin {
        MarkOrigin::ConstRoot(l) => format!(
            "it comes from `{}`, which is `const`",
            local_name(tcx, b, l).unwrap_or_default()
        ),
        MarkOrigin::ByValueParam(l) => format!(
            "it comes from `{}`, a parameter not marked `let`",
            local_name(tcx, b, l).unwrap_or_default()
        ),
        MarkOrigin::TopConst(d) => {
            format!("it comes from `{}`, a top-level `const`", name_of(tcx, d))
        }
        MarkOrigin::StringLiteral => "it points at a string literal".to_owned(),
        MarkOrigin::ConstLiteral(_) => "it points at a constant literal".to_owned(),
        MarkOrigin::ReadonlyField(adt, f) => format!(
            "it comes from the `readonly` field `{}`",
            tcx.field_def(adt, None, f).name
        ),
        MarkOrigin::ReadonlyRef(adt, f) => format!(
            "it comes from {}",
            readonly_field_words(tcx.field_def(adt, None, f))
        ),
        MarkOrigin::RawDerived(_) => "it was made from a raw pointer".to_owned(),
        MarkOrigin::ReadOnlyResult(d) => readonly_reason(tcx, d).0,
        MarkOrigin::ConstPointing(d) => {
            format!(
                "`{}` returns a reference that may point at a constant",
                name_of(tcx, d)
            )
        }
        MarkOrigin::StringPart(d) => {
            format!("`{}` returns a string that may be a part", name_of(tcx, d))
        }
    }
}

/// EN0608, EN0609 and EN0616 at a write or a writing pass (S:772-775, S:795, S:939).
fn mark_write(
    cx: &BodyCx,
    m: &MarkError,
    origin: MarkOrigin,
    target: &str,
    callee: Option<DefId>,
) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let label = match callee {
        // S:773: the callee hands out a reference the caller writes through.
        Some(f) if is_source_pass(cx, m.at) => {
            format!("`{}` hands out a writable reference to it", name_of(tcx, f))
        }
        Some(f) => format!("`{}` writes through it", name_of(tcx, f)),
        None => "written here".to_owned(),
    };
    match origin {
        MarkOrigin::ConstRoot(l) | MarkOrigin::ByValueParam(l) => {
            let root = local_name(tcx, b, l).unwrap_or_else(|| target.to_owned());
            let param = matches!(origin, MarkOrigin::ByValueParam(_));
            let message = match callee {
                Some(f) if is_source_pass(cx, m.at) => format!(
                    "`{}` hands out a writable reference, but `{root}` is `const`",
                    name_of(tcx, f)
                ),
                Some(f) => {
                    let param_name =
                        written_param(cx, m.at, f, m.arg).unwrap_or_else(|| "it".to_owned());
                    format!(
                        "`{}` can change `{param_name}`, but `{root}` is `const`",
                        name_of(tcx, f)
                    )
                }
                // A write through a reference to the `const` value (S:795).
                None if written_root(cx, m.at).is_some_and(|w| w != l) => {
                    "cannot mutate immutable data".to_owned()
                }
                None => format!("cannot change `{target}`, because `{root}` is `const`"),
            };
            let message = match param {
                true => message.replace(
                    &format!("`{root}` is `const`"),
                    &format!("`{root}` is a parameter not marked `let`"),
                ),
                false => message,
            };
            let label = match written_root(cx, m.at).filter(|w| *w != l && callee.is_none()) {
                Some(w) => format!(
                    "`{}` points at `{root}`, which is `const`",
                    local_name(tcx, b, w).unwrap_or_else(|| target.to_owned())
                ),
                None => label,
            };
            let d = Diagnostic::new(m.code, message, m.span, label);
            let name = decl_span(b, l);
            match (
                param,
                keyword_before(map, name, "const"),
                word_in(map, name, &root),
            ) {
                (false, Some(kw), _) => d.with_help(Help::machine(
                    format!("declare it `let {root}`"),
                    vec![Edit::replace(kw, "let")],
                )),
                (true, _, Some(at)) => d.with_help(Help::machine(
                    format!("mark it `let {root}`"),
                    vec![Edit::insert(at.lo, "let ")],
                )),
                _ => d,
            }
        }
        MarkOrigin::TopConst(d) => {
            let name = name_of(tcx, d);
            let message = match target == name {
                true => format!("cannot change `{target}`, because it is a top-level `const`"),
                false => {
                    format!("cannot change `{target}`, because `{name}` is a top-level `const`")
                }
            };
            Diagnostic::new(m.code, message, m.span, label)
        }
        MarkOrigin::ConstLiteral(_) => Diagnostic::new(
            m.code,
            "cannot mutate immutable data",
            m.span,
            format!("`{target}` points at a constant literal"),
        )
        .with_help(Help::text("copy the literal into a `let` array first")),
        MarkOrigin::ReadonlyField(adt, f) => {
            let field = sym(tcx.field_def(adt, None, f).name);
            let message = match (callee, field_path(target, &field)) {
                // A class passed whole for a shape the callee writes, or one whose
                // field the callee hands back writable (H42).
                (Some(c), None) if is_source_pass(cx, m.at) => format!(
                    "`{}` hands out a writable reference to `{target}.{field}`, but `{field}` is `readonly`",
                    name_of(tcx, c)
                ),
                (Some(c), None) => format!(
                    "`{}` can write `{target}.{field}`, but `{field}` is `readonly`",
                    name_of(tcx, c)
                ),
                (_, Some(path)) if path == target => {
                    format!("cannot write `{target}`, because it is `readonly`")
                }
                _ => format!("cannot write `{target}`, because `{field}` is `readonly`"),
            };
            Diagnostic::new(m.code, message, m.span, label)
                .note("a `readonly` field is set only by its class's constructor")
        }
        MarkOrigin::ReadonlyRef(adt, f) => {
            let fd = tcx.field_def(adt, None, f);
            let field = sym(fd.name);
            let whole = fd.readonly_refs.contains(&Vec::new());
            let message = match (field_path(target, &field), whole) {
                (Some(path), true) => {
                    format!("cannot write through `{path}`, because it is `readonly &`")
                }
                (Some(path), false) => {
                    format!("cannot write through `{path}`, because it holds a `readonly &` part")
                }
                (None, _) => format!(
                    "cannot write through `{target}`, because it comes from {}",
                    readonly_field_words(fd)
                ),
            };
            Diagnostic::new(m.code, message, m.span, label)
        }
        MarkOrigin::ReadOnlyResult(f) => {
            let (why, declared) = readonly_reason(tcx, f);
            let library = tcx.module(tcx.def(f).module).library;
            // T:907: a library's string part, as `slice` returns, can't grow.
            if library && written_is_str(cx, m.at) {
                return Diagnostic::new(
                    m.code,
                    "a part of a string can't grow; copy it with `.toString()`",
                    m.span,
                    label,
                )
                .note(why);
            }
            // S:941: a write's label names the `readonly` the signature declares;
            // a pass names the callee that writes.
            let label = match declared && callee.is_none() {
                true => format!("`{}` returns a `readonly` reference", name_of(tcx, f)),
                false => label,
            };
            let d = Diagnostic::new(
                m.code,
                format!("cannot change the object returned by `{}`", name_of(tcx, f)),
                m.span,
                label,
            );
            let raw = matches!(
                crate::contract(tcx, f).result,
                ResultPerm::ReadOnly(enrang_hir::Reason::RawDeref)
            );
            match (declared && !library, raw) {
                (true, _) => d.with_help(Help::text(format!(
                    "to allow this, remove `readonly` from the return type of `{}`",
                    name_of(tcx, f)
                ))),
                // S:773, T:986: with no source, its storage belongs to no caller.
                (false, true) => d
                    .note(why)
                    .with_help(Help::text("take a `&` parameter that owns the storage")),
                (false, false) => d.note(why),
            }
        }
        MarkOrigin::StringPart(f) => {
            let d = Diagnostic::new(
                m.code,
                format!(
                    "`{}` returns a string that may be a part, so it can't grow",
                    name_of(tcx, f)
                ),
                m.span,
                label,
            );
            // T:906: append to the string the part came from, `s += "!";`.
            match grow_directly(cx, m, f) {
                Some((src, rhs)) => d.with_help(Help::text(format!(
                    "change `{src}` directly: `{src} += {rhs};`"
                ))),
                None => d.with_help(Help::text("copy it first: `.toString()`")),
            }
        }
        MarkOrigin::ConstPointing(f) => Diagnostic::new(
            m.code,
            format!(
                "`{}` returns a reference that may point at a constant",
                name_of(tcx, f)
            ),
            m.span,
            label,
        ),
        MarkOrigin::StringLiteral => {
            Diagnostic::new(m.code, "cannot change a string literal", m.span, label)
                .with_help(Help::text("copy it first: `.toString()`"))
        }
        MarkOrigin::RawDerived(_) => Diagnostic::new(
            m.code,
            "cannot write through a reference made from a raw pointer",
            m.span,
            label,
        )
        .with_help(Help::text("take a `&` parameter that owns the storage")),
    }
}

/// Why `f`'s result is read-only, as S:939 words each reason (N6), and whether
/// its signature says `readonly`, which only then a help may offer to remove.
fn readonly_reason(tcx: &Tcx, f: DefId) -> (String, bool) {
    use enrang_hir::Reason;
    let name = name_of(tcx, f);
    let reason = match &crate::contract(tcx, f).result {
        ResultPerm::ReadOnly(r) => Some(r.clone()),
        _ => None,
    };
    let declared = tcx.sig_opt(f).is_some_and(|s| s.ret_readonly);
    let param = |i: u32| {
        let this = usize::from(tcx.takes_this(f));
        match (this, i) {
            (1, 0) => "this".to_owned(),
            _ => (tcx.sig_opt(f))
                .and_then(|s| s.params.get(i as usize - this))
                .map_or_else(|| format!("#{i}"), |p| sym(p.name)),
        }
    };
    let text = match reason {
        Some(Reason::AliasedParts) => {
            format!("`{name}` returns two references that may point at the same data")
        }
        Some(Reason::StoredSource(n)) => {
            let into = (crate::contract(tcx, f).stores.iter())
                .find(|s| s.from == n)
                .map(|s| param(s.into));
            match into {
                Some(m) => format!(
                    "`{name}` also keeps a reference from `{}` in `{m}`",
                    param(n)
                ),
                None => format!("`{name}` also keeps a reference from `{}`", param(n)),
            }
        }
        Some(Reason::ReadonlyField(path, field)) => {
            let fd = (tcx.adts())
                .find(|(_, a)| tcx.def(a.def).path == path)
                .map(|(a, _)| tcx.field_def(a, None, field));
            match fd {
                Some(fd) => format!(
                    "`{name}` returns a reference reached from {}",
                    readonly_field_words(fd)
                ),
                None => format!("`{name}` returns a reference reached from a `readonly &` field"),
            }
        }
        Some(Reason::StringPart) => format!("`{name}` returns a string that may be a part"),
        Some(Reason::Constant(_) | Reason::Static(_) | Reason::ConstLiteral) => {
            format!("`{name}` returns a reference that may point at a constant")
        }
        Some(Reason::ReadonlyResult(inner)) => {
            let inner = inner.segments.last().map_or_else(String::new, sym);
            format!("`{name}` returns what `{inner}` returns, a read-only reference")
        }
        _ => format!("`{name}` returns a read-only reference"),
    };
    (text, declared)
}

/// The root local of the place a statement at `at` writes.
fn written_root(cx: &BodyCx, at: Point) -> Option<Local> {
    match cx.body.stmt_at(at).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => Some(dest.local),
        _ => None,
    }
}

/// The path to field `field` that `target` is written through: `this.src` of
/// `this.src[0]` or of `this.src.slice(...)`, `this.id` of `this.id`; `None`
/// when `target` reaches it some other way (`r[0]` after `const r = &this.cells`).
fn field_path(target: &str, field: &str) -> Option<String> {
    if target == field {
        return Some(target.to_owned());
    }
    let dotted = format!(".{field}");
    let mut from = 0;
    while let Some(i) = target[from..].find(&dotted).map(|i| i + from) {
        let end = i + dotted.len();
        let next = target[end..].chars().next();
        if next.is_none_or(|c| !(c.is_alphanumeric() || c == '_' || c == '$')) {
            return Some(target[..end].to_owned());
        }
        from = end;
    }
    None
}

/// A field with a `readonly` part as a note names it: the `readonly &` field
/// `src`, the `readonly` field `cells`, or the field `t` with a `readonly &` part.
fn readonly_field_words(fd: &enrang_hir::FieldDef) -> String {
    match (
        fd.readonly_refs.contains(&Vec::new()),
        fd.readonly_refs.is_empty(),
    ) {
        (true, _) => format!("the `readonly &` field `{}`", fd.name),
        (false, false) => format!("a `readonly &` part of the field `{}`", fd.name),
        (false, true) => format!("the `readonly` field `{}`", fd.name),
    }
}

/// Whether the statement or call at `at` writes a `string` through a reference.
fn written_is_str(cx: &BodyCx, at: Point) -> bool {
    let (tcx, b) = (cx.tcx, cx.body);
    let is_str = |t: Ty| match tcx.kind(t) {
        TyKind::Str => true,
        TyKind::Ref(i) => tcx.kind(i) == TyKind::Str,
        _ => false,
    };
    match b.stmt_at(at).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => place_ty(cx, *dest).is_some_and(is_str),
        _ => call_of(b, at)
            .and_then(|(_, args, _)| args.first()?.place())
            .and_then(|p| place_ty(cx, p))
            .is_some_and(is_str),
    }
}

/// T:906's help for a string part grown by `+=`: the string the part came from,
/// the first source argument of the call to `f` as written, and the appended
/// text.
fn grow_directly(cx: &BodyCx, m: &MarkError, f: DefId) -> Option<(String, String)> {
    let (tcx, b) = (cx.tcx, cx.body);
    let map = tcx.map();
    let written = text(map, m.span);
    let (_, rhs) = written.split_once("+=")?;
    let rhs = rhs.trim().trim_end_matches(';').trim();
    if rhs.is_empty() {
        return None;
    }
    let src = points(b).find_map(|p| {
        let (callee, args, _) = call_of(b, p)?;
        if callee_def(callee) != Some(f) {
            return None;
        }
        args.iter()
            .filter_map(|a| a.place())
            .find_map(|a| receiver_text(cx, p, a))
    })?;
    Some((src, rhs.to_owned()))
}

/// Whether the marked argument of the call at `at` is a source whose result is
/// written through (S:773's `book`), rather than a parameter the callee writes.
fn is_source_pass(cx: &BodyCx, at: Point) -> bool {
    let b = cx.body;
    let Some((callee, args, _)) = call_of(b, at) else {
        return false;
    };
    let info = crate::cx::call_info(cx, callee, args);
    info.perms.iter().all(|p| *p != Perm::Write) && matches!(info.result, ResultPerm::Writable)
}

/// The name of the parameter of `f` that the marked argument, the call's
/// argument `arg`, is passed to (S:775), else of the first one the call writes.
fn written_param(cx: &BodyCx, at: Point, f: DefId, arg: Option<usize>) -> Option<String> {
    let tcx = cx.tcx;
    let (callee, args, _) = call_of(cx.body, at)?;
    let info = crate::cx::call_info(cx, callee, args);
    let first = usize::from(tcx.takes_this(f));
    let a = match arg {
        Some(a) => a,
        None => {
            let i = info.perms.iter().position(|p| *p == Perm::Write)?;
            *info.args_map.get(i)?
        }
    };
    match a.checked_sub(first) {
        None => Some("the object".to_owned()),
        Some(k) => tcx.sig_opt(f)?.params.get(k).map(|p| sym(p.name)),
    }
}

// ---------------------------------------------------------------------------------
// Stores (EN0616 of `held`).

pub fn report_store(cx: &BodyCx, e: &StoreError) -> Diagnostic {
    let (tcx, b) = (cx.tcx, cx.body);
    let into = match b.stmt_at(e.at).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => place_text(tcx, b, *dest),
        _ => None,
    };
    match e.kind {
        StoreErrorKind::ReadSet => Diagnostic::new(
            Code::EN0616,
            // S:957 / T:995: `` `src` is declared `readonly &`, so it can't hold
            // a reference from `dst` `` when both fields are known.
            match (stored_field(cx, e.at, into_field(cx, e.at)), into_field(cx, e.at)) {
                (Some(from), Some(f)) => format!(
                    "`{f}` is declared `readonly &`, so it can't hold a reference from `{from}`"
                ),
                _ => match &into {
                    Some(f) => format!("`{f}` is `readonly &`, so it can't take a reference that another field writes through"),
                    None => "a `readonly &` field can't take a reference that another field writes through".to_owned(),
                },
            },
            e.span,
            "stored here",
        )
        .with_help(Help::text(
            "store a reference from a parameter, or from another `readonly &` field",
        )),
        StoreErrorKind::Captured => Diagnostic::new(
            Code::EN0616,
            match captured_name(cx, e.at).or_else(|| captured_receiver(cx, e.at)) {
                Some(c) => format!("cannot store a reference into captured `{c}`"),
                None => "cannot store a reference into a captured value".to_owned(),
            },
            e.span,
            "stored here",
        )
        .note("what an arrow captures lives outside it, so a reference stored there could outlive what it points at"),
        StoreErrorKind::Consumed(i) => {
            let who = match (i, owner_def(b)) {
                (0, Some(d)) if tcx.takes_this(d) => "`this`".to_owned(),
                (_, Some(d)) => {
                    let k = i as usize - usize::from(tcx.takes_this(d));
                    tcx.sig_opt(d)
                        .and_then(|s| s.params.get(k))
                        .map_or_else(|| "a parameter".to_owned(), |p| format!("`{}`", p.name))
                }
                _ => "a parameter".to_owned(),
            };
            // T:1015: an Own `this` is "consumed", a by-value parameter
            // "by-value".
            let kind = match who.as_str() {
                "`this`" => "consumed",
                _ => "by-value",
            };
            Diagnostic::new(
                Code::EN0616,
                format!("cannot store a reference into a value reached through {kind} {who}"),
                e.span,
                "stored here",
            )
            .note("a consumed value is disposed of when the function ends, so nothing stored in it reaches the caller")
            .with_help(Help::text(
                "write the field directly, or take the value by reference",
            ))
        }
    }
}

/// The name of the field a store at `at` writes, `src` of `w.src = p`.
fn into_field(cx: &BodyCx, at: Point) -> Option<String> {
    let b = cx.body;
    let Some(StatementKind::Assign { dest, .. }) = b.stmt_at(at).map(|s| &s.kind) else {
        return None;
    };
    let projs = b.projs(*dest);
    let (Proj::Field(f), base) = projs.split_last()? else {
        return None;
    };
    let pt = base
        .iter()
        .try_fold(PlaceTy::of(b.locals[dest.local].ty), |t, q| {
            t.project(cx.tcx, *q)
        })?;
    field_name(cx.tcx, pt, *f)
}

/// The field the reference a store at `at` writes was read from, through the
/// temporaries and calls that carry it: `dst` of `const p = w.dst; w.src = p;`
/// or of `this.src = this.dst.slice(0, 1);`. `None` when it is the field
/// written itself, or none is found.
fn stored_field(cx: &BodyCx, at: Point, into: Option<String>) -> Option<String> {
    let (tcx, b) = (cx.tcx, cx.body);
    let Some(StatementKind::Assign { value, .. }) = b.stmt_at(at).map(|s| &s.kind) else {
        return None;
    };
    let mut op = match value {
        Rvalue::Use(o) | Rvalue::Convert(_, o) => o.place()?,
        _ => return None,
    };
    for _ in 0..b.locals.len() {
        if let Some((Proj::Field(f), base)) = b.projs(op).split_last() {
            let pt = base
                .iter()
                .try_fold(PlaceTy::of(b.locals[op.local].ty), |t, q| {
                    t.project(tcx, *q)
                })?;
            let name = field_name(tcx, pt, *f)?;
            return (Some(&name) != into.as_ref()).then_some(name);
        }
        if !op.is_local() {
            return None;
        }
        // The value's own definition: a copy, a borrow, or a call's result,
        // through its receiver.
        op = b.blocks.iter().find_map(|blk| {
            let st = blk.stmts.iter().find_map(|s| match &s.kind {
                StatementKind::Assign { dest, value } if *dest == op => match value {
                    Rvalue::Use(o) | Rvalue::Convert(_, o) => o.place(),
                    Rvalue::Ref { place, .. } => Some(*place),
                    _ => None,
                },
                _ => None,
            });
            st.or_else(|| match &blk.term.kind {
                TerminatorKind::Call { dest, args, .. } if *dest == op => {
                    args.first().and_then(|a| a.place())
                }
                _ => None,
            })
        })?;
        // A reborrow `&*x` carries what the reference `x` holds.
        if b.projs(op) == [Proj::Deref] {
            op = Place::local(op.local);
        }
    }
    None
}

/// The captured variable a call's store at `at` writes into: its receiver's
/// place, in an arrow body (`lx` of `lx.setSrc(&t)`).
fn captured_receiver(cx: &BodyCx, at: Point) -> Option<String> {
    let b = cx.body;
    let (_, args, _) = call_of(b, at)?;
    let mut p = args.first()?.place()?;
    for _ in 0..b.locals.len() {
        if p.local == Local(1) {
            return capture_of(cx, p);
        }
        p = temp_source(b, p.local).or_else(|| {
            b.blocks
                .iter()
                .flat_map(|blk| &blk.stmts)
                .find_map(|s| match &s.kind {
                    StatementKind::Assign {
                        dest,
                        value: Rvalue::Ref { place, .. },
                    } if *dest == p => Some(*place),
                    _ => None,
                })
        })?;
    }
    None
}

/// The captured variable a store at `at` writes into, in an arrow body.
fn captured_name(cx: &BodyCx, at: Point) -> Option<String> {
    let b = cx.body;
    let dest = match b.stmt_at(at).map(|s| &s.kind) {
        Some(StatementKind::Assign { dest, .. }) => *dest,
        _ => return None,
    };
    if dest.local != Local(1) {
        return place_text(cx.tcx, b, dest);
    }
    capture_of(cx, dest)
}

/// The variable an arrow's place `(*(*_1).k)...` captures, as its parent names
/// it.
/// A place reached through a capture, as the parent names it: `u.name` for
/// `(*(*_env).k).name` of an arrow capturing `u`, `this.items` through a captured
/// `this`, and `name` for `*_1` of a local function's hidden argument `name`.
fn captured_text(cx: &BodyCx, p: Place) -> Option<String> {
    let (tcx, b) = (cx.tcx, cx.body);
    let projs = b.projs(p);
    match b.owner {
        BodyOwner::Arrow(..) => {
            let [Proj::Deref, Proj::Field(f), rest @ ..] = projs else {
                return None;
            };
            let var = capture_of(cx, p)?;
            let pt = PlaceTy::of(b.locals[p.local].ty)
                .project(tcx, Proj::Deref)?
                .project(tcx, Proj::Field(*f))?;
            projs_text_from(tcx, b, var, pt, rest, true)
        }
        BodyOwner::Fn(d) => {
            let hidden = crate::r3::hidden(tcx, d, b).contains(&(p.local.0.wrapping_sub(1)));
            if !hidden || b.locals[p.local].kind != LocalKind::Arg {
                return None;
            }
            let var = local_name(tcx, b, p.local)?;
            let pt = PlaceTy::of(b.locals[p.local].ty);
            projs_text_from(tcx, b, var, pt, projs, true)
        }
        _ => None,
    }
}

fn capture_of(cx: &BodyCx, dest: Place) -> Option<String> {
    let b = cx.body;
    if dest.local != Local(1) {
        return None;
    }
    // `(*(*_1).k)...`: the arrow's capture `k`.
    match b.projs(dest) {
        [Proj::Deref, Proj::Field(f), ..] => capture_name(cx, enrang_base::Idx::index(*f)),
        _ => None,
    }
}

/// The variable an arrow's capture `k` holds, as the arrow's parent names it.
pub(crate) fn capture_name(cx: &BodyCx, k: usize) -> Option<String> {
    let BodyOwner::Arrow(parent, arrow) = cx.body.owner else {
        return None;
    };
    let parent_body = cx.bodies.values().find(|x| match (x.owner, parent) {
        (BodyOwner::Fn(a), enrang_hir::BodyOwner::Fn(c)) => a == c,
        (BodyOwner::Statements(a), enrang_hir::BodyOwner::Statements(c)) => a == c,
        (BodyOwner::Test(a), enrang_hir::BodyOwner::Test(c)) => a == c,
        _ => false,
    })?;
    // The env aggregate of the closure value that makes this arrow.
    points(parent_body).find_map(|p| match parent_body.stmt_at(p).map(|s| &s.kind) {
        Some(StatementKind::Assign {
            value:
                Rvalue::ClosureValue {
                    func: enrang_mir::ClosureFn::Arrow(a),
                    env,
                },
            ..
        }) if *a == arrow => {
            let env_def = points(parent_body).find_map(|q| {
                match parent_body.stmt_at(q).map(|s| &s.kind) {
                    Some(StatementKind::Assign {
                        dest,
                        value: Rvalue::Aggregate(_, ops),
                    }) if dest == env => ops.get(k).cloned(),
                    _ => None,
                }
            })?;
            let src = match env_def {
                Operand::Copy(p) | Operand::Move(p) => p,
                Operand::Const(_) => return None,
            };
            // A capture `&x [closure-capture]` names `x`.
            points(parent_body)
                .find_map(|q| match parent_body.stmt_at(q).map(|s| &s.kind) {
                    Some(StatementKind::Assign {
                        dest,
                        value: Rvalue::Ref { place, .. },
                    }) if *dest == src => place_text(cx.tcx, parent_body, *place),
                    _ => None,
                })
                .or_else(|| place_text(cx.tcx, parent_body, src))
        }
        _ => None,
    })
}

// ---------------------------------------------------------------------------------
// Contracts (EN0615, EN0714, EN0418).

pub fn report_contract(tcx: &Tcx, f: &FitError) -> Diagnostic {
    let map = tcx.map();
    match f.code {
        Code::EN0418 => {
            let class = name_of(tcx, f.found);
            Diagnostic::new(
                f.code,
                format!("`{class}` writes through its reference fields, so copying it would make two writers"),
                f.site,
                "declared `implements Copy` here",
            )
            .with_help(Help::text(format!(
                "if `{class}` only reads through them, write `readonly` before their types or before the return types that hand them out, or remove `implements Copy`"
            )))
        }
        Code::EN0714 => {
            let found = qualified(tcx, f.found);
            if f.found == f.member {
                // A function converted to an `fn` type is reported at the
                // coercion, with no secondary span (S:939).
                let label = match f.slot.is_some() {
                    true => "converted here",
                    false => "returned here",
                };
                return Diagnostic::new(
                    f.code,
                    format!("`{found}` returns a reference its signature does not allow"),
                    f.site,
                    label,
                )
                .note("a returned reference may borrow only from the parameters its signature names as sources");
            }
            // S:931: the source outside the base's, and the ones it allows.
            let member = qualified(tcx, f.member);
            let sources = |c: &enrang_hir::Contract| match &c.sources {
                enrang_hir::RetSources::Params(v) => v.clone(),
                enrang_hir::RetSources::NoLoans => Vec::new(),
            };
            let imp = sources(&crate::contract(tcx, f.found));
            let base = crate::declared::as_virtual((*crate::contract(tcx, f.member)).clone());
            let this = usize::from(tcx.takes_this(f.member));
            // Parameters first, then `this`, as S:931 lists them.
            let mut decl = sources(&base);
            decl.sort_by_key(|i| (this == 1 && *i == 0, *i));
            let name = |i: u32| match (this, i) {
                (1, 0) => "this".to_owned(),
                _ => (tcx.sig_opt(f.member))
                    .and_then(|s| s.params.get(i as usize - this))
                    .map_or_else(|| format!("#{i}"), |p| sym(p.name)),
            };
            let quoted: Vec<String> = decl.iter().map(|i| format!("`{}`", name(*i))).collect();
            let message = match imp.iter().find(|i| !decl.contains(i)) {
                Some(&o) if !quoted.is_empty() => format!(
                    "`{found}` returns a reference into `{}`, but `{member}` returns only into {}",
                    name(o),
                    quoted.join(" or ")
                ),
                _ => format!("`{found}` returns a reference that `{member}` does not allow"),
            };
            let d = Diagnostic::new(f.code, message, f.site, "returned here")
                .with_secondary(tcx.def(f.member).name_span, "declared here");
            let expected: Vec<String> = (decl.iter())
                .map(|i| match name(*i).as_str() {
                    "this" => "the object".to_owned(),
                    n => format!("`{n}`"),
                })
                .collect();
            match expected.is_empty() {
                true => d,
                false => d.with_help(Help::text(format!(
                    "through a `&{}`, callers only expect {}",
                    parent_name(tcx, f.member),
                    expected.join(" or ")
                ))),
            }
        }
        Code::EN0615 => misfit(tcx, map, f),
        // A local function passed as a closure that stores through what it
        // captures (A:1360, S:981): its hidden arguments.
        Code::EN0616 => {
            let found = name_of(tcx, f.found);
            let message = match f.captured {
                Some((v, true)) => format!("`{found}` stores a reference into captured `{v}`"),
                Some((v, false)) => format!("`{found}` stores captured `{v}` into a parameter"),
                None => format!("`{found}` stores a reference into what it captures"),
            };
            Diagnostic::new(f.code, message, f.site, "passed as a closure here")
                .note("as a closure a local function captures the variables it uses, which live outside it, so a reference stored there could outlive what it points at")
                .with_help(Help::text(format!(
                    "call `{found}()` directly, which applies its stores as any call does"
                )))
        }
        // R3's Own-`this` row (A:1284, S:929): a `move` method returns a
        // reference into the object it consumes.
        Code::EN0710 => Diagnostic::new(
            f.code,
            format!(
                "`{}` returns a reference into the object it consumes",
                name_of(tcx, f.found)
            ),
            f.site,
            "this reference would point at the consumed object",
        )
        .note("a `move` method gives up its object, which is disposed of when the method ends")
        .with_help(Help::text(
            "return the value itself, or take `this` by reference",
        )),
        _ => Diagnostic::new(f.code, f.code.title(), f.site, ""),
    }
}

/// EN0615 at a value whose function rows do not fit its slot's (S:682, T:583,
/// `S2-13-value`).
pub fn report_row(tcx: &Tcx, e: &crate::rows::RowError) -> Diagnostic {
    use crate::rows::RowKind;
    // The slot's own function type keeps the names its declaration wrote (D14).
    // The value's row in a help is the slot's type with other marks, so it takes
    // the slot's names too, as written syntax needs (D14).
    let spell = |t: Ty| match t == e.slot || t == e.from {
        true => tcx.fn_ty_string(t, e.slot_names.as_deref()),
        false => tcx.ty_string(t),
    };
    let (from, to) = (spell(e.from), spell(e.to));
    let param = |i: usize| match (e.slot == e.to, &e.slot_names) {
        (true, Some(names)) if i < names.len() => format!("`{}`", sym(names[i])),
        _ => format!("its parameter {}", i + 1),
    };
    let src = &e.source;
    match &e.kind {
        RowKind::Writes { param: p } => {
            let what = match p {
                Some(i) => format!("writes {}", param(*i)),
                None => "returns a read-only reference".to_owned(),
            };
            Diagnostic::new(
                Code::EN0615,
                format!("`{src}` may hold a function that {what}, so it can't become a `{to}`"),
                e.site,
                "converted here",
            )
            .note("a function value may write only what its type's `let` marks allow")
            .with_help(Help::text(format!(
                "declare the slot's type with the row the value needs: `{from}`"
            )))
        }
        RowKind::Nested => Diagnostic::new(
            Code::EN0615,
            format!("`{src}` holds a `{from}` where a `{to}` is expected"),
            e.site,
            "converted here",
        )
        .note("type checking ignores `let` marks, but below the top of a type a function type's row must be equal, since code holding the outer value may store into it or call through it with either row"),
        RowKind::Signature {
            found,
            member,
            param: p,
        } => {
            let found_name = qualified(tcx, *found);
            let what = match p.and_then(|i| tcx.sig_opt(*found)?.params.get(i).map(|x| x.name)) {
                Some(n) => format!("takes `{}` as a `{from}`", sym(n)),
                None => format!("returns a `{from}`"),
            };
            match member {
                Some(m) => Diagnostic::new(
                    Code::EN0615,
                    format!(
                        "`{found_name}` {what}, but `{}` declares a `{to}`",
                        qualified(tcx, *m)
                    ),
                    e.site,
                    "declared here",
                )
                .with_secondary(tcx.def(*m).name_span, "the declaration it stands for")
                .note("a function type's row nested inside a signature must be equal to the one it stands for, since callers through either may pass or return any function the row allows"),
                None => Diagnostic::new(
                    Code::EN0615,
                    format!("`{found_name}` {what}, but its function type declares a `{to}`"),
                    e.site,
                    "converted here",
                )
                .note("a function type's row nested inside a signature must be equal to the function's own"),
            }
        }
        RowKind::Arrow { param } => {
            let what = match param {
                Some(n) => format!("takes `{}` as a `{from}`", sym(n)),
                None => format!("returns a `{from}`"),
            };
            Diagnostic::new(
                Code::EN0615,
                format!("this arrow {what}, but its function type declares a `{to}`"),
                e.site,
                "converted here",
            )
            .note("a function type's row nested inside a signature must be equal to the function's own")
        }
        RowKind::StringForm { param: i } => Diagnostic::new(
            Code::EN0615,
            format!(
                "`{src}` may hold a function that takes {} as a part, so it can't become a `{to}`",
                param(*i)
            ),
            e.site,
            "converted here",
        )
        .with_help(Help::text(format!(
            "declare the wider row where the value comes from: `{to}`"
        ))),
    }
}

/// EN0615 (G18, S:623, S:935, S:1339, plan d.10).
fn misfit(tcx: &Tcx, map: &SourceMap, f: &FitError) -> Diagnostic {
    let found_name = match name_of(tcx, f.found) {
        n if n.is_empty() || tcx.def(f.found).kind == DefKind::Module => "this arrow".to_owned(),
        n => format!("`{n}`"),
    };
    // N12 (S:1133): a `const` mark in a body containing `unsafe`, broken by a
    // safe operation that writes, or hands on to a writer, what it marks.
    if let Some(i) = f.marked {
        let this = usize::from(tcx.takes_this(f.found));
        let param = (i as usize)
            .checked_sub(this)
            .and_then(|k| tcx.sig_opt(f.found)?.params.get(k).map(|p| sym(p.name)));
        let (message, target, mark) = match (this == 1 && i == 0, param) {
            (true, _) | (false, None) => (
                format!("{found_name} is marked `const`, but it changes the object"),
                "this".to_owned(),
                name_of(tcx, f.found),
            ),
            (false, Some(p)) => (
                format!("`{p}` is marked `const`, but {found_name} changes it"),
                p.clone(),
                p,
            ),
        };
        return Diagnostic::new(
            f.code,
            message,
            f.site,
            format!("this needs exclusive access to `{target}`"),
        )
        .note("in a body containing `unsafe`, the safe code treats a `const` reference as shared: it may not write it, or pass it to a function that does")
        .with_help(Help::text(format!(
            "remove `const` before `{mark}` if the body changes it"
        )));
    }
    if f.found == f.member {
        if crate::declared::is_role(tcx, f.found) {
            return Diagnostic::new(
                f.code,
                format!("{found_name} writes a parameter that it may only read"),
                f.site,
                "this write needs exclusive access",
            )
            .note("the parameters of `@entry`, `@panicHandler`, `@interrupt` and `test.each` are read-only");
        }
        if let Some(slot) = &f.slot
            && let Some(d) = slot_misfit(tcx, f, &found_name, slot)
        {
            return d;
        }
        return Diagnostic::new(
            f.code,
            format!("{found_name} does more with its references than its function type allows"),
            f.site,
            "converted here",
        )
        .note(
            "a function value may write only what its type's `let` marks allow, and store nothing",
        );
    }
    let imp = crate::contract(tcx, f.found);
    let decl = crate::declared::as_virtual((*crate::contract(tcx, f.member)).clone());
    let owner = parent_name(tcx, f.member);
    let member_name = tcx.def(f.member).name_span;
    let this = usize::from(tcx.takes_this(f.found));
    let written: Vec<usize> = (0..imp.perms.len())
        .filter(|&q| {
            imp.perms[q] == Perm::Write
                && decl.perms.get(q).copied().unwrap_or(Perm::Read) < Perm::Write
        })
        .collect();
    if let Some(&q) = written.first() {
        let object = this == 1 && q == 0;
        let sig = tcx.sig_opt(f.member);
        let param = |q: usize| {
            sig.and_then(|s| s.params.get(q - this))
                .map(|p| sym(p.name))
        };
        let what = match object {
            true => "the object".to_owned(),
            false => param(q).map_or_else(|| "a parameter".to_owned(), |p| format!("`{p}`")),
        };
        let target = match object {
            true => "this".to_owned(),
            false => param(q).unwrap_or_default(),
        };
        // At the class (a structural satisfaction, or a `let` mark the body
        // needs no write for), the label names the method, not a write.
        let found_def = tcx.def(f.found);
        let at_class = !(found_def.span.lo <= f.site.lo && f.site.hi <= found_def.span.hi);
        let marked_let = match object {
            true => {
                tcx.sig_opt(f.found).and_then(|s| s.receiver)
                    == Some(enrang_hir::Receiver::Ref(enrang_hir::Mark::Let))
            }
            false => tcx
                .sig_opt(f.found)
                .and_then(|s| s.params.get(q - this))
                .is_some_and(|p| p.mark == enrang_hir::Mark::Let),
        };
        let class = parent_name(tcx, f.found);
        let fname = name_of(tcx, f.found);
        let label = match (at_class, marked_let) {
            (false, _) => format!("this write needs exclusive access to `{target}`"),
            (true, true) => format!("`{fname}` is marked `let` in `{class}`"),
            (true, false) => format!("`{fname}` in `{class}` changes {what}"),
        };
        let d = Diagnostic::new(
            f.code,
            format!("{found_name} changes {what}, but `{owner}` declares that it doesn't"),
            f.site,
            label,
        )
        .with_secondary(member_name, "declared here without `let`");
        // The declaration with `let` where the implementation writes: the
        // member from its name to its `;`.
        let decl_span = tcx.def(f.member).span;
        let line = Span {
            lo: member_name.lo,
            hi: decl_span.hi.max(member_name.hi),
        };
        let line_text = text(map, line);
        let mut edits = Vec::new();
        let mut inserts: Vec<(usize, &str)> = Vec::new();
        for &q in &written {
            let at = match this == 1 && q == 0 {
                true => Some(member_name.lo),
                false => sig
                    .and_then(|s| s.params.get(q - this))
                    .map(|p| p.span.lo)
                    .filter(|lo| line.lo <= *lo && *lo <= line.hi),
            };
            if let Some(at) = at {
                edits.push(Edit::insert(at, "let "));
                inserts.push(((at.0 - line.lo.0) as usize, "let "));
            }
        }
        let mut shown = line_text.to_owned();
        for (at, s) in inserts.iter().rev() {
            if *at <= shown.len() {
                shown.insert_str(*at, s);
            }
        }
        let mut shown = shown.trim_end().to_owned();
        if !shown.ends_with(';') {
            shown.push(';');
        }
        let subject = match object {
            true => "the object",
            false => "it",
        };
        let name = name_of(tcx, f.member);
        let short = line_text.contains('{') || line_text.contains('\n');
        let message = match (short, object) {
            (true, true) => format!(
                "if implementations may change {subject}, write `let` before `{name}` in `{owner}`"
            ),
            // The edit marks the parameter, which the help names (A:1314).
            (true, false) => format!(
                "if implementations may change {subject}, write `let` before `{}` in `{owner}.{name}`",
                param(q).unwrap_or_default()
            ),
            (false, _) => {
                format!("if implementations may change {subject}, write `{shown}` in `{owner}`")
            }
        };
        // A library member is never the user's to edit (as G07's help, A:1314),
        // and an implementation that also stores what the member declares no
        // store of would still not fit once marked `let`, so the edit is withheld
        // there (the store is the next report, A:1314).
        let library = tcx.module(tcx.def(f.member).module).library;
        let stores_more = imp
            .stores
            .iter()
            .any(|s| !(decl.stores.iter()).any(|d| d.from == s.from && d.into == s.into));
        return match (library, edits.is_empty() || stores_more) {
            (true, _) => d.with_help(Help::text(format!(
                "an implementation of `{owner}.{name}` may only read {subject}"
            ))),
            (false, true) => d.with_help(Help::text(message)),
            (false, false) => d.with_help(Help::suggest(message, edits)),
        };
    }
    if decl.result == ResultPerm::Writable && matches!(imp.result, ResultPerm::ReadOnly(_)) {
        return Diagnostic::new(
            f.code,
            format!(
                "`{}` returns a read-only reference, but `{owner}` declares a writable one",
                qualified(tcx, f.found)
            ),
            f.site,
            "returns a read-only reference",
        )
        .with_secondary(member_name, "declared here")
        .with_help(readonly_result_help(tcx, map, f.member));
    }
    if imp
        .perms
        .iter()
        .zip(&decl.perms)
        .any(|(a, b)| (*a == Perm::Own) != (*b == Perm::Own))
    {
        return Diagnostic::new(
            f.code,
            format!(
                "`{}` and `{}` must both be `move` or both not",
                qualified(tcx, f.found),
                qualified(tcx, f.member)
            ),
            f.site,
            "here",
        )
        .with_secondary(member_name, "declared here");
    }
    // A store the declared ones do not cover.
    let store = imp.stores.iter().find(|s| {
        !decl
            .stores
            .iter()
            .any(|d| d.from == s.from && d.into == s.into)
    });
    // A store the declared one covers with fewer bits (A:1365): it keeps the
    // parameter itself, not only what its fields hold (T:852), or keeps it in a
    // `readonly &` field, which joins the read set too (T:849).
    let paired = imp.stores.iter().find_map(|s| {
        let d = (decl.stores.iter()).find(|d| d.from == s.from && d.into == s.into)?;
        Some((s, d))
    });
    let sig = tcx.sig_opt(f.found);
    let name = |i: u32| -> String {
        let i = i as usize;
        match (this, i) {
            (1, 0) => "this".to_owned(),
            _ => sig
                .and_then(|s| s.params.get(i - this))
                .map_or_else(|| format!("#{i}"), |p| sym(p.name)),
        }
    };
    let (found_q, member_q) = (qualified(tcx, f.found), qualified(tcx, f.member));
    let into_this = |s: &enrang_hir::Store| this == 1 && s.into == 0;
    let message = match (store, paired) {
        (Some(s), _) => format!(
            "`{found_q}` stores `{}` into `{}`, but `{member_q}` declares no such store",
            name(s.from),
            name(s.into),
        ),
        (None, Some((s, d)))
            if !s.fields_only && !s.read_set_only && (d.fields_only || d.read_set_only) =>
        {
            let only = match d.fields_only {
                true => "fields",
                false => "`readonly &` fields",
            };
            let (p, m) = (name(s.from), name(s.into));
            match into_this(s) || p == m {
                true => format!(
                    "`{found_q}` keeps `{p}` itself, but `{member_q}` keeps only what `{p}`'s {only} hold"
                ),
                false => format!(
                    "`{found_q}` keeps `{p}` itself in `{m}`, but `{member_q}` keeps only what `{p}`'s {only} hold"
                ),
            }
        }
        (None, Some((s, d))) if s.read && !d.read => {
            let p = name(s.from);
            let field = readonly_ref_field(tcx, f.found).map_or_else(
                || "a `readonly &` field".to_owned(),
                |x| format!("the `readonly &` field `{x}`"),
            );
            format!(
                "`{found_q}` keeps `{p}` in {field}, but `{member_q}` keeps it in another field"
            )
        }
        _ => format!("`{found_q}` keeps more of its parameters than `{member_q}` declares"),
    };
    Diagnostic::new(f.code, message, f.site, "stored here")
        .with_secondary(member_name, "declared here")
}

/// EN0615 at an `fn` value or closure value that does not fit its slot's row
/// (A:1356, A:1365): `` `reset` stores `s` into `lx`, which `fn(let lx: &Lexer,
/// s: &string) => void` can't declare ``; a write the row's marks do not allow; a
/// read-only result where the row's is writable, with T:584's help to write
/// `readonly` before the type's result.
fn slot_misfit(
    tcx: &Tcx,
    f: &FitError,
    found: &str,
    slot: &crate::fit::SlotFit,
) -> Option<Diagnostic> {
    // The slot's type as written: its declaration's names, else the value's own.
    let names = slot.names.clone().unwrap_or_else(|| slot.params.clone());
    let ty = tcx.fn_ty_string(slot.ty, Some(&names));
    let param = |i: u32| slot.slots.get(i as usize).map(|n| sym(*n));
    let note =
        "a function value may write only what its type's `let` marks allow, and store nothing";
    if let Some(s) = slot
        .imp
        .stores
        .iter()
        .find(|s| !(slot.row.stores.iter()).any(|d| d.from == s.from && d.into == s.into))
    {
        let (from, into) = (param(s.from)?, param(s.into)?);
        return Some(
            Diagnostic::new(
                f.code,
                format!("{found} stores `{from}` into `{into}`, which `{ty}` can't declare"),
                f.site,
                "converted here",
            )
            .note(note),
        );
    }
    let written = (0..slot.imp.perms.len()).find(|&q| {
        slot.imp.perms[q] == Perm::Write
            && slot.row.perms.get(q).copied().unwrap_or(Perm::Read) < Perm::Write
    });
    if let Some(q) = written {
        let p = param(q as u32)?;
        return Some(
            Diagnostic::new(
                f.code,
                format!("{found} changes `{p}`, which `{ty}` can't declare"),
                f.site,
                "converted here",
            )
            .note(note),
        );
    }
    if slot.row.result == ResultPerm::Writable && matches!(slot.imp.result, ResultPerm::ReadOnly(_))
    {
        // `readonly` before the result: after the `=>` that follows the
        // parameter list's `)`.
        let close = {
            let mut depth = 0i32;
            ty.char_indices().find_map(|(i, c)| {
                match c {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                (depth == 0 && c == ')').then_some(i)
            })?
        };
        let arrow = close + ty[close..].find("=> ")? + 3;
        let fixed = format!("{}readonly {}", &ty[..arrow], &ty[arrow..]);
        return Some(
            Diagnostic::new(
                f.code,
                format!(
                    "{found} returns a read-only reference, but `{ty}` declares a writable one"
                ),
                f.site,
                "converted here",
            )
            .with_help(Help::text(format!(
                "if callers only read it, write `readonly` before the type's result: `{fixed}`"
            ))),
        );
    }
    None
}

/// The one `readonly &` field the class of method `f` declares itself, if one.
fn readonly_ref_field(tcx: &Tcx, f: DefId) -> Option<String> {
    let adt = tcx.adt_of(tcx.def(f).parent?)?;
    let class = tcx.adt(adt).as_class()?;
    let fields: Vec<String> = (0..class.fields.len())
        .map(|i| tcx.field_def(adt, None, <FieldIdx as enrang_base::Idx>::new(i)))
        .filter(|fd| fd.declared_in == adt && fd.readonly_refs.contains(&Vec::new()))
        .map(|fd| sym(fd.name))
        .collect();
    match fields.as_slice() {
        [one] => Some(one.clone()),
        _ => None,
    }
}

/// S:625's help for a read-only result where the declaration's is writable: the
/// declaration with `readonly` before its return type, `` write `let next():
/// readonly &string | null;` in `TokenReader` ``, with that edit when it is the
/// user's to make.
fn readonly_result_help(tcx: &Tcx, map: &SourceMap, member: DefId) -> Help {
    let data = tcx.def(member);
    let owner = parent_name(tcx, member);
    let name = name_of(tcx, member);
    let library = tcx.module(data.module).library;
    let ret = tcx
        .sig_opt(member)
        .and_then(|sig| written_ret(map, data, &tcx.ty_string(sig.ret)));
    let decl = text(map, data.span);
    match ret {
        Some(at) if !library && !decl.contains('{') && !decl.contains('\n') => {
            let k = (at.lo.0 - data.span.lo.0) as usize;
            let mut shown = decl.trim_end().to_owned();
            if k <= shown.len() {
                shown.insert_str(k, "readonly ");
            }
            if !shown.ends_with(';') {
                shown.push(';');
            }
            Help::suggest(
                format!("if callers only read it, write `{shown}` in `{owner}`"),
                vec![Edit::insert(at.lo, "readonly ")],
            )
        }
        Some(at) if !library => Help::suggest(
            format!(
                "if callers only read it, write `readonly` before the return type of `{name}` in `{owner}`"
            ),
            vec![Edit::insert(at.lo, "readonly ")],
        ),
        _ => Help::text(format!(
            "an implementation of `{owner}.{name}` must return a writable reference"
        )),
    }
}

// ---------------------------------------------------------------------------------
// Module-level and phase 4 reports.

/// EN0610 at a `this` in a field initialiser or an override's default (K8, A:998).
pub fn report_init_this(span: Span) -> Diagnostic {
    Diagnostic::new(
        Code::EN0610,
        "`this` can't be used in a field initialiser",
        span,
        "the object is not built yet here",
    )
    .note("field initialisers run while the object is built, before the constructor's body, so they can't read the object")
    .with_help(Help::text("set the field in the constructor instead"))
}

/// EN0804: a reference to a field of a `@packed` class that may be misaligned
/// (A:653, S:1300), phase 4.
pub fn report_packed(tcx: &Tcx, b: &Body, place: Place, span: Span) -> Diagnostic {
    let shown = place_text(tcx, b, place).unwrap_or_else(|| text(tcx.map(), span).to_owned());
    // The borrow as written, with its `&` (T:676: a loop's `&q`).
    let span = with_amp(tcx.map(), span);
    Diagnostic::new(
        Code::EN0804,
        format!("reference to the packed field `{shown}`, which may be misaligned"),
        span,
        "a `@packed` class aligns its fields to 1 byte",
    )
    .with_help(Help::text(format!(
        "copy the field into a local first: `const v = {shown};`"
    )))
}
