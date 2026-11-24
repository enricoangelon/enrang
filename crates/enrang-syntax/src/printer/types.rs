//! Printing types: no space before a `<`, `| null`, closure and function pointer
//! types, object and tuple types, and the parentheses of `Paren` type nodes.

use crate::ast::*;
use crate::token::Punct;

use super::doc::{Doc, concat, group, indent, join, line, nil, text};
use super::{ListItem, ListOpts, Printer, pos};

impl Printer<'_> {
    pub(super) fn ty(&mut self, ty: &TypeExpr) -> Doc {
        let lead = if self.has_place(ty.span) {
            self.leading(pos(ty.span.lo))
        } else {
            nil()
        };
        let doc = self.ty_kind(ty);
        concat(vec![lead, doc])
    }

    fn ty_kind(&mut self, ty: &TypeExpr) -> Doc {
        match &ty.kind {
            TypeExprKind::Named { path, args } => {
                let names: Vec<Doc> = path.iter().map(|name| self.ident(name)).collect();
                let args = self.type_args(args);
                concat(vec![join(&text("."), names), args])
            }
            TypeExprKind::Nullable(inner) => match &inner.kind {
                TypeExprKind::Union(members) => {
                    let mut docs = self.union_members(members);
                    docs.push((None, text("null")));
                    union_chain(docs)
                }
                _ => concat(vec![self.ty(inner), text(" | null")]),
            },
            TypeExprKind::Ref(inner) => concat(vec![text("&"), self.ty(inner)]),
            TypeExprKind::Raw(inner) => concat(vec![text("*"), self.ty(inner)]),
            TypeExprKind::ReadonlyRef(inner) => concat(vec![text("readonly &"), self.ty(inner)]),
            TypeExprKind::Array(inner) => concat(vec![self.ty(inner), text("[]")]),
            TypeExprKind::Fixed(inner, len) => {
                let inner = self.ty(inner);
                let len = self.expr(len);
                concat(vec![inner, text("["), len, text("]")])
            }
            TypeExprKind::Tuple(elems) => {
                let close = self.close_of(ty.span);
                let opts = ListOpts::new("[", "]").close_at(close);
                self.list(
                    elems,
                    |elem| elem.span,
                    |p, elem| ListItem::plain(p.ty(elem)),
                    opts,
                )
                .doc
            }
            TypeExprKind::FnPtr(fn_ptr) => {
                let decorators: Vec<Doc> = fn_ptr
                    .decorators
                    .iter()
                    .map(|decorator| {
                        let doc = self.decorator(decorator);
                        concat(vec![doc, text(" ")])
                    })
                    .collect();
                let unsafe_ = if fn_ptr.is_unsafe {
                    text("unsafe ")
                } else {
                    nil()
                };
                let params = self.typed_params(&fn_ptr.params, |p| {
                    concat(vec![text(" => "), p.ret_type(&fn_ptr.ret)])
                });
                concat(vec![concat(decorators), unsafe_, text("fn"), params])
            }
            TypeExprKind::Closure(closure) => self.typed_params(&closure.params, |p| {
                concat(vec![text(" => "), p.ty(&closure.ret)])
            }),
            TypeExprKind::Object(fields) => {
                let close = self.close_of(ty.span);
                let opts = ListOpts::braces().close_at(close);
                self.list(
                    fields,
                    |(name, _, ty)| name.span.to(ty.span),
                    |p, (name, optional, ty)| {
                        let name = p.ident(name);
                        let mark = if *optional { text("?: ") } else { text(": ") };
                        ListItem::plain(concat(vec![name, mark, p.ty(ty)]))
                    },
                    opts,
                )
                .doc
            }
            TypeExprKind::StrUnion(members) => {
                let mut docs = Vec::with_capacity(members.len());
                for (at, lit) in members.iter().enumerate() {
                    let trailing = if at > 0 && self.has_place(lit.span) {
                        self.code_comment(pos(lit.span.lo))
                    } else {
                        None
                    };
                    docs.push((trailing, self.str_lit(lit)));
                }
                union_chain(docs)
            }
            TypeExprKind::Union(members) => {
                let docs = self.union_members(members);
                union_chain(docs)
            }
            TypeExprKind::Paren(inner) => concat(vec![text("("), self.ty(inner), text(")")]),
            TypeExprKind::Void => text("void"),
            TypeExprKind::Never => text("never"),
            TypeExprKind::NullLit => text("null"),
            TypeExprKind::Error => self.error_text(ty.span),
        }
    }

    /// The members of a union, each with the comment that follows the `|` before it
    /// on its line, if one does.
    fn union_members(&mut self, members: &[TypeExpr]) -> Vec<(Option<Doc>, Doc)> {
        let mut docs = Vec::with_capacity(members.len() + 1);
        for (at, member) in members.iter().enumerate() {
            let trailing = if at > 0 && self.has_place(member.span) {
                self.code_comment(pos(member.span.lo))
            } else {
                None
            };
            docs.push((trailing, self.ty(member)));
        }
        docs
    }

    /// `(let x: T, y: U)` of a closure or function pointer type, then `suffix`.
    fn typed_params(
        &mut self,
        params: &[TypedParam],
        suffix: impl FnOnce(&mut Self) -> Doc,
    ) -> Doc {
        let close = params
            .last()
            .and_then(|last| self.closer_after(pos(last.ty.span.hi), Punct::RParen));
        let opts = ListOpts::params().close_at(close);
        self.list_then(
            params,
            |param| param.name.span.to(param.ty.span),
            |p, param| {
                let mark = if param.is_let { text("let ") } else { nil() };
                let name = p.ident(&param.name);
                let ty = p.ty(&param.ty);
                ListItem::plain(concat(vec![mark, name, text(": "), ty]))
            },
            opts,
            suffix,
        )
        .doc
    }

    /// `[readonly] Type`.
    pub(super) fn ret_type(&mut self, ret: &RetType) -> Doc {
        let readonly = if ret.readonly {
            text("readonly ")
        } else {
            nil()
        };
        concat(vec![readonly, self.ty(&ret.ty)])
    }

    /// `<T extends A & B, U>`, or nothing.
    pub(super) fn type_params(&mut self, params: &[TypeParam]) -> Doc {
        if params.is_empty() {
            return nil();
        }
        let close = params.last().and_then(|last| {
            let end = last
                .bounds
                .last()
                .map_or(last.name.span, |bound| bound.span);
            self.closer_after(pos(end.hi), Punct::Gt)
        });
        let opts = ListOpts {
            fill: false,
            ..ListOpts::new("<", ">")
        }
        .close_at(close);
        self.list(
            params,
            |param| match param.bounds.last() {
                Some(bound) => param.name.span.to(bound.span),
                None => param.name.span,
            },
            |p, param| {
                let name = p.ident(&param.name);
                ListItem::plain(concat(vec![name, p.bounds(&param.bounds)]))
            },
            opts,
        )
        .doc
    }

    /// ` extends A & B`, or nothing.
    pub(super) fn bounds(&mut self, bounds: &[TypeExpr]) -> Doc {
        if bounds.is_empty() {
            return nil();
        }
        let bounds: Vec<Doc> = bounds.iter().map(|bound| self.ty(bound)).collect();
        concat(vec![text(" extends "), join(&text(" & "), bounds)])
    }
}

/// `A | B | null` from its members, each with the trailing comment of the `|`
/// before it: flat when it fits, else each line ends with its `|` and the members
/// after the first go one per line, indented 2 more, as a long operator chain does
/// (SPEC 12.5 Width, Operators).
fn union_chain(members: Vec<(Option<Doc>, Doc)>) -> Doc {
    let mut members = members.into_iter();
    let Some((_, first)) = members.next() else {
        return nil();
    };
    let mut rest = Vec::new();
    for (trailing, member) in members {
        rest.push(text(" |"));
        rest.extend(trailing);
        rest.push(line());
        rest.push(member);
    }
    group(concat(vec![first, indent(concat(rest))]))
}
