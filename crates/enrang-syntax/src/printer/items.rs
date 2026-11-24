//! Printing the file, imports (sorted by the Imports rule), decorators as placed,
//! items, signatures and their breaking, class and enum bodies one member per line,
//! and the test items of SPEC 3.6 (SPEC 12.5).

use enrang_base::Span;

use crate::ast::*;
use crate::token::Punct;

use super::comments::SeqEl;
use super::doc::{Doc, GroupId, concat, group, hardline, indent, line, nil, text};
use super::exprs::Arg;
use super::stmts::after_condition;
use super::{ListItem, ListOpts, Printer, pos};

/// An element of the file's top-level sequence.
enum Top<'f> {
    /// An import, and whether to sort the names of its brace list.
    Import(&'f Import, bool),
    Stmt(&'f Stmt),
    Item(&'f Item),
}

/// An element of an enum body.
enum EnumEl<'f> {
    Variant(&'f Variant),
    /// The `;` before the methods.
    Semi,
    Method(&'f MethodDecl),
}

/// An element of a class, interface or `extend` body.
enum Member<'f> {
    Class(&'f ClassMember),
    Iface(&'f IfaceMember),
    Extend(&'f ExtendMember),
}

impl Printer<'_> {
    pub(super) fn file(&mut self, file: &File) -> Doc {
        let mut els: Vec<SeqEl<Top<'_>>> = Vec::new();
        for group in self.import_groups(&file.imports) {
            let sorted = !self.import_group_commented(&group);
            let mut order = group.clone();
            if sorted {
                order.sort_by(|a, b| a.path.value.as_str().cmp(b.path.value.as_str()));
            }
            for (slot, import) in group.iter().zip(order) {
                els.push(SeqEl {
                    blank_at: self.has_place(slot.span).then(|| pos(slot.span.lo)),
                    ..SeqEl::new(import.span, Top::Import(import, sorted))
                });
            }
        }
        let mut rest: Vec<SeqEl<Top<'_>>> = file
            .stmts
            .iter()
            .map(|stmt| SeqEl::new(stmt.span, Top::Stmt(stmt)))
            .chain(
                file.items
                    .iter()
                    .map(|item| SeqEl::new(item_span(item), Top::Item(item))),
            )
            .collect();
        if self.real {
            rest.sort_by_key(|el| el.span.lo);
        }
        els.extend(rest);
        let close = self.real.then(|| self.start + self.src.len() as u32 + 1);
        let seq = self.seq(None, close, &els, false, |p, el| match el {
            Top::Import(import, sort) => p.import(import, *sort),
            Top::Stmt(stmt) => p.stmt(stmt),
            Top::Item(item) => p.item(item),
        });
        seq.doc
    }

    /// The groups of consecutive import lines: a blank line ends a group.
    fn import_groups<'f>(&self, imports: &'f [Import]) -> Vec<Vec<&'f Import>> {
        let mut groups: Vec<Vec<&Import>> = Vec::new();
        for import in imports {
            let joins = match groups.last().and_then(|group| group.last()) {
                Some(prev) => {
                    !self.has_place(import.span)
                        || !self.blank_between(pos(prev.span.hi), pos(import.span.lo))
                }
                None => false,
            };
            match groups.last_mut() {
                Some(group) if joins => group.push(import),
                _ => groups.push(vec![import]),
            }
        }
        groups
    }

    /// Whether a line holding only white space lies between two positions.
    fn blank_between(&self, lo: u32, hi: u32) -> bool {
        let between = self.slice(lo, hi);
        let mut lines = between.split('\n');
        lines.next();
        let mut middle: Vec<&str> = lines.collect();
        middle.pop();
        middle.iter().any(|line| line.trim().is_empty())
    }

    /// SPEC 12.5 Imports: "a group or brace list holding a comment stays as
    /// written", lines and names alike, as does a group right after
    /// `// enrang-fmt-ignore`. A comment on the line of the group's last import counts
    /// as held; one on a line before the group does not.
    fn import_group_commented(&self, group: &[&Import]) -> bool {
        let (Some(first), Some(last)) = (group.first(), group.last()) else {
            return false;
        };
        if !self.has_place(first.span) {
            return false;
        }
        let (lo, hi) = (pos(first.span.lo), pos(last.span.hi));
        if self.has_comment_in(lo, hi) {
            return true;
        }
        let pending = &self.comments[self.next_comment..];
        let trailing = pending
            .iter()
            .find(|comment| comment.lo >= hi)
            .is_some_and(|comment| !self.slice(hi, comment.lo).contains('\n'));
        let ignored = pending
            .iter()
            .rev()
            .find(|comment| comment.hi <= lo)
            .is_some_and(|comment| {
                self.is_ignore(comment) && self.slice(comment.hi, lo).trim().is_empty()
            });
        trailing || ignored
    }

    fn import(&mut self, import: &Import, sort_names: bool) -> Doc {
        let public = if import.public {
            text("public ")
        } else {
            nil()
        };
        let what = match &import.kind {
            ImportKind::Named(names) => {
                let mut names: Vec<&ImportName> = names.iter().collect();
                if sort_names {
                    names.sort_by(|a, b| a.name.name.as_str().cmp(b.name.name.as_str()));
                }
                let close = names
                    .iter()
                    .map(|name| import_name_span(name))
                    .max_by_key(|span| span.hi)
                    .and_then(|span| self.closer_after(pos(span.hi), Punct::RBrace));
                let opts = ListOpts::braces().close_at(close);
                self.list(
                    &names,
                    |name| import_name_span(name),
                    |p, name| {
                        let doc = p.ident(&name.name);
                        let doc = match &name.alias {
                            Some(alias) => concat(vec![doc, text(" as "), p.ident(alias)]),
                            None => doc,
                        };
                        ListItem::plain(doc)
                    },
                    opts,
                )
                .doc
            }
            ImportKind::Namespace(name) => concat(vec![text("* as "), self.ident(name)]),
        };
        let path = self.str_lit(&import.path);
        concat(vec![
            public,
            text("import "),
            what,
            text(" from "),
            path,
            text(";"),
        ])
    }

    pub(super) fn item(&mut self, item: &Item) -> Doc {
        let decorators = self.decorators(&item.decorators);
        let vis = visibility(item.visibility);
        let kind = match &item.kind {
            ItemKind::Function(decl) => self.function_decl(decl),
            ItemKind::Class(class) => self.class(class),
            ItemKind::Enum(decl) => self.enum_decl(decl),
            ItemKind::Interface(decl) => self.interface(decl),
            ItemKind::TypeAlias(alias) => {
                let name = self.ident(&alias.name);
                let params = self.type_params(&alias.type_params);
                let ty = self.ty(&alias.ty);
                concat(vec![
                    text("type "),
                    name,
                    params,
                    text(" = "),
                    ty,
                    text(";"),
                ])
            }
            ItemKind::TopConst(decl) => {
                let name = self.ident(&decl.name);
                let ty = match &decl.ty {
                    Some(ty) => concat(vec![text(": "), self.ty(ty)]),
                    None => nil(),
                };
                let lhs = concat(vec![text("const "), name, ty]);
                concat(vec![self.rhs(lhs, "=", &decl.value), text(";")])
            }
            ItemKind::UnsafeLet(decl) => {
                let name = self.ident(&decl.name);
                let ty = self.ty(&decl.ty);
                let lhs = concat(vec![text("unsafe let "), name, text(": "), ty]);
                let decl = match &decl.value {
                    Some(value) => self.rhs(lhs, "=", value),
                    None => lhs,
                };
                concat(vec![decl, text(";")])
            }
            ItemKind::DeclareFn(decl) => {
                let name = self.ident(&decl.name);
                let (sig, _) =
                    self.signature(&decl.type_params, &decl.params, |p| match &decl.ret {
                        Some(ret) => concat(vec![text(": "), p.ty(ret)]),
                        None => nil(),
                    });
                concat(vec![text("declare function "), name, sig, text(";")])
            }
            ItemKind::Extend(decl) => self.extend(decl),
            ItemKind::StaticAssert { cond, message } => concat(vec![
                self.assert_call(cond, message.as_ref(), item.span),
                text(";"),
            ]),
            ItemKind::Describe(describe) => self.describe(describe),
            ItemKind::Test(test) => self.test(test),
            ItemKind::CompileCase(case) => self.compile_case(case),
        };
        concat(vec![decorators, vis, kind])
    }

    /// Decorators as placed (SPEC 12.5 Decorators): each on the declaration's line,
    /// followed by one space, or on a line of its own, as the source had it. A
    /// decorator followed by a comment on its line keeps it as a trailing comment on
    /// a line of its own, and the comments between the last decorator and the
    /// declaration's first word go before that word.
    pub(super) fn decorators(&mut self, decorators: &[Decorator]) -> Doc {
        let mut parts = Vec::with_capacity(decorators.len() * 2 + 1);
        for decorator in decorators {
            parts.push(self.decorator(decorator));
            if !self.has_place(decorator.span) {
                parts.push(text(" "));
                continue;
            }
            let found = self.take_trailing(pos(decorator.span.hi), false);
            if !found.is_empty() {
                parts.push(self.trailing_doc(&found));
                parts.push(hardline());
            } else if self.newline_after(pos(decorator.span.hi)) {
                parts.push(hardline());
            } else {
                parts.push(text(" "));
            }
        }
        if let Some(last) = decorators.last()
            && self.has_place(last.span)
        {
            let next = self.token_at(pos(last.span.hi));
            if let Some(lo) = self.tokens.get(next).map(|token| pos(token.span.lo)) {
                parts.push(self.leading(lo));
            }
        }
        concat(parts)
    }

    pub(super) fn decorator(&mut self, decorator: &Decorator) -> Doc {
        let lead = if self.has_place(decorator.span) {
            self.leading(pos(decorator.span.lo))
        } else {
            nil()
        };
        let name = self.ident(&decorator.name);
        let args = match &decorator.args {
            Some(args) => {
                let close = self.close_of(decorator.span);
                self.args(args, close)
            }
            None => nil(),
        };
        concat(vec![lead, text("@"), name, args])
    }

    pub(super) fn function_decl(&mut self, decl: &FunctionDecl) -> Doc {
        let unsafe_ = if decl.is_unsafe {
            text("unsafe ")
        } else {
            nil()
        };
        let name = self.ident(&decl.name);
        let (sig, sig_id) = self.signature(&decl.type_params, &decl.params, |p| {
            p.ret_suffix(decl.ret.as_ref())
        });
        let body = self.body(&decl.body);
        let body = after_condition(sig_id, body);
        concat(vec![unsafe_, text("function "), name, sig, text(" "), body])
    }

    fn ret_suffix(&mut self, ret: Option<&RetType>) -> Doc {
        match ret {
            Some(ret) => concat(vec![text(": "), self.ret_type(ret)]),
            None => nil(),
        }
    }

    /// `<T>(params)` and `suffix`, the return type and `where` clause, which belong to
    /// the parameters' group (SPEC 12.5 Signatures): parameters that do not fit break
    /// one per line, closed by `): Ret`; type parameters that do not fit break first.
    /// Returns the id of the parameters' group, which a body follows: when it broke,
    /// the body goes one statement per line, so `): Ret {` ends its line.
    fn signature(
        &mut self,
        type_params: &[TypeParam],
        params: &[Param],
        suffix: impl FnOnce(&mut Self) -> Doc,
    ) -> (Doc, GroupId) {
        let type_params = self.type_params(type_params);
        let close = params
            .last()
            .and_then(|last| self.closer_after(pos(last.span.hi), Punct::RParen));
        let opts = ListOpts::params().close_at(close);
        let params = self.list_then(
            params,
            |param| param.span,
            |p, param| ListItem::plain(p.param(param)),
            opts,
            suffix,
        );
        (concat(vec![type_params, params.doc]), params.id)
    }

    fn param(&mut self, param: &Param) -> Doc {
        let mark = mark(param.mark);
        let binding = self.binding(&param.binding);
        let optional = if param.optional { text("?") } else { nil() };
        let ty = self.ty(&param.ty);
        let decl = concat(vec![mark, binding, optional, text(": "), ty]);
        match &param.default {
            Some(default) => self.rhs(decl, "=", default),
            None => decl,
        }
    }

    fn ctor_param(&mut self, param: &CtorParam) -> Doc {
        let property = visibility(param.property);
        let readonly = if param.is_readonly {
            text("readonly ")
        } else {
            nil()
        };
        let mark = mark(param.mark);
        let name = self.ident(&param.name);
        let optional = if param.optional { text("?") } else { nil() };
        let ty = self.ty(&param.ty);
        let decl = concat(vec![
            property,
            readonly,
            mark,
            name,
            optional,
            text(": "),
            ty,
        ]);
        match &param.default {
            Some(default) => self.rhs(decl, "=", default),
            None => decl,
        }
    }

    /// `(where T extends A, U extends B)`, or nothing.
    fn where_clause(&mut self, preds: &[WherePred]) -> Doc {
        if preds.is_empty() {
            return nil();
        }
        let preds: Vec<Doc> = preds
            .iter()
            .map(|pred| {
                let name = self.ident(&pred.param);
                let bounds = self.bounds(&pred.bounds);
                concat(vec![name, bounds])
            })
            .collect();
        clause(
            " where",
            preds.into_iter().map(|pred| (None, pred)).collect(),
        )
    }

    fn method(&mut self, method: &MethodDecl) -> Doc {
        let vis = visibility(method.visibility);
        let static_ = if method.receiver == Receiver::Static {
            text("static ")
        } else {
            nil()
        };
        let abstract_ = if method.is_abstract {
            text("abstract ")
        } else {
            nil()
        };
        let override_ = if method.is_override {
            text("override ")
        } else {
            nil()
        };
        let receiver = match method.receiver {
            Receiver::Let => text("let "),
            Receiver::Const => text("const "),
            Receiver::Move => text("move "),
            Receiver::Plain | Receiver::Static => nil(),
        };
        let unsafe_ = if method.is_unsafe {
            text("unsafe ")
        } else {
            nil()
        };
        let name = self.ident(&method.name);
        let (sig, sig_id) = self.signature(&method.type_params, &method.params, |p| {
            let ret = p.ret_suffix(method.ret.as_ref());
            let where_ = p.where_clause(&method.where_clause);
            concat(vec![ret, where_])
        });
        let body = match &method.body {
            Some(body) => {
                let body = self.body(body);
                concat(vec![text(" "), after_condition(sig_id, body)])
            }
            None => text(";"),
        };
        concat(vec![
            vis, static_, abstract_, override_, receiver, unsafe_, name, sig, body,
        ])
    }

    /// The positions after the `{` and at the `}` of a body that follows `after`.
    fn body_braces(&self, after: Span) -> (Option<u32>, Option<u32>) {
        if self.has_place(after) {
            self.braces_after(pos(after.hi))
        } else {
            (None, None)
        }
    }

    /// A class, interface or `extend` body: one member per line.
    fn members(&mut self, after: Span, members: Vec<SeqEl<Member<'_>>>) -> Doc {
        let (open, close) = self.body_braces(after);
        let seq = self.seq(open, close, &members, false, |p, member| match member {
            Member::Class(member) => p.class_member(member),
            Member::Iface(member) => match member {
                IfaceMember::Method(method) => p.method(method),
                IfaceMember::Field(field) => {
                    let name = p.ident(&field.name);
                    let optional = if field.optional { text("?") } else { nil() };
                    let ty = p.ty(&field.ty);
                    concat(vec![name, optional, text(": "), ty, text(";")])
                }
            },
            Member::Extend(member) => {
                let decorators = p.decorators(&member.decorators);
                concat(vec![decorators, p.method(&member.method)])
            }
        });
        self.braces(seq, false).0
    }

    fn class(&mut self, class: &ClassDecl) -> Doc {
        let modifier = match class.modifier {
            ClassModifier::Plain => nil(),
            ClassModifier::Abstract => text("abstract "),
            ClassModifier::Final => text("final "),
        };
        let name = self.ident(&class.name);
        let params = self.type_params(&class.type_params);
        let mut header_end = class
            .type_params
            .last()
            .map_or(class.name.span, type_param_span);
        let extends = match &class.extends {
            Some(base) => {
                header_end = base.span;
                concat(vec![text(" extends "), self.ty(base)])
            }
            None => nil(),
        };
        let implements = if class.implements.is_empty() {
            nil()
        } else {
            let mut tys = Vec::with_capacity(class.implements.len());
            for (at, ty) in class.implements.iter().enumerate() {
                let trailing = if at > 0 && self.has_place(ty.span) {
                    self.code_comment(pos(ty.span.lo))
                } else {
                    None
                };
                tys.push((trailing, self.ty(ty)));
            }
            if let Some(last) = class.implements.last() {
                header_end = last.span;
            }
            clause(" implements", tys)
        };
        let members = class
            .members
            .iter()
            .map(|member| {
                let span = decorated(member.span, &member.decorators);
                SeqEl::new(span, Member::Class(member))
            })
            .collect();
        let body = self.members(header_end, members);
        concat(vec![
            modifier,
            text("class "),
            name,
            params,
            extends,
            implements,
            text(" "),
            body,
        ])
    }

    fn class_member(&mut self, member: &ClassMember) -> Doc {
        let decorators = self.decorators(&member.decorators);
        let kind = match &member.kind {
            ClassMemberKind::Field(field) => {
                let vis = visibility(field.visibility);
                let override_ = if field.is_override {
                    text("override ")
                } else {
                    nil()
                };
                let readonly = if field.is_readonly {
                    text("readonly ")
                } else {
                    nil()
                };
                let name = self.ident(&field.name);
                let optional = if field.optional { text("?") } else { nil() };
                let ty = self.ty(&field.ty);
                let decl = concat(vec![
                    vis,
                    override_,
                    readonly,
                    name,
                    optional,
                    text(": "),
                    ty,
                ]);
                let decl = match &field.default {
                    Some(default) => self.rhs(decl, "=", default),
                    None => decl,
                };
                concat(vec![decl, text(";")])
            }
            ClassMemberKind::Constructor(ctor) => {
                let vis = visibility(ctor.visibility);
                let close = ctor
                    .params
                    .last()
                    .and_then(|last| self.closer_after(pos(last.span.hi), Punct::RParen));
                let opts = ListOpts::params().close_at(close);
                let params = self.list(
                    &ctor.params,
                    |param| param.span,
                    |p, param| ListItem::plain(p.ctor_param(param)),
                    opts,
                );
                let body = self.body(&ctor.body);
                let body = after_condition(params.id, body);
                concat(vec![vis, text("constructor"), params.doc, text(" "), body])
            }
            ClassMemberKind::Destructor(dtor) => {
                let vis = visibility(dtor.visibility);
                let body = self.body(&dtor.body).0;
                concat(vec![vis, text("destructor() "), body])
            }
            ClassMemberKind::Method(method) => self.method(method),
        };
        concat(vec![decorators, kind])
    }

    fn enum_decl(&mut self, decl: &EnumDecl) -> Doc {
        let name = self.ident(&decl.name);
        let params = self.type_params(&decl.type_params);
        let header_end = decl
            .type_params
            .last()
            .map_or(decl.name.span, type_param_span);
        let mut els: Vec<SeqEl<EnumEl<'_>>> = decl
            .variants
            .iter()
            .map(|variant| {
                let span = decorated(variant.span, &variant.decorators);
                SeqEl::row(span, EnumEl::Variant(variant))
            })
            .collect();
        if !decl.methods.is_empty() {
            els.push(SeqEl::row(Span::DUMMY, EnumEl::Semi));
            els.extend(
                decl.methods
                    .iter()
                    .map(|method| SeqEl::new(method.span, EnumEl::Method(method))),
            );
        }
        let (open, close) = self.body_braces(header_end);
        let seq = self.seq(open, close, &els, true, |p, el| match el {
            EnumEl::Variant(variant) => {
                let doc = p.variant(variant);
                concat(vec![doc, text(",")])
            }
            EnumEl::Semi => text(";"),
            EnumEl::Method(method) => p.method(method),
        });
        let body = self.braces(seq, false).0;
        concat(vec![text("enum "), name, params, text(" "), body])
    }

    fn variant(&mut self, variant: &Variant) -> Doc {
        let decorators = self.decorators(&variant.decorators);
        let name = self.ident(&variant.name);
        let payload = match &variant.payload {
            VariantPayload::Unit => nil(),
            VariantPayload::Fields(fields) => {
                let close = fields
                    .last()
                    .and_then(|last| self.closer_after(pos(last.ty.span.hi), Punct::RBrace));
                let opts = ListOpts::braces().close_at(close);
                let list = self
                    .list(
                        fields,
                        |field| field.name.span.to(field.ty.span),
                        |p, field| {
                            let name = p.ident(&field.name);
                            ListItem::plain(concat(vec![name, text(": "), p.ty(&field.ty)]))
                        },
                        opts,
                    )
                    .doc;
                concat(vec![text(" "), list])
            }
            VariantPayload::Value(value) => concat(vec![text(" = "), self.expr(value)]),
        };
        concat(vec![decorators, name, payload])
    }

    fn interface(&mut self, decl: &InterfaceDecl) -> Doc {
        let name = self.ident(&decl.name);
        let params = self.type_params(&decl.type_params);
        let header_end = decl
            .type_params
            .last()
            .map_or(decl.name.span, type_param_span);
        let members = decl
            .members
            .iter()
            .map(|member| {
                let span = match member {
                    IfaceMember::Method(method) => method.span,
                    IfaceMember::Field(field) => field.span,
                };
                SeqEl::new(span, Member::Iface(member))
            })
            .collect();
        let body = self.members(header_end, members);
        concat(vec![text("interface "), name, params, text(" "), body])
    }

    fn extend(&mut self, decl: &ExtendDecl) -> Doc {
        let params = self.type_params(&decl.type_params);
        let ty = self.ty(&decl.ty);
        let members = decl
            .members
            .iter()
            .map(|member| {
                let span = decorated(member.span, &member.decorators);
                SeqEl::new(span, Member::Extend(member))
            })
            .collect();
        let body = self.members(decl.ty.span, members);
        concat(vec![text("extend"), params, text(" "), ty, text(" "), body])
    }

    // -----------------------------------------------------------------------------
    // SPEC 3.6: test items, printed as the calls they look like.

    fn describe(&mut self, describe: &DescribeItem) -> Doc {
        let (open, close) = self.body_braces(describe.name.span);
        let paren = close.and_then(|close| self.closer_after(close + 1, Punct::RParen));
        let opts = ListOpts {
            hug: true,
            ..ListOpts::new("(", ")")
        }
        .close_at(paren);
        let items = &describe.items;
        let args = [Some(&describe.name), None];
        let list = self.list(
            &args,
            |arg| arg.map_or(Span::DUMMY, |name| name.span),
            |p, arg| match arg {
                Some(name) => ListItem::plain(p.str_lit(name)),
                None => {
                    let els: Vec<SeqEl<&Item>> = items
                        .iter()
                        .map(|item| SeqEl::new(item_span(item), item))
                        .collect();
                    let seq = p.seq(open, close, &els, false, |p, item| p.item(item));
                    let one_line = match items.as_slice() {
                        [only] => !item_holds_block(only),
                        _ => false,
                    };
                    let (body, id) = p.braces(seq, one_line);
                    ListItem {
                        doc: concat(vec![text("() => "), body]),
                        hug: Some(id),
                    }
                }
            },
            opts,
        );
        concat(vec![text("describe"), list.doc, text(";")])
    }

    fn test(&mut self, test: &TestDecl) -> Doc {
        let mode = match test.mode {
            None => "",
            Some(TestMode::Only) => ".only",
            Some(TestMode::Skip) => ".skip",
            Some(TestMode::Todo) => ".todo",
            Some(TestMode::Panics) => ".panics",
            Some(TestMode::Each) => ".each",
        };
        let mut args = vec![Arg::Str(&test.name)];
        match &test.extra {
            Some(TestExtra::Message(message)) => args.push(Arg::Str(message)),
            Some(TestExtra::Cases(cases)) => args.push(Arg::Arrow(cases)),
            None => {}
        }
        if let Some(body) = &test.body {
            args.push(Arg::Arrow(body));
        }
        if let Some(options) = &test.options {
            args.push(Arg::Expr(options));
        }
        let close = args
            .last()
            .map(Arg::span)
            .and_then(|span| self.closer_after(pos(span.hi), Punct::RParen));
        let list = self.arg_list(&args, close);
        concat(vec![text("test"), text(mode), list, text(";")])
    }

    fn compile_case(&mut self, case: &CompileCase) -> Doc {
        let word = match case.kind {
            CompileKind::Fails => "compileFails",
            CompileKind::Ok => "compileOk",
        };
        let mut args = vec![Arg::Str(&case.name), Arg::Raw(&case.source)];
        if let Some(options) = &case.options {
            args.push(Arg::Expr(options));
        }
        let close = args
            .last()
            .map(Arg::span)
            .and_then(|span| self.closer_after(pos(span.hi), Punct::RParen));
        let list = self.arg_list(&args, close);
        concat(vec![text(word), list, text(";")])
    }
}

fn visibility(vis: Option<Visibility>) -> Doc {
    match vis {
        Some(Visibility::Public) => text("public "),
        Some(Visibility::Private) => text("private "),
        Some(Visibility::Protected) => text("protected "),
        None => nil(),
    }
}

fn mark(mark: ParamMark) -> Doc {
    match mark {
        ParamMark::Plain => nil(),
        ParamMark::Let => text("let "),
        ParamMark::Const => text("const "),
    }
}

/// A node's span with its decorators.
fn decorated(span: Span, decorators: &[Decorator]) -> Span {
    decorators
        .iter()
        .fold(span, |span, decorator| span.to(decorator.span))
}

fn item_span(item: &Item) -> Span {
    decorated(item.span, &item.decorators)
}

fn type_param_span(param: &TypeParam) -> Span {
    match param.bounds.last() {
        Some(bound) => param.name.span.to(bound.span),
        None => param.name.span,
    }
}

fn import_name_span(name: &ImportName) -> Span {
    match &name.alias {
        Some(alias) => name.name.span.to(alias.span),
        None => name.name.span,
    }
}

/// Whether a test item holds a block, so a `describe` body holding only it splits.
fn item_holds_block(item: &Item) -> bool {
    match &item.kind {
        ItemKind::Describe(_) => true,
        ItemKind::Test(test) => {
            test.body.is_some()
                || matches!(&test.extra, Some(TestExtra::Cases(cases))
                    if matches!(cases.body, ArrowBody::Block(_)))
        }
        _ => false,
    }
}

/// ` implements A, B` or ` where T extends A, U extends B`, each item with the
/// trailing comment of the `,` before it: on one line when it fits, else the word
/// ends its line and the items go one per line after it, each but the last ending
/// with `,`, indented 2 more (SPEC 12.5 Width, Lists).
fn clause(word: &str, items: Vec<(Option<Doc>, Doc)>) -> Doc {
    let mut parts = Vec::with_capacity(items.len() * 4);
    for (at, (trailing, item)) in items.into_iter().enumerate() {
        if at > 0 {
            parts.push(text(","));
        }
        parts.extend(trailing);
        parts.push(line());
        parts.push(item);
    }
    group(concat(vec![text(word), indent(concat(parts))]))
}
