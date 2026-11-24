//! SPEC 3.2 types: `NullableType`, prefix `&` and `*` with `split_token` for `&&` and
//! `**`, postfix `[]` and `[N]`, named types and their arguments with the closing
//! `>` split, function pointer and closure types, object and tuple types, the
//! `readonly` of a field's or a function's type, and the unions SPEC 3.2 rejects or
//! keeps for phase 2.
//!
//! In a pure type position the spacing before `<` is irrelevant; after `as` a `<`
//! with no space before it starts arguments only if they parse, and otherwise the
//! type ends at the name (SPEC 3.4, Disambiguation).

use enrang_base::{BytePos, Span};
use enrang_diag::Code;

use super::{Guess, Parser, hints, recover};
use crate::ast::{ClosureType, FnPtrType, RetType, StrLit, TypeExpr, TypeExprKind, TypedParam};
use crate::token::{Contextual, Keyword, Punct, TokenKind};

/// Whether `readonly` may stand before `ty` as a return type: after one `| null`,
/// a reference, a tuple with a reference part, or a name, which may be a
/// borrowing class that sema judges (SPEC 3.1 `RetType`).
fn takes_readonly(ty: &TypeExpr) -> bool {
    let mut inner = match &ty.kind {
        TypeExprKind::Nullable(inner) => inner,
        _ => ty,
    };
    while let TypeExprKind::Paren(paren) = &inner.kind {
        inner = paren;
    }
    match &inner.kind {
        TypeExprKind::Ref(_)
        | TypeExprKind::ReadonlyRef(_)
        | TypeExprKind::Named { .. }
        | TypeExprKind::Error => true,
        TypeExprKind::Tuple(elems) => elems.iter().any(|elem| {
            let elem = match &elem.kind {
                TypeExprKind::Nullable(inner) => inner,
                _ => elem,
            };
            matches!(
                elem.kind,
                TypeExprKind::Ref(_) | TypeExprKind::ReadonlyRef(_)
            )
        }),
        _ => false,
    }
}

impl Parser<'_> {
    /// `Type = PrefixType { "|" PrefixType }`: one trailing `| null` is `Nullable`,
    /// and any other `|` a `Union` that phase 2 rejects (EN0406). Object types
    /// joined by `|` are EN0215 and a string literal among the operands EN0216;
    /// `A & B` is EN1024 and keeps `A`; `T extends U ? X : Y` is EN1023.
    pub(super) fn parse_type(&mut self) -> TypeExpr {
        if !self.enter() {
            return self.error_ty();
        }
        let lo = self.lo();
        let ty = self.parse_type_from(lo, None);
        self.leave();
        ty
    }

    /// `parse_type` from `lo`, whose first operand is `first` when it is already
    /// parsed, as a field's tuple type is.
    fn parse_type_from(&mut self, lo: BytePos, mut first: Option<TypeExpr>) -> TypeExpr {
        // A `type` alias's own right side may be a string-literal union; a type
        // nested in it may not.
        let in_alias = std::mem::replace(&mut self.in_alias, false);
        let mut operands = Vec::new();
        let mut pipes = Vec::new();
        let mut strings = Vec::new();
        loop {
            if let Some(ty) = first.take() {
                operands.push(ty);
                self.skip_intersection();
            } else if matches!(self.peek().kind, TokenKind::Str(_)) {
                let token = self.bump();
                strings.push(token.span);
                operands.push(self.mk_ty(TypeExprKind::Error, token.span));
            } else {
                operands.push(self.parse_prefix_type(false));
                self.skip_intersection();
            }
            if !self.at(Punct::Pipe) {
                break;
            }
            pipes.push(self.bump().span);
        }
        let span = self.span_from(lo);
        let ty = if let Some(&first) = strings.first() {
            hints::string_type(self, first, in_alias);
            self.mk_ty(TypeExprKind::Error, span)
        } else if operands.len() == 1 {
            operands.pop().expect("one operand")
        } else {
            let nullable = operands
                .last()
                .is_some_and(|ty| ty.kind == TypeExprKind::NullLit);
            if nullable {
                operands.pop();
            }
            let objects = operands.len() >= 2
                && operands
                    .iter()
                    .all(|ty| matches!(ty.kind, TypeExprKind::Object(_)));
            if objects {
                hints::object_union(self, pipes[0]);
                self.mk_ty(TypeExprKind::Error, span)
            } else if nullable {
                let inner = if operands.len() == 1 {
                    operands.pop().expect("one operand")
                } else {
                    let first = operands.first().map_or(span, |ty| ty.span);
                    let last = operands.last().map_or(span, |ty| ty.span);
                    self.mk_ty(TypeExprKind::Union(operands), first.to(last))
                };
                self.mk_ty(TypeExprKind::Nullable(Box::new(inner)), span)
            } else {
                self.mk_ty(TypeExprKind::Union(operands), span)
            }
        };
        if self.at_word(Contextual::Extends) {
            self.conditional_type(lo)
        } else {
            ty
        }
    }

    /// `& B` after a type's operand, outside a bound: EN1024 at the first `&`, and
    /// the operands after it dropped.
    fn skip_intersection(&mut self) {
        if !self.at(Punct::Amp) {
            return;
        }
        let amp = self.peek().span;
        hints::intersection(self, amp);
        while self.eat(Punct::Amp) {
            self.parse_prefix_type(false);
        }
    }

    /// `T extends U ? X : Y` after the type that starts at `lo`: EN1023, an
    /// `Error` type.
    fn conditional_type(&mut self, lo: BytePos) -> TypeExpr {
        self.bump();
        self.parse_prefix_type(false);
        if self.eat(Punct::Question) {
            self.parse_type();
            if self.eat(Punct::Colon) {
                self.parse_type();
            }
        }
        let span = self.span_from(lo);
        hints::report_deferred(self, Code::EN1023, span, "computes a type");
        self.mk_ty(TypeExprKind::Error, span)
    }

    /// A `PrefixType`: one operand of `|`, with no `|` after it.
    pub(super) fn parse_type_operand(&mut self) -> TypeExpr {
        self.parse_prefix_type(false)
    }

    /// The type after `as`: a `PrefixType` whose `<` after a name starts arguments
    /// only with no space before it, and only if they parse.
    pub(super) fn parse_cast_type(&mut self) -> TypeExpr {
        self.parse_prefix_type(true)
    }

    /// `PrefixType = "&" PrefixType | "*" PrefixType | PostfixType`; `&&` and `**`
    /// split into two (SPEC 2).
    fn parse_prefix_type(&mut self, cast: bool) -> TypeExpr {
        if !self.enter() {
            return self.error_ty();
        }
        let lo = self.lo();
        if matches!(
            self.peek().kind,
            TokenKind::Punct(Punct::AmpAmp | Punct::StarStar)
        ) {
            self.split_current();
        }
        let ty = if self.at_kw(Keyword::Readonly) {
            // Only a field's type and a return type take `readonly`, and each
            // consumes it before it gets here.
            let keyword = self.bump().span;
            hints::readonly_misplaced(self, keyword);
            self.parse_prefix_type(cast)
        } else if self.eat(Punct::Amp) {
            if matches!(self.peek().kind, TokenKind::Lifetime(_)) {
                hints::lifetime(self);
            }
            let inner = self.parse_prefix_type(cast);
            let span = self.span_from(lo);
            self.mk_ty(TypeExprKind::Ref(Box::new(inner)), span)
        } else if self.eat(Punct::Star) {
            let inner = self.parse_prefix_type(cast);
            let span = self.span_from(lo);
            self.mk_ty(TypeExprKind::Raw(Box::new(inner)), span)
        } else {
            self.parse_postfix_type(cast)
        };
        self.leave();
        ty
    }

    /// `PostfixType = PrimaryType { "[" [ ConstExpr ] "]" }`, left to right:
    /// `T[3][4]` is `Fixed(Fixed(T, 3), 4)`.
    fn parse_postfix_type(&mut self, cast: bool) -> TypeExpr {
        let lo = self.lo();
        let primary = self.parse_primary_type(cast);
        self.parse_postfix_type_from(lo, primary)
    }

    fn parse_postfix_type_from(&mut self, lo: BytePos, mut ty: TypeExpr) -> TypeExpr {
        let mut links = 0;
        while self.at(Punct::LBracket) && self.enter() {
            links += 1;
            self.bump();
            let kind = if self.eat(Punct::RBracket) {
                TypeExprKind::Array(Box::new(ty))
            } else {
                let len = self.parse_expr();
                self.expect(Punct::RBracket);
                TypeExprKind::Fixed(Box::new(ty), Box::new(len))
            };
            let span = self.span_from(lo);
            ty = self.mk_ty(kind, span);
        }
        self.depth -= links;
        ty
    }

    /// `PrimaryType = NamedType | "(" Type ")" | FnPtrType | ClosureType | "void"
    /// | "never" | "null" | ObjectType | TupleType`.
    fn parse_primary_type(&mut self, cast: bool) -> TypeExpr {
        let lo = self.lo();
        let token = self.peek();
        match token.kind {
            TokenKind::Ident(_) => self.parse_named_type(cast),
            TokenKind::Punct(Punct::LParen) if self.closure_type_ahead() => {
                self.parse_closure_type()
            }
            TokenKind::Punct(Punct::LParen) => {
                self.bump();
                let inner = self.parse_type();
                self.expect(Punct::RParen);
                let span = self.span_from(lo);
                self.mk_ty(TypeExprKind::Paren(Box::new(inner)), span)
            }
            TokenKind::Punct(Punct::At) | TokenKind::Keyword(Keyword::Unsafe | Keyword::Fn) => {
                self.parse_fn_ptr_type()
            }
            TokenKind::Keyword(k @ (Keyword::Void | Keyword::Never | Keyword::Null)) => {
                self.bump();
                let kind = match k {
                    Keyword::Void => TypeExprKind::Void,
                    Keyword::Never => TypeExprKind::Never,
                    _ => TypeExprKind::NullLit,
                };
                self.mk_ty(kind, token.span)
            }
            // `{ [K in T]: X }`, a mapped type, and `{ [k: K]: V }`, an index
            // signature: type-level computation.
            TokenKind::Punct(Punct::LBrace) if self.nth_is(1, Punct::LBracket) => {
                recover::skip_group(self);
                let span = self.span_from(lo);
                hints::report_deferred(self, Code::EN1023, span, "computes a type");
                self.mk_ty(TypeExprKind::Error, span)
            }
            TokenKind::Punct(Punct::LBrace) => self.parse_object_type(),
            TokenKind::Punct(Punct::LBracket) => {
                self.bump();
                let elems = self.comma_list(Punct::RBracket, |p| Some(p.parse_type()));
                let span = self.span_from(lo);
                self.mk_ty(TypeExprKind::Tuple(elems), span)
            }
            _ => match hints::type_start(self) {
                Some(ty) => ty,
                None => {
                    self.expected("a type");
                    self.error_ty()
                }
            },
        }
    }

    /// `(` then `)`, `let`, or a name and `:`: the parameters of a closure type,
    /// which a parenthesised type can never start with.
    fn closure_type_ahead(&self) -> bool {
        let second = self.nth(1);
        second.is(Punct::RParen)
            || second.is_keyword(Keyword::Let)
            || (matches!(second.kind, TokenKind::Ident(_)) && self.nth_is(2, Punct::Colon))
    }

    /// `NamedType = Ident { "." Ident } [ "<" Type % "," ">" ]`.
    pub(super) fn parse_named_type(&mut self, cast: bool) -> TypeExpr {
        let lo = self.lo();
        let Some(first) = self.ident() else {
            return self.error_ty();
        };
        let mut path = vec![first];
        while self.at(Punct::Dot) && matches!(self.nth(1).kind, TokenKind::Ident(_)) {
            self.bump();
            path.push(self.ident_or_error());
        }
        if let [name] = path.as_slice() {
            let name = *name;
            hints::promise(self, &name);
        }
        let args = if !self.at(Punct::Lt) {
            Vec::new()
        } else if !cast {
            self.parse_type_args()
        } else if self.peek().space_before {
            Vec::new()
        } else {
            self.speculate_as(Guess::CastTypeArgs, |p| Some(p.parse_type_args()))
                .unwrap_or_default()
        };
        let span = self.span_from(lo);
        self.mk_ty(TypeExprKind::Named { path, args }, span)
    }

    /// `"<" Type % "," ">"`, from the `<`. The closing `>` may be the first half of
    /// `>>`, `>>>`, `>=` or `>>=`.
    pub(super) fn parse_type_args(&mut self) -> Vec<TypeExpr> {
        self.bump();
        let mut args = Vec::new();
        loop {
            if self.eat_closing_angle() {
                break;
            }
            if matches!(self.peek().kind, TokenKind::Lifetime(_)) {
                hints::lifetime(self);
                if self.eat(Punct::Comma) {
                    continue;
                }
                if !self.eat_closing_angle() {
                    self.expected("`,` or `>`");
                }
                break;
            }
            args.push(self.parse_type());
            if self.eat(Punct::Comma) {
                continue;
            }
            if !self.eat_closing_angle() {
                self.expected("`,` or `>`");
            }
            break;
        }
        args
    }

    /// `ClosureType = "(" TypedParam % "," ")" "=>" Type`, accepted in every type
    /// position: outside a parameter it is EN0705, in phase 2.
    fn parse_closure_type(&mut self) -> TypeExpr {
        let lo = self.lo();
        self.bump();
        let params = self.comma_list(Punct::RParen, |p| Some(p.parse_typed_param()));
        self.expect(Punct::FatArrow);
        let ret = self.parse_type();
        let span = self.span_from(lo);
        self.mk_ty(
            TypeExprKind::Closure(ClosureType {
                params,
                ret: Box::new(ret),
            }),
            span,
        )
    }

    /// `TypedParam = [ "let" ] Ident ":" Type`.
    fn parse_typed_param(&mut self) -> TypedParam {
        let is_let = self.eat_kw(Keyword::Let);
        let name = self.ident_or_error();
        let ty = if self.expect(Punct::Colon) {
            self.parse_type()
        } else {
            self.error_ty()
        };
        TypedParam { is_let, name, ty }
    }

    /// `FnPtrType = { Decorator } [ "unsafe" ] "fn" "(" TypedParam % "," ")" "=>"
    /// RetType`.
    fn parse_fn_ptr_type(&mut self) -> TypeExpr {
        let lo = self.lo();
        let decorators = self.parse_decorators();
        let is_unsafe = self.eat_kw(Keyword::Unsafe);
        if !self.expect_kw(Keyword::Fn) {
            return self.error_ty();
        }
        let params = if self.expect(Punct::LParen) {
            self.comma_list(Punct::RParen, |p| Some(p.parse_typed_param()))
        } else {
            Vec::new()
        };
        self.expect(Punct::FatArrow);
        let ret = self.parse_ret_type();
        let span = self.span_from(lo);
        self.mk_ty(
            TypeExprKind::FnPtr(FnPtrType {
                decorators,
                is_unsafe,
                params,
                ret: Box::new(ret),
            }),
            span,
        )
    }

    /// `ObjectType = "{" ( MemberName [ "?" ] ":" Type ) % "," "}"`. A `;` between
    /// fields, as an interface writes them, is EN0100 with a fix-it to `,`.
    fn parse_object_type(&mut self) -> TypeExpr {
        let lo = self.lo();
        self.bump();
        let fields = self.separated_list(Punct::RBrace, Some(Punct::Semi), |p| {
            let name = p.member_name()?;
            let optional = p.eat(Punct::Question);
            let ty = if p.expect(Punct::Colon) {
                p.parse_type()
            } else {
                p.error_ty()
            };
            Some((name, optional, ty))
        });
        let span = self.span_from(lo);
        self.mk_ty(TypeExprKind::Object(fields), span)
    }

    /// `RetType = [ "readonly" ] Type`.
    pub(super) fn parse_ret_type(&mut self) -> RetType {
        let keyword = self.peek().span;
        let readonly = self.eat_kw(Keyword::Readonly);
        let ty = self.parse_type();
        if readonly && !takes_readonly(&ty) {
            hints::readonly_return(self, keyword);
            return RetType {
                readonly: false,
                ty,
            };
        }
        RetType { readonly, ty }
    }

    /// `FieldType = [ "readonly" ] Type | "[" FieldType % "," "]" [ "|" "null" ]`.
    /// `readonly &T` is `ReadonlyRef(T)`, also under `| null` and as a tuple part.
    pub(super) fn parse_field_type(&mut self) -> TypeExpr {
        if !self.enter() {
            return self.error_ty();
        }
        let lo = self.lo();
        let keyword = self.peek().span;
        let ty = if self.eat_kw(Keyword::Readonly) {
            let ty = self.parse_type();
            self.readonly_ref(lo, keyword, ty)
        } else if self.at(Punct::LBracket) {
            self.bump();
            let elems = self.comma_list(Punct::RBracket, |p| Some(p.parse_field_type()));
            let span = self.span_from(lo);
            let tuple = self.mk_ty(TypeExprKind::Tuple(elems), span);
            let tuple = self.parse_postfix_type_from(lo, tuple);
            self.parse_type_from(lo, Some(tuple))
        } else {
            self.parse_type()
        };
        self.leave();
        ty
    }

    /// `readonly` and the type after it: `&T` becomes `ReadonlyRef(T)`, and `&T |
    /// null` becomes `Nullable(ReadonlyRef(T))`.
    fn readonly_ref(&mut self, lo: BytePos, keyword: Span, ty: TypeExpr) -> TypeExpr {
        let span = self.span_from(lo);
        let TypeExpr { id, kind, .. } = ty;
        match kind {
            TypeExprKind::Ref(referent) => TypeExpr {
                id,
                span,
                kind: TypeExprKind::ReadonlyRef(referent),
            },
            TypeExprKind::Nullable(inner) => {
                let TypeExpr {
                    id: inner_id,
                    span: inner_span,
                    kind: inner_kind,
                } = *inner;
                let inner = match inner_kind {
                    TypeExprKind::Ref(referent) => TypeExpr {
                        id: inner_id,
                        span: Span {
                            lo,
                            hi: inner_span.hi,
                        },
                        kind: TypeExprKind::ReadonlyRef(referent),
                    },
                    other => {
                        hints::readonly_field(self, keyword);
                        TypeExpr {
                            id: inner_id,
                            span: inner_span,
                            kind: other,
                        }
                    }
                };
                TypeExpr {
                    id,
                    span,
                    kind: TypeExprKind::Nullable(Box::new(inner)),
                }
            }
            TypeExprKind::Error => TypeExpr {
                id,
                span,
                kind: TypeExprKind::Error,
            },
            other => {
                hints::readonly_field(self, keyword);
                TypeExpr {
                    id,
                    span,
                    kind: other,
                }
            }
        }
    }

    /// A `StringLit`, or EN0100.
    pub(super) fn parse_str_lit(&mut self) -> Option<StrLit> {
        let token = self.peek();
        match token.kind {
            TokenKind::Str(value) => {
                self.bump();
                Some(StrLit {
                    value,
                    span: token.span,
                })
            }
            _ => {
                self.expected("a string");
                None
            }
        }
    }
}
