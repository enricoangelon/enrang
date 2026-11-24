//! `erase` and the walk under it: trees compare by structure once spans and ids are
//! blank, and the walk reaches every span and id however deep.

use enrang_base::{BytePos, Span, intern};
use enrang_syntax::ast::*;
use enrang_syntax::{MutVisitor, Walk, erase};
use enrang_testkit::Harness;

/// Builds nodes with fresh ids and spans that never repeat.
struct Build {
    ids: NodeIdGen,
    at: u32,
}

impl Build {
    fn new(start: u32) -> Build {
        Build {
            ids: NodeIdGen::new(),
            at: start,
        }
    }

    fn span(&mut self) -> Span {
        self.at += 2;
        Span {
            lo: BytePos(self.at),
            hi: BytePos(self.at + 1),
        }
    }

    fn ident(&mut self, name: &str) -> Ident {
        Ident {
            name: intern(name),
            span: self.span(),
        }
    }

    fn expr(&mut self, kind: ExprKind) -> Expr {
        Expr {
            id: self.ids.next_id(),
            span: self.span(),
            kind,
        }
    }

    fn ty(&mut self, kind: TypeExprKind) -> TypeExpr {
        TypeExpr {
            id: self.ids.next_id(),
            span: self.span(),
            kind,
        }
    }

    /// `f(x as i64[3])`.
    fn call(&mut self, op_name: &str) -> Expr {
        let callee = self.expr(ExprKind::Ident(intern(op_name)));
        let x = self.expr(ExprKind::Ident(intern("x")));
        let i64_name = self.ident("i64");
        let named = self.ty(TypeExprKind::Named {
            path: vec![i64_name],
            args: Vec::new(),
        });
        let three = self.expr(ExprKind::Int {
            value: 3,
            text: intern("3"),
        });
        let fixed = self.ty(TypeExprKind::Fixed(Box::new(named), Box::new(three)));
        let cast = self.expr(ExprKind::Cast(Box::new(x), fixed));
        self.expr(ExprKind::Call {
            callee: Box::new(callee),
            type_args: Vec::new(),
            args: vec![cast],
        })
    }

    /// A file holding one item `private function name(): void { return f(x as i64[3]); }`.
    fn file(&mut self, name: &str) -> File {
        let call = self.call("f");
        let ret = Stmt {
            id: self.ids.next_id(),
            kind: StmtKind::Return(Some(call)),
            span: self.span(),
        };
        let body = Block {
            stmts: vec![ret],
            span: self.span(),
        };
        let void = self.ty(TypeExprKind::Void);
        let decl = FunctionDecl {
            is_unsafe: false,
            name: self.ident(name),
            type_params: Vec::new(),
            params: Vec::new(),
            ret: Some(RetType {
                readonly: false,
                ty: void,
            }),
            body,
            span: self.span(),
        };
        let item = Item {
            id: self.ids.next_id(),
            decorators: Vec::new(),
            visibility: Some(Visibility::Private),
            kind: ItemKind::Function(decl),
            span: self.span(),
        };
        File {
            imports: Vec::new(),
            stmts: Vec::new(),
            items: vec![item],
            span: self.span(),
        }
    }
}

/// Counts what a walk visits, and how much of it is not blank.
#[derive(Default)]
struct Count {
    spans: usize,
    real_spans: usize,
    ids: usize,
    real_ids: usize,
}

impl MutVisitor for Count {
    fn visit_span(&mut self, span: &mut Span) {
        self.spans += 1;
        if !span.is_dummy() {
            self.real_spans += 1;
        }
    }

    fn visit_id(&mut self, id: &mut NodeId) {
        self.ids += 1;
        if *id != NodeId(0) {
            self.real_ids += 1;
        }
    }
}

fn count<T: Walk + Clone>(node: &T) -> Count {
    let mut count = Count::default();
    node.clone().walk(&mut count);
    count
}

pub fn register(h: &mut Harness) {
    h.case("trees/the walk reaches every span and id", || {
        let call = Build::new(100).call("f");
        let seen = count(&call);
        // The call, its callee, the cast, `x`, the fixed type, the named type and `3`.
        assert_eq!(seen.ids, 7);
        // Their spans and the span of the identifier `i64`.
        assert_eq!(seen.spans, 8);
        assert_eq!(seen.real_spans, 8);
    });
    h.case("trees/erase blanks every span and id", || {
        let file = Build::new(100).file("main");
        let before = count(&file);
        assert!(before.spans > 10, "{}", before.spans);
        let after = count(&erase(&file));
        assert_eq!((after.spans, after.ids), (before.spans, before.ids));
        assert_eq!((after.real_spans, after.real_ids), (0, 0));
    });
    h.case(
        "trees/trees that differ only in place are equal erased",
        || {
            let a = Build::new(100).file("main");
            let mut other = Build::new(5000);
            other.ids.next_id();
            let b = other.file("main");
            assert_ne!(a, b);
            assert_eq!(erase(&a), erase(&b));
        },
    );
    h.case("trees/trees that differ in structure stay apart", || {
        let a = Build::new(100).file("main");
        let b = Build::new(100).file("other");
        assert_ne!(erase(&a), erase(&b));
        let c = Build::new(100).call("f");
        let d = Build::new(100).call("g");
        assert_ne!(erase(&c), erase(&d));
    });
    h.case(
        "trees/for...in, asm options and keyword arm values have places",
        || {
            let mut b = Build::new(100);
            let source = ForOfSource::Expr(b.expr(ExprKind::Ident(intern("o"))));
            let span = b.span();
            let body = Block {
                stmts: Vec::new(),
                span,
            };
            let for_of = ForOfStmt {
                mutable: false,
                binding: Binding::Name(b.ident("k")),
                in_keyword: None,
                source,
                body,
                span: b.span(),
            };
            let for_in = ForOfStmt {
                in_keyword: Some(b.span()),
                ..for_of.clone()
            };
            assert_eq!(count(&for_in).spans, count(&for_of).spans + 1);
            assert_ne!(erase(&for_in), erase(&for_of), "`in` is not `of`");
            let empty_in = AsmOption {
                kind: AsmOptionKind::In(Vec::new()),
                span: b.span(),
            };
            assert_eq!(count(&empty_in).real_spans, 1);
            for value in [
                ArmValue::Null(b.span()),
                ArmValue::Ok(b.span()),
                ArmValue::Err(b.span()),
            ] {
                assert_eq!(count(&value).real_spans, 1, "{value:?}");
                assert_eq!(count(&erase(&value)).real_spans, 0, "{value:?}");
            }
        },
    );
    h.case("trees/node ids count up from zero", || {
        let mut ids = NodeIdGen::new();
        assert_eq!(ids.count(), 0);
        assert_eq!(ids.next_id(), NodeId(0));
        assert_eq!(ids.next_id(), NodeId(1));
        assert_eq!(ids.count(), 2);
        use enrang_base::Idx;
        assert_eq!(NodeId::new(5), NodeId(5));
        assert_eq!(NodeId(9).index(), 9);
    });
}
