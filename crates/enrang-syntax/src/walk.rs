//! A walk over every span and node id of a tree, and [`erase`], which blanks them so
//! that two trees compare by structure alone.
//!
//! The round trips of TESTING 11, 14 and 17 compare the tree of a file with the tree
//! of its reprint: equal apart from where things are and what ids they got. Each
//! struct's walk destructures it whole, so a field added to the tree and forgotten
//! here does not compile.

use enrang_base::{Span, Symbol};

use crate::ast::*;

/// What a walk does at each span and id. Both default to nothing.
pub trait MutVisitor {
    fn visit_span(&mut self, _span: &mut Span) {}
    fn visit_id(&mut self, _id: &mut NodeId) {}
}

/// A node whose spans and ids can be walked, children in field order.
pub trait Walk {
    fn walk(&mut self, vis: &mut dyn MutVisitor);
}

/// A copy of `node` with every span `Span::DUMMY` and every id `NodeId(0)`.
pub fn erase<T: Walk + Clone>(node: &T) -> T {
    struct Eraser;

    impl MutVisitor for Eraser {
        fn visit_span(&mut self, span: &mut Span) {
            *span = Span::DUMMY;
        }

        fn visit_id(&mut self, id: &mut NodeId) {
            *id = NodeId(0);
        }
    }

    let mut copy = node.clone();
    copy.walk(&mut Eraser);
    copy
}

impl Walk for Span {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        vis.visit_span(self);
    }
}

impl Walk for NodeId {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        vis.visit_id(self);
    }
}

impl<T: Walk> Walk for Vec<T> {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        for node in self {
            node.walk(vis);
        }
    }
}

impl<T: Walk> Walk for Option<T> {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        if let Some(node) = self {
            node.walk(vis);
        }
    }
}

impl<T: Walk> Walk for Box<T> {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        (**self).walk(vis);
    }
}

impl<A: Walk, B: Walk> Walk for (A, B) {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        self.0.walk(vis);
        self.1.walk(vis);
    }
}

impl<A: Walk, B: Walk, C: Walk> Walk for (A, B, C) {
    fn walk(&mut self, vis: &mut dyn MutVisitor) {
        self.0.walk(vis);
        self.1.walk(vis);
        self.2.walk(vis);
    }
}

/// Types with no span and no id inside.
macro_rules! walk_leaf {
    ($($ty:ty),+ $(,)?) => {
        $(impl Walk for $ty {
            fn walk(&mut self, _vis: &mut dyn MutVisitor) {}
        })+
    };
}

walk_leaf!(
    bool,
    u128,
    Symbol,
    Visibility,
    ParamMark,
    ClassModifier,
    Receiver,
    TestMode,
    CompileKind,
    UnOp,
    BinOp,
    LogOp,
    AssignOp,
);

/// Structs, walked field by field. The `let` names every field, so a missing one is
/// a compile error.
macro_rules! walk_struct {
    ($($ty:ident { $($field:ident),+ $(,)? })+) => {
        $(impl Walk for $ty {
            fn walk(&mut self, vis: &mut dyn MutVisitor) {
                let $ty { $($field),+ } = self;
                $($field.walk(vis);)+
            }
        })+
    };
}

walk_struct! {
    Ident { name, span }
    StrLit { value, span }
    File { imports, stmts, items, span }
    Import { public, kind, path, span }
    ImportName { name, alias }
    Decorator { name, args, span }
    Item { id, decorators, visibility, kind, span }
    FunctionDecl { is_unsafe, name, type_params, params, ret, body, span }
    RetType { readonly, ty }
    TypeParam { name, bounds }
    Param { mark, binding, optional, ty, default, span }
    TopConst { name, ty, value }
    UnsafeLet { name, ty, value }
    DeclareFn { name, type_params, params, ret, span }
    ClassDecl { modifier, name, type_params, extends, implements, members, span }
    ClassMember { decorators, kind, span }
    FieldDecl { visibility, is_override, is_readonly, name, optional, ty, default }
    Constructor { visibility, params, body }
    CtorParam { property, is_readonly, mark, name, optional, ty, default, span }
    Destructor { visibility, body }
    MethodDecl {
        visibility,
        is_abstract,
        is_override,
        receiver,
        is_unsafe,
        name,
        type_params,
        params,
        ret,
        where_clause,
        body,
        span,
    }
    WherePred { param, bounds }
    EnumDecl { name, type_params, variants, methods, span }
    Variant { decorators, name, payload, span }
    EnumField { name, ty }
    InterfaceDecl { name, type_params, members, span }
    IfaceField { name, optional, ty, span }
    TypeAlias { name, type_params, ty }
    ExtendDecl { type_params, ty, members }
    ExtendMember { decorators, method, span }
    DescribeItem { name, items }
    TestDecl { mode, name, extra, body, options }
    CompileCase { kind, name, source, options }
    ExpectStmt { actual, negated, matcher, args, span }
    TypeExpr { id, span, kind }
    FnPtrType { decorators, is_unsafe, params, ret }
    ClosureType { params, ret }
    TypedParam { is_let, name, ty }
    Block { stmts, span }
    Stmt { id, kind, span }
    VarDecl { mutable, binding, ty, init, span }
    IfStmt { cond, then_block, else_branch, span }
    WhileStmt { cond, body, span }
    ForStmt { init, cond, step, body, span }
    ForOfStmt { mutable, binding, in_keyword, source, body, span }
    Expr { id, span, kind }
    FieldInit { name, value, span }
    MatchArm { values, guard, body, span }
    AsmExpr { template, options }
    AsmOption { kind, span }
    RegBinding { reg, value }
    ArrowFn { params, ret, body, span }
    ArrowParam { is_let, name, ty }
}

/// Enums, walked variant by variant. A tuple variant lists a name per field and a
/// struct variant its fields; the match is exhaustive, so a missing variant is a
/// compile error.
macro_rules! walk_enum {
    ($($ty:ident {
        $($variant:ident $(($($bind:ident),+))? $({ $($field:ident),+ })?),+ $(,)?
    })+) => {
        $(impl Walk for $ty {
            fn walk(&mut self, vis: &mut dyn MutVisitor) {
                match self {
                    $($ty::$variant $(($($bind),+))? $({ $($field),+ })? => {
                        $($($bind.walk(vis);)+)?
                        $($($field.walk(vis);)+)?
                    })+
                }
            }
        })+
    };
}

walk_enum! {
    ImportKind { Named(a), Namespace(a) }
    ItemKind {
        Function(a),
        Class(a),
        Enum(a),
        Interface(a),
        TypeAlias(a),
        TopConst(a),
        UnsafeLet(a),
        DeclareFn(a),
        Extend(a),
        StaticAssert { cond, message },
        Describe(a),
        Test(a),
        CompileCase(a),
    }
    ClassMemberKind { Field(a), Constructor(a), Destructor(a), Method(a) }
    VariantPayload { Unit, Fields(a), Value(a) }
    IfaceMember { Method(a), Field(a) }
    TestExtra { Message(a), Cases(a) }
    MatcherArg { Expr(a), Arm(a) }
    TypeExprKind {
        Named { path, args },
        Nullable(a),
        Ref(a),
        Raw(a),
        ReadonlyRef(a),
        Array(a),
        Fixed(a, b),
        Tuple(a),
        FnPtr(a),
        Closure(a),
        Object(a),
        StrUnion(a),
        Union(a),
        Paren(a),
        Void,
        Never,
        NullLit,
        Error,
    }
    StmtKind {
        VarDecl(a),
        If(a),
        While(a),
        DoWhile(a),
        For(a),
        ForOf(a),
        Return(a),
        Break(a),
        Continue(a),
        Block(a),
        Unsafe(a),
        Labeled(a, b),
        Expr(a),
        LocalFn { decorators, decl },
        Expect(a),
        Assert { cond, message },
    }
    ElseBranch { If(a), Block(a) }
    ForInit { VarDecl(a), Expr(a) }
    ForOfSource { Range(a, b), Expr(a) }
    Binding { Name(a), Object { fields, span }, Tuple { elems, span } }
    ExprKind {
        Int { value, text },
        Float(a),
        Str(a),
        Template(a),
        RawTemplate(a),
        Bool(a),
        Null,
        Paren(a),
        Ident(a),
        This,
        Super,
        Array(a),
        Repeat(a, b),
        TypeMember { ty, name },
        New { ty, init },
        CaseLit { path, args, fields },
        ObjectLit(a),
        Match { subject, arms },
        SizeForm(a),
        Asm(a),
        Unary(a, b),
        Borrow(a),
        Deref(a),
        VoidOp(a),
        Binary(a, b, c),
        Logical(a, b, c),
        Coalesce(a, b),
        Ternary(a, b, c),
        Cast(a, b),
        Assign { op, target, value },
        IncDec { target, inc, prefix },
        Member { base, name, optional },
        Index(a, b),
        Call { callee, type_args, args },
        Try(a),
        NonNull(a),
        Arrow(a),
        Error,
    }
    NewInit { Args(a), Fields(a) }
    ArrayElem { Item(a), Spread { dots, expr } }
    TplPart { Str(a), Expr(a) }
    ArmValue { Value(a), Null(a), Case(a), Ok(a), Err(a), Range(a, b) }
    ArmBody { Expr(a), Block(a), Return(a), Break(a), Continue(a) }
    SizeForm { SizeOf(a), AlignOf(a), OffsetOf(a, b) }
    AsmOptionKind { In(a), Out(a), Clobbers(a) }
    ArrowBody { Expr(a), Block(a) }
}
