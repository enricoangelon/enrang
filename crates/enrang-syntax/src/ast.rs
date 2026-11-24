//! The syntax tree (ARCHITECTURE 2.3), with every node SPEC 3 needs.
//!
//! The tree keeps what `enrang fmt` prints back (SPEC 12.5): each number literal's
//! spelling, each pair of parentheses around an expression or a type as a `Paren`
//! node, the `dots` of a spread, a field shorthand, `@d` against `@d()`. It records a
//! string literal's value, not its quotes or escapes, whose spelling the printer
//! reads from the source under the literal's span; it records neither the
//! parentheses around arrow parameters nor the optional `;` after a statement
//! `match`. Comments are not in the tree: the printer takes them from the source
//! between token spans, so every node a comment can sit beside has a span.
//!
//! Every type derives `Eq`. Spans and ids differ between a tree and its reprint, so
//! trees are compared after [`crate::erase`] has blanked both.

use enrang_base::{Idx, Span, Symbol};

use crate::token::Punct;

/// Identifies an item, statement, expression or type node of one session.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct NodeId(pub u32);

impl Idx for NodeId {
    fn new(i: usize) -> Self {
        NodeId(u32::try_from(i).expect("node index exceeds u32"))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// Hands out node ids in order, across every file of a session.
#[derive(Debug, Default)]
pub struct NodeIdGen {
    next: u32,
}

impl NodeIdGen {
    pub fn new() -> NodeIdGen {
        NodeIdGen::default()
    }

    /// A fresh id. Panics after `u32::MAX` ids.
    pub fn next_id(&mut self) -> NodeId {
        let id = NodeId(self.next);
        self.next = self.next.checked_add(1).expect("node ids exceed u32");
        id
    }

    /// How many ids have been handed out.
    pub fn count(&self) -> u32 {
        self.next
    }

    /// Takes back the ids handed out since `count` was read: the parser drops every
    /// node a failed speculation built, so ids stay dense and in source order.
    pub(crate) fn rewind(&mut self, count: u32) {
        self.next = count.min(self.next);
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

/// A string literal outside an expression: an import path, a test name, a message.
/// `value` has its escapes decoded; the spelling is the source under `span`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct StrLit {
    pub value: Symbol,
    pub span: Span,
}

// ---------------------------------------------------------------------------------
// SPEC 3.1: files and items.

/// `File = { Import } { TopStmt } { Item }`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct File {
    /// Named, `* as ns`, or `public import` (a re-export).
    pub imports: Vec<Import>,
    /// A program's top-level statements and the local functions and top-level
    /// `assert`s among them, in order.
    pub stmts: Vec<Stmt>,
    /// Declarations, `extend`, test items and the `assert`s among them, in order. A
    /// file with no statements is no program, so its unmarked functions (EN0226) and
    /// top-level `assert`s are items too, and its `stmts` stay empty.
    pub items: Vec<Item>,
    pub span: Span,
}

/// `Import = [ "public" ] "import" ( "{" ImportName % "," "}" | "*" "as" Ident )
/// "from" StringLit ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Import {
    pub public: bool,
    pub kind: ImportKind,
    pub path: StrLit,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ImportKind {
    Named(Vec<ImportName>),
    Namespace(Ident),
}

/// `ImportName = Ident [ "as" Ident ]`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct ImportName {
    pub name: Ident,
    pub alias: Option<Ident>,
}

/// `Decorator = "@" Ident [ "(" DecoratorArg % "," ")" ]`. `args` is `None` for
/// `@d` and `Some` for `@d(...)`, even empty. Each argument is a literal, an
/// identifier, or an object literal of literals and arrays of literals.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Decorator {
    pub name: Ident,
    pub args: Option<Vec<Expr>>,
    pub span: Span,
}

/// `Item = { Decorator } ItemVis ItemKind | { Decorator } ExtendDecl | TestItem
/// | TopAssert`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Item {
    pub id: NodeId,
    pub decorators: Vec<Decorator>,
    /// A declaration, `unsafe let` included, states `public` or `private` (missing:
    /// EN0226), while `extend`, test items and `assert` state none.
    pub visibility: Option<Visibility>,
    pub kind: ItemKind,
    pub span: Span,
}

/// Class members may also be `protected`; interface members state none.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Visibility {
    Public,
    Private,
    Protected,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ItemKind {
    Function(FunctionDecl),
    Class(ClassDecl),
    Enum(EnumDecl),
    Interface(InterfaceDecl),
    TypeAlias(TypeAlias),
    TopConst(TopConst),
    UnsafeLet(UnsafeLet),
    DeclareFn(DeclareFn),
    Extend(ExtendDecl),
    /// `TopAssert = "assert" "(" Expr [ "," StringLit ] [ "," ] ")" ";"`.
    StaticAssert {
        cond: Expr,
        message: Option<StrLit>,
    },
    /// Only in a `.test.en` part, else EN1112.
    Describe(DescribeItem),
    Test(TestDecl),
    CompileCase(CompileCase),
}

/// `FunctionDecl = [ "unsafe" ] "function" Ident [ TypeParams ] "(" Param % "," ")"
/// [ ":" RetType ] Block`. A library module may name it with any `MemberName`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FunctionDecl {
    pub is_unsafe: bool,
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret: Option<RetType>,
    pub body: Block,
    pub span: Span,
}

/// `RetType = [ "readonly" ] Type`. The `readonly` belongs to the function, not to
/// its type (ARCHITECTURE 2.3).
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct RetType {
    pub readonly: bool,
    pub ty: TypeExpr,
}

/// `TypeParam = Ident [ "extends" Bound { "&" Bound } ]`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypeParam {
    pub name: Ident,
    pub bounds: Vec<TypeExpr>,
}

/// `Param = [ "let" | "const" ] Binding [ "?" ] ":" ParamType [ "=" Expr ]`.
/// `ParamType` is a `TypeExpr`: a closure type, and a parenthesised closure type
/// with `| null`, are `Closure` and `Nullable(Closure)`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Param {
    pub mark: ParamMark,
    pub binding: Binding,
    /// `x?: T`.
    pub optional: bool,
    pub ty: TypeExpr,
    pub default: Option<Expr>,
    pub span: Span,
}

/// `x`, `let x`, `const x`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ParamMark {
    Plain,
    Let,
    Const,
}

/// `TopConst = "const" Ident [ ":" Type ] "=" ConstExpr ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TopConst {
    pub name: Ident,
    pub ty: Option<TypeExpr>,
    pub value: Expr,
}

/// `UnsafeLet = "unsafe" "let" Ident ":" Type [ "=" ConstExpr ] ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct UnsafeLet {
    pub name: Ident,
    pub ty: TypeExpr,
    pub value: Option<Expr>,
}

/// `DeclareFn = "declare" "function" Ident [ TypeParams ] "(" Param % "," ")"
/// [ ":" Type ] ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct DeclareFn {
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret: Option<TypeExpr>,
    pub span: Span,
}

/// `ClassDecl = [ "abstract" | "final" ] "class" Ident [ TypeParams ]
/// [ "extends" NamedType ] [ "implements" NamedType { "," NamedType } ]
/// "{" { ClassMember } "}"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ClassDecl {
    pub modifier: ClassModifier,
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub extends: Option<TypeExpr>,
    pub implements: Vec<TypeExpr>,
    pub members: Vec<ClassMember>,
    pub span: Span,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ClassModifier {
    Plain,
    Abstract,
    Final,
}

/// `ClassMember = { Decorator } ( FieldDecl | Constructor | Destructor | MethodDecl )`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ClassMember {
    pub decorators: Vec<Decorator>,
    pub kind: ClassMemberKind,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ClassMemberKind {
    Field(FieldDecl),
    Constructor(Constructor),
    Destructor(Destructor),
    Method(MethodDecl),
}

/// `FieldDecl = Visibility [ "override" ] [ "readonly" ] MemberName [ "?" ] ":"
/// FieldType [ "=" Expr ] ";"`. `FieldType`'s `readonly &T` is `ReadonlyRef`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FieldDecl {
    /// `None` when missing, which is EN0226.
    pub visibility: Option<Visibility>,
    pub is_override: bool,
    /// The modifier before the name: no assignment after construction.
    pub is_readonly: bool,
    pub name: Ident,
    pub optional: bool,
    pub ty: TypeExpr,
    pub default: Option<Expr>,
}

/// `Constructor = Visibility "constructor" "(" CtorParam % "," ")" Block`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Constructor {
    pub visibility: Option<Visibility>,
    pub params: Vec<CtorParam>,
    pub body: Block,
}

/// `CtorParam = [ Visibility [ "readonly" ] ] [ "let" | "const" ] Ident [ "?" ] ":"
/// FieldType [ "=" Expr ]`. A visibility makes the parameter a field.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CtorParam {
    pub property: Option<Visibility>,
    pub is_readonly: bool,
    pub mark: ParamMark,
    pub name: Ident,
    pub optional: bool,
    pub ty: TypeExpr,
    pub default: Option<Expr>,
    pub span: Span,
}

/// `Destructor = "public" "destructor" "(" ")" Block`. The visibility is kept as
/// written, so that a wrong or missing one can be reported and printed back.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Destructor {
    pub visibility: Option<Visibility>,
    pub body: Block,
}

/// `MethodDecl = Visibility [ "static" | "abstract" ] [ "override" ]
/// [ "let" | "const" | "move" ] [ "unsafe" ] MemberName [ TypeParams ]
/// "(" Param % "," ")" [ ":" RetType ] [ WhereClause ] ( Block | ";" )`.
///
/// Interface members (`IfaceMember`'s method form) use it too, with no visibility,
/// no body and `is_abstract` false.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct MethodDecl {
    pub visibility: Option<Visibility>,
    pub is_abstract: bool,
    pub is_override: bool,
    /// `static` is a receiver kind: a static method has no `this` to mark.
    pub receiver: Receiver,
    pub is_unsafe: bool,
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret: Option<RetType>,
    pub where_clause: Vec<WherePred>,
    /// `None` for `;` in place of the body.
    pub body: Option<Block>,
    pub span: Span,
}

/// `m()`, `let m()`, `const m()`, `move m()`, `static m()`.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Receiver {
    Plain,
    Let,
    Const,
    Move,
    Static,
}

/// `WherePred = Ident "extends" Bound { "&" Bound }`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct WherePred {
    pub param: Ident,
    pub bounds: Vec<TypeExpr>,
}

/// `EnumDecl = "enum" Ident [ TypeParams ] "{" Variant % "," [ ";" { MethodDecl } ]
/// "}"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct EnumDecl {
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub variants: Vec<Variant>,
    pub methods: Vec<MethodDecl>,
    pub span: Span,
}

/// `Variant = { Decorator } Ident [ "{" EnumField % "," "}" | "=" ( ConstExpr |
/// StringLit ) ]`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Variant {
    pub decorators: Vec<Decorator>,
    pub name: Ident,
    pub payload: VariantPayload,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum VariantPayload {
    Unit,
    Fields(Vec<EnumField>),
    /// `= 3` or `= "text"`.
    Value(Expr),
}

/// `EnumField = MemberName ":" Type`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct EnumField {
    pub name: Ident,
    pub ty: TypeExpr,
}

/// `InterfaceDecl = "interface" Ident [ TypeParams ] "{" { IfaceMember } "}"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct InterfaceDecl {
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub members: Vec<IfaceMember>,
    pub span: Span,
}

/// `IfaceMember = [ "static" ] [ "let" | "move" ] [ "unsafe" ] MemberName
/// [ TypeParams ] "(" Param % "," ")" [ ":" RetType ] [ WhereClause ] ";"
/// | MemberName [ "?" ] ":" Type ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum IfaceMember {
    Method(MethodDecl),
    Field(IfaceField),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct IfaceField {
    pub name: Ident,
    pub optional: bool,
    pub ty: TypeExpr,
    pub span: Span,
}

/// `TypeAlias = "type" Ident [ TypeParams ] "=" ( Type | StringLit { "|" StringLit } )
/// ";"`. The string-literal form is `TypeExprKind::StrUnion`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypeAlias {
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub ty: TypeExpr,
}

/// `ExtendDecl = "extend" [ TypeParams ] Type "{" { { Decorator } MethodDecl } "}"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExtendDecl {
    pub type_params: Vec<TypeParam>,
    pub ty: TypeExpr,
    pub members: Vec<ExtendMember>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExtendMember {
    pub decorators: Vec<Decorator>,
    pub method: MethodDecl,
    pub span: Span,
}

// ---------------------------------------------------------------------------------
// SPEC 3.6: test declarations.

/// `DescribeItem = "describe" "(" StringLit "," "(" ")" "=>" "{" { DescribeItem |
/// TestDecl | CompileCase } "}" [ "," ] ")" ";"`. Each entry of `items` is an
/// `Item` of kind `Describe`, `Test` or `CompileCase`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct DescribeItem {
    pub name: StrLit,
    pub items: Vec<Item>,
}

/// `TestDecl = "test" [ "." TestMode ] "(" StringLit [ "," TestExtra ]
/// [ "," TestBody ] [ "," ObjectLit ] [ "," ] ")" ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TestDecl {
    pub mode: Option<TestMode>,
    pub name: StrLit,
    pub extra: Option<TestExtra>,
    /// `TestBody = ( Ident | "(" [ ArrowParam ] ")" [ ":" Type ] ) "=>" Block`: an
    /// arrow with at most one parameter and a block body.
    pub body: Option<ArrowFn>,
    /// The options literal, an `ExprKind::ObjectLit`.
    pub options: Option<Expr>,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum TestMode {
    Only,
    Skip,
    Todo,
    Panics,
    Each,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TestExtra {
    /// `test.panics`: the expected message substring.
    Message(StrLit),
    /// `test.each`: `() => Expr`, the case generator.
    Cases(ArrowFn),
}

/// `CompileCase = ("compileFails" | "compileOk") "(" StringLit "," RawTemplate
/// [ "," ObjectLit ] [ "," ] ")" ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CompileCase {
    pub kind: CompileKind,
    pub name: StrLit,
    /// The snippet as written, and the span of the whole `raw` literal, which a
    /// `FileOrigin::Snippet` maps back to.
    pub source: StrLit,
    pub options: Option<Expr>,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum CompileKind {
    Fails,
    Ok,
}

/// `ExpectStmt = "expect" "(" Expr [ "," ] ")" [ "." "not" ] "." Ident
/// "(" MatcherArg % "," ")" ";"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ExpectStmt {
    pub actual: Expr,
    pub negated: bool,
    pub matcher: Ident,
    pub args: Vec<MatcherArg>,
    pub span: Span,
}

/// `MatcherArg = Expr | ArmValue`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum MatcherArg {
    Expr(Expr),
    /// Only for `toMatchPattern`, as an enum case.
    Arm(ArmValue),
}

// ---------------------------------------------------------------------------------
// SPEC 3.2: types.

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypeExpr {
    pub id: NodeId,
    pub span: Span,
    pub kind: TypeExprKind,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TypeExprKind {
    /// `NamedType = Ident { "." Ident } [ "<" Type % "," ">" ]`.
    Named {
        path: Vec<Ident>,
        args: Vec<TypeExpr>,
    },
    /// `T | null`.
    Nullable(Box<TypeExpr>),
    /// `&T`.
    Ref(Box<TypeExpr>),
    /// `*T`.
    Raw(Box<TypeExpr>),
    /// `readonly &T`, holding `T`, only in a field's type, as the field or a reference
    /// part of its tuple (SPEC 3.1); `readonly` before a return type belongs to the
    /// function, not to its type.
    ReadonlyRef(Box<TypeExpr>),
    /// `T[]`.
    Array(Box<TypeExpr>),
    /// `T[N]`.
    Fixed(Box<TypeExpr>, Box<Expr>),
    /// `TupleType = "[" Type % "," "]"`.
    Tuple(Vec<TypeExpr>),
    FnPtr(FnPtrType),
    /// Parameter position only, else EN0705 in phase 2, so the parser accepts it in
    /// any type position.
    Closure(ClosureType),
    /// `ObjectType = "{" ( MemberName [ "?" ] ":" Type ) % "," "}"`: each field's
    /// name, whether it has `?`, and its type.
    Object(Vec<(Ident, bool, TypeExpr)>),
    /// String literals joined by `|`: a whole `TypeAlias`, anywhere else EN0216.
    StrUnion(Vec<StrLit>),
    /// Any other `|` than `| null`, which is EN0406 in phase 2, so phase 1 keeps it.
    /// Object types joined by `|` are EN0215 in phase 1 instead.
    Union(Vec<TypeExpr>),
    /// `"(" Type ")"`, kept so that `enrang fmt` prints the parentheses written.
    Paren(Box<TypeExpr>),
    Void,
    Never,
    /// The type `null`.
    NullLit,
    /// What the parser left after a reported error.
    Error,
}

/// `FnPtrType = { Decorator } [ "unsafe" ] "fn" "(" TypedParam % "," ")" "=>"
/// RetType`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FnPtrType {
    pub decorators: Vec<Decorator>,
    pub is_unsafe: bool,
    pub params: Vec<TypedParam>,
    pub ret: Box<RetType>,
}

/// `ClosureType = "(" TypedParam % "," ")" "=>" Type`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ClosureType {
    pub params: Vec<TypedParam>,
    pub ret: Box<TypeExpr>,
}

/// `TypedParam = [ "let" ] Ident ":" Type`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TypedParam {
    pub is_let: bool,
    pub name: Ident,
    pub ty: TypeExpr,
}

// ---------------------------------------------------------------------------------
// SPEC 3.3: statements.

/// `Block = "{" { Stmt } "}"`; the span covers both braces.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Stmt {
    pub id: NodeId,
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum StmtKind {
    VarDecl(VarDecl),
    If(IfStmt),
    While(WhileStmt),
    /// `DoStmt = "do" Block "while" "(" Expr ")" ";"`.
    DoWhile(WhileStmt),
    For(ForStmt),
    ForOf(ForOfStmt),
    Return(Option<Expr>),
    Break(Option<Ident>),
    Continue(Option<Ident>),
    Block(Block),
    Unsafe(Block),
    /// `LabeledStmt = Ident ":" ( WhileStmt | DoStmt | ForStmt | ForOfStmt )`.
    Labeled(Ident, Box<Stmt>),
    /// `ExprStmt`, and `MatchStmt`, whose optional `;` the tree drops and `fmt` never
    /// prints (SPEC 3.3, 12.5).
    Expr(Expr),
    /// Only among a program's top-level statements.
    LocalFn {
        decorators: Vec<Decorator>,
        decl: FunctionDecl,
    },
    Expect(ExpectStmt),
    /// A `TopAssert` among a program's top-level statements (`TopStmt`).
    Assert {
        cond: Expr,
        message: Option<StrLit>,
    },
}

/// `VarDecl = "const" Binding [ ":" Type ] "=" Expr ";" | "let" Binding [ ":" Type ]
/// [ "=" Expr ] ";"`. A `const` without a value is EN0116 and keeps `init: None`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct VarDecl {
    /// `let`, against `const`.
    pub mutable: bool,
    pub binding: Binding,
    pub ty: Option<TypeExpr>,
    pub init: Option<Expr>,
    pub span: Span,
}

/// `IfStmt = "if" "(" Expr ")" Block [ "else" ( IfStmt | Block ) ]`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct IfStmt {
    pub cond: Expr,
    pub then_block: Block,
    pub else_branch: Option<ElseBranch>,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ElseBranch {
    If(Box<IfStmt>),
    Block(Block),
}

/// `WhileStmt = "while" "(" Expr ")" Block`, and the parts of a `DoStmt`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct WhileStmt {
    pub cond: Expr,
    pub body: Block,
    pub span: Span,
}

/// `ForStmt = "for" "(" ( VarDecl | ExprStmt | ";" ) [ Expr ] ";" [ Expr ] ")" Block`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ForStmt {
    /// `None` for a bare `;`.
    pub init: Option<ForInit>,
    pub cond: Option<Expr>,
    pub step: Option<Expr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ForInit {
    VarDecl(VarDecl),
    Expr(Expr),
}

/// `ForOfStmt = "for" "(" ( "const" | "let" ) Binding "of" ForSource ")" Block`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ForOfStmt {
    pub mutable: bool,
    pub binding: Binding,
    /// The `in` of TypeScript's `for (const k in o)`, written where `of` goes. SPEC 16
    /// makes `for...in` EN1015, a phase 2 code of sema, so the tree keeps the loop
    /// and the place for it; `None` for `of`.
    pub in_keyword: Option<Span>,
    pub source: ForOfSource,
    pub body: Block,
    pub span: Span,
}

/// `ForSource = Expr ".." Expr | Expr`. No range expression exists, so a range lives
/// here and in `ArmValue`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ForOfSource {
    Range(Expr, Expr),
    Expr(Expr),
}

/// `Binding = Ident | ObjPattern | TuplePattern` (SPEC 3.3): destructuring binds,
/// never tests, and nests. A `= default` is EN1010 and `...` EN1013, both dropped.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Binding {
    Name(Ident),
    /// `ObjPattern = "{" ( MemberName [ ":" Binding ] ) % "," "}"`:
    /// `{ a, b: c, d: { e } }`.
    Object {
        fields: Vec<(Ident, Option<Binding>)>,
        span: Span,
    },
    /// `TuplePattern = "[" Binding % "," "]"`: `[a, [b, c]]`.
    Tuple {
        elems: Vec<Binding>,
        span: Span,
    },
}

// ---------------------------------------------------------------------------------
// SPEC 3.4: expressions.

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Expr {
    pub id: NodeId,
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ExprKind {
    /// The value, and the spelling `fmt` prints back.
    Int {
        value: u128,
        text: Symbol,
    },
    /// The literal's text, parsed once at its final width.
    Float(Symbol),
    /// The value; the spelling is the source under the span.
    Str(Symbol),
    /// The span covers the backticks; the text as written is the source under it.
    Template(Vec<TplPart>),
    /// The text between the backticks, exactly.
    RawTemplate(Symbol),
    Bool(bool),
    Null,
    Paren(Box<Expr>),
    Ident(Symbol),
    This,
    /// `super`, only as `super(...)` or `super.name` (SPEC 3.4 `Primary`).
    Super,
    /// `ArrayLit = "[" ArrayElem % "," "]"`, a tuple value where one is expected.
    Array(Vec<ArrayElem>),
    /// `RepeatLit = "[" Expr ";" ConstExpr "]"`.
    Repeat(Box<Expr>, Box<Expr>),
    /// `TypeMember = NamedType [ "[" "]" ] "." MemberName`: `Stack<i64>.empty`,
    /// `i64[].withCapacity`, `E<i64>.V`.
    TypeMember {
        ty: TypeExpr,
        name: Ident,
    },
    /// `new C(args)` or `new C { f: v }`.
    New {
        ty: TypeExpr,
        init: NewInit,
    },
    /// `Shape.Circle { radius: 2.5 }`, with no `new`; `args` are those of a
    /// `TypeMember` path, as in `E<i64>.V { x: 1 }`.
    CaseLit {
        path: Vec<Ident>,
        args: Vec<TypeExpr>,
        fields: Vec<FieldInit>,
    },
    /// `{ f: v }`: the expected class's named form, or an anonymous object.
    ObjectLit(Vec<FieldInit>),
    Match {
        subject: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    SizeForm(SizeForm),
    Asm(AsmExpr),
    /// Prefix `!`, `-`, `~`.
    Unary(UnOp, Box<Expr>),
    /// Prefix `&`.
    Borrow(Box<Expr>),
    /// Prefix `*`.
    Deref(Box<Expr>),
    /// `void e`.
    VoidOp(Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Logical(LogOp, Box<Expr>, Box<Expr>),
    Coalesce(Box<Expr>, Box<Expr>),
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `e as T`.
    Cast(Box<Expr>, TypeExpr),
    /// A value: the assigned value.
    Assign {
        op: AssignOp,
        target: Box<Expr>,
        value: Box<Expr>,
    },
    /// A value: new if prefix, else old.
    IncDec {
        target: Box<Expr>,
        inc: bool,
        prefix: bool,
    },
    /// `.name` or `?.name`. Type arguments live only on `Call` and `TypeMember`.
    Member {
        base: Box<Expr>,
        name: Ident,
        optional: bool,
    },
    Index(Box<Expr>, Box<Expr>),
    Call {
        callee: Box<Expr>,
        type_args: Vec<TypeExpr>,
        args: Vec<Expr>,
    },
    /// Postfix `?`.
    Try(Box<Expr>),
    /// Postfix `!`.
    NonNull(Box<Expr>),
    Arrow(ArrowFn),
    /// What the parser left after a reported error.
    Error,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum NewInit {
    Args(Vec<Expr>),
    Fields(Vec<FieldInit>),
}

/// `ArrayElem = Expr | "..." Expr`. `...` appears nowhere else.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArrayElem {
    Item(Expr),
    Spread { dots: Span, expr: Expr },
}

/// `FieldInit = MemberName [ ":" Expr ]`. `value` is `None` for the shorthand
/// `{ name }`, which `fmt` prints back as written.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct FieldInit {
    pub name: Ident,
    pub value: Option<Expr>,
    pub span: Span,
}

/// One part of a template literal.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum TplPart {
    /// Text, escapes decoded.
    Str(Symbol),
    /// A `${ }` hole.
    Expr(Expr),
}

/// `MatchArm = ( "default" | ArmValue { "," ArmValue } ) [ "if" Expr ] "=>"
/// ( Expr | Block | "return" [ Expr ] | "break" [ Ident ] | "continue" [ Ident ] )`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct MatchArm {
    /// Empty for `default`.
    pub values: Vec<ArmValue>,
    pub guard: Option<Expr>,
    pub body: ArmBody,
    pub span: Span,
}

/// `ArmValue = Literal | "-" IntLit | "null" | NamedPath | "Ok" | "Err" | Expr ".."
/// Expr | Expr`. A path of identifiers is always `Case`, since only names tell a
/// case from a constant; sema decides. `null`, `Ok` and `Err` keep the span of
/// their word, which comments between arm values are placed by.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArmValue {
    /// A literal, a negative integer, or a condition under `match (true)`.
    Value(Expr),
    Null(Span),
    Case(Vec<Ident>),
    Ok(Span),
    Err(Span),
    Range(Expr, Expr),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArmBody {
    Expr(Expr),
    Block(Block),
    Return(Option<Expr>),
    Break(Option<Ident>),
    Continue(Option<Ident>),
}

/// `SizeForm = ("sizeOf" | "alignOf") "<" Type ">" "(" ")" | "offsetOf" "<" Type ">"
/// "(" StringLit [ "," ] ")"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum SizeForm {
    SizeOf(TypeExpr),
    AlignOf(TypeExpr),
    OffsetOf(TypeExpr, StrLit),
}

/// `AsmExpr = "asm" "(" ( TemplateLit | StringLit ) [ "," AsmOptions ] [ "," ] ")"`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AsmExpr {
    /// A `Template` or `Str` expression. A hole is EN0915 in phase 4, so it is kept.
    pub template: Box<Expr>,
    /// `AsmOptions = "{" AsmOption % "," "}"`, in the order written; `None` when
    /// there is no options literal at all.
    pub options: Option<Vec<AsmOption>>,
}

/// `AsmOption = "in" ":" RegMap | "out" ":" RegMap | "clobbers" ":" "[" StringLit %
/// "," "]"`. The span runs from the key to the closing brace or bracket, so a
/// comment beside an option, even an empty `in: {}`, has a place.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AsmOption {
    pub kind: AsmOptionKind,
    pub span: Span,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum AsmOptionKind {
    In(Vec<RegBinding>),
    Out(Vec<RegBinding>),
    Clobbers(Vec<StrLit>),
}

/// One entry of `RegMap = "{" ( RegName [ ":" Expr ] ) % "," "}"`: `{ edx }` is
/// `{ edx: edx }`, kept as the shorthand.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct RegBinding {
    pub reg: Ident,
    pub value: Option<Expr>,
}

/// `ArrowFn = ( Ident | "(" ArrowParam % "," ")" [ ":" RetType ] ) "=>"
/// ( Expr | Block )`. The tree records no parentheses around the parameters.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ArrowFn {
    pub params: Vec<ArrowParam>,
    pub ret: Option<RetType>,
    pub body: ArrowBody,
    pub span: Span,
}

/// `ArrowParam = [ "let" ] Ident [ ":" Type ]`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ArrowParam {
    pub is_let: bool,
    pub name: Ident,
    pub ty: Option<TypeExpr>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArrowBody {
    Expr(Box<Expr>),
    Block(Block),
}

/// Prefix operators that stay `Unary`; `&`, `*`, `void`, `++` and `--` have nodes of
/// their own.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum UnOp {
    Not,
    Neg,
    BitNot,
}

impl UnOp {
    pub fn as_str(self) -> &'static str {
        match self {
            UnOp::Not => "!",
            UnOp::Neg => "-",
            UnOp::BitNot => "~",
        }
    }
}

/// The binary operators of SPEC 3.5 levels 4 to 11.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum BinOp {
    Mul,
    Div,
    Rem,
    Add,
    Sub,
    Shl,
    Shr,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    BitAnd,
    BitXor,
    BitOr,
}

impl BinOp {
    pub const ALL: &'static [BinOp] = &[
        BinOp::Mul,
        BinOp::Div,
        BinOp::Rem,
        BinOp::Add,
        BinOp::Sub,
        BinOp::Shl,
        BinOp::Shr,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::Eq,
        BinOp::Ne,
        BinOp::BitAnd,
        BinOp::BitXor,
        BinOp::BitOr,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::BitAnd => "&",
            BinOp::BitXor => "^",
            BinOp::BitOr => "|",
        }
    }

    /// The level in SPEC 3.5's table: lower binds tighter.
    pub fn precedence(self) -> u8 {
        match self {
            BinOp::Mul | BinOp::Div | BinOp::Rem => 4,
            BinOp::Add | BinOp::Sub => 5,
            BinOp::Shl | BinOp::Shr => 6,
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 7,
            BinOp::Eq | BinOp::Ne => 8,
            BinOp::BitAnd => 9,
            BinOp::BitXor => 10,
            BinOp::BitOr => 11,
        }
    }

    /// Levels 7 and 8 do not associate: a chain is EN0107.
    pub fn is_comparison(self) -> bool {
        matches!(self.precedence(), 7 | 8)
    }

    /// The operator a punctuator spells in binary position.
    pub fn from_punct(punct: Punct) -> Option<BinOp> {
        BinOp::ALL
            .iter()
            .copied()
            .find(|op| op.as_str() == punct.as_str())
    }
}

/// `&&` and `||`, SPEC 3.5 levels 12 and 13.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum LogOp {
    And,
    Or,
}

impl LogOp {
    pub fn as_str(self) -> &'static str {
        match self {
            LogOp::And => "&&",
            LogOp::Or => "||",
        }
    }

    pub fn precedence(self) -> u8 {
        match self {
            LogOp::And => 12,
            LogOp::Or => 13,
        }
    }

    pub fn from_punct(punct: Punct) -> Option<LogOp> {
        match punct {
            Punct::AmpAmp => Some(LogOp::And),
            Punct::PipePipe => Some(LogOp::Or),
            _ => None,
        }
    }
}

/// SPEC 3.5 level 14, `??`, is right-associative.
pub const COALESCE_PRECEDENCE: u8 = 14;
/// SPEC 3.5 level 15, `? :`.
pub const TERNARY_PRECEDENCE: u8 = 15;
/// SPEC 3.5 level 3, `as`, tighter than `*`, unlike TypeScript.
pub const CAST_PRECEDENCE: u8 = 3;

/// `AssignOp`, SPEC 3.5 level 16, right-associative.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum AssignOp {
    Assign,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

impl AssignOp {
    pub const ALL: &'static [AssignOp] = &[
        AssignOp::Assign,
        AssignOp::Add,
        AssignOp::Sub,
        AssignOp::Mul,
        AssignOp::Div,
        AssignOp::Rem,
        AssignOp::BitAnd,
        AssignOp::BitOr,
        AssignOp::BitXor,
        AssignOp::Shl,
        AssignOp::Shr,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            AssignOp::Assign => "=",
            AssignOp::Add => "+=",
            AssignOp::Sub => "-=",
            AssignOp::Mul => "*=",
            AssignOp::Div => "/=",
            AssignOp::Rem => "%=",
            AssignOp::BitAnd => "&=",
            AssignOp::BitOr => "|=",
            AssignOp::BitXor => "^=",
            AssignOp::Shl => "<<=",
            AssignOp::Shr => ">>=",
        }
    }

    pub fn from_punct(punct: Punct) -> Option<AssignOp> {
        AssignOp::ALL
            .iter()
            .copied()
            .find(|op| op.as_str() == punct.as_str())
    }
}

/// SPEC 3.5 level 16.
pub const ASSIGN_PRECEDENCE: u8 = 16;
