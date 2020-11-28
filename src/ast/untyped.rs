use crate::parser::{Position, Span, Spanned};

pub type Attribute = Spanned<String>;

#[derive(Debug, Clone)]
pub enum Ty {
    Tuple(Vec<Ty>),
    TypeVariable(String),
    Func(Box<Ty>, Box<Ty>),
    TypeRef(Spanned<String>, Option<Spanned<String>>),
    List(Box<Ty>),
    Unit,
    Int,
    Float,
    String,
    Bool,
}

#[derive(Debug, Clone)]
pub struct RecordDeclaration {
    pub ident: Spanned<String>,
    pub fields: Vec<(Spanned<String>, Ty, Option<Attribute>)>,
}

#[derive(Debug, Clone)]
pub struct SumTypeDeclaration {
    pub ident: Spanned<String>,
    pub variants: Vec<(Spanned<String>, Ty)>,
}

#[derive(Debug, Clone)]
pub enum TypeDeclaration {
    TypeAlias(Spanned<String>, Ty),
    Record(RecordDeclaration),
    Sum(SumTypeDeclaration),
}

impl TypeDeclaration {
    pub fn ident(&self) -> Spanned<String> {
        match self {
            Self::TypeAlias(ident, _) => ident.clone(),
            Self::Record(r) => r.ident.clone(),
            Self::Sum(st) => st.ident.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct NamedFunctionTypeSignature {
    pub ident: Spanned<String>,
    pub from: Ty,
    pub to: Ty,
}

#[derive(Debug, Clone)]
pub enum TypeClassItem {
    Method(NamedFunctionTypeSignature),
}

#[derive(Debug, Clone)]
pub struct TypeClassImplItem {
    pub what: Spanned<String>,
    pub who: Spanned<String>,
    pub body: (Spanned<String>, Expr),
}

#[derive(Debug, Clone)]
pub struct ClosedTypeClass {
    pub ident: Spanned<String>,
    pub value_param: Option<(Spanned<String>, Vec<Spanned<String>>)>,
    pub typeclass_items: Vec<(TypeClassItem, Option<Attribute>)>,
    pub typeclass_members: Vec<TypeDeclaration>,
    pub typeclass_member_impls: Vec<TypeClassImplItem>,
}

#[derive(Debug, Clone, Copy)]
pub enum Operator {
    BinOpMul,
    BinOpDiv,
    BinOpAdd,
    BinOpSub,
    BinOpGreater,
    BinOpLess,
}

#[derive(Debug, Clone)]
pub enum Expr {
    FieldAccess(Box<Expr>, Spanned<String>),
    Symbol(Spanned<String>),
    Lambda(Spanned<String>, Box<Expr>),
    Record(Vec<(Spanned<String>, Expr)>),
    Tuple(Vec<Expr>),
    StringLiteral(Spanned<String>),
    BooleanLiteral(Spanned<bool>),
    IntegerLiteral(Spanned<i64>),
    Application(Box<Expr>, Box<Expr>),
    // TODO
    ListConstructor(),
    GroupedExpr(Box<Expr>),
    BinaryOp(Operator, Box<Expr>, Box<Expr>),
    LetBinding(Spanned<String>, Box<Expr>, Box<Expr>),
    Match(
        Box<Expr>,
        Vec<(Spanned<String>, Option<Spanned<String>>, Expr)>,
    ),
    Conditional(Box<Expr>, Box<Expr>, Box<Expr>),
    Unit(Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        use Expr::*;

        match self {
            FieldAccess(e, s) => e.span().encompass(s.1),
            IntegerLiteral(i) => i.1,
            Symbol(s) => s.1,
            Lambda(p, e) => p.1.encompass(e.span()),
            BooleanLiteral(b) => b.1,
            Record(_fields) => Span(Position(0, 0), Position(0, 0)),
            StringLiteral(s) => s.1,
            Application(l, r) => l.span().encompass(r.span()),
            ListConstructor() => Span(Position(0, 0), Position(0, 0)),
            GroupedExpr(e) => e.span(),
            LetBinding(p, r, b) => p.1.encompass(r.span().encompass(b.span())),
            BinaryOp(_o, e, r) => e.span().encompass(r.span()),
            Conditional(cond, cons, alt) => {
                cond.span().encompass(cons.span()).encompass(alt.span())
            }
            Tuple(fields) => fields
                .iter()
                .map(|e| e.span())
                .fold_first(|s1, s2| s1.encompass(s2))
                .unwrap(),
            Match(expr, arms) => arms
                .iter()
                .map(|(_, _, e)| e.span())
                .fold(expr.span(), |acc, s| acc.encompass(s)),
            Unit(s) => *s,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDecl {
    ident: Spanned<String>,
    params: Vec<Spanned<String>>,
    body: Expr,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Type(TypeDeclaration),
    TypeAnnotation(Spanned<String>, Ty),
    ClosedTypeClass(ClosedTypeClass),
    Binding(Spanned<String>, Expr),
}

#[derive(Debug, Clone)]
pub struct Untyped {
    pub declarations: Vec<Declaration>,
}

impl Untyped {
    pub fn new() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }
}
