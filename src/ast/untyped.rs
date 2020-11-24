use crate::parser::{Span, Spanned};

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

#[derive(Debug, Clone)]
pub enum Operator {
    BinOpMul,
}

#[derive(Debug, Clone)]
pub enum Expr {
    FieldAccess(Box<Expr>, Spanned<String>),
    Symbol(Spanned<String>),
    Lambda(Spanned<String>, Box<Expr>),
    Record(Vec<(Spanned<String>, Expr)>),
    StringLiteral(Spanned<String>),
    Application(Box<Expr>, Box<Expr>),
    // TODO
    ListConstructor(),
    GroupedExpr(Box<Expr>),
    BinaryOp(Operator, Box<Expr>, Box<Expr>),
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
