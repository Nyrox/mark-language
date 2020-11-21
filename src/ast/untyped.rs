use crate::parser::{Span, Spanned};

#[derive(Debug, Clone)]
pub struct Record {
    pub fields: Vec<(Spanned<String>, Ty, Option<Attribute>)>,
}

#[derive(Debug, Clone)]
pub enum Ty {
    Tuple(Vec<Ty>),
    Sum(Vec<(Spanned<String>, Ty)>),
    Record(Record),
    TypeVariable(String),
    Func(Box<Ty>, Box<Ty>),
    TypeRef(String, Option<Spanned<String>>),
    List(Box<Ty>),
    Unit,
    Int,
    Float,
    String,
}

impl Ty {
    pub fn visit<F, E>(&mut self, f: &mut F) -> Result<(), E>
    where
        F: FnMut(&mut Ty) -> Result<(), E>,
    {
        f(self)?;

        use Ty::*;
        match self {
            Tuple(tys) => tys.iter_mut().map(|t| t.visit(f)).collect(),
            Sum(tys) => tys.iter_mut().map(|(_, t)| t.visit(f)).collect(),
            Ty::Record(r) => r.fields.iter_mut().map(|(_, t, _)| t.visit(f)).collect(),
            Func(l, r) => {
                l.visit(f)?;
                r.visit(f)
            }
            List(t) => t.visit(f),
            TypeRef(_, _) | TypeVariable(_) | Unit | Int | Float | String => Ok(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeDeclaration {
    pub ident: Spanned<String>,
    pub ty: Ty,
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

pub type Attribute = Spanned<String>;

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
