use crate::parser::{Span, Spanned};


#[derive(Debug, Clone)]
pub struct Record {
	pub fields: Vec<(Spanned<String>, Ty, Option<Attribute>)>,
}

#[derive(Debug, Clone)]
pub enum Ty {
    Tuple(Vec<Box<Ty>>),
	Sum(Vec<(Spanned<String>, Box<Ty>)>),
	Record(Box<Record>),
	Annotated(Box<Ty>, Spanned<String>),
    TypeVariable(String),
    Func(Box<Ty>, Box<Ty>),
	TypeRef(String, Option<Spanned<String>>),
	List(Box<Ty>),
    Unit,
    Int,
	Float,
	String,
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
pub enum Declaration {
	Type(TypeDeclaration),
	TypeAnnotation(Spanned<String>, Ty),
	ClosedTypeClass(ClosedTypeClass),
	Binding(Spanned<String>, Expr),
}


#[derive(Debug, Clone)]
pub enum Expr {
	FieldAccess(Box<Expr>, Spanned<String>),
	Symbol(Spanned<String>),
	Lambda(Spanned<String>, Box<Expr>),
}

#[derive(Debug, Clone)]
pub struct FunctionDecl {
	ident: Spanned<String>,
	params: Vec<Spanned<String>>,
	body: Expr,
}


#[derive(Debug, Clone)]
pub struct Ast {
    pub declarations: Vec<Declaration>,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }
}
