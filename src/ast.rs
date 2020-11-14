use crate::parser::{Span, Spanned};

#[derive(Debug, Clone)]
pub enum Ty {
    Tuple(Vec<Box<Ty>>),
    Sum(Vec<(Spanned<String>, Box<Ty>)>),
    TypeVariable(String),
    Func(Box<Ty>, Box<Ty>),
    TypeRef(String),
    Unit,
    Int,
    Float,
}

#[derive(Debug, Clone)]
pub struct TypeDeclaration {
    pub ident: Spanned<String>,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    TypeDeclaration(TypeDeclaration),
}

#[derive(Debug, Clone)]
pub struct Ast {
    declarations: Vec<Declaration>,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }
}
