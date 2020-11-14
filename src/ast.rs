use crate::parser::Span;


pub struct TypeDeclaration {
	pub source_span: Span,
}


pub enum Declaration {
	TypeDeclaration(TypeDeclaration),
}

pub struct Ast {
	declarations: Vec<Declaration>,
}
