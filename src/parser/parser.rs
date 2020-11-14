
use super::{Spanned, scanner::{Token}};

#[derive(Debug, Clone)]
pub enum ParsingError {

}

#[derive(Debug, Clone)]
pub struct Parser<'a> {
	remaining: &'a [Spanned<Token>],
}



impl<'a> Parser<'a> {
	pub fn new(input: &'a [Spanned<Token>]) -> Self {
		Self {
			remaining: input
		}
	}

	pub fn parse(self) -> Result<crate::ast::Ast, ParsingError> {

	}
}
