use super::{Spanned, Token};
use crate::ast::{Ast, Declaration, Ty, TypeDeclaration};

#[derive(Debug, Clone)]
pub enum ParsingError {
    UnexpectedEndOfInput,
    UnexpectedToken(Spanned<Token>, Option<Token>),
}

#[derive(Debug)]
pub struct Parser<'a> {
    remaining: &'a [Spanned<Token>],
    ast: Ast,
}

type ParseFn<T> = fn(&mut Parser) -> Result<T, ParsingError>;

/// Basics
impl<'a> Parser<'a> {
    pub fn new(input: &'a [Spanned<Token>]) -> Self {
        Self {
            remaining: input,
            ast: Ast::new(),
        }
    }
}

/// Token Processing
impl Parser<'_> {
    pub fn next(&mut self) -> Option<&Spanned<Token>> {
        if self.remaining.len() == 0 {
            return None;
        }
        let ret = &self.remaining[0];
        dbg!(ret);
        self.remaining = &self.remaining[1..];
        Some(ret)
    }

    pub fn peek(&self) -> Option<&Spanned<Token>> {
        if self.remaining.len() == 0 {
            return None;
        }

        Some(&self.remaining[0])
    }

    pub fn expect_next(&mut self) -> Result<&Spanned<Token>, ParsingError> {
        self.next().ok_or(ParsingError::UnexpectedEndOfInput)
    }

    pub fn expect_token(&mut self, token: Token) -> Result<&Spanned<Token>, ParsingError> {
        let next = self.expect_next()?;

        if &token == &next.0 {
            Ok(next)
        } else {
            Err(ParsingError::UnexpectedToken(next.clone(), Some(token)))
        }
    }

    pub fn expect_identifier(&mut self) -> Result<Spanned<String>, ParsingError> {
        let next = self.expect_next()?;

        if let Token::Identifier(ref s) = &next.0 {
            Ok(Spanned(s.clone(), next.1))
        } else {
            Err(ParsingError::UnexpectedToken(
                next.clone(),
                Some(Token::Identifier(String::new())),
            ))
        }
    }

    pub fn maybe_expect(&mut self, token: &Token) -> Option<&Spanned<Token>> {
        if token == &self.peek()?.0 {
            self.next().clone()
        } else {
            None
        }
    }
}

/// Parser rules
impl Parser<'_> {
    pub fn parse(mut self) -> Result<Ast, ParsingError> {
        loop {
            if self.remaining.len() == 0 {
                break;
            }

            self.parse_declaration()?;
        }

        Ok(self.ast)
    }

    pub fn parse_declaration(&mut self) -> Result<Declaration, ParsingError> {
        match self.expect_next()? {
            Spanned(Token::Type, _) => {
                let ident = self.expect_identifier()?;

                self.expect_token(Token::Equals)?;

                let ty = self.parse_type_sig()?;

                Ok(Declaration::TypeDeclaration(TypeDeclaration { ident, ty }))
            }
            t => Err(ParsingError::UnexpectedToken(t.clone(), None)),
        }
    }

    pub fn parse_type_sig(&mut self) -> Result<Ty, ParsingError> {
        match self.expect_next()? {
            Spanned(Token::LeftParen, _) => {
                // tuple
                if self.maybe_expect(&Token::RightParen).is_some() {
                    Ok(Ty::Unit)
                } else {
                    let members = self.parse_punctuated_list(
                        |parser| {
                            let r = parser.parse_type_sig()?;
                            Ok(box r)
                        },
                        Token::Comma,
                    )?;

                    self.expect_token(Token::RightParen)?;
                    Ok(Ty::Tuple(members))
                }
            }
            Spanned(Token::Int, _) => Ok(Ty::Int),
            t => Err(ParsingError::UnexpectedToken(t.clone(), None)),
        }
    }

    pub fn parse_punctuated_list<T>(
        &mut self,
        f: ParseFn<T>,
        punctuator: Token,
    ) -> Result<Vec<T>, ParsingError> {
        let mut out = Vec::new();

        loop {
            out.push(f(self)?);

            if self.maybe_expect(&punctuator).is_none() {
                break;
            }
        }

        Ok(out)
    }
}
