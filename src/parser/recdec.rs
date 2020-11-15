use super::{Spanned, Token};
use crate::ast::{*};

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

            let decl = self.parse_declaration()?;
            self.ast.declarations.push(decl);
        }

        Ok(self.ast)
    }

    pub fn parse_declaration(&mut self) -> Result<Declaration, ParsingError> {
        match self.peek().ok_or(ParsingError::UnexpectedEndOfInput)? {
            Spanned(Token::Type, _) => {
                Ok(Declaration::Type(self.parse_type_decl()?))
            }
            Spanned(Token::Closed, _) => {
                Ok(Declaration::ClosedTypeClass(self.parse_closed_type_class()?))
            }
            t => Err(ParsingError::UnexpectedToken(t.clone(), None)),
        }
    }

    pub fn parse_type_decl(&mut self) -> Result<TypeDeclaration, ParsingError> {
        self.expect_token(Token::Type)?;
        let ident = self.expect_identifier()?;

        self.expect_token(Token::Equals)?;

        match self.peek().ok_or_else(|| ParsingError::UnexpectedEndOfInput)? {
            Spanned(Token::Pipe, _) => {
                self.expect_next()?;

                let variants = self.parse_punctuated_list(|parser| {
                    let ident = parser.expect_identifier()?;

                    let ty = if parser.maybe_expect(&Token::Of).is_some() {
                        parser.parse_type_sig()?
                    } else {
                        Ty::Unit
                    };

                    Ok((ident, box ty))
                }, Token::Pipe)?;

                let ty = Ty::Sum(variants);
                Ok(TypeDeclaration { ident, ty })
            }
            _ => {
                let ty = self.parse_type_sig()?;
                Ok(TypeDeclaration { ident, ty })
            }
        }
    }

    pub fn parse_closed_type_class(&mut self) -> Result<ClosedTypeClass, ParsingError> {
        self.expect_token(Token::Closed)?;
        self.expect_token(Token::TypeClass)?;
                
        let ident = self.expect_identifier()?;

        // value params
        let value_param = if self.maybe_expect(&Token::Less).is_some() {
            let ident = self.expect_identifier()?;
            self.expect_token(Token::Colon)?;
            let variants = self.parse_punctuated_list(Self::expect_identifier, Token::Pipe)?;

            Some((ident, variants))
        } else {
            None
        };

        let mut typeclass_items = Vec::new();
        let mut typeclass_members = Vec::new();
        let mut typeclass_impls = Vec::new();

        match self.peek().ok_or(ParsingError::UnexpectedEndOfInput)? {
            Spanned(Token::Identifier(_), _) => {
                typeclass_items.push((TypeClassItem::Method(self.parse_named_func_sig()), None));
            }
        }

        ClosedTypeClass {
            ident,
            value_param,
            typeclass_items,
            typeclass_members,
            typeclass_member_impls,
        }
    }

    pub fn parse_named_func_sig(&mut self) -> Result<NamedFunctionTypeSignature, ParsingError> {
        let ident = self.expect_identifier()?;

        self.expect_token(Token::Colon)?;
        self.expect_token(Token::Colon)?;

        let ty = self.parse_type_sig()?;
        if ty.is_function() {
            NamedFunctionTypeSignature { ident, }
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
            Spanned(Token::Float, _) => Ok(Ty::Float),
            Spanned(Token::String, _) => Ok(Ty::String),
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
