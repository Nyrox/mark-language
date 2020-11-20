use super::{Spanned, Token};
use crate::ast::{*};

#[derive(Debug, Clone)]
pub enum ParsingError {
    UnexpectedEndOfInput,
    UnexpectedToken(Spanned<Token>, Option<Token>),
    ExpectedFunctionType(Ty),
}

#[derive(Debug)]
pub struct Parser<'a> {
    remaining: &'a [Spanned<Token>],
    ast: Ast,
    last_consumed: Option<&'a Spanned<Token>>,
}

type ParseFn<T> = fn(&mut Parser) -> Result<T, ParsingError>;

/// Basics
impl<'a> Parser<'a> {
    pub fn new(input: &'a [Spanned<Token>]) -> Self {
        Self {
            remaining: input,
            ast: Ast::new(),
            last_consumed: None,
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
        self.last_consumed = Some(ret);
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

    pub fn peek2(&self) -> Option<&Spanned<Token>> {
        if self.remaining.len() < 2 {
            return None;
        }

        Some(&self.remaining[1])
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

	pub fn maybe_expect_identifier(&mut self) -> Option<Spanned<String>> {
		if let Some(Spanned(Token::Identifier(i), span)) = self.peek() {
			let i = i.clone();
			let span= span.clone();
			self.next();
			Some(Spanned(i.clone(), span))
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
			Spanned(Token::Identifier(i), span) => {
				// make borrowchk happy
				let i = i.clone();
				let span = span.clone();

				self.expect_next()?;

				if let Some(_) = self.maybe_expect(&Token::Colon) {
					// type annotation
					self.expect_token(Token::Colon)?;

					Ok(Declaration::TypeAnnotation(Spanned(i, span), self.parse_type()?))
				} else {
					let params = match self.peek().ok_or(ParsingError::UnexpectedEndOfInput)? {
						Spanned(Token::LeftParen, span) => {
							let span = span.clone();

							self.expect_next()?;
							self.expect_token(Token::RightParen)?;
							vec![Spanned("_".to_owned(), span)]
						}
						Spanned(Token::Equals, _) => {
							vec![]
						}
						_ => {
							let mut params = Vec::new();
							while let Some(i) = self.maybe_expect_identifier() {
								params.push(i);
							}
							params
						}
					};

					self.expect_token(Token::Equals)?;

					let mut expr = self.parse_expr()?;
					for p in params.into_iter().rev() {
						expr = Expr::Lambda(p, box expr);
					}

					Ok(Declaration::Binding(Spanned(i.clone(), span), expr))
				}
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
                        parser.parse_type()?
                    } else {
                        Ty::Unit
                    };

                    Ok((ident, box ty))
                }, Token::Pipe)?;

                let ty = Ty::Sum(variants);
                Ok(TypeDeclaration { ident, ty })
            }
            Spanned(Token::LeftBrace, _) => {
                Ok(TypeDeclaration { ident, ty: Ty::Record(box self.parse_record_type()?) })
            }
            _ => {
                let ty = self.parse_type()?;
                Ok(TypeDeclaration { ident, ty })
            }
        }
    }

    pub fn parse_record_type(&mut self) -> Result<Record, ParsingError> {
        self.expect_token(Token::LeftBrace)?;

        let fields = self.parse_punctuated_list(|parser| {
            let attr = if parser.maybe_expect(&Token::LeftBracket).is_some() {
                let attr = parser.expect_identifier()?;
                parser.expect_token(Token::RightBracket)?;
                Some(attr)
            } else {
                None
            };

            let ident = parser.expect_identifier()?;
            parser.expect_token(Token::Colon)?;
            let ty = parser.parse_type()?;
            Ok((ident, ty, attr))
        }, Token::Comma)?;
        self.expect_token(Token::RightBrace)?;

        Ok(Record {
            fields
        })
    }

    pub fn parse_closed_type_class(&mut self) -> Result<ClosedTypeClass, ParsingError> {
        self.expect_token(Token::Closed)?;
        self.expect_token(Token::TypeClass)?;

        let ident = self.expect_identifier()?;

        // value params
        let value_param = if self.maybe_expect(&Token::Less).is_some() {
            let ident = self.expect_identifier()?;
            self.expect_token(Token::Colon)?;
            let variants = self.parse_punctuated_list(|parser| parser.expect_identifier(), Token::Pipe)?;

            self.expect_token(Token::Greater)?;

            Some((ident, variants))
        } else {
            None
        };

        self.expect_token(Token::Begin)?;

        let mut typeclass_items = Vec::new();
        let mut typeclass_members = Vec::new();
        let mut typeclass_member_impls = Vec::new();

        loop {
            match self.peek().ok_or(ParsingError::UnexpectedEndOfInput)? {
                Spanned(Token::Identifier(_), _) => {
                    typeclass_items.push((TypeClassItem::Method(self.parse_named_func_sig()?), None));
                }
                Spanned(Token::LeftBracket, _) => {
                    self.expect_next()?;
                    let attr = self.expect_identifier()?;
                    self.expect_token(Token::RightBracket)?;

                    typeclass_items.push((TypeClassItem::Method(self.parse_named_func_sig()?), Some(attr)))
                }
                Spanned(Token::Type, _) => {
                    typeclass_members.push(self.parse_type_decl()?);
                }
                Spanned(Token::Impl, _) => {
                    self.expect_next()?;

                    let what = self.expect_identifier()?;
                    self.expect_token(Token::For)?;
                    let who = self.expect_identifier()?;
                    let p =self.expect_identifier()?;
                    self.expect_token(Token::Equals)?;

                    let body = self.parse_expr()?;

                    typeclass_member_impls.push(TypeClassImplItem {
                        what, who, body: (p, body)
                    });
                }
                Spanned(Token::End, _) => {
                    self.expect_next()?;
                    break;
                }
                t => return Err(ParsingError::UnexpectedToken(t.clone(), None))
            }
        }


        Ok(ClosedTypeClass {
            ident,
            value_param,
            typeclass_items,
            typeclass_members,
            typeclass_member_impls,
        })
    }

    pub fn parse_named_func_sig(&mut self) -> Result<NamedFunctionTypeSignature, ParsingError> {
        let ident = self.expect_identifier()?;

        self.expect_token(Token::Colon)?;
        self.expect_token(Token::Colon)?;

        let ty = self.parse_type()?;
        if let Ty::Func(l, r) = ty {
            Ok(NamedFunctionTypeSignature { ident, from: *l, to: *r })
        } else {
            Err(ParsingError::ExpectedFunctionType(ty))
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParsingError> {
        self.parse_expr_bp(0)
    }

    pub fn parse_expr_bp(&mut self, min_bp: u8) -> Result<Expr, ParsingError> {
        // basic blocks
        let mut lhs = match self.expect_next()? {
            Spanned(Token::Identifier(i), span) => Expr::Symbol(Spanned(i.clone(), *span)),
            t => return Err(ParsingError::UnexpectedToken(t.clone(), None)),
        };

        loop {
            let (t, (l_bp, r_bp)) = match self.peek() {
                Some(t) if Self::infix_binding_power(t).is_some() => (t.clone(), Self::infix_binding_power(t).unwrap()),
                _ => break,
            };
            if l_bp < min_bp {
                break;
            }

            self.expect_next()?;

            // field access
            if let Spanned(Token::Dot, _) = t {
                let field = match self.expect_next()? {
                    Spanned(Token::Identifier(i), span) => Spanned(i.clone(), *span),
                    Spanned(Token::IntegerLiteral(i), span) => Spanned(i.to_string(), *span),
                    t => return Err(ParsingError::UnexpectedToken(t.clone(), None)),
                };
                lhs = Expr::FieldAccess(box lhs, field);
            } else {
                let rhs = self.parse_expr_bp(r_bp)?;

                match t {

                    _ => return Err(ParsingError::UnexpectedToken(t, None))
                }
            }
        }

        // if the next token is on the same line, we try function application
        // TODO: Improve
        if self.peek().ok_or(ParsingError::UnexpectedEndOfInput)?.1.0 == self.last_consumed.unwrap().1.0 {
            panic!()
        }

        Ok(lhs)
    }

    pub fn parse_type(&mut self) -> Result<Ty, ParsingError> {
        let lhs = match self.expect_next()?.clone() {
            Spanned(Token::LeftParen, _) => {
                // tuple
                if self.maybe_expect(&Token::RightParen).is_some() {
                    Ok(Ty::Unit)
                } else {
                    let members = self.parse_punctuated_list(
                        |parser| {
                            let r = parser.parse_type()?;
                            Ok(box r)
                        },
                        Token::Comma,
                    )?;

                    self.expect_token(Token::RightParen)?;

                    if members.len() == 1 {
                        Ok(*members[0].clone())
                    } else {
                        Ok(Ty::Tuple(members))
                    }
                }
            }
            Spanned(Token::Int, _) => Ok(Ty::Int),
            Spanned(Token::Float, _) => Ok(Ty::Float),
            Spanned(Token::String, _) => Ok(Ty::String),
            Spanned(Token::Self_, _) => Ok(Ty::TypeRef("Self".to_owned(), None)),
            Spanned(Token::Identifier(i), _) => {
                let attr = if self.maybe_expect(&Token::Less).is_some() {
                    let attr = self.expect_identifier()?;
                    self.expect_token(Token::Greater)?;
                    Some(attr)
                } else { None };

                Ok(Ty::TypeRef(i.clone(), attr))
            }
            t => Err(ParsingError::UnexpectedToken(t.clone(), None)),
        }?;

        if self.maybe_expect(&Token::Minus).is_some() {
            self.expect_token(Token::Greater)?;

            Ok(Ty::Func(box lhs, box self.parse_type()?))
        } else if let Some(Spanned(Token::LeftBracket, _)) = self.peek() {
            if let Some(Spanned(Token::RightBracket, _)) = self.peek2() {
                self.expect_token(Token::LeftBracket)?;
                self.expect_token(Token::RightBracket)?;
                Ok(Ty::List(box lhs))
            } else {
                Ok(lhs)
            }
        } else{
            Ok(lhs)
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

    pub fn infix_binding_power(t: &Token) -> Option<(u8, u8)> {
        match t {
            &Token::Dot => Some((3, 4)),
            _ => None,
        }
    }
}
