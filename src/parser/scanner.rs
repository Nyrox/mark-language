use super::{Position, Span, Spanned, Token};

#[derive(Debug, Clone)]
pub enum ScanningProduct {
    Skip,
    Finished,
    Token(Spanned<Token>),
}

#[derive(Clone, Debug)]
pub enum ScanningError {
    UnexpectedCharacter(Spanned<char>),
    InvalidLiteral(Spanned<()>),
    UnexpectedEndOfFile,
}

type ScanningResult = Result<ScanningProduct, ScanningError>;

pub struct Scanner<I: Iterator<Item = char>> {
    input: I,
    line: u32,
    offset: u32,
    peeked: Option<char>,
}

impl<I: Iterator<Item = char>> Scanner<I> {
    pub fn new(input: I) -> Self {
        Scanner {
            input,
            line: 1,
            offset: 0,
            peeked: None,
        }
    }

    pub fn scan_all(mut self) -> Result<Vec<Spanned<Token>>, ScanningError> {
        let mut output = Vec::new();

        loop {
            match self.scan_token()? {
                ScanningProduct::Skip => (),
                ScanningProduct::Finished => return Ok(output),
                ScanningProduct::Token(token) => {
                    output.push(token);
                }
            }
        }
    }

    pub fn advance(&mut self) -> Option<char> {
        self.offset += 1;
        match self.peeked {
            None => self.input.next(),
            Some(c) => {
                self.peeked = None;
                Some(c)
            }
        }
    }

    pub fn peek(&mut self) -> Option<char> {
        match self.peeked {
            Some(c) => Some(c),
            None => {
                self.peeked = self.input.next();
                self.peeked
            }
        }
    }

    pub fn keyword(&self, what: &str) -> Option<Token> {
        match what.to_owned().as_str() {
            "return" => Some(Token::Return),
            "let" => Some(Token::Let),
            "mut" => Some(Token::Mut),
            "if" => Some(Token::If),
            "else" => Some(Token::Else),
            "type" => Some(Token::Type),
            "then" => Some(Token::Then),
            "of" => Some(Token::Of),
            "closed" => Some(Token::Closed),
            "typeclass" => Some(Token::TypeClass),
            "begin" => Some(Token::Begin),
            "end" => Some(Token::End),
            "Self" => Some(Token::Self_),
            "impl" => Some(Token::Impl),
            "match" => Some(Token::Match),
            "with" => Some(Token::With),
            "Int" => Some(Token::Int),
			"Float" => Some(Token::Float),
			"String" => Some(Token::String),
			"for" => Some(Token::For),
            _ => None,
        }
    }

    pub fn position(&self) -> Position {
        Position(self.line, self.offset)
    }

    pub fn scan_token(&mut self) -> ScanningResult {
        let from = self.position();
        let c = match self.advance() {
            Some(c) => c,
            None => {
                return Ok(ScanningProduct::Finished);
            }
        };
        let peeked = self.peek();

        let to = self.position();
        let tok = |t| Ok(ScanningProduct::Token(Spanned(t, Span(from, to))));

        match c {
            '(' => tok(Token::LeftParen),
            ')' => tok(Token::RightParen),
            '{' => tok(Token::LeftBrace),
            '}' => tok(Token::RightBrace),
            '-' => tok(Token::Minus),
            '+' => tok(Token::Plus),
            '\'' => tok(Token::Tick),
            '|' => tok(Token::Pipe),
            '[' => tok(Token::LeftBracket),
            ']' => tok(Token::RightBracket),
            ':' => tok(Token::Colon),
            '/' => match peeked {
                Some('/') => {
                    while self.advance().ok_or(ScanningError::UnexpectedEndOfFile)? != '\n' {}
                    self.offset = 0;
                    self.line += 1;

                    Ok(ScanningProduct::Skip)
                }
                _ => tok(Token::Slash),
			},
			'"' => {
				let mut string = String::new();
				loop {
					match self.advance() {
						Some('"') => break,
						Some(c) => string.push(c),
						None => Err(ScanningError::UnexpectedEndOfFile)?,
					}
				};

				Ok(ScanningProduct::Token(Spanned(Token::StringLiteral(string), Span(from, self.position()))))
			}
            '*' => tok(Token::Star),
            ',' => tok(Token::Comma),
            '.' => tok(Token::Dot),
            '<' if peeked == Some('=') => {
                self.advance();
                tok(Token::LessEq)
            }
            '>' if peeked == Some('=') => {
                self.advance();
                tok(Token::GreaterEq)
            }
            '=' if peeked == Some('=') => {
                self.advance();
                tok(Token::EqualsEquals)
            }
            '<' => tok(Token::Less),
            '>' => tok(Token::Greater),
            '=' => tok(Token::Equals),

            '\n' => {
                self.line += 1;
                self.offset = 0;
                Ok(ScanningProduct::Skip)
            }
            c if c.is_whitespace() => Ok(ScanningProduct::Skip),
            c if c.is_numeric() => self.scan_numerics(c),
            c if c.is_alphanumeric() || c == '_' => self.scan_identifier(c),
            c => {
                return Err(ScanningError::UnexpectedCharacter(Spanned(
                    c,
                    Span(from, self.position()),
                )))
            }
        }
    }

    pub fn scan_identifier(&mut self, begin: char) -> ScanningResult {
        let mut from = self.position();
        from.1 = from.1 - 1;

        let mut ident = String::new();
        ident.push(begin);

        loop {
            match self.peek() {
                Some(c) if c.is_alphanumeric() || c == '_' => ident.push(self.advance().unwrap()),
                _ => {
                    break;
                }
            }
        }

        let to = self.position();

        Ok(match self.keyword(&ident) {
            Some(k) => ScanningProduct::Token(Spanned(k, Span(from, to))),
            None => ScanningProduct::Token(Spanned(Token::Identifier(ident), Span(from, to))),
        })
    }

    pub fn scan_numerics(&mut self, begin: char) -> ScanningResult {
        let mut from = self.position();
        from.1 = from.1 - 1;

        let mut text = String::new();
        text.push(begin);

        while self.peek().unwrap().is_numeric() {
            text.push(self.advance().unwrap());
        }

        if self.peek().unwrap() == '.' {
            text.push(self.advance().unwrap());
            while self.peek().unwrap().is_numeric() {
                text.push(self.advance().unwrap());
            }
            let to = self.position();

            match text.parse::<f64>() {
                Ok(f) => Ok(ScanningProduct::Token(Spanned(
                    Token::FloatLiteral(f),
                    Span(from, to),
                ))),
                Err(_) => Err(ScanningError::InvalidLiteral(Spanned((), Span(from, to)))),
            }
        } else {
            let to = self.position();
            match text.parse::<i64>() {
                Ok(i) => Ok(ScanningProduct::Token(Spanned(
                    Token::IntegerLiteral(i),
                    Span(from, to),
                ))),
                Err(_) => Err(ScanningError::InvalidLiteral(Spanned((), Span(from, to)))),
            }
        }
    }
}
