use {
    crate::scanner::{Scanner, Token, TokenInfo},
    std::{
        fmt::{self, Display},
        iter::Peekable,
    },
};

#[derive(Debug)]
pub enum Stmt<'a> {
    Expr(Expr<'a>),
    Print(Expr<'a>),
}

#[derive(Debug)]
pub enum Expr<'a> {
    Literal {
        literal: TokenInfo<'a>,
    },
    Unary {
        operator: TokenInfo<'a>,
        expr: Box<Expr<'a>>,
    },
    Binary {
        operator: TokenInfo<'a>,
        left: Box<Expr<'a>>,
        right: Box<Expr<'a>>,
    },
    Grouping {
        expr: Box<Expr<'a>>,
    },
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Literal { literal } => literal.lexeme.fmt(f),
            Self::Unary { operator, expr } => {
                write!(f, "({} {})", operator.lexeme, expr)
            }
            Self::Binary {
                operator,
                left,
                right,
            } => {
                write!(f, "({} {} {})", operator.lexeme, left, right)
            }
            Self::Grouping { expr } => write!(f, "{}", expr),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum ParseErrorType {
    MissingRightParen,
    MissingSemicolon,
    ExpectedExpression,
}

impl Display for ParseErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::MissingRightParen => write!(f, "Missing right parenthesis"),
            Self::MissingSemicolon => write!(f, "Missing semicolon"),
            Self::ExpectedExpression => write!(f, "Expected expression"),
        }
    }
}

// TODO unify this error type with SourceError
#[derive(Debug)]
struct ParseError<'a> {
    ty: ParseErrorType,
    token: Option<TokenInfo<'a>>,
}

impl<'a> Display for ParseError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.token {
            Some(token) => write!(f, "[line {}] Error: {}", token.line, self.ty),
            // TODO indicate line of error
            None => write!(f, "[end of file] Error: {}", self.ty),
        }
    }
}

fn report_parse_error(err: ParseError) {
    eprintln!("{}", err);
}

#[derive(Debug)]
pub struct Parser<'a> {
    scanner: Peekable<Scanner<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(scanner: Scanner<'a>) -> Self {
        Self {
            scanner: scanner.peekable(),
        }
    }

    pub fn parse(&mut self) -> Option<Vec<Stmt<'a>>> {
        let mut stmts = Vec::new();
        let mut had_error = false;
        while let Some(_) = self.scanner.peek() {
            match self.parse_statement() {
                Ok(stmt) => stmts.push(stmt),
                Err(err) => {
                    report_parse_error(err);
                    had_error = true;
                }
            }
        }

        if had_error {
            None
        } else {
            Some(stmts)
        }
    }

    fn parse_statement(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        if self.scanner.peek().expect("not at end").token == Token::Print {
            self.parse_print_statement()
        } else {
            self.parse_expression_statement()
        }
    }

    fn parse_print_statement(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        let next = self.scanner.next();
        debug_assert!(next.is_some_and(|token| token.token == Token::Print));

        let expr = self.parse_expression()?;

        let next = self.scanner.peek();
        if next.is_some_and(|token| token.token == Token::Semicolon) {
            self.scanner.next();
            Ok(Stmt::Print(expr))
        } else {
            Err(ParseError {
                ty: ParseErrorType::MissingSemicolon,
                token: next.copied(),
            })
        }
    }

    fn parse_expression_statement(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        let expr = self.parse_expression()?;

        let next = self.scanner.peek();
        if next.is_some_and(|token| token.token == Token::Semicolon) {
            self.scanner.next();
            Ok(Stmt::Expr(expr))
        } else {
            Err(ParseError {
                ty: ParseErrorType::MissingSemicolon,
                token: next.copied(),
            })
        }
    }

    fn parse_expression(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        let mut left = self.parse_comparison()?;

        while let Some(operator) = self.matches(&[Token::BangEqual, Token::EqualEqual]) {
            let right = self.parse_comparison()?;
            left = Expr::Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        let mut left = self.parse_term()?;

        while let Some(operator) = self.matches(&[
            Token::Greater,
            Token::GreaterEqual,
            Token::Less,
            Token::LessEqual,
        ]) {
            let right = self.parse_term()?;
            left = Expr::Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_term(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        let mut left = self.parse_factor()?;

        while let Some(operator) = self.matches(&[Token::Minus, Token::Plus]) {
            let right = self.parse_factor()?;
            left = Expr::Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_factor(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        let mut left = self.parse_unary()?;

        while let Some(operator) = self.matches(&[Token::Slash, Token::Star]) {
            let right = self.parse_unary()?;
            left = Expr::Binary {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        if let Some(operator) = self.matches(&[Token::Bang, Token::Minus]) {
            Ok(Expr::Unary {
                operator,
                expr: Box::new(self.parse_unary()?),
            })
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        let next_token = self.scanner.peek();
        match next_token.map(|token| token.token) {
            Some(Token::False | Token::True | Token::Nil | Token::String | Token::Number(_)) => {
                let literal = self.scanner.next().expect("peeked value before");
                Ok(Expr::Literal { literal })
            }
            Some(Token::LeftParen) => {
                self.scanner.next();
                let expr = self.parse_expression()?;

                let after_expr = self.scanner.peek();
                if after_expr.is_some_and(|token| token.token == Token::RightParen) {
                    self.scanner.next();
                    Ok(Expr::Grouping {
                        expr: Box::new(expr),
                    })
                } else {
                    Err(ParseError {
                        ty: ParseErrorType::MissingRightParen,
                        token: after_expr.copied(),
                    })
                }
            }
            _ => Err(ParseError {
                ty: ParseErrorType::ExpectedExpression,
                token: next_token.copied(),
            }),
        }
    }

    fn matches(&mut self, tokens: &[Token]) -> Option<TokenInfo<'a>> {
        if self
            .scanner
            .peek()
            .is_some_and(|next_token| tokens.contains(&next_token.token))
        {
            self.scanner.next()
        } else {
            None
        }
    }
}
