use {
    crate::scanner::{Scanner, Token, TokenInfo},
    std::{
        fmt::{self, Display},
        iter::Peekable,
    },
};

#[derive(Debug)]
pub enum Stmt<'a> {
    VariableDeclaration {
        name: TokenInfo<'a>,
        initializer: Option<Expr<'a>>,
    },
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
    Variable {
        name: TokenInfo<'a>,
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
            Self::Variable { name } => write!(f, "{}", name.lexeme),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum ParseErrorType {
    MissingRightParen,
    MissingSemicolon,
    ExpectedExpression,
    ExpectedVariableName,
}

impl Display for ParseErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::MissingRightParen => write!(f, "Missing right parenthesis"),
            Self::MissingSemicolon => write!(f, "Missing semicolon"),
            Self::ExpectedExpression => write!(f, "Expected expression"),
            Self::ExpectedVariableName => write!(f, "Expected variable name"),
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
        while self.scanner.peek().is_some() {
            match self.parse_declaration() {
                Ok(stmt) => stmts.push(stmt),
                Err(err) => {
                    self.synchronize();
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

    fn parse_declaration(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        if self.matches(|token| token == Token::Var).is_some() {
            self.parse_variable_declaration()
        } else {
            self.parse_statement()
        }
    }

    fn parse_variable_declaration(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        let name = self.try_consume(Token::Identifier, ParseErrorType::ExpectedVariableName)?;
        let initializer = match self.matches(|token| token == Token::Equal) {
            Some(_) => Some(self.parse_expression()?),
            None => None,
        };
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        Ok(Stmt::VariableDeclaration { name, initializer })
    }

    fn parse_statement(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        if self.matches(|token| token == Token::Print).is_some() {
            self.parse_print_statement()
        } else {
            self.parse_expression_statement()
        }
    }

    fn parse_print_statement(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        let expr = self.parse_expression()?;
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        Ok(Stmt::Print(expr))
    }

    fn parse_expression_statement(&mut self) -> Result<Stmt<'a>, ParseError<'a>> {
        let expr = self.parse_expression()?;
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        Ok(Stmt::Expr(expr))
    }

    fn parse_expression(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        self.parse_equality()
    }

    fn parse_equality(&mut self) -> Result<Expr<'a>, ParseError<'a>> {
        let mut left = self.parse_comparison()?;

        while let Some(operator) =
            self.matches(|token| (token == Token::BangEqual) || (token == Token::EqualEqual))
        {
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

        while let Some(operator) = self.matches(|token| {
            [
                Token::Greater,
                Token::GreaterEqual,
                Token::Less,
                Token::LessEqual,
            ]
            .contains(&token)
        }) {
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

        while let Some(operator) =
            self.matches(|token| (token == Token::Minus) || (token == Token::Plus))
        {
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

        while let Some(operator) =
            self.matches(|token| (token == Token::Slash) || (token == Token::Star))
        {
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
        if let Some(operator) =
            self.matches(|token| (token == Token::Bang) || (token == Token::Minus))
        {
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
                Ok(Expr::Literal {
                    literal: self.scanner.next().unwrap(),
                })
            }
            Some(Token::LeftParen) => {
                self.scanner.next();
                let expr = self.parse_expression()?;
                self.try_consume(Token::RightParen, ParseErrorType::MissingRightParen)?;
                Ok(Expr::Grouping {
                    expr: Box::new(expr),
                })
            }
            Some(Token::Identifier) => Ok(Expr::Variable {
                name: self.scanner.next().unwrap(),
            }),
            _ => Err(ParseError {
                ty: ParseErrorType::ExpectedExpression,
                token: next_token.copied(),
            }),
        }
    }

    fn try_consume(
        &mut self,
        token: Token,
        err_ty: ParseErrorType,
    ) -> Result<TokenInfo<'a>, ParseError<'a>> {
        let next = self.scanner.peek();
        match next {
            Some(next_token) if next_token.token == token => Ok(self.scanner.next().unwrap()),
            _ => Err(ParseError {
                ty: err_ty,
                token: next.copied(),
            }),
        }
    }

    fn matches<F: FnOnce(Token) -> bool>(&mut self, is_match: F) -> Option<TokenInfo<'a>> {
        if self.scanner.peek().is_some_and(|next| is_match(next.token)) {
            self.scanner.next()
        } else {
            None
        }
    }

    fn synchronize(&mut self) {
        self.scanner.next();
        while let Some(next) = self.scanner.peek() {
            match next.token {
                Token::Class
                | Token::Fun
                | Token::Var
                | Token::For
                | Token::If
                | Token::While
                | Token::Print
                | Token::Return => {
                    return;
                }
                Token::Semicolon => {
                    self.scanner.next();
                    return;
                }
                _ => (),
            }
        }
    }
}
