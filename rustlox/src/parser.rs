use {
    crate::{
        data_types::Value,
        scanner::Scanner,
        syntax_tree::{Expr, FunctionDefinition, Stmt, SyntaxTree, Variable},
        token::{Token, TokenInfo},
    },
    std::{
        fmt::{self, Display},
        iter::Peekable,
    },
};

#[derive(Clone, Copy, Debug)]
enum ParseErrorType {
    MissingOpeningParenInControlFlowStmt,
    MissingOpeningParenInFunctionDeclaration,
    MissingClosingParenInControlFlowStmt,
    MissingClosingParenInFunctionDeclaration,
    MissingParenAfterFunctionArgs,
    MissingSemicolon,
    ExpectedBlockAfterParameters,
    ExpectedExpression,
    ExpectedFunctionName,
    ExpectedFunctionParameterName,
    ExpectedVariableName,
    InvalidAssignmentTarget,
    TooManyFunctionArguments,
    TooManyFunctionParameters,
    UnclosedGrouping,
    UnterminatedBlock,
}

impl Display for ParseErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::MissingOpeningParenInControlFlowStmt => {
                write!(f, "Missing '(' in control flow statement")
            }
            Self::MissingOpeningParenInFunctionDeclaration => {
                write!(f, "Missing '(' in function declaration")
            }
            Self::MissingClosingParenInControlFlowStmt => {
                write!(f, "Missing ')' in control flow statement")
            }
            Self::MissingClosingParenInFunctionDeclaration => {
                write!(f, "Missing ')' in function declaration")
            }
            Self::MissingParenAfterFunctionArgs => {
                write!(f, "Expected ')' after function arguments")
            }
            Self::MissingSemicolon => write!(f, "Missing semicolon"),
            Self::ExpectedBlockAfterParameters => write!(f, "Expected '{{' after parameter list"),
            Self::ExpectedExpression => write!(f, "Expected expression"),
            Self::ExpectedFunctionName => write!(f, "Expected function name"),
            Self::ExpectedFunctionParameterName => write!(f, "Expected parameter name"),
            Self::ExpectedVariableName => write!(f, "Expected variable name"),
            Self::InvalidAssignmentTarget => write!(f, "Invalid assignment target"),
            Self::TooManyFunctionArguments => write!(f, "Functions may have at most 255 arguments"),
            Self::TooManyFunctionParameters => {
                write!(f, "Functions may have at most 255 parameters")
            }
            Self::UnclosedGrouping => write!(f, "Missing ')', unclosed grouping"),
            Self::UnterminatedBlock => write!(f, "Expected terminating '}}' after block"),
        }
    }
}

// TODO unify this error type with SourceError
#[derive(Debug)]
struct ParseError {
    ty: ParseErrorType,
    token: Option<TokenInfo>,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.token {
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

    pub fn parse(&mut self) -> Option<SyntaxTree> {
        let mut stmts = Vec::new();
        let mut had_error = false;
        while self.scanner.peek().is_some() {
            match self.parse_declaration() {
                Ok(stmt) => stmts.push(stmt),
                Err(err) => {
                    report_parse_error(err);
                    self.synchronize();
                    had_error = true;
                }
            }
        }

        if had_error {
            None
        } else {
            Some(SyntaxTree { program: stmts })
        }
    }

    fn parse_declaration(&mut self) -> Result<Stmt, ParseError> {
        if self.matches(|token| token == Token::Var).is_some() {
            self.parse_variable_declaration()
        } else if self.matches(|token| token == Token::Fun).is_some() {
            self.parse_function_declaration()
        } else {
            self.parse_statement()
        }
    }

    fn parse_variable_declaration(&mut self) -> Result<Stmt, ParseError> {
        let name = self.try_consume(Token::Identifier, ParseErrorType::ExpectedVariableName)?;
        let initializer = match self.matches(|token| token == Token::Equal) {
            Some(_) => Some(self.parse_expression()?),
            None => None,
        };
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        Ok(Stmt::VariableDeclaration { name, initializer })
    }

    fn parse_function_declaration(&mut self) -> Result<Stmt, ParseError> {
        let function_name =
            self.try_consume(Token::Identifier, ParseErrorType::ExpectedFunctionName)?;
        self.try_consume(
            Token::LeftParen,
            ParseErrorType::MissingOpeningParenInFunctionDeclaration,
        )?;

        let mut parameters = Vec::new();
        if self
            .scanner
            .peek()
            .filter(|token| token.token == Token::RightParen)
            .is_none()
        {
            loop {
                let param_name = self.try_consume(
                    Token::Identifier,
                    ParseErrorType::ExpectedFunctionParameterName,
                )?;
                parameters.push(param_name);
                if self.matches(|token| token == Token::Comma).is_none() {
                    break;
                }
            }
        }

        let closing_paren = self.try_consume(
            Token::RightParen,
            ParseErrorType::MissingClosingParenInFunctionDeclaration,
        )?;

        self.try_consume(
            Token::LeftBrace,
            ParseErrorType::ExpectedBlockAfterParameters,
        )?;
        let body = self.parse_block()?;

        if parameters.len() < 255 {
            Ok(Stmt::FunctionDeclaration(FunctionDefinition {
                name: function_name,
                parameters,
                body,
            }))
        } else {
            Err(ParseError {
                ty: ParseErrorType::TooManyFunctionParameters,
                token: Some(closing_paren),
            })
        }
    }

    fn parse_statement(&mut self) -> Result<Stmt, ParseError> {
        if self.matches(|token| token == Token::Print).is_some() {
            self.parse_print_statement()
        } else if let Some(return_keyword) = self.matches(|token| token == Token::Return) {
            let return_value = if self
                .scanner
                .peek()
                .is_some_and(|token| token.token != Token::Semicolon)
            {
                Some(self.parse_expression()?)
            } else {
                None
            };
            self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
            Ok(Stmt::Return {
                keyword: return_keyword,
                value: return_value,
            })
        } else if self.matches(|token| token == Token::LeftBrace).is_some() {
            Ok(Stmt::Block(self.parse_block()?))
        } else if self.matches(|token| token == Token::If).is_some() {
            self.parse_if_statement()
        } else if self.matches(|token| token == Token::While).is_some() {
            self.parse_while_statement()
        } else if self.matches(|token| token == Token::For).is_some() {
            self.parse_for_statement()
        } else {
            self.parse_expression_statement()
        }
    }

    fn parse_print_statement(&mut self) -> Result<Stmt, ParseError> {
        let expr = self.parse_expression()?;
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        Ok(Stmt::Print(Box::new(expr)))
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        let mut stmts = Vec::new();
        while self
            .scanner
            .peek()
            .is_some_and(|token| token.token != Token::RightBrace)
        {
            stmts.push(self.parse_declaration()?);
        }
        self.try_consume(Token::RightBrace, ParseErrorType::UnterminatedBlock)?;
        Ok(stmts)
    }

    fn parse_if_statement(&mut self) -> Result<Stmt, ParseError> {
        self.try_consume(
            Token::LeftParen,
            ParseErrorType::MissingOpeningParenInControlFlowStmt,
        )?;
        let condition = self.parse_expression()?;
        self.try_consume(
            Token::RightParen,
            ParseErrorType::MissingClosingParenInControlFlowStmt,
        )?;
        let then_stmt = self.parse_statement()?;
        let else_stmt = if self.matches(|token| token == Token::Else).is_some() {
            Some(self.parse_statement()?)
        } else {
            None
        };

        Ok(Stmt::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_stmt),
            else_branch: else_stmt.map(Box::new),
        })
    }

    fn parse_while_statement(&mut self) -> Result<Stmt, ParseError> {
        self.try_consume(
            Token::LeftParen,
            ParseErrorType::MissingOpeningParenInControlFlowStmt,
        )?;
        let condition = self.parse_expression()?;
        self.try_consume(
            Token::RightParen,
            ParseErrorType::MissingClosingParenInControlFlowStmt,
        )?;
        let body = self.parse_statement()?;

        Ok(Stmt::While {
            condition: Box::new(condition),
            body: Box::new(body),
        })
    }

    fn parse_for_statement(&mut self) -> Result<Stmt, ParseError> {
        self.try_consume(
            Token::LeftParen,
            ParseErrorType::MissingOpeningParenInControlFlowStmt,
        )?;
        let initializer = if self.matches(|token| token == Token::Semicolon).is_some() {
            None
        } else if self.matches(|token| token == Token::Var).is_some() {
            Some(self.parse_variable_declaration()?)
        } else {
            Some(self.parse_expression_statement()?)
        };
        let condition = if self
            .scanner
            .peek()
            .is_some_and(|token| token.token == Token::Semicolon)
        {
            Expr::Literal(Value::Boolean(true))
        } else {
            self.parse_expression()?
        };
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        let increment = if self
            .scanner
            .peek()
            .is_some_and(|token| token.token != Token::RightParen)
        {
            Some(self.parse_expression()?)
        } else {
            None
        };
        self.try_consume(
            Token::RightParen,
            ParseErrorType::MissingClosingParenInControlFlowStmt,
        )?;

        let body = self.parse_statement()?;

        let body = if let Some(increment) = increment {
            Stmt::Block(vec![body, Stmt::Expr(Box::new(increment))])
        } else {
            body
        };

        let while_loop = Stmt::While {
            condition: Box::new(condition),
            body: Box::new(body),
        };

        Ok(if let Some(initializer) = initializer {
            Stmt::Block(vec![initializer, while_loop])
        } else {
            while_loop
        })
    }

    fn parse_expression_statement(&mut self) -> Result<Stmt, ParseError> {
        let expr = self.parse_expression()?;
        self.try_consume(Token::Semicolon, ParseErrorType::MissingSemicolon)?;
        Ok(Stmt::Expr(Box::new(expr)))
    }

    fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParseError> {
        let left = self.parse_or()?;

        match self.matches(|token| token == Token::Equal) {
            Some(equal) => {
                let value = self.parse_assignment()?;
                if let Expr::Variable(variable) = left {
                    Ok(Expr::Assignment {
                        variable,
                        value: Box::new(value),
                    })
                } else {
                    Err(ParseError {
                        ty: ParseErrorType::InvalidAssignmentTarget,
                        token: Some(equal),
                    })
                }
            }
            None => Ok(left),
        }
    }

    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and()?;

        while let Some(or_token) = self.matches(|token| token == Token::Or) {
            let right = self.parse_and()?;
            left = Expr::Logical {
                operator: or_token,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_equality()?;

        while let Some(and_token) = self.matches(|token| token == Token::And) {
            let right = self.parse_equality()?;
            left = Expr::Logical {
                operator: and_token,
                left: Box::new(left),
                right: Box::new(right),
            };
        }

        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParseError> {
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

    fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
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

    fn parse_term(&mut self) -> Result<Expr, ParseError> {
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

    fn parse_factor(&mut self) -> Result<Expr, ParseError> {
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

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        if let Some(operator) =
            self.matches(|token| (token == Token::Bang) || (token == Token::Minus))
        {
            Ok(Expr::Unary {
                operator,
                expr: Box::new(self.parse_unary()?),
            })
        } else {
            self.parse_function_call()
        }
    }

    fn parse_function_call(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;
        while let Some(opening_paren) = self.matches(|token| token == Token::LeftParen) {
            expr = self.parse_function_arguments(opening_paren, expr)?;
        }
        Ok(expr)
    }

    fn parse_function_arguments(
        &mut self,
        opening_paren: TokenInfo,
        callee: Expr,
    ) -> Result<Expr, ParseError> {
        let mut arguments = Vec::new();
        if self
            .scanner
            .peek()
            .filter(|token| token.token == Token::RightParen)
            .is_none()
        {
            loop {
                arguments.push(self.parse_expression()?);
                if self.matches(|token| token == Token::Comma).is_none() {
                    break;
                }
            }
        }

        let closing_paren = self.try_consume(
            Token::RightParen,
            ParseErrorType::MissingParenAfterFunctionArgs,
        )?;

        if arguments.len() < 255 {
            Ok(Expr::FunctionCall {
                callee: Box::new(callee),
                arguments,
                opening_paren,
                closing_paren,
            })
        } else {
            Err(ParseError {
                ty: ParseErrorType::TooManyFunctionArguments,
                token: Some(closing_paren),
            })
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        if self.matches(|token| token == Token::Nil).is_some() {
            Ok(Expr::Literal(Value::Nil))
        } else if self.matches(|token| token == Token::True).is_some() {
            Ok(Expr::Literal(Value::Boolean(true)))
        } else if self.matches(|token| token == Token::False).is_some() {
            Ok(Expr::Literal(Value::Boolean(false)))
        } else if let Some(token) = self.matches(|token| token == Token::Number) {
            Ok(Expr::Literal(Value::Number(token.lexeme.parse().expect(
                "scanner only produces lexemes that can be parsed as a f64",
            ))))
        } else if let Some(token) = self.matches(|token| token == Token::String) {
            Ok(Expr::Literal(Value::String(
                token.lexeme[1..token.lexeme.len() - 1].to_owned(),
            )))
        } else if self.matches(|token| token == Token::LeftParen).is_some() {
            let expr = self.parse_expression()?;
            self.try_consume(Token::RightParen, ParseErrorType::UnclosedGrouping)?;
            Ok(Expr::Grouping(Box::new(expr)))
        } else if let Some(token) = self.matches(|token| token == Token::Identifier) {
            Ok(Expr::Variable(Variable::new(token)))
        } else {
            Err(ParseError {
                ty: ParseErrorType::ExpectedExpression,
                token: self.scanner.peek().cloned(),
            })
        }
    }

    fn try_consume(
        &mut self,
        token: Token,
        err_ty: ParseErrorType,
    ) -> Result<TokenInfo, ParseError> {
        let next = self.scanner.peek();
        match next {
            Some(next_token) if next_token.token == token => Ok(self.scanner.next().unwrap()),
            _ => Err(ParseError {
                ty: err_ty,
                token: next.cloned(),
            }),
        }
    }

    fn matches<F: FnOnce(Token) -> bool>(&mut self, is_match: F) -> Option<TokenInfo> {
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
                _ => {
                    self.scanner.next();
                }
            }
        }
    }
}
