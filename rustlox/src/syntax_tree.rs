use crate::{data_types::Value, token::TokenInfo};

#[derive(Clone, Debug)]
pub enum Stmt {
    VariableDeclaration {
        name: TokenInfo,
        initializer: Option<Expr>,
    },
    FunctionDeclaration {
        name: TokenInfo,
        parameters: Vec<TokenInfo>,
        body: Vec<Stmt>,
    },
    Expr(Box<Expr>),
    Print(Box<Expr>),
    Return {
        keyword: TokenInfo,
        value: Option<Expr>,
    },
    Block(Vec<Stmt>),
    If {
        condition: Box<Expr>,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>,
    },
    While {
        condition: Box<Expr>,
        body: Box<Stmt>,
    },
}

#[derive(Clone, Debug)]
pub enum Expr {
    Literal(Value),
    Unary {
        operator: TokenInfo,
        expr: Box<Expr>,
    },
    Binary {
        operator: TokenInfo,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Logical {
        operator: TokenInfo,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Grouping(Box<Expr>),
    Variable {
        name: TokenInfo,
    },
    Assignment {
        name: TokenInfo,
        value: Box<Expr>,
    },
    FunctionCall {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
        opening_paren: TokenInfo,
        closing_paren: TokenInfo,
    },
}
