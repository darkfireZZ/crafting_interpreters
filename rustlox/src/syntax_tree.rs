use crate::{data_types::Value, token::TokenInfo};

#[derive(Clone, Debug)]
pub struct SyntaxTree {
    pub program: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    VariableDeclaration {
        name: TokenInfo,
        initializer: Option<Expr>,
    },
    FunctionDeclaration(FunctionDefinition),
    ClassDeclaration(ClassDefinition),
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
    Get {
        object: Box<Expr>,
        property: TokenInfo,
    },
    Set {
        object: Box<Expr>,
        property: TokenInfo,
        value: Box<Expr>,
    },
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
    Variable(Variable),
    Super {
        keyword: Variable,
        method_name: TokenInfo,
    },
    This(Variable),
    Assignment {
        variable: Variable,
        value: Box<Expr>,
    },
    FunctionCall {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
        opening_paren: TokenInfo,
        closing_paren: TokenInfo,
    },
}

#[derive(Clone, Debug)]
pub struct FunctionDefinition {
    pub name: TokenInfo,
    pub parameters: Vec<TokenInfo>,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub struct ClassDefinition {
    pub name: TokenInfo,
    pub methods: Vec<FunctionDefinition>,
    pub superclass: Option<Variable>,
}

#[derive(Clone, Debug)]
pub struct Variable {
    name: TokenInfo,
    depth: Option<usize>,
}

impl Variable {
    pub fn new(name: TokenInfo) -> Self {
        Self { name, depth: None }
    }

    pub fn depth(&self) -> Option<usize> {
        self.depth
    }

    pub fn name(&self) -> &TokenInfo {
        &self.name
    }

    pub fn resolve_depth(&mut self, depth: usize) {
        self.depth = Some(depth);
    }
}
