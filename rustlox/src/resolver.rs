use {
    crate::{
        error_group::ErrorGroup,
        syntax_tree::{Expr, FunctionDefinition, Stmt, SyntaxTree, Variable},
        token::TokenInfo,
    },
    std::{
        collections::hash_map::{self, HashMap},
        fmt::{self, Display},
    },
};

pub fn resolve(syntax_tree: &mut SyntaxTree) -> Result<(), ErrorGroup<ResolutionError>> {
    Resolver::new().resolve(syntax_tree)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResolutionStatus {
    Declared,
    Defined,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FunctionType {
    Function,
    Method,
}

#[derive(Debug)]
struct Resolver {
    scopes: Vec<HashMap<String, ResolutionStatus>>,
    current_function: Option<FunctionType>,
    errors: ErrorGroup<ResolutionError>,
}

impl Resolver {
    fn new() -> Self {
        Self {
            scopes: Vec::new(),
            current_function: None,
            errors: ErrorGroup::new(),
        }
    }

    fn resolve(mut self, syntax_tree: &mut SyntaxTree) -> Result<(), ErrorGroup<ResolutionError>> {
        self.resolve_stmts(&mut syntax_tree.program);
        self.errors.error_or_else(|| ())
    }

    fn resolve_stmts(&mut self, stmts: &mut [Stmt]) {
        for stmt in stmts {
            self.resolve_stmt(stmt);
        }
    }

    fn resolve_stmt(&mut self, stmt: &mut Stmt) {
        match stmt {
            Stmt::Expr(expr) => self.resolve_expr(expr),
            Stmt::Block(stmts) => {
                self.begin_scope();
                self.resolve_stmts(stmts);
                self.end_scope();
            }
            Stmt::VariableDeclaration { name, initializer } => {
                self.declare(name);
                if let Some(initializer) = initializer {
                    self.resolve_expr(initializer);
                }
                self.define(name);
            }
            Stmt::FunctionDeclaration(function) => {
                self.declare(&function.name);
                self.define(&function.name);
                self.resolve_function(function, FunctionType::Function);
            }
            Stmt::ClassDeclaration(class) => {
                self.declare(&class.name);
                self.define(&class.name);

                for method in &mut class.methods {
                    self.resolve_function(method, FunctionType::Method);
                }
            }
            Stmt::Print(expr) => self.resolve_expr(expr),
            Stmt::Return { keyword, value } => {
                if self.current_function.is_none() {
                    self.errors.add(ResolutionError {
                        ty: ResolutionErrorType::ReturnFromGlobalScope,
                        token: keyword.clone(),
                    });
                }

                if let Some(value) = value {
                    self.resolve_expr(value);
                }
            }
            Stmt::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.resolve_expr(condition);
                self.resolve_stmt(then_branch);
                if let Some(else_branch) = else_branch {
                    self.resolve_stmt(else_branch)
                }
            }
            Stmt::While { condition, body } => {
                self.resolve_expr(condition);
                self.resolve_stmt(body);
            }
        }
    }

    fn resolve_expr(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Variable(variable) => {
                if self
                    .scopes
                    .last()
                    .and_then(|current_scope| current_scope.get(&variable.name().lexeme))
                    .is_some_and(|status| *status == ResolutionStatus::Declared)
                {
                    self.errors.add(ResolutionError {
                        ty: ResolutionErrorType::ReadLocalVarInItsOwnInitializer,
                        token: variable.name().clone(),
                    });
                } else {
                    self.resolve_local(variable);
                }
            }
            Expr::Get { object, .. } => {
                self.resolve_expr(object);
            }
            Expr::Set { object, value, .. } => {
                self.resolve_expr(value);
                self.resolve_expr(object);
            }
            Expr::Assignment { variable, value } => {
                self.resolve_expr(value);
                self.resolve_local(variable);
            }
            Expr::Unary { expr, .. } => self.resolve_expr(expr),
            Expr::Binary { left, right, .. } => {
                self.resolve_expr(left);
                self.resolve_expr(right);
            }
            Expr::Logical { left, right, .. } => {
                self.resolve_expr(left);
                self.resolve_expr(right);
            }
            Expr::Grouping(expr) => self.resolve_expr(expr),
            Expr::FunctionCall {
                callee, arguments, ..
            } => {
                self.resolve_expr(callee);
                for arg in arguments {
                    self.resolve_expr(arg);
                }
            }
            Expr::Literal { .. } => {}
        }
    }

    fn resolve_function(&mut self, function: &mut FunctionDefinition, function_type: FunctionType) {
        let enclosing_func_type = self.current_function;
        self.current_function = Some(function_type);
        self.begin_scope();
        for param in &function.parameters {
            self.declare(param);
            self.define(param);
        }
        self.resolve_stmts(&mut function.body);
        self.end_scope();
        self.current_function = enclosing_func_type;
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }

    fn declare(&mut self, variable: &TokenInfo) {
        if let Some(current_scope) = self.scopes.last_mut() {
            match current_scope.entry(variable.lexeme.clone()) {
                hash_map::Entry::Occupied(_) => {
                    self.errors.add(ResolutionError {
                        ty: ResolutionErrorType::MultipleDefinitionsWithSameName,
                        token: variable.clone(),
                    });
                }
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(ResolutionStatus::Declared);
                }
            }
        }
    }

    fn define(&mut self, variable: &TokenInfo) {
        if let Some(current_scope) = self.scopes.last_mut() {
            *current_scope
                .get_mut(&variable.lexeme)
                .expect("variable is always declared before it is defined") =
                ResolutionStatus::Defined;
        }
    }

    fn resolve_local(&mut self, variable: &mut Variable) {
        if let Some((depth, _)) = self
            .scopes
            .iter()
            .rev()
            .enumerate()
            .find(|(_, scope)| scope.contains_key(&variable.name().lexeme))
        {
            variable.resolve_depth(depth);
        }
    }
}

#[derive(Clone, Debug)]
pub struct ResolutionError {
    ty: ResolutionErrorType,
    token: TokenInfo,
}

impl Display for ResolutionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[line {}]: {}", self.token.line, self.ty)
    }
}

#[derive(Clone, Debug)]
enum ResolutionErrorType {
    ReadLocalVarInItsOwnInitializer,
    ReturnFromGlobalScope,
    MultipleDefinitionsWithSameName,
}

impl Display for ResolutionErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ReadLocalVarInItsOwnInitializer => {
                write!(f, "Cannot read local variable in its own initializer")
            }
            Self::ReturnFromGlobalScope => {
                write!(f, "Cannot return from top-level code")
            }
            Self::MultipleDefinitionsWithSameName => {
                write!(
                    f,
                    "There is already a variable with this name in this scope"
                )
            }
        }
    }
}
