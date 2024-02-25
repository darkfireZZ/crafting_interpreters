use {
    crate::{
        data_types::{BuiltInFunction, ClassInstance, LoxClass, LoxFunction, Value, ValueType},
        syntax_tree::{Expr, Stmt, SyntaxTree, Variable},
        token::{Token, TokenInfo},
    },
    std::{
        cell::RefCell,
        collections::HashMap,
        fmt::{self, Display},
        ops::Deref,
        rc::Rc,
        time::{SystemTime, UNIX_EPOCH},
    },
};

#[derive(Debug)]
pub struct RuntimeError {
    ty: RuntimeErrorType,
    token: TokenInfo,
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[line {}] Runtime error: {}", self.token.line, self.ty)
    }
}

impl std::error::Error for RuntimeError {}

#[derive(Debug)]
enum RuntimeErrorType {
    ExpectedDifferentType {
        expected: Vec<ValueType>,
        actual: ValueType,
    },
    IncorrectArgumentCount {
        expected: u8,
        actual: u8,
    },
    PropertyAccessOnNonInstance,
    TypeNotCallable(ValueType),
    UndefinedProperty,
    UndefinedVariable,
    Return(Value),
}

impl Display for RuntimeErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ExpectedDifferentType { expected, actual } => match expected.len() {
                0 => panic!("Interpreter bug, there must always be an expected type"),
                1 => write!(f, "Expected value of type {}, was {}", expected[0], actual),
                _ => {
                    let mut expected_str = String::from("[");
                    expected_str.push_str(expected[0].as_str());
                    for expected_ty in expected.iter().skip(1) {
                        expected_str.push_str(", ");
                        expected_str.push_str(expected_ty.as_str());
                    }
                    write!(
                        f,
                        "Expected value to be any of {}, was {}",
                        expected_str, actual
                    )
                }
            },
            Self::IncorrectArgumentCount { expected, actual } => {
                write!(f, "Expected {expected} arguments, but got {actual}")
            }
            Self::PropertyAccessOnNonInstance => write!(f, "Only class instances have properties"),
            Self::TypeNotCallable(ty) => write!(f, "{ty} is not callable"),
            Self::UndefinedProperty => write!(f, "Undefined property"),
            Self::UndefinedVariable => write!(f, "Undefined variable"),
            Self::Return(_) => write!(f, "Return is only valid inside a function"),
        }
    }
}

fn convert_value_to_number(value: Value, error_token: &TokenInfo) -> Result<f64, RuntimeError> {
    value.convert_to_number().ok_or_else(|| RuntimeError {
        ty: RuntimeErrorType::ExpectedDifferentType {
            actual: value.value_type(),
            expected: vec![ValueType::Number],
        },
        token: error_token.clone(),
    })
}

#[derive(Debug)]
pub struct Interpreter {
    globals: Rc<RefCell<Environment>>,
    current_env: Rc<RefCell<Environment>>,
}

impl Interpreter {
    pub fn new() -> Self {
        // TODO: ideally this should be put in a macro
        let globals = HashMap::from([(
            String::from("clock"),
            Value::BuiltInFunction(BuiltInFunction::Clock),
        )]);
        let globals = Rc::new(RefCell::new(Environment::new_global(globals)));
        Self {
            current_env: Rc::clone(&globals),
            globals,
        }
    }

    pub fn eval(&mut self, syntax_tree: &SyntaxTree) -> Result<(), RuntimeError> {
        self.eval_stmts(&syntax_tree.program)
    }

    fn eval_stmts(&mut self, stmts: &[Stmt]) -> Result<(), RuntimeError> {
        for stmt in stmts {
            self.eval_stmt(stmt)?;
        }
        Ok(())
    }

    fn eval_stmt(&mut self, stmt: &Stmt) -> Result<(), RuntimeError> {
        match stmt {
            Stmt::Print(expr) => {
                // TODO: What if writing to stdout fails
                println!("{}", self.eval_expr(expr)?);
            }
            Stmt::Expr(expr) => {
                self.eval_expr(expr)?;
            }
            Stmt::VariableDeclaration { name, initializer } => {
                let initializer = match initializer {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Nil,
                };
                self.current_env
                    .borrow_mut()
                    .define_variable(name.lexeme.to_owned(), initializer);
            }
            Stmt::FunctionDeclaration(function) => {
                let name = function.name.lexeme.to_owned();
                let value = Value::LoxFunction(Rc::new(LoxFunction {
                    definition: function.clone(),
                    closure: Rc::clone(&self.current_env),
                }));
                self.current_env.borrow_mut().define_variable(name, value)
            }
            Stmt::ClassDeclaration(class) => {
                let methods = class
                    .methods
                    .iter()
                    .map(|function_definition| {
                        let name = function_definition.name.lexeme.to_owned();
                        let value = Rc::new(LoxFunction {
                            definition: function_definition.clone(),
                            closure: Rc::clone(&self.current_env),
                        });
                        (name, value)
                    })
                    .collect();
                let name = class.name.lexeme.to_owned();
                let value = Value::LoxClass(Rc::new(LoxClass {
                    name: name.clone(),
                    methods,
                    definition: class.clone(),
                }));
                self.current_env.borrow_mut().define_variable(name, value)
            }
            Stmt::Block(stmts) => {
                let mut block_env = Rc::new(RefCell::new(Environment::new_inside(Rc::clone(
                    &self.current_env,
                ))));
                std::mem::swap(&mut self.current_env, &mut block_env);
                let result = self.eval_stmts(stmts);
                std::mem::swap(&mut self.current_env, &mut block_env);
                result?;
            }
            Stmt::If {
                condition,
                then_branch,
                else_branch,
            } => {
                if self.eval_expr(condition)?.is_truthy() {
                    self.eval_stmt(then_branch)?;
                } else if let Some(else_branch) = else_branch {
                    self.eval_stmt(else_branch)?;
                }
            }
            Stmt::While { condition, body } => {
                while self.eval_expr(condition)?.is_truthy() {
                    self.eval_stmt(body)?;
                }
            }
            Stmt::Return { keyword, value } => {
                let value = match value {
                    Some(expr) => self.eval_expr(expr)?,
                    None => Value::Nil,
                };

                return Err(RuntimeError {
                    ty: RuntimeErrorType::Return(value),
                    token: keyword.clone(),
                });
            }
        }
        Ok(())
    }

    fn eval_expr(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        match expr {
            Expr::Literal(value) => Ok(value.clone()),
            Expr::Get { object, property } => {
                let object = self.eval_expr(object)?;
                if let Value::ClassInstance(object) = object {
                    ClassInstance::get_property(&object, &property.lexeme).ok_or_else(|| {
                        RuntimeError {
                            ty: RuntimeErrorType::UndefinedProperty,
                            token: property.clone(),
                        }
                    })
                } else {
                    Err(RuntimeError {
                        ty: RuntimeErrorType::PropertyAccessOnNonInstance,
                        token: property.clone(),
                    })
                }
            }
            Expr::Set {
                object,
                property,
                value,
            } => {
                if let Value::ClassInstance(object) = self.eval_expr(object)? {
                    let value = self.eval_expr(value)?;
                    object
                        .borrow_mut()
                        .set_property(property.lexeme.to_owned(), value.clone());
                    Ok(value)
                } else {
                    Err(RuntimeError {
                        ty: RuntimeErrorType::PropertyAccessOnNonInstance,
                        token: property.clone(),
                    })
                }
            }
            Expr::Unary { operator, expr } => self.eval_unary(operator, expr),
            Expr::Binary {
                operator,
                left,
                right,
            } => self.eval_binary(operator, left, right),
            Expr::Logical {
                operator,
                left,
                right,
            } => self.eval_logical(operator, left, right),
            Expr::Grouping(expr) => self.eval_expr(expr),
            Expr::Variable(variable) => self.look_up_variable(variable),
            Expr::This(this_variable) => self.look_up_variable(this_variable),
            Expr::Assignment { variable, value } => {
                let value = self.eval_expr(value)?;
                self.assign_to_variable(variable, value.clone())?;
                Ok(value)
            }
            Expr::FunctionCall {
                callee,
                arguments,
                opening_paren,
                ..
            } => self.eval_function_call(callee, arguments, opening_paren),
        }
    }

    fn eval_unary(&mut self, operator: &TokenInfo, expr: &Expr) -> Result<Value, RuntimeError> {
        let val = self.eval_expr(expr)?;
        Ok(match operator.token {
            Token::Minus => Value::Number(-convert_value_to_number(val, operator)?),
            Token::Bang => Value::Boolean(!val.is_truthy()),
            _ => panic!(
                "Interpreter bug, tried to evaluate {} as unary operator",
                operator
            ),
        })
    }

    fn eval_binary(
        &mut self,
        operator: &TokenInfo,
        left: &Expr,
        right: &Expr,
    ) -> Result<Value, RuntimeError> {
        let left = self.eval_expr(left)?;
        let right = self.eval_expr(right)?;

        Ok(match operator.token {
            Token::Plus => match (left, right) {
                (Value::Number(left), Value::Number(right)) => Value::Number(left + right),
                (Value::String(left), Value::String(right)) => {
                    let mut concat = left;
                    concat.push_str(&right);
                    Value::String(concat)
                }
                (left @ (Value::Number(_) | Value::String(_)), right) => {
                    return Err(RuntimeError {
                        ty: RuntimeErrorType::ExpectedDifferentType {
                            actual: right.value_type(),
                            expected: vec![left.value_type()],
                        },
                        token: operator.clone(),
                    })
                }
                (left, _) => {
                    return Err(RuntimeError {
                        ty: RuntimeErrorType::ExpectedDifferentType {
                            actual: left.value_type(),
                            expected: vec![ValueType::String, ValueType::Number],
                        },
                        token: operator.clone(),
                    })
                }
            },
            Token::Minus => Value::Number(
                convert_value_to_number(left, operator)?
                    - convert_value_to_number(right, operator)?,
            ),
            Token::Star => Value::Number(
                convert_value_to_number(left, operator)?
                    * convert_value_to_number(right, operator)?,
            ),
            Token::Slash => Value::Number(
                convert_value_to_number(left, operator)?
                    / convert_value_to_number(right, operator)?,
            ),
            Token::Greater => Value::Boolean(
                convert_value_to_number(left, operator)?
                    > convert_value_to_number(right, operator)?,
            ),
            Token::GreaterEqual => Value::Boolean(
                convert_value_to_number(left, operator)?
                    >= convert_value_to_number(right, operator)?,
            ),
            Token::Less => Value::Boolean(
                convert_value_to_number(left, operator)?
                    < convert_value_to_number(right, operator)?,
            ),
            Token::LessEqual => Value::Boolean(
                convert_value_to_number(left, operator)?
                    <= convert_value_to_number(right, operator)?,
            ),
            Token::EqualEqual => Value::Boolean(left == right),
            Token::BangEqual => Value::Boolean(left != right),
            _ => panic!(
                "Interpreter bug, tried to evaluate {} as binary operator",
                operator
            ),
        })
    }

    fn eval_logical(
        &mut self,
        operator: &TokenInfo,
        left: &Expr,
        right: &Expr,
    ) -> Result<Value, RuntimeError> {
        let left = self.eval_expr(left)?;
        match operator.token {
            Token::And => {
                if !left.is_truthy() {
                    return Ok(left);
                }
            }
            Token::Or => {
                if left.is_truthy() {
                    return Ok(left);
                }
            }
            _ => panic!(
                "Interpreter bug, tried to evaluate {} as logical operator",
                operator
            ),
        }

        self.eval_expr(right)
    }

    fn eval_function_call(
        &mut self,
        callee: &Expr,
        arguments: &[Expr],
        opening_paren: &TokenInfo,
    ) -> Result<Value, RuntimeError> {
        let callee = self.eval_expr(callee)?;
        let arguments = arguments
            .iter()
            .map(|arg| self.eval_expr(arg))
            .collect::<Result<_, _>>()?;

        match callee {
            Value::BuiltInFunction(function) => {
                self.call_function(&function, arguments, opening_paren)
            }
            Value::LoxFunction(function) => {
                self.call_function(function.deref(), arguments, opening_paren)
            }
            Value::LoxClass(class) => self.call_function(&class, arguments, opening_paren),
            _ => Err(RuntimeError {
                ty: RuntimeErrorType::TypeNotCallable(callee.value_type()),
                token: opening_paren.clone(),
            }),
        }
    }

    fn call_function<F: Callable>(
        &mut self,
        callee: &F,
        arguments: Vec<Value>,
        opening_paren: &TokenInfo,
    ) -> Result<Value, RuntimeError> {
        let num_args =
            u8::try_from(arguments.len()).expect("parser allows no more than 255 arguments");
        let arity = callee.arity();
        if num_args == arity {
            callee.call(self, arguments)
        } else {
            Err(RuntimeError {
                ty: RuntimeErrorType::IncorrectArgumentCount {
                    expected: arity,
                    actual: num_args,
                },
                token: opening_paren.clone(),
            })
        }
    }

    fn look_up_variable(&self, variable: &Variable) -> Result<Value, RuntimeError> {
        if let Some(depth) = variable.depth() {
            self.current_env
                .borrow()
                .get_variable_at(variable.name(), depth)
        } else {
            self.globals.borrow().get_variable(variable.name())
        }
    }

    fn assign_to_variable(
        &mut self,
        variable: &Variable,
        value: Value,
    ) -> Result<(), RuntimeError> {
        if let Some(depth) = variable.depth() {
            self.current_env
                .borrow_mut()
                .set_variable_at(variable.name(), depth, value)
        } else {
            self.globals
                .borrow_mut()
                .set_variable(variable.name(), value)
        }
    }
}

trait Callable {
    fn arity(&self) -> u8;
    fn call(
        &self,
        interpreter: &mut Interpreter,
        arguments: Vec<Value>,
    ) -> Result<Value, RuntimeError>;
}

impl Callable for BuiltInFunction {
    fn arity(&self) -> u8 {
        match self {
            Self::Clock => 0,
        }
    }

    fn call(
        &self,
        _interpreter: &mut Interpreter,
        _arguments: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        match self {
            Self::Clock => {
                let elapsed_secs = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .expect("the UNIX epoch will always be earlier than now")
                    .as_millis() as f64
                    / 1000.0;
                Ok(Value::Number(elapsed_secs))
            }
        }
    }
}

impl Callable for LoxFunction {
    fn arity(&self) -> u8 {
        u8::try_from(self.definition.parameters.len())
            .expect("parser will only allows declarations with at most 255 parameters")
    }

    fn call(
        &self,
        interpreter: &mut Interpreter,
        arguments: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        let arguments = self
            .definition
            .parameters
            .iter()
            .map(|token| token.lexeme.clone())
            .zip(arguments)
            .collect();

        let mut function_env = Rc::new(RefCell::new(Environment {
            variables: arguments,
            enclosing_env: Some(Rc::clone(&self.closure)),
        }));

        std::mem::swap(&mut interpreter.current_env, &mut function_env);
        let result = interpreter.eval_stmts(&self.definition.body);
        std::mem::swap(&mut interpreter.current_env, &mut function_env);

        match result {
            Ok(()) => Ok(Value::Nil),
            Err(err) => {
                if let RuntimeErrorType::Return(return_value) = err.ty {
                    Ok(return_value)
                } else {
                    Err(err)
                }
            }
        }
    }
}

impl Callable for Rc<LoxClass> {
    fn arity(&self) -> u8 {
        0
    }

    fn call(
        &self,
        _interpreter: &mut Interpreter,
        _arguments: Vec<Value>,
    ) -> Result<Value, RuntimeError> {
        Ok(Value::ClassInstance(Rc::new(RefCell::new(ClassInstance {
            properties: HashMap::new(),
            class: Rc::clone(self),
        }))))
    }
}

// TODO this struct should be private
#[derive(Debug)]
pub struct Environment {
    variables: HashMap<String, Value>,
    enclosing_env: Option<Rc<RefCell<Self>>>,
}

impl Environment {
    fn new_global(globals: HashMap<String, Value>) -> Self {
        Self {
            variables: globals,
            enclosing_env: None,
        }
    }

    fn new_inside(enclosing_env: Rc<RefCell<Self>>) -> Self {
        Self {
            variables: HashMap::new(),
            enclosing_env: Some(enclosing_env),
        }
    }

    fn define_variable(&mut self, name: String, value: Value) {
        self.variables.insert(name, value);
    }

    fn get_variable_at(&self, name: &TokenInfo, depth: usize) -> Result<Value, RuntimeError> {
        if depth == 0 {
            self.get_variable(name)
        } else {
            self.enclosing_env
                .as_ref()
                .expect("variable resolution guarantees there is an environment at the given depth")
                .borrow()
                .get_variable_at(name, depth - 1)
        }
    }

    fn get_variable(&self, name: &TokenInfo) -> Result<Value, RuntimeError> {
        self.variables
            .get(&name.lexeme)
            .cloned()
            .ok_or_else(|| RuntimeError {
                ty: RuntimeErrorType::UndefinedVariable,
                token: name.clone(),
            })
    }

    fn set_variable_at(
        &mut self,
        name: &TokenInfo,
        depth: usize,
        value: Value,
    ) -> Result<(), RuntimeError> {
        if depth == 0 {
            self.set_variable(name, value)
        } else {
            self.enclosing_env
                .as_mut()
                .expect("variable resolution guarantees there is an environment at the given depth")
                .borrow_mut()
                .set_variable_at(name, depth - 1, value)
        }
    }

    fn set_variable(&mut self, name: &TokenInfo, value: Value) -> Result<(), RuntimeError> {
        match self.variables.get_mut(&name.lexeme) {
            Some(variable) => {
                *variable = value;
                Ok(())
            }
            None => Err(RuntimeError {
                ty: RuntimeErrorType::UndefinedVariable,
                token: name.clone(),
            }),
        }
    }
}

pub fn bind_function(
    class: &Rc<RefCell<ClassInstance>>,
    function: &Rc<LoxFunction>,
) -> LoxFunction {
    let mut env = Environment::new_inside(Rc::clone(&function.closure));
    env.define_variable(String::from("this"), Value::ClassInstance(Rc::clone(class)));
    LoxFunction {
        definition: function.definition.clone(),
        closure: Rc::new(RefCell::new(env)),
    }
}
