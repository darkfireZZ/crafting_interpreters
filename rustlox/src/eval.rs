use {
    crate::{
        parser::{Expr, Stmt},
        scanner::{Token, TokenInfo},
    },
    std::{
        collections::HashMap,
        fmt::{self, Display},
        time::{SystemTime, UNIX_EPOCH},
    },
};

#[derive(Debug)]
pub struct RuntimeError<'a> {
    ty: RuntimeErrorType,
    token: TokenInfo<'a>,
}

impl Display for RuntimeError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[line {}] Runtime error: {}", self.token.line, self.ty)
    }
}

impl std::error::Error for RuntimeError<'_> {}

#[derive(Debug)]
enum RuntimeErrorType {
    ExpectedDifferentType {
        expected: Vec<ValueType>,
        actual: ValueType,
    },
    IncorrectArgumentCount {
        expected: u8,
        actual: u8
    },
    TypeNotCallable(ValueType),
    UndefinedVariable,
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
            Self::IncorrectArgumentCount { expected, actual } => write!(f, "Expected {expected} arguments, but got {actual}"),
            Self::TypeNotCallable(ty) => write!(f, "{ty} is not callable"),
            Self::UndefinedVariable => write!(f, "Undefined variable"),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueType {
    Nil,
    Boolean,
    Number,
    String,
    BuiltInFunction,
}

impl ValueType {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Nil => "nil",
            Self::Boolean => "boolean",
            Self::Number => "number",
            Self::String => "string",
            Self::BuiltInFunction => "built-in function",
        }
    }
}

impl Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Nil,
    Boolean(bool),
    Number(f64),
    String(String),
    BuiltInFunction(BuiltInFunction),
}

impl Value {
    fn value_type(&self) -> ValueType {
        match self {
            Self::Nil => ValueType::Nil,
            Self::Boolean(_) => ValueType::Boolean,
            Self::Number(_) => ValueType::Number,
            Self::String(_) => ValueType::String,
            Self::BuiltInFunction(_) => ValueType::BuiltInFunction,
        }
    }

    fn is_truthy(&self) -> bool {
        !matches!(self, Self::Nil | Self::Boolean(false))
    }

    fn convert_to_number<'a>(&self, error_token: &TokenInfo<'a>) -> Result<f64, RuntimeError<'a>> {
        match self {
            Self::Number(val) => Ok(*val),
            _ => Err(RuntimeError {
                ty: RuntimeErrorType::ExpectedDifferentType {
                    actual: self.value_type(),
                    expected: vec![ValueType::Number],
                },
                token: *error_token,
            }),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Boolean(val) => val.fmt(f),
            Self::Number(val) => val.fmt(f),
            Self::String(val) => val.fmt(f),
            Self::BuiltInFunction(function) => write!(f, "<built-in function \"{}\">", function),
        }
    }
}

#[derive(Debug)]
pub struct Interpreter {
    environments: Vec<HashMap<String, Value>>,
}

impl Interpreter {
    pub fn new() -> Self {
        // TODO: ideally this should be put in a macro
        let globals = [
            (String::from("clock"), Value::BuiltInFunction(BuiltInFunction::Clock)),
        ];
        Self {
            environments: vec![HashMap::from(globals)],
        }
    }

    pub fn eval<'a>(&mut self, program: &[Stmt<'a>]) -> Result<(), RuntimeError<'a>> {
        for stmt in program {
            self.eval_stmt(stmt)?;
        }
        Ok(())
    }

    fn eval_stmt<'a>(&mut self, stmt: &Stmt<'a>) -> Result<(), RuntimeError<'a>> {
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
                self.define_variable(name.lexeme.to_owned(), initializer);
            }
            Stmt::Block(stmts) => {
                self.environments.push(HashMap::new());
                let result = self.eval(stmts);
                self.environments.pop().expect("is local environment");
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
        }
        Ok(())
    }

    fn eval_expr<'a>(&mut self, expr: &Expr<'a>) -> Result<Value, RuntimeError<'a>> {
        match expr {
            Expr::Literal(value) => Ok(value.clone()),
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
            Expr::Variable { name } => self.get_variable(name),
            Expr::Assignment { name, value } => {
                let value = self.eval_expr(value)?;
                self.set_variable(name, value.clone())?;
                Ok(value)
            }
            Expr::FunctionCall { callee, arguments, opening_paren, .. } => self.eval_function_call(callee, arguments, *opening_paren)
        }
    }

    fn eval_unary<'a>(
        &mut self,
        operator: &TokenInfo<'a>,
        expr: &Expr<'a>,
    ) -> Result<Value, RuntimeError<'a>> {
        let val = self.eval_expr(expr)?;
        Ok(match operator.token {
            Token::Minus => Value::Number(-val.convert_to_number(operator)?),
            Token::Bang => Value::Boolean(!val.is_truthy()),
            _ => panic!(
                "Interpreter bug, tried to evaluate {} as unary operator",
                operator
            ),
        })
    }

    fn eval_binary<'a>(
        &mut self,
        operator: &TokenInfo<'a>,
        left: &Expr<'a>,
        right: &Expr<'a>,
    ) -> Result<Value, RuntimeError<'a>> {
        let left = self.eval_expr(left)?;
        let right = self.eval_expr(right)?;

        Ok(match operator.token {
            Token::Plus => match (&left, &right) {
                (Value::Number(left), Value::Number(right)) => Value::Number(left + right),
                (Value::String(left), Value::String(right)) => {
                    let mut concat = left.to_owned();
                    concat.push_str(right);
                    Value::String(concat)
                }
                (Value::Number(_) | Value::String(_), _) => {
                    return Err(RuntimeError {
                        ty: RuntimeErrorType::ExpectedDifferentType {
                            actual: right.value_type(),
                            expected: vec![left.value_type()],
                        },
                        token: *operator,
                    })
                }
                _ => {
                    return Err(RuntimeError {
                        ty: RuntimeErrorType::ExpectedDifferentType {
                            actual: left.value_type(),
                            expected: vec![ValueType::String, ValueType::Number],
                        },
                        token: *operator,
                    })
                }
            },
            Token::Minus => Value::Number(
                left.convert_to_number(operator)? - right.convert_to_number(operator)?,
            ),
            Token::Star => Value::Number(
                left.convert_to_number(operator)? * right.convert_to_number(operator)?,
            ),
            Token::Slash => Value::Number(
                left.convert_to_number(operator)? / right.convert_to_number(operator)?,
            ),
            Token::Greater => Value::Boolean(
                left.convert_to_number(operator)? > right.convert_to_number(operator)?,
            ),
            Token::GreaterEqual => Value::Boolean(
                left.convert_to_number(operator)? >= right.convert_to_number(operator)?,
            ),
            Token::Less => Value::Boolean(
                left.convert_to_number(operator)? < right.convert_to_number(operator)?,
            ),
            Token::LessEqual => Value::Boolean(
                left.convert_to_number(operator)? <= right.convert_to_number(operator)?,
            ),
            Token::EqualEqual => Value::Boolean(left == right),
            Token::BangEqual => Value::Boolean(left != right),
            _ => panic!(
                "Interpreter bug, tried to evaluate {} as binary operator",
                operator
            ),
        })
    }

    fn eval_logical<'a>(
        &mut self,
        operator: &TokenInfo<'a>,
        left: &Expr<'a>,
        right: &Expr<'a>,
    ) -> Result<Value, RuntimeError<'a>> {
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

    fn eval_function_call<'a>(&mut self, callee: &Expr<'a>, arguments: &[Expr<'a>], opening_paren: TokenInfo<'a>) -> Result<Value, RuntimeError<'a>> {
        let callee = self.eval_expr(callee)?;
        let arguments: Vec<_> = arguments.iter().map(|arg| self.eval_expr(arg)).collect::<Result<_, _>>()?;

        match callee {
            Value::BuiltInFunction(function) => self.call_function(function, arguments, opening_paren),
            _ => Err(RuntimeError {
                ty: RuntimeErrorType::TypeNotCallable(callee.value_type()),
                token: opening_paren,
            })
        }
    }

    fn call_function<'a, F: Callable>(&mut self, callee: F, arguments: Vec<Value>, opening_paren: TokenInfo<'a>) -> Result<Value, RuntimeError<'a>> {
        let num_args = u8::try_from(arguments.len()).expect("parser allows no more than 255 arguments");
        let arity = callee.arity();
        if num_args == arity {
            callee.call(self, arguments)
        } else {
            Err(RuntimeError {
                ty: RuntimeErrorType::IncorrectArgumentCount { expected: arity, actual: num_args },
                token: opening_paren,
            })
        }
    }

    fn define_variable(&mut self, name: String, value: Value) {
        let last_index = self.environments.len() - 1;
        self.environments.get_mut(last_index).expect("global environment is always defined").insert(name, value);
    }

    fn get_variable<'a>(&self, name: &TokenInfo<'a>) -> Result<Value, RuntimeError<'a>> {
        // TODO: Cloning is not optimal, it would probably be possible to use a Cow here
        self.environments.iter().rev().find_map(|env| env.get(name.lexeme)).cloned().ok_or(
            RuntimeError {
                ty: RuntimeErrorType::UndefinedVariable,
                token: *name,
            }
        )
    }

    fn set_variable<'a>(&mut self, name: &TokenInfo<'a>, value: Value) -> Result<(), RuntimeError<'a>> {
        let variable_ref = self.environments.iter_mut().rev().find_map(|env| env.get_mut(name.lexeme)).ok_or(RuntimeError {
            ty: RuntimeErrorType::UndefinedVariable,
            token: *name,
        })?;
        *variable_ref = value;
        Ok(())
    }
}

trait Callable {
    fn arity(&self) -> u8;
    fn call(&self, interpreter: &mut Interpreter, arguments: Vec<Value>) -> Result<Value, RuntimeError<'static>>;
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum BuiltInFunction {
    Clock,
}

impl Callable for BuiltInFunction {
    fn arity(&self) -> u8 {
        match self {
            Self::Clock => 0,
        }
    }

    fn call(&self, _interpreter: &mut Interpreter, _arguments: Vec<Value>) -> Result<Value, RuntimeError<'static>> {
        match self {
            Self::Clock => {
                let elapsed_secs = SystemTime::now().duration_since(UNIX_EPOCH).expect("the UNIX epoch will always be earlier than now").as_millis() as f64 / 1000.0;
                Ok(Value::Number(elapsed_secs))
            },
        }
    }
}

impl Display for BuiltInFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Clock => write!(f, "clock"),
        }
    }
}
