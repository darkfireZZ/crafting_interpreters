use {
    crate::{
        parser::{Expr, Stmt},
        scanner::{Token, TokenInfo},
    },
    std::fmt::{self, Display},
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
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueType {
    Nil,
    Boolean,
    Number,
    String,
}

impl ValueType {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Nil => "nil",
            Self::Boolean => "boolean",
            Self::Number => "number",
            Self::String => "string",
        }
    }
}

impl Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Nil,
    Boolean(bool),
    Number(f64),
    String(String),
}

impl Value {
    fn value_type(&self) -> ValueType {
        match self {
            Self::Nil => ValueType::Nil,
            Self::Boolean(_) => ValueType::Boolean,
            Self::Number(_) => ValueType::Number,
            Self::String(_) => ValueType::String,
        }
    }

    fn convert_to_boolean(&self) -> bool {
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
        }
    }
}

pub fn eval<'a>(program: &[Stmt<'a>]) -> Result<(), RuntimeError<'a>> {
    for stmt in program {
        eval_stmt(stmt)?;
    }
    Ok(())
}

fn eval_stmt<'a>(stmt: &Stmt<'a>) -> Result<(), RuntimeError<'a>> {
    match stmt {
        Stmt::Print(expr) => {
            // TODO: What if writing to stdout fails
            println!("{}", eval_expr(expr)?);
        },
        Stmt::Expr(expr) => { eval_expr(expr)?; },
    }
    Ok(())
}

fn eval_expr<'a>(expr: &Expr<'a>) -> Result<Value, RuntimeError<'a>> {
    match expr {
        Expr::Literal { literal } => Ok(eval_literal(literal)),
        Expr::Unary { operator, expr } => eval_unary(operator, expr),
        Expr::Binary {
            operator,
            left,
            right,
        } => eval_binary(operator, left, right),
        Expr::Grouping { expr } => eval_expr(expr),
    }
}

fn eval_literal(literal: &TokenInfo<'_>) -> Value {
    match literal.token {
        Token::Nil => Value::Nil,
        Token::True => Value::Boolean(true),
        Token::False => Value::Boolean(false),
        Token::Number(val) => Value::Number(val),
        Token::String => Value::String(literal.lexeme[1..literal.lexeme.len() - 1].to_owned()),
        _ => panic!(
            "Interpreter bug, tried to evaluate {} as a literal",
            literal
        ),
    }
}

fn eval_unary<'a>(operator: &TokenInfo<'a>, expr: &Expr<'a>) -> Result<Value, RuntimeError<'a>> {
    let val = eval_expr(expr)?;
    Ok(match operator.token {
        Token::Minus => Value::Number(-val.convert_to_number(operator)?),
        Token::Bang => Value::Boolean(!val.convert_to_boolean()),
        _ => panic!(
            "Interpreter bug, tried to evaluate {} as unary operator",
            operator
        ),
    })
}

fn eval_binary<'a>(
    operator: &TokenInfo<'a>,
    left: &Expr<'a>,
    right: &Expr<'a>,
) -> Result<Value, RuntimeError<'a>> {
    let left = eval_expr(left)?;
    let right = eval_expr(right)?;

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
        Token::Minus => {
            Value::Number(left.convert_to_number(operator)? - right.convert_to_number(operator)?)
        }
        Token::Star => {
            Value::Number(left.convert_to_number(operator)? * right.convert_to_number(operator)?)
        }
        Token::Slash => {
            Value::Number(left.convert_to_number(operator)? / right.convert_to_number(operator)?)
        }
        Token::Greater => {
            Value::Boolean(left.convert_to_number(operator)? > right.convert_to_number(operator)?)
        }
        Token::GreaterEqual => {
            Value::Boolean(left.convert_to_number(operator)? >= right.convert_to_number(operator)?)
        }
        Token::Less => {
            Value::Boolean(left.convert_to_number(operator)? < right.convert_to_number(operator)?)
        }
        Token::LessEqual => {
            Value::Boolean(left.convert_to_number(operator)? <= right.convert_to_number(operator)?)
        }
        Token::EqualEqual => Value::Boolean(left == right),
        Token::BangEqual => Value::Boolean(left != right),
        _ => panic!(
            "Interpreter bug, tried to evaluate {} as binary operator",
            operator
        ),
    })
}
