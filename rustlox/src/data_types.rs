use {
    crate::{
        // TODO ideally, there should be no reference to eval in this module
        eval::Environment,
        syntax_tree::Stmt,
        token::TokenInfo,
    },
    std::{
        cell::RefCell,
        fmt::{self, Display},
        rc::Rc,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueType {
    Nil,
    Boolean,
    Number,
    String,
    BuiltInFunction,
    LoxFunction,
}

impl ValueType {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Nil => "nil",
            Self::Boolean => "boolean",
            Self::Number => "number",
            Self::String => "string",
            Self::BuiltInFunction => "built-in function",
            Self::LoxFunction => "function",
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
    LoxFunction(Rc<LoxFunction>),
}

impl Value {
    pub fn value_type(&self) -> ValueType {
        match self {
            Self::Nil => ValueType::Nil,
            Self::Boolean(_) => ValueType::Boolean,
            Self::Number(_) => ValueType::Number,
            Self::String(_) => ValueType::String,
            Self::BuiltInFunction(_) => ValueType::BuiltInFunction,
            Self::LoxFunction(_) => ValueType::LoxFunction,
        }
    }

    pub fn is_truthy(&self) -> bool {
        !matches!(self, Self::Nil | Self::Boolean(false))
    }

    pub fn convert_to_number(&self) -> Option<f64> {
        match self {
            Self::Number(val) => Some(*val),
            _ => None,
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
            Self::LoxFunction(function) => write!(f, "<fn {} >", function.name),
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum BuiltInFunction {
    Clock,
}

impl Display for BuiltInFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Clock => write!(f, "clock"),
        }
    }
}

#[derive(Debug)]
pub struct LoxFunction {
    pub name: TokenInfo,
    pub parameters: Vec<TokenInfo>,
    pub body: Vec<Stmt>,
    pub closure: Rc<RefCell<Environment>>,
}

impl PartialEq for LoxFunction {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for LoxFunction {}
