use {
    crate::{
        // TODO ideally, there should be no reference to eval in this module
        eval::{self, Environment},
        syntax_tree::{ClassDefinition, FunctionDefinition},
    },
    std::{
        cell::RefCell,
        collections::HashMap,
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
    LoxClass,
    ClassInstance,
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
            Self::LoxClass => "class",
            Self::ClassInstance => "class instance",
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
    LoxClass(Rc<LoxClass>),
    ClassInstance(Rc<RefCell<ClassInstance>>),
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
            Self::LoxClass(_) => ValueType::LoxClass,
            Self::ClassInstance(_) => ValueType::ClassInstance,
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
            Self::BuiltInFunction(function) => write!(f, "<built-in fn {}>", function),
            Self::LoxFunction(function) => write!(f, "<fn {}>", function.definition.name.lexeme),
            Self::LoxClass(class) => write!(f, "<class {}>", class.definition.name.lexeme),
            Self::ClassInstance(instance) => {
                write!(
                    f,
                    "<{} instance>",
                    instance.borrow().class.definition.name.lexeme
                )
            }
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
    pub definition: FunctionDefinition,
    pub is_constructor: bool,
    pub closure: Rc<RefCell<Environment>>,
}

// TODO: This equality operation doesn't work correctly on bound functions
impl PartialEq for LoxFunction {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for LoxFunction {}

#[derive(Debug)]
pub struct LoxClass {
    pub name: String,
    pub methods: HashMap<String, Rc<LoxFunction>>,
    pub superclass: Option<Rc<LoxClass>>,
    pub definition: ClassDefinition,
}

impl LoxClass {
    fn get_method(&self, method_name: &str) -> Option<&Rc<LoxFunction>> {
        self.methods.get(method_name).or_else(|| {
            self.superclass
                .as_ref()
                .and_then(|superclass| superclass.get_method(method_name))
        })
    }
}

impl PartialEq for LoxClass {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for LoxClass {}

#[derive(Clone, Debug)]
pub struct ClassInstance {
    pub class: Rc<LoxClass>,
    pub properties: HashMap<String, Value>,
}

impl ClassInstance {
    pub fn get_property(this: &Rc<RefCell<ClassInstance>>, property_name: &str) -> Option<Value> {
        this.borrow()
            .properties
            .get(property_name)
            .cloned()
            .or_else(|| {
                Self::get_method(this, property_name)
                    .map(|method| Value::LoxFunction(Rc::new(method)))
            })
    }

    pub fn get_method(this: &Rc<RefCell<ClassInstance>>, method_name: &str) -> Option<LoxFunction> {
        this.borrow()
            .class
            .get_method(method_name)
            .map(|method| eval::bind_function(this, method))
    }

    pub fn set_property(&mut self, property_name: String, value: Value) {
        self.properties.insert(property_name, value);
    }
}

impl PartialEq for ClassInstance {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for ClassInstance {}
