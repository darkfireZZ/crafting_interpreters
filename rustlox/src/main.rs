use {
    crate::{
        error_group::ErrorGroup,
        eval::{Interpreter, RuntimeError},
        parser::ParseError,
        resolver::ResolutionError,
        scanner::TokenizationError,
    },
    std::{
        fmt::{self, Display},
        io::{self, Write},
        process::ExitCode,
    },
};

mod error_group;

mod eval;
mod parser;
mod resolver;
mod scanner;

mod data_types;
mod syntax_tree;
mod token;

#[derive(Debug)]
enum InterpreterError {
    Tokenization(ErrorGroup<TokenizationError>),
    Parsing(ErrorGroup<ParseError>),
    Resolution(ResolutionError),
    Runtime(RuntimeError),
}

impl Display for InterpreterError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Tokenization(err) => err.fmt(f),
            Self::Parsing(err) => err.fmt(f),
            Self::Resolution(err) => err.fmt(f),
            Self::Runtime(err) => err.fmt(f),
        }
    }
}

impl From<ErrorGroup<TokenizationError>> for InterpreterError {
    fn from(errors: ErrorGroup<TokenizationError>) -> Self {
        Self::Tokenization(errors)
    }
}

impl From<ErrorGroup<ParseError>> for InterpreterError {
    fn from(errors: ErrorGroup<ParseError>) -> Self {
        Self::Parsing(errors)
    }
}
impl From<ResolutionError> for InterpreterError {
    fn from(err: ResolutionError) -> Self {
        Self::Resolution(err)
    }
}

impl From<RuntimeError> for InterpreterError {
    fn from(err: RuntimeError) -> Self {
        Self::Runtime(err)
    }
}

fn main() -> ExitCode {
    let args = std::env::args();

    let result = match args.len() {
        1 => run_prompt(),
        2 => {
            let script_name = args
                .into_iter()
                .nth(1)
                .expect("There is exactly 1 argument");
            run_file(&script_name)
        }
        _ => {
            eprintln!("Usage: rustlox [script]");
            std::process::exit(1);
        }
    };

    match result {
        Ok(_) => ExitCode::from(0),
        Err(err) => {
            eprintln!("{}", err);
            ExitCode::from(1)
        }
    }
}

const PROMPT_SYMBOL: &str = "> ";
fn run_prompt() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut stderr = io::stderr();
    let mut buffer = String::new();

    let mut interpreter = Interpreter::new();

    loop {
        write!(stdout, "{}", PROMPT_SYMBOL)?;
        stdout.flush()?;

        if stdin.read_line(&mut buffer)? == 0 {
            return Ok(());
        }

        if let Err(err) = run(&mut interpreter, &buffer) {
            writeln!(stderr, "{}", err)?;
        }

        buffer.clear();
    }
}

fn run_file(script_name: &str) -> io::Result<()> {
    let script = std::fs::read_to_string(script_name)?;
    let mut interpreter = Interpreter::new();
    if let Err(err) = run(&mut interpreter, &script) {
        writeln!(io::stderr(), "{}", err)?;
    }
    Ok(())
}

fn run(interpreter: &mut Interpreter, source: &str) -> Result<(), InterpreterError> {
    let tokens = scanner::tokenize(source)?;
    let mut syntax_tree = parser::parse(tokens)?;
    resolver::resolve(&mut syntax_tree)?;
    interpreter.eval(&syntax_tree)?;
    Ok(())
}
