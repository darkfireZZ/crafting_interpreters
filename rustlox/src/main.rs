use {
    crate::{
        eval::{Interpreter, RuntimeError},
        parser::Parser,
        scanner::Scanner,
    },
    std::{
        fmt::{self, Display},
        io::{self, Write},
        process::ExitCode,
    },
};

mod eval;
mod parser;
mod scanner;

#[derive(Debug)]
enum InterpreterError<'a> {
    RuntimeError(RuntimeError<'a>),
}

impl fmt::Display for InterpreterError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::RuntimeError(err) => err.fmt(f),
        }
    }
}

impl std::error::Error for InterpreterError<'_> {}

impl<'a> From<RuntimeError<'a>> for InterpreterError<'a> {
    fn from(err: RuntimeError<'a>) -> Self {
        Self::RuntimeError(err)
    }
}

#[derive(Debug)]
struct SourceError {
    ty: SourceErrorType,
    line: usize,
}

impl Display for SourceError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[line {}] Error: {}", self.line, self.ty)
    }
}

impl std::error::Error for SourceError {}

#[derive(Debug)]
enum SourceErrorType {
    UnexpectedCharacter(char),
    UnterminatedStringLiteral,
    UnterminatedMultilineComment,
}

impl Display for SourceErrorType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedCharacter(c) => {
                write!(f, "Unexpected character \"{}\"", c.escape_default())
            }
            Self::UnterminatedStringLiteral => {
                write!(f, "Unterminated string literal")
            }
            Self::UnterminatedMultilineComment => {
                write!(f, "Unterminated multiline comment")
            }
        }
    }
}

fn report_error(err: SourceError) {
    eprintln!("{}", err);
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

fn run<'a>(interpreter: &mut Interpreter, source: &'a str) -> Result<(), InterpreterError<'a>> {
    let scanner = Scanner::new(source);
    let mut parser = Parser::new(scanner);
    // TODO don't unwrap here
    let stmts = parser.parse().unwrap();
    interpreter.eval(&stmts).map_err(InterpreterError::from)
}
