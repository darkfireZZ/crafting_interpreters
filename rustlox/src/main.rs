use {
    crate::scanner::Scanner,
    std::{
        fmt::{self, Display},
        io::{self, Write},
        process::ExitCode,
    },
};

mod scanner;

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
enum Error {
    Cli,
    Io(io::Error),
    Source(SourceError),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Cli => write!(f, "Usage: rustlox [script]"),
            Self::Io(io_err) => io_err.fmt(f),
            Self::Source(src_err) => src_err.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
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
        _ => Err(Error::Cli),
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
fn run_prompt() -> Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut buffer = String::new();

    loop {
        write!(stdout, "{}", PROMPT_SYMBOL)?;
        stdout.flush()?;

        if stdin.read_line(&mut buffer)? == 0 {
            return Ok(());
        }

        // TODO: Don't exit on source error
        run(&buffer)?;

        buffer.clear();
    }
}

fn run_file(script_name: &str) -> Result<()> {
    let script = std::fs::read_to_string(script_name)?;
    run(&script)
}

fn run(source: &str) -> Result<()> {
    for token in Scanner::new(source) {
        println!("{}", token);
    }

    Ok(())
}
