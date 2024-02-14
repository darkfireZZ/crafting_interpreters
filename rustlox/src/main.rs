use std::{
    fmt::{self, Display},
    io::{self, Write},
    process::ExitCode,
};

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
enum Error {
    CliError,
    IoError(io::Error),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::CliError => write!(f, "Usage: rustlox [script]"),
            Self::IoError(io_err) => io_err.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Self::IoError(err)
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
        _ => Err(Error::CliError),
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

struct Scanner {}

impl Scanner {
    fn new(_source: &str) -> Self {
        unimplemented!()
    }
}

impl Iterator for Scanner {
    type Item = String;
    fn next(&mut self) -> Option<Self::Item> {
        unimplemented!()
    }
}
