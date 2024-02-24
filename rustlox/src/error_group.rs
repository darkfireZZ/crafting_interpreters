use std::fmt::{self, Display};

#[derive(Clone, Debug)]
pub struct ErrorGroup<Error: Display> {
    errors: Vec<Error>,
}

impl<Error: Display> ErrorGroup<Error> {
    pub fn new() -> Self {
        Self { errors: Vec::new() }
    }

    pub fn add(&mut self, error: Error) {
        self.errors.push(error)
    }

    pub fn error_or_else<F: FnOnce() -> T, T>(self, or_else: F) -> Result<T, Self> {
        if self.errors.is_empty() {
            Ok(or_else())
        } else {
            Err(self)
        }
    }
}

impl<Error: Display> Display for ErrorGroup<Error> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in &self.errors {
            writeln!(f, "{}", error)?;
        }
        Ok(())
    }
}
