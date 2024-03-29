use {
    crate::{
        error_group::ErrorGroup,
        token::{Token, TokenInfo},
    },
    std::fmt::{self, Display},
};

pub fn tokenize(src: &str) -> Result<Tokenization, ErrorGroup<TokenizationError>> {
    let mut tokens = Vec::new();
    let mut errors = ErrorGroup::new();

    for result in Scanner::new(src) {
        match result {
            Ok(token) => tokens.push(token),
            Err(error) => errors.add(error),
        }
    }

    errors.error_or_else(|| Tokenization { tokens })
}

pub struct Tokenization {
    pub tokens: Vec<TokenInfo>,
}

fn is_identifier_start_char(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn identifier_or_keyword_to_token(identifier: &str) -> Token {
    match identifier {
        "and" => Token::And,
        "class" => Token::Class,
        "else" => Token::Else,
        "false" => Token::False,
        "for" => Token::For,
        "fun" => Token::Fun,
        "if" => Token::If,
        "nil" => Token::Nil,
        "or" => Token::Or,
        "print" => Token::Print,
        "return" => Token::Return,
        "super" => Token::Super,
        "this" => Token::This,
        "true" => Token::True,
        "var" => Token::Var,
        "while" => Token::While,
        _ => Token::Identifier,
    }
}

#[derive(Debug)]
struct Scanner<'a> {
    source: &'a str,
    current_line: usize,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            current_line: 1,
        }
    }

    fn consume(&mut self, token: Token, length: usize) -> TokenInfo {
        let (lexeme, remainder) = self.source.split_at(length);

        self.source = remainder;

        TokenInfo {
            token,
            lexeme: lexeme.to_owned(),
            line: self.current_line,
        }
    }

    fn consume_string_literal(&mut self) -> Result<TokenInfo, TokenizationError> {
        debug_assert_eq!(self.source.as_bytes()[0], b'"');

        // Already count opening and closing double quotes.
        let mut len = 2;
        for c in self.source[1..].chars() {
            if c == '\n' {
                self.current_line += 1;
            } else if c == '\"' {
                return Ok(self.consume(Token::String, len));
            }
            len += c.len_utf8();
        }

        // If the loop terminates, all characters in the source have been
        // consumed but no closing double quote was found.

        self.source = "";

        Err(TokenizationError {
            ty: TokenizationErrorType::UnterminatedStringLiteral,
            line: self.current_line,
        })
    }

    fn consume_number_literal(&mut self) -> TokenInfo {
        debug_assert!(self.source.as_bytes()[0].is_ascii_digit());

        let end_index = match self.source[1..]
            .find(|c: char| !c.is_ascii_digit())
            .map(|index| index + 1)
        {
            Some(index) => {
                if self.source.as_bytes()[index] == b'.'
                    && self
                        .source
                        .as_bytes()
                        .get(index + 1)
                        .is_some_and(u8::is_ascii_digit)
                {
                    self.source[index + 1..]
                        .find(|c: char| !c.is_ascii_digit())
                        .map(|end_index| end_index + index + 1)
                        .unwrap_or(self.source.len())
                } else {
                    index
                }
            }
            None => self.source.len(),
        };

        self.consume(Token::Number, end_index)
    }

    fn consume_identifier_or_keyword(&mut self) -> TokenInfo {
        debug_assert!(is_identifier_start_char(self.source.as_bytes()[0]));

        let end_index = 1 + self.source[1..]
            .as_bytes()
            .iter()
            .take_while(|c| c.is_ascii_alphanumeric() || **c == b'_')
            .count();
        let token = identifier_or_keyword_to_token(&self.source[..end_index]);
        self.consume(token, end_index)
    }

    fn consume_multiline_comment(&mut self) -> Result<(), TokenizationError> {
        debug_assert_eq!(self.source.as_bytes()[0], b'/');
        debug_assert_eq!(self.source.as_bytes()[1], b'*');

        let mut len = 2;

        let mut prev_is_star = false;
        for c in self.source[2..].as_bytes() {
            len += 1;
            match c {
                b'\n' => {
                    self.current_line += 1;
                    prev_is_star = false;
                }
                b'*' => {
                    prev_is_star = true;
                }
                b'/' if prev_is_star => {
                    self.source = &self.source[len..];
                    return Ok(());
                }
                _ => {
                    prev_is_star = false;
                }
            }
        }

        self.source = "";

        Err(TokenizationError {
            ty: TokenizationErrorType::UnterminatedMultilineComment,
            line: self.current_line,
        })
    }
}

impl Iterator for Scanner<'_> {
    type Item = Result<TokenInfo, TokenizationError>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(next_byte) = self.source.as_bytes().first() {
                match next_byte {
                    b'(' => return Some(Ok(self.consume(Token::LeftParen, 1))),
                    b')' => return Some(Ok(self.consume(Token::RightParen, 1))),
                    b'{' => return Some(Ok(self.consume(Token::LeftBrace, 1))),
                    b'}' => return Some(Ok(self.consume(Token::RightBrace, 1))),
                    b',' => return Some(Ok(self.consume(Token::Comma, 1))),
                    b'.' => return Some(Ok(self.consume(Token::Dot, 1))),
                    b'-' => return Some(Ok(self.consume(Token::Minus, 1))),
                    b'+' => return Some(Ok(self.consume(Token::Plus, 1))),
                    b';' => return Some(Ok(self.consume(Token::Semicolon, 1))),
                    b'*' => return Some(Ok(self.consume(Token::Star, 1))),
                    b'!' => {
                        return Some(Ok(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::BangEqual, 2)
                        } else {
                            self.consume(Token::Bang, 1)
                        }))
                    }
                    b'=' => {
                        return Some(Ok(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::EqualEqual, 2)
                        } else {
                            self.consume(Token::Equal, 1)
                        }))
                    }
                    b'<' => {
                        return Some(Ok(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::LessEqual, 2)
                        } else {
                            self.consume(Token::Less, 1)
                        }))
                    }
                    b'>' => {
                        return Some(Ok(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::GreaterEqual, 2)
                        } else {
                            self.consume(Token::Greater, 1)
                        }))
                    }
                    b'/' => match self.source.as_bytes().get(1) {
                        Some(&b'/') => {
                            let end_of_comment =
                                self.source.find('\n').unwrap_or(self.source.len());
                            self.source = &self.source[end_of_comment..];
                        }
                        Some(&b'*') => {
                            if let Err(error) = self.consume_multiline_comment() {
                                return Some(Err(error));
                            }
                        }
                        _ => return Some(Ok(self.consume(Token::Slash, 1))),
                    },
                    b'"' => return Some(self.consume_string_literal()),
                    digit if digit.is_ascii_digit() => {
                        return Some(Ok(self.consume_number_literal()))
                    }
                    c if is_identifier_start_char(*c) => {
                        return Some(Ok(self.consume_identifier_or_keyword()))
                    }
                    b'\n' => {
                        self.current_line += 1;
                        self.source = &self.source[1..];
                    }
                    b' ' | b'\r' | b'\t' => {
                        self.source = &self.source[1..];
                    }
                    _ => {
                        let unexpected_char =
                            self.source.chars().next().expect("source is non-empty");
                        self.source = &self.source[unexpected_char.len_utf8()..];
                        return Some(Err(TokenizationError {
                            ty: TokenizationErrorType::UnexpectedCharacter(unexpected_char),
                            line: self.current_line,
                        }));
                    }
                }
            } else {
                return None;
            }
        }
    }
}

#[derive(Debug)]
pub struct TokenizationError {
    ty: TokenizationErrorType,
    line: usize,
}

impl Display for TokenizationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[line {}] Error: {}", self.line, self.ty)
    }
}

impl std::error::Error for TokenizationError {}

#[derive(Debug)]
enum TokenizationErrorType {
    UnexpectedCharacter(char),
    UnterminatedStringLiteral,
    UnterminatedMultilineComment,
}

impl Display for TokenizationErrorType {
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
