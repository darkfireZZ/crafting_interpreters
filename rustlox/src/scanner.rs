use {
    crate::{SourceError, SourceErrorType},
    std::fmt::{self, Display},
};

#[derive(Debug)]
pub enum Token {
    // Single-character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    Identifier,
    String,
    Number(f64),

    // Keywords
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

#[derive(Debug)]
pub struct TokenInfo<'a> {
    token: Token,
    lexeme: &'a str,
    line: usize,
}

impl<'a> Display for TokenInfo<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} {} {}", self.token, self.lexeme, self.line)
    }
}

pub struct Scanner<'a> {
    source: &'a str,
    current_line: usize,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            current_line: 0,
        }
    }

    fn consume(&mut self, token: Token, length: usize) -> TokenInfo<'a> {
        let (lexeme, remainder) = self.source.split_at(length);

        self.source = remainder;

        TokenInfo {
            token,
            lexeme,
            line: self.current_line,
        }
    }

    fn consume_string_literal(&mut self) -> Result<TokenInfo<'a>, SourceError> {
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

        Err(SourceError {
            ty: SourceErrorType::UnterminatedStringLiteral,
            line: self.current_line,
        })
    }

    fn consume_number_literal(&mut self) -> TokenInfo<'a> {
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

        let number_value = self.source[..end_index]
            .parse()
            .expect("valid f64 string representation");

        self.consume(Token::Number(number_value), end_index)
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = TokenInfo<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(next_byte) = self.source.as_bytes().first() {
                match next_byte {
                    b'(' => return Some(self.consume(Token::LeftParen, 1)),
                    b')' => return Some(self.consume(Token::RightParen, 1)),
                    b'{' => return Some(self.consume(Token::LeftBrace, 1)),
                    b'}' => return Some(self.consume(Token::RightBrace, 1)),
                    b',' => return Some(self.consume(Token::Comma, 1)),
                    b'.' => return Some(self.consume(Token::Dot, 1)),
                    b'-' => return Some(self.consume(Token::Minus, 1)),
                    b'+' => return Some(self.consume(Token::Plus, 1)),
                    b';' => return Some(self.consume(Token::Semicolon, 1)),
                    b'*' => return Some(self.consume(Token::Star, 1)),
                    b'!' => {
                        return Some(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::BangEqual, 2)
                        } else {
                            self.consume(Token::Bang, 1)
                        })
                    }
                    b'=' => {
                        return Some(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::EqualEqual, 2)
                        } else {
                            self.consume(Token::Equal, 1)
                        })
                    }
                    b'<' => {
                        return Some(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::LessEqual, 2)
                        } else {
                            self.consume(Token::Less, 1)
                        })
                    }
                    b'>' => {
                        return Some(if self.source.as_bytes().get(1) == Some(&b'=') {
                            self.consume(Token::GreaterEqual, 2)
                        } else {
                            self.consume(Token::Greater, 1)
                        })
                    }
                    b'/' => {
                        if self.source.as_bytes().get(1) == Some(&b'/') {
                            let end_of_comment =
                                self.source.find('\n').unwrap_or(self.source.len());
                            self.source = &self.source[end_of_comment..];
                        } else {
                            return Some(self.consume(Token::Slash, 1));
                        }
                    }
                    b'"' => match self.consume_string_literal() {
                        Ok(token) => {
                            return Some(token);
                        }
                        Err(error) => crate::report_error(error),
                    },
                    digit if digit.is_ascii_digit() => return Some(self.consume_number_literal()),
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
                        let error = SourceError {
                            ty: SourceErrorType::UnexpectedCharacter(unexpected_char),
                            line: self.current_line,
                        };
                        crate::report_error(error);
                    }
                }
            } else {
                return None;
            }
        }
    }
}
