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
    Identifier(String),
    String(String),
    Number(String),

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
                            line: self.current_line,
                            ty: SourceErrorType::UnexpectedCharacter(unexpected_char),
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
