//! The WebIDL tokenizer, WebIDL §2 "Interface definition language", the
//! list of tokens: `integer`, `decimal`, `identifier`, `string`, `whitespace`,
//! `comment` and `other`.
//!
//! Whitespace and comments are dropped. Keywords are identifiers here; the
//! parser tells them apart (a keyword is an identifier the grammar spells as
//! a terminal, WebIDL §2, and an identifier written with a leading `_` is
//! never a keyword).

/// A token.
#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    /// `identifier` (and the keywords), without a leading `_`. `-Infinity`
    /// is one token, as the grammar has it as a terminal.
    Ident {
        /// The text.
        name: String,
        /// Written with a leading `_`.
        escaped: bool,
    },
    /// `integer`, as written.
    Integer(String),
    /// `decimal`, as written.
    Decimal(String),
    /// `string`, without the quotes.
    Str(String),
    /// `...`.
    Ellipsis,
    /// `other`: any one other character.
    Punct(char),
}

/// A token and the line it starts on (from 1).
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// The token.
    pub tok: Tok,
    /// Its line.
    pub line: u32,
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic()
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '-'
}

struct Lexer {
    chars: Vec<char>,
    pos: usize,
    line: u32,
}

impl Lexer {
    fn at(&self, n: usize) -> Option<char> {
        self.chars.get(self.pos.saturating_add(n)).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.at(0)?;
        self.pos = self.pos.saturating_add(1);
        if c == '\n' {
            self.line = self.line.saturating_add(1);
        }
        Some(c)
    }

    fn starts_with(&self, s: &str) -> bool {
        s.chars().enumerate().all(|(i, c)| self.at(i) == Some(c))
    }

    fn take_while(&mut self, f: impl Fn(char) -> bool) -> String {
        let mut s = String::new();
        while let Some(c) = self.at(0).filter(|&c| f(c)) {
            s.push(c);
            self.bump();
        }
        s
    }

    /// `integer` or `decimal`, at a digit, a `.` before a digit, or a `-`
    /// before either.
    fn number(&mut self) -> Tok {
        let mut s = String::new();
        if self.at(0) == Some('-') {
            s.push('-');
            self.bump();
        }
        if self.at(0) == Some('0') && matches!(self.at(1), Some('x' | 'X')) {
            s.push_str(&self.take_while(|c| c == '0'));
            if let Some(x) = self.bump() {
                s.push(x);
            }
            s.push_str(&self.take_while(|c| c.is_ascii_hexdigit()));
            return Tok::Integer(s);
        }
        s.push_str(&self.take_while(|c| c.is_ascii_digit()));
        let mut decimal = false;
        if self.at(0) == Some('.') {
            decimal = true;
            s.push('.');
            self.bump();
            s.push_str(&self.take_while(|c| c.is_ascii_digit()));
        }
        let exp_digit = |l: &Self, n: usize| l.at(n).is_some_and(|c| c.is_ascii_digit());
        if matches!(self.at(0), Some('e' | 'E')) {
            let signed = matches!(self.at(1), Some('+' | '-'));
            if exp_digit(self, if signed { 2 } else { 1 }) {
                decimal = true;
                if let Some(e) = self.bump() {
                    s.push(e);
                }
                if signed && let Some(sign) = self.bump() {
                    s.push(sign);
                }
                s.push_str(&self.take_while(|c| c.is_ascii_digit()));
            }
        }
        if decimal {
            Tok::Decimal(s)
        } else {
            Tok::Integer(s)
        }
    }
}

/// Tokenize `src`.
pub fn lex(src: &str) -> Result<Vec<Token>, String> {
    let mut l = Lexer {
        chars: src.chars().collect(),
        pos: 0,
        line: 1,
    };
    let mut out = Vec::new();
    while let Some(c) = l.at(0) {
        let line = l.line;
        if matches!(c, '\t' | '\n' | '\r' | ' ') {
            l.bump();
            continue;
        }
        if l.starts_with("//") {
            l.take_while(|c| c != '\n');
            continue;
        }
        if l.starts_with("/*") {
            l.bump();
            l.bump();
            loop {
                if l.starts_with("*/") {
                    l.bump();
                    l.bump();
                    break;
                }
                if l.bump().is_none() {
                    return Err(format!("{line}: unterminated comment"));
                }
            }
            continue;
        }
        let tok = if c == '"' {
            l.bump();
            let s = l.take_while(|c| c != '"');
            if l.bump().is_none() {
                return Err(format!("{line}: unterminated string"));
            }
            Tok::Str(s)
        } else if c.is_ascii_digit()
            || (c == '.' && l.at(1).is_some_and(|d| d.is_ascii_digit()))
            || (c == '-' && l.at(1).is_some_and(|d| d.is_ascii_digit()))
            || (c == '-' && l.at(1) == Some('.') && l.at(2).is_some_and(|d| d.is_ascii_digit()))
        {
            l.number()
        } else if l.starts_with("...") {
            l.bump();
            l.bump();
            l.bump();
            Tok::Ellipsis
        } else if l.starts_with("-Infinity") && !l.at(9).is_some_and(is_ident_char) {
            for _ in 0..9 {
                l.bump();
            }
            Tok::Ident {
                name: "-Infinity".to_owned(),
                escaped: false,
            }
        } else if is_ident_start(c) || (c == '_' && l.at(1).is_some_and(is_ident_start)) {
            let escaped = c == '_';
            if escaped {
                l.bump();
            }
            let name = l.take_while(is_ident_char);
            Tok::Ident { name, escaped }
        } else {
            l.bump();
            Tok::Punct(c)
        };
        out.push(Token { tok, line });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Tok> {
        lex(s)
            .unwrap_or_default()
            .into_iter()
            .map(|t| t.tok)
            .collect()
    }

    fn id(s: &str) -> Tok {
        Tok::Ident {
            name: s.to_owned(),
            escaped: false,
        }
    }

    #[test]
    fn numbers() {
        assert_eq!(
            toks("1 -2 0x1F 0 1.5 -.5 5. 1e3 2E-2 .5e+1"),
            vec![
                Tok::Integer("1".into()),
                Tok::Integer("-2".into()),
                Tok::Integer("0x1F".into()),
                Tok::Integer("0".into()),
                Tok::Decimal("1.5".into()),
                Tok::Decimal("-.5".into()),
                Tok::Decimal("5.".into()),
                Tok::Decimal("1e3".into()),
                Tok::Decimal("2E-2".into()),
                Tok::Decimal(".5e+1".into()),
            ]
        );
    }

    #[test]
    fn infinity_ellipsis_and_identifiers() {
        assert_eq!(
            toks("-Infinity Infinity -x ... . _interface a-b _x"),
            vec![
                id("-Infinity"),
                id("Infinity"),
                Tok::Punct('-'),
                id("x"),
                Tok::Ellipsis,
                Tok::Punct('.'),
                Tok::Ident {
                    name: "interface".into(),
                    escaped: true
                },
                id("a-b"),
                Tok::Ident {
                    name: "x".into(),
                    escaped: true
                },
            ]
        );
    }

    #[test]
    fn comments_strings_and_lines() {
        let t = lex("// a\n/* b\n c */ \"d e\" ;").unwrap_or_default();
        assert_eq!(
            t,
            vec![
                Token {
                    tok: Tok::Str("d e".into()),
                    line: 3
                },
                Token {
                    tok: Tok::Punct(';'),
                    line: 3
                },
            ]
        );
        assert!(lex("/* x").is_err());
        assert!(lex("\"x").is_err());
    }
}
