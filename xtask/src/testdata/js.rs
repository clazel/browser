//! Just enough JavaScript to read the literal tables in WPT test files:
//! `null`, numbers, strings, arrays and object literals with identifier or
//! string keys.
//! Anything else is an error, so a changed upstream file fails loudly
//! instead of being half-read.

/// A literal, with the 1-based line it starts on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub line: usize,
    pub lit: Lit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit {
    Null,
    Bool(bool),
    Num(u64),
    /// A string as JavaScript sees it: UTF-16 code units.
    Str(Vec<u16>),
    Arr(Vec<Node>),
    Obj(Vec<(String, Node)>),
}

impl Node {
    pub fn boolean(&self) -> Result<bool, String> {
        match &self.lit {
            Lit::Bool(b) => Ok(*b),
            other => Err(format!(
                "line {}: expected a boolean, found {other:?}",
                self.line
            )),
        }
    }

    pub fn num(&self) -> Result<u64, String> {
        match &self.lit {
            Lit::Num(n) => Ok(*n),
            other => Err(format!(
                "line {}: expected a number, found {other:?}",
                self.line
            )),
        }
    }

    pub fn byte(&self) -> Result<u8, String> {
        let n = self.num()?;
        u8::try_from(n).map_err(|_| format!("line {}: {n} is not a byte", self.line))
    }

    pub fn str_units(&self) -> Result<&[u16], String> {
        match &self.lit {
            Lit::Str(s) => Ok(s),
            other => Err(format!(
                "line {}: expected a string, found {other:?}",
                self.line
            )),
        }
    }

    /// The string as Rust text; a lone surrogate is an error.
    pub fn string(&self) -> Result<String, String> {
        String::from_utf16(self.str_units()?)
            .map_err(|_| format!("line {}: string has a lone surrogate", self.line))
    }

    /// True for `null`.
    pub fn is_null(&self) -> bool {
        self.lit == Lit::Null
    }

    pub fn array(&self) -> Result<&[Node], String> {
        match &self.lit {
            Lit::Arr(a) => Ok(a),
            other => Err(format!(
                "line {}: expected an array, found {other:?}",
                self.line
            )),
        }
    }

    pub fn bytes(&self) -> Result<Vec<u8>, String> {
        self.array()?.iter().map(Node::byte).collect()
    }

    /// Field `key` of an object literal.
    pub fn field(&self, key: &str) -> Result<&Node, String> {
        match &self.lit {
            Lit::Obj(fields) => fields
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v)
                .ok_or_else(|| format!("line {}: object has no field {key:?}", self.line)),
            other => Err(format!(
                "line {}: expected an object, found {other:?}",
                self.line
            )),
        }
    }
}

/// A cursor over a source file.
pub struct Parser {
    chars: Vec<char>,
    pos: usize,
    line: usize,
}

impl Parser {
    pub fn new(source: &str) -> Self {
        Self {
            chars: source.chars().collect(),
            pos: 0,
            line: 1,
        }
    }

    /// A parser positioned at char offset `pos` of `source`.
    pub fn at(source: &str, pos: usize) -> Self {
        let mut p = Self::new(source);
        while p.pos < pos && p.peek().is_some() {
            p.bump();
        }
        p
    }

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    pub fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos = self.pos.saturating_add(1);
        if c == '\n' {
            self.line = self.line.saturating_add(1);
        }
        Some(c)
    }

    pub fn err<T>(&self, what: &str) -> Result<T, String> {
        Err(format!(
            "line {}: {what}, found {:?}",
            self.line,
            self.peek()
                .map_or_else(|| "end of file".to_owned(), String::from)
        ))
    }

    /// Skip whitespace and `//` / `/* */` comments.
    pub fn skip_trivia(&mut self) {
        loop {
            match (self.peek(), self.chars.get(self.pos.saturating_add(1))) {
                (Some(c), _) if c.is_whitespace() => {
                    self.bump();
                }
                (Some('/'), Some('/')) => {
                    while self.peek().is_some_and(|c| c != '\n') {
                        self.bump();
                    }
                }
                (Some('/'), Some('*')) => {
                    self.bump();
                    self.bump();
                    while self.peek().is_some() && !self.rest_starts_with("*/") {
                        self.bump();
                    }
                    self.bump();
                    self.bump();
                }
                _ => return,
            }
        }
    }

    pub fn rest_starts_with(&self, s: &str) -> bool {
        s.chars()
            .enumerate()
            .all(|(i, c)| self.chars.get(self.pos.saturating_add(i)) == Some(&c))
    }

    /// Consume `s` (after trivia) if it comes next.
    pub fn eat(&mut self, s: &str) -> bool {
        self.skip_trivia();
        if self.rest_starts_with(s) {
            for _ in s.chars() {
                self.bump();
            }
            true
        } else {
            false
        }
    }

    /// The next character after trivia is `c` (not consumed).
    pub fn next_is(&mut self, c: char) -> bool {
        self.skip_trivia();
        self.peek() == Some(c)
    }

    pub fn expect(&mut self, s: &str) -> Result<(), String> {
        if self.eat(s) {
            Ok(())
        } else {
            self.err(&format!("expected {s:?}"))
        }
    }

    /// One literal.
    pub fn literal(&mut self) -> Result<Node, String> {
        self.skip_trivia();
        let line = self.line;
        let lit = match self.peek() {
            Some('[') => {
                self.bump();
                Lit::Arr(self.list(']', Self::literal)?)
            }
            Some('{') => {
                self.bump();
                Lit::Obj(self.list('}', |p| {
                    let key = match p.peek() {
                        Some(q @ ('\'' | '"')) => {
                            p.bump();
                            String::from_utf16(&p.string_body(q)?)
                                .map_err(|_| format!("line {}: key has a lone surrogate", p.line))?
                        }
                        _ => p.ident()?,
                    };
                    p.expect(":")?;
                    Ok((key, p.literal()?))
                })?)
            }
            Some(q @ ('\'' | '"')) => {
                self.bump();
                Lit::Str(self.string_body(q)?)
            }
            Some(c) if c.is_ascii_digit() => Lit::Num(self.number()?),
            Some('t') if self.rest_starts_with("true") => {
                for _ in 0..4 {
                    self.bump();
                }
                Lit::Bool(true)
            }
            Some('n') if self.rest_starts_with("null") => {
                for _ in 0..4 {
                    self.bump();
                }
                Lit::Null
            }
            Some('f') if self.rest_starts_with("false") => {
                for _ in 0..5 {
                    self.bump();
                }
                Lit::Bool(false)
            }
            _ => return self.err("expected a literal"),
        };
        Ok(Node { line, lit })
    }

    /// Comma-separated items up to `close`, trailing comma allowed.
    pub fn list<T>(
        &mut self,
        close: char,
        mut item: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<Vec<T>, String> {
        let mut items = Vec::new();
        loop {
            self.skip_trivia();
            if self.peek() == Some(close) {
                self.bump();
                return Ok(items);
            }
            items.push(item(self)?);
            self.skip_trivia();
            if !self.eat(",") && self.peek() != Some(close) {
                return self.err(&format!("expected ',' or {close:?}"));
            }
        }
    }

    pub fn ident(&mut self) -> Result<String, String> {
        self.skip_trivia();
        let mut s = String::new();
        while let Some(c) = self
            .peek()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '$')
        {
            s.push(c);
            self.bump();
        }
        if s.is_empty() || s.starts_with(|c: char| c.is_ascii_digit()) {
            return self.err("expected an identifier");
        }
        Ok(s)
    }

    fn number(&mut self) -> Result<u64, String> {
        let radix = if self.rest_starts_with("0x") || self.rest_starts_with("0X") {
            self.bump();
            self.bump();
            16
        } else {
            10
        };
        let mut digits = String::new();
        while let Some(c) = self
            .peek()
            .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
        {
            if c != '_' {
                digits.push(c);
            }
            self.bump();
        }
        u64::from_str_radix(&digits, radix)
            .map_err(|e| format!("line {}: bad number {digits:?}: {e}", self.line))
    }

    fn hex(&mut self, len: usize) -> Result<u32, String> {
        let mut s = String::new();
        for _ in 0..len {
            match self.bump() {
                Some(c) if c.is_ascii_hexdigit() => s.push(c),
                _ => return self.err("expected a hex digit"),
            }
        }
        u32::from_str_radix(&s, 16).map_err(|e| e.to_string())
    }

    fn string_body(&mut self, quote: char) -> Result<Vec<u16>, String> {
        let mut units = Vec::new();
        let mut buf = [0u16; 2];
        loop {
            let Some(c) = self.bump() else {
                return self.err("unterminated string");
            };
            if c == quote {
                return Ok(units);
            }
            if c == '\n' {
                return self.err("newline in string");
            }
            if c != '\\' {
                units.extend_from_slice(c.encode_utf16(&mut buf));
                continue;
            }
            let unit = match self.bump() {
                Some('u') if self.peek() == Some('{') => {
                    return self.err("\\u{...} escapes are not supported");
                }
                Some('u') => self.hex(4)?,
                Some('x') => self.hex(2)?,
                Some('0') if !self.peek().is_some_and(|c| c.is_ascii_digit()) => 0,
                Some('n') => 0x0A,
                Some('f') => 0x0C,
                Some('r') => 0x0D,
                Some('t') => 0x09,
                Some(e @ ('\\' | '\'' | '"')) => u32::from(e),
                _ => return self.err("unsupported escape"),
            };
            units.push(u16::try_from(unit).map_err(|e| e.to_string())?);
        }
    }
}

/// UTF-16 code units to scalar values; a lone surrogate is an error.
pub fn scalars(units: &[u16]) -> Result<Vec<u32>, String> {
    char::decode_utf16(units.iter().copied())
        .map(|r| r.map(u32::from).map_err(|e| e.to_string()))
        .collect()
}

/// Char offsets of every occurrence of `needle` in `source`.
pub fn find_all(source: &str, needle: &str) -> Vec<usize> {
    source
        .match_indices(needle)
        .map(|(byte, m)| {
            source
                .get(..byte)
                .map_or(0, |pre| pre.chars().count())
                .saturating_add(m.chars().count())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{Lit, Node, Parser, scalars};

    #[test]
    fn parses_wpt_shapes() -> Result<(), String> {
        let src = "[\n  { encoding: 'utf-8', input: [0xFF, 0x0_1], name: 'a\\'b' }, // c\n  \"\\uD834\\uDD1E\\xA2\\0\",\n]";
        let n = Parser::new(src).literal()?;
        let rows = n.array()?;
        let first = rows.first().ok_or("no rows")?;
        assert_eq!(first.field("input")?.bytes()?, vec![0xFF, 0x01]);
        assert_eq!(first.field("name")?.string()?, "a'b");
        let second = rows.get(1).ok_or("no second row")?;
        assert_eq!(second.line, 3);
        assert_eq!(scalars(second.str_units()?)?, vec![0x1D11E, 0xA2, 0]);
        assert!(matches!(n.lit, Lit::Arr(_)));
        let obj = Parser::new("{ \"IBM866\": [1, null], 'k': true }").literal()?;
        let index = obj.field("IBM866")?.array()?;
        assert!(index.get(1).is_some_and(Node::is_null));
        assert!(obj.field("k")?.boolean()?);
        Ok(())
    }

    #[test]
    fn rejects_what_it_does_not_know() {
        assert!(Parser::new("[a]").literal().is_err());
        assert!(Parser::new("'\\u{1F600}'").literal().is_err());
        assert!(Parser::new("[1 2]").literal().is_err());
        assert!(Parser::new("'abc").literal().is_err());
    }
}
