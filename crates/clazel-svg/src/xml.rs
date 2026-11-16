//! The tokenizer: the small piece of XML 1.0 the scope needs, written for
//! this crate (CLAUDE.md rule 8). It reads a document held in memory, which
//! may be a prefix: running out of bytes is [`Stop::Eof`], never an error,
//! so "needs more" and "malformed" are told apart exactly.
//!
//! What it reads: an optional UTF-8 byte order mark, an optional XML
//! declaration, comments, start tags (with `/>`), end tags, attributes with
//! quoted values, and white space in content. Everything else the standard
//! has (a `DOCTYPE`, `CDATA`, processing instructions, character and entity
//! references, text, names with a namespace prefix) is
//! [`Error::Unsupported`]; what XML calls not well-formed (a missing quote,
//! a duplicate attribute, a `<` in a value, mismatched tags) is
//! [`Error::Malformed`].
//!
//! XML 1.0 (Fifth Edition, W3C Recommendation 26 November 2008):
//! section 2.3 (names `Name`, white space `S`), 2.5 (comments), 2.8
//! (prolog, `XMLDecl`), 3.1 (tags, `STag`, `ETag`, `EmptyElemTag`,
//! `Attribute`), 3.3.3 (attribute-value normalization, which turns each
//! white space character into a space: the grammars read here treat all of
//! them alike, so it is not done).

use crate::limits::MAX_ATTRS;
use clazel_image_shape::Error;

/// Why a read stopped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stop {
    /// The document ended inside a construct that is valid so far.
    Eof,
    /// The document is refused.
    Fail(Error),
}

impl From<Error> for Stop {
    fn from(e: Error) -> Stop {
        Stop::Fail(e)
    }
}

pub(crate) type Read<T> = Result<T, Stop>;

pub(crate) fn malformed<T>(why: &'static str) -> Read<T> {
    Err(Stop::Fail(Error::Malformed(why)))
}

pub(crate) fn unsupported<T>(what: &'static str) -> Read<T> {
    Err(Stop::Fail(Error::Unsupported(what)))
}

/// XML 1.0 section 2.3, `S`: space, tab, line feed, carriage return.
pub(crate) fn is_space(b: u8) -> bool {
    matches!(b, 0x20 | 0x09 | 0x0A | 0x0D)
}

/// One attribute: raw name and raw value (between the quotes, no
/// references in it).
#[derive(Debug, Clone, Copy)]
pub(crate) struct Attr<'a> {
    pub name: &'a [u8],
    pub value: &'a [u8],
}

/// A start tag.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Tag<'a> {
    pub name: &'a [u8],
    attrs: [Attr<'a>; MAX_ATTRS],
    count: usize,
    /// Ended with `/>`.
    pub empty: bool,
}

impl<'a> Tag<'a> {
    /// The attributes, in document order.
    pub(crate) fn attrs(&self) -> &[Attr<'a>] {
        self.attrs.get(..self.count).unwrap_or(&[])
    }
}

/// What `next_markup` found.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Item<'a> {
    Start(Tag<'a>),
    /// The name of an end tag.
    End(&'a [u8]),
}

/// A cursor over the document.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Reader<'a> {
    doc: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(doc: &'a [u8]) -> Reader<'a> {
        Reader { doc, pos: 0 }
    }

    /// Bytes consumed so far.
    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    fn peek(&self) -> Read<u8> {
        self.doc.get(self.pos).copied().ok_or(Stop::Eof)
    }

    fn bump(&mut self) {
        self.pos = self.pos.saturating_add(1);
    }

    fn skip_space(&mut self) -> bool {
        let start = self.pos;
        while self.doc.get(self.pos).is_some_and(|&b| is_space(b)) {
            self.bump();
        }
        self.pos != start
    }

    /// Whether the rest of the document starts with `pat`: `Eof` if what
    /// is left is a proper prefix of it (more bytes could make it so).
    fn at(&self, pat: &[u8]) -> Read<bool> {
        let rest = self.doc.get(self.pos..).unwrap_or(&[]);
        if rest.starts_with(pat) {
            Ok(true)
        } else if pat.starts_with(rest) {
            Err(Stop::Eof)
        } else {
            Ok(false)
        }
    }

    /// Moves past the first `pat` at or after the cursor.
    fn skip_past(&mut self, pat: &[u8]) -> Read<()> {
        let mut p = self.pos;
        loop {
            let rest = self.doc.get(p..).unwrap_or(&[]);
            if rest.starts_with(pat) {
                self.pos = p.saturating_add(pat.len());
                return Ok(());
            }
            if rest.is_empty() {
                self.pos = self.doc.len();
                return Err(Stop::Eof);
            }
            p = p.saturating_add(1);
        }
    }

    /// XML 1.0 section 2.3, `Name`, as far as ASCII goes: a letter or `_`,
    /// then letters, digits, `-`, `_` and `.`. A `:` (a namespace prefix) is
    /// unsupported; any other byte is not a name.
    fn name(&mut self) -> Read<&'a [u8]> {
        let start = self.pos;
        loop {
            match self.doc.get(self.pos) {
                None => return Err(Stop::Eof),
                Some(&b) => {
                    let first = self.pos == start;
                    let ok = b.is_ascii_alphabetic()
                        || b == b'_'
                        || (!first && (b.is_ascii_digit() || b == b'-' || b == b'.'));
                    if ok {
                        self.bump();
                    } else if b == b':' {
                        return unsupported("a namespace prefix");
                    } else {
                        break;
                    }
                }
            }
        }
        if self.pos == start {
            return malformed("a name was expected");
        }
        self.doc.get(start..self.pos).ok_or(Stop::Eof)
    }

    /// XML 1.0 section 2.8: the optional byte order mark, the optional
    /// `XMLDecl` (skipped to its `?>`: its version and encoding are not
    /// read) and nothing else; comments and white space before the root are
    /// `next_markup`'s.
    pub(crate) fn prolog(&mut self) -> Read<()> {
        const BOM: [u8; 3] = [0xEF, 0xBB, 0xBF];
        let rest = self.doc.get(self.pos..).unwrap_or(&[]);
        if rest.starts_with(&BOM) {
            self.pos = self.pos.saturating_add(3);
        } else if BOM.starts_with(rest) && !rest.is_empty() {
            return Err(Stop::Eof);
        }
        if self.at(b"<?xml")? {
            self.pos = self.pos.saturating_add(5);
            if is_space(self.peek()?) {
                self.skip_past(b"?>")?;
            } else {
                return unsupported("a processing instruction");
            }
        }
        Ok(())
    }

    /// The next start or end tag, after skipping white space and comments.
    /// Text is refused: as malformed outside the root element (not XML at
    /// all), as unsupported inside it (text and references are content the
    /// scope does not have).
    /// Anything else in content is refused.
    pub(crate) fn next_markup(&mut self, outside_root: bool) -> Read<Item<'a>> {
        loop {
            self.skip_space();
            if self.peek()? != b'<' {
                return if outside_root {
                    malformed("text before the root element")
                } else {
                    unsupported("text or a reference in content")
                };
            }
            if self.at(b"<!--")? {
                // XML 1.0 section 2.5: a comment runs to the first `-->`.
                // (`--` inside it, not well-formed there, is not checked.)
                self.pos = self.pos.saturating_add(4);
                self.skip_past(b"-->")?;
                continue;
            }
            if self.at(b"<!")? {
                return unsupported("a DOCTYPE or CDATA section");
            }
            if self.at(b"<?")? {
                return unsupported("a processing instruction");
            }
            self.bump();
            if self.peek()? == b'/' {
                self.bump();
                let name = self.name()?;
                self.skip_space();
                if self.peek()? != b'>' {
                    return malformed("an end tag with more than a name");
                }
                self.bump();
                return Ok(Item::End(name));
            }
            return self.start_tag().map(Item::Start);
        }
    }

    /// XML 1.0 section 3.1: `STag` and `EmptyElemTag`, after the `<`.
    fn start_tag(&mut self) -> Read<Tag<'a>> {
        let name = self.name()?;
        let blank = Attr {
            name: &[],
            value: &[],
        };
        let mut tag = Tag {
            name,
            attrs: [blank; MAX_ATTRS],
            count: 0,
            empty: false,
        };
        loop {
            let spaced = self.skip_space();
            match self.peek()? {
                b'>' => {
                    self.bump();
                    return Ok(tag);
                }
                b'/' => {
                    self.bump();
                    if self.peek()? != b'>' {
                        return malformed("a / in a tag that does not end it");
                    }
                    self.bump();
                    tag.empty = true;
                    return Ok(tag);
                }
                _ => {}
            }
            if !spaced {
                return malformed("an attribute with no white space before it");
            }
            let attr_name = self.name()?;
            self.skip_space();
            if self.peek()? != b'=' {
                return malformed("an attribute with no value");
            }
            self.bump();
            self.skip_space();
            let quote = self.peek()?;
            if quote != b'"' && quote != b'\'' {
                return malformed("an attribute value without quotes");
            }
            self.bump();
            let start = self.pos;
            loop {
                match self.peek()? {
                    b if b == quote => break,
                    b'<' => return malformed("a < in an attribute value"),
                    b'&' => return unsupported("a reference in an attribute value"),
                    _ => self.bump(),
                }
            }
            let value = self.doc.get(start..self.pos).ok_or(Stop::Eof)?;
            self.bump();
            if tag.attrs().iter().any(|a| a.name == attr_name) {
                return malformed("a repeated attribute");
            }
            let slot = tag
                .attrs
                .get_mut(tag.count)
                .ok_or(Stop::Fail(Error::Unsupported("too many attributes")))?;
            *slot = Attr {
                name: attr_name,
                value,
            };
            tag.count = tag.count.saturating_add(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn items(s: &str) -> Result<Vec<String>, Stop> {
        items_b(s.as_bytes())
    }

    fn items_b(s: &[u8]) -> Result<Vec<String>, Stop> {
        let mut r = Reader::new(s);
        r.prolog()?;
        let mut out = vec![];
        loop {
            match r.next_markup(false) {
                Ok(Item::Start(t)) => {
                    let attrs: Vec<String> = t
                        .attrs()
                        .iter()
                        .map(|a| {
                            format!(
                                "{}={}",
                                String::from_utf8_lossy(a.name),
                                String::from_utf8_lossy(a.value)
                            )
                        })
                        .collect();
                    out.push(format!(
                        "<{}{} {}",
                        String::from_utf8_lossy(t.name),
                        if t.empty { "/" } else { "" },
                        attrs.join(",")
                    ));
                }
                Ok(Item::End(n)) => out.push(format!("</{}", String::from_utf8_lossy(n))),
                Err(Stop::Eof) => return Ok(out),
                Err(e) => return Err(e),
            }
        }
    }

    #[test]
    fn tags_and_attributes() {
        assert_eq!(
            items("<?xml version=\"1.0\"?>\n<!-- c --><a x='1' y=\"2\"><b/></a>"),
            Ok(vec![
                "<a x=1,y=2".to_string(),
                "<b/ ".to_string(),
                "</a".to_string()
            ])
        );
    }

    #[test]
    fn refusals() {
        for (s, unsup) in [
            ("<a b=1>", false),
            ("<a b='1'c='2'>", false),
            ("<a b='1' b='2'>", false),
            ("<a b='<'>", false),
            ("<a></b c>", false),
            ("<a>text</a>", true),
            ("<a b='&amp;'>", true),
            ("<a>&amp;</a>", true),
            ("<!DOCTYPE a><a>", true),
            ("<a><![CDATA[x]]></a>", true),
            ("<a><?pi x?></a>", true),
            ("<x:a>", true),
            ("<a x:b='1'>", true),
            ("<a b='1' c='2' d='3' e='4' f='5' g='6' h='7'>", true),
            ("<1a>", false),
            ("<>", false),
        ] {
            let got = match items(s) {
                Err(Stop::Fail(Error::Unsupported(_))) => "unsupported",
                Err(Stop::Fail(Error::Malformed(_))) => "malformed",
                _ => "accepted",
            };
            assert_eq!(got, if unsup { "unsupported" } else { "malformed" }, "{s}");
        }
    }

    #[test]
    fn prefixes_are_eof_not_errors() {
        let doc = "\u{feff}<?xml version='1.0'?><!--x--><svg a=\"b\" c='d'><path/></svg>";
        for n in 0..=doc.len() {
            let r = items_b(doc.as_bytes().get(..n).unwrap_or(&[]));
            assert!(!matches!(r, Err(Stop::Fail(_))), "{n}: {r:?}");
        }
    }
}
