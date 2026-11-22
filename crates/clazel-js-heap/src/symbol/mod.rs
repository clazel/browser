//! Symbols and property keys (phase-7.md item 7.5).
//!
//! [`contract`] states what the symbol table and the key encoding must do
//! (Y1 to Y5). [`Symbols`] is the table; [`PropertyKeys`] pairs it with the
//! string [`Interner`] so that strings and symbols are both property keys
//! with one [`Key`] type, which is what [`crate::shape::Shapes`] takes.

pub mod contract;

use crate::string::{Interner, JsString, Key, TooLong};
use contract::{
    Description, PropertyKey, SYMBOL_BIT, WELL_KNOWN, WELL_KNOWN_COUNT, decode, encode,
};

pub use contract::SymbolId;

/// Why a symbol or key operation failed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// A table is full (Y5): 2^31 strings or 2^31 symbols.
    TooMany,
    /// A string past the length limit.
    TooLong,
    /// The key or id names nothing in the table.
    Unknown,
}

impl From<TooLong> for Error {
    fn from(_: TooLong) -> Self {
        Self::TooLong
    }
}

macro_rules! well_known {
    ($($name:ident = $id:expr, $js:expr;)*) => {
        $(
            #[doc = concat!("`Symbol.", $js, "` (§6.1.5.1, Table 1).")]
            pub const $name: SymbolId = SymbolId($id);
        )*
    };
}

well_known! {
    ASYNC_ITERATOR = 0, "asyncIterator";
    HAS_INSTANCE = 1, "hasInstance";
    IS_CONCAT_SPREADABLE = 2, "isConcatSpreadable";
    ITERATOR = 3, "iterator";
    MATCH = 4, "match";
    MATCH_ALL = 5, "matchAll";
    REPLACE = 6, "replace";
    SEARCH = 7, "search";
    SPECIES = 8, "species";
    SPLIT = 9, "split";
    TO_PRIMITIVE = 10, "toPrimitive";
    TO_STRING_TAG = 11, "toStringTag";
    UNSCOPABLES = 12, "unscopables";
}

/// The symbol table.
#[derive(Debug)]
pub struct Symbols {
    descriptions: Vec<Description<JsString>>,
}

impl Default for Symbols {
    fn default() -> Self {
        Self::new()
    }
}

impl Symbols {
    /// A table holding the thirteen well-known symbols at ids 0 to 12 (Y1).
    #[must_use]
    pub fn new() -> Self {
        let descriptions = WELL_KNOWN
            .iter()
            .map(|n| {
                // The names are short ASCII: far under the string limit.
                match JsString::from_rust_str(&format!("Symbol.{n}")) {
                    Ok(s) => Description::Text(s),
                    Err(_) => Description::Undefined,
                }
            })
            .collect();
        Self { descriptions }
    }

    /// A new symbol, distinct from every other (Y2), with the description
    /// it is given (Y3).
    ///
    /// # Errors
    /// [`Error::TooMany`] when 2^31 symbols exist (Y5).
    pub fn create(&mut self, description: Description<JsString>) -> Result<SymbolId, Error> {
        let id = u32::try_from(self.descriptions.len()).map_err(|_| Error::TooMany)?;
        if id >= SYMBOL_BIT {
            return Err(Error::TooMany);
        }
        self.descriptions.push(description);
        Ok(SymbolId(id))
    }

    /// The symbol's description (`Symbol.prototype.description`'s source).
    #[must_use]
    pub fn description(&self, id: SymbolId) -> Option<&Description<JsString>> {
        usize::try_from(id.0)
            .ok()
            .and_then(|i| self.descriptions.get(i))
    }

    /// Whether `id` is one of the thirteen well-known symbols.
    #[must_use]
    pub const fn is_well_known(id: SymbolId) -> bool {
        id.0 < WELL_KNOWN_COUNT
    }

    /// The number of symbols, well-known ones included.
    #[must_use]
    pub fn len(&self) -> usize {
        self.descriptions.len()
    }

    /// Always false: the well-known symbols are there from the start.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.descriptions.is_empty()
    }
}

/// Strings and symbols as property keys.
#[derive(Debug, Default)]
pub struct PropertyKeys {
    strings: Interner,
    symbols: Symbols,
}

impl PropertyKeys {
    /// Empty string table; the symbol table has the well-known symbols.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The key for a string, interning it (equal strings, one key).
    ///
    /// # Errors
    /// [`Error::TooMany`] when 2^31 strings are interned and `s` is new
    /// (Y5); [`Error::TooLong`].
    pub fn string_key(&mut self, s: &JsString) -> Result<Key, Error> {
        if let Some(k) = self.strings.find(s) {
            return Ok(k);
        }
        if self.strings.issued() >= usize::try_from(SYMBOL_BIT).unwrap_or(usize::MAX) {
            return Err(Error::TooMany);
        }
        let k = self.strings.intern(s)?;
        encode(PropertyKey::String(k)).ok_or(Error::TooMany)
    }

    /// The key for a symbol.
    ///
    /// # Errors
    /// [`Error::Unknown`] if the id names no symbol of this table.
    pub fn symbol_key(&self, id: SymbolId) -> Result<Key, Error> {
        self.symbols.description(id).ok_or(Error::Unknown)?;
        encode(PropertyKey::Symbol(id)).ok_or(Error::Unknown)
    }

    /// A new symbol and its key.
    ///
    /// # Errors
    /// As [`Symbols::create`].
    pub fn new_symbol(
        &mut self,
        description: Description<JsString>,
    ) -> Result<(SymbolId, Key), Error> {
        let id = self.symbols.create(description)?;
        let key = encode(PropertyKey::Symbol(id)).ok_or(Error::TooMany)?;
        Ok((id, key))
    }

    /// What a key is: a string (resolved) or a symbol (Y4).
    #[must_use]
    pub fn classify(&self, key: Key) -> Option<PropertyKey> {
        let p = decode(key);
        match p {
            PropertyKey::String(k) => self.strings.resolve(k).map(|_| p),
            PropertyKey::Symbol(s) => self.symbols.description(s).map(|_| p),
        }
    }

    /// The string a key stands for, if it is a string key.
    #[must_use]
    pub fn string(&self, key: Key) -> Option<&JsString> {
        match decode(key) {
            PropertyKey::String(k) => self.strings.resolve(k),
            PropertyKey::Symbol(_) => None,
        }
    }

    /// The symbol table.
    #[must_use]
    pub const fn symbols(&self) -> &Symbols {
        &self.symbols
    }

    /// The string table.
    #[must_use]
    pub const fn strings(&self) -> &Interner {
        &self.strings
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shape::{Attrs, ROOT, Shapes};

    fn js(s: &str) -> JsString {
        JsString::from_rust_str(s).unwrap_or_else(|_| JsString::empty())
    }

    #[test]
    fn well_known_ids_are_fixed() {
        let t = Symbols::new();
        assert_eq!(t.len(), 13);
        assert_eq!(ITERATOR, SymbolId(3));
        assert_eq!(UNSCOPABLES, SymbolId(12));
        for (i, name) in WELL_KNOWN.iter().enumerate() {
            let id = SymbolId(u32::try_from(i).unwrap_or(u32::MAX));
            assert!(Symbols::is_well_known(id));
            assert_eq!(
                t.description(id),
                Some(&Description::Text(js(&format!("Symbol.{name}"))))
            );
        }
        assert!(!Symbols::is_well_known(SymbolId(13)));
        assert_eq!(
            t.description(TO_PRIMITIVE),
            Some(&Description::Text(js("Symbol.toPrimitive")))
        );
    }

    #[test]
    fn created_symbols_are_unique() {
        let mut t = Symbols::new();
        let a = t.create(Description::Text(js("x")));
        let b = t.create(Description::Text(js("x")));
        let c = t.create(Description::Undefined);
        let d = t.create(Description::Text(JsString::empty()));
        assert_eq!(a, Ok(SymbolId(13)));
        assert_eq!(b, Ok(SymbolId(14)));
        assert_eq!(c, Ok(SymbolId(15)));
        assert_eq!(d, Ok(SymbolId(16)));
        assert_ne!(a, b, "same description, different symbols");
        assert_eq!(t.description(SymbolId(15)), Some(&Description::Undefined));
        assert_ne!(
            t.description(SymbolId(15)),
            t.description(SymbolId(16)),
            "undefined is not the empty string"
        );
        assert_eq!(t.description(SymbolId(17)), None);
        assert_eq!(t.len(), 17);
    }

    #[test]
    fn strings_and_symbols_never_share_a_key() {
        let mut k = PropertyKeys::new();
        let s = k.string_key(&js("iterator"));
        let again = k.string_key(&js("iterator"));
        assert_eq!(s, again);
        let sym = k.symbol_key(ITERATOR);
        assert_ne!(s, sym, "the string \"iterator\" is not Symbol.iterator");
        let (id, key) = k
            .new_symbol(Description::Text(js("iterator")))
            .unwrap_or((SymbolId(0), Key(0)));
        assert_ne!(Ok(key), sym);
        assert_ne!(Ok(key), s);
        assert_eq!(k.classify(key), Some(PropertyKey::Symbol(id)));
        assert_eq!(k.string(key), None);
        let sk = s.unwrap_or(Key(0));
        assert_eq!(k.string(sk).map(JsString::len), Some(8));
        assert_eq!(k.classify(Key(sk.0 + 100)), None);
        assert_eq!(k.symbol_key(SymbolId(99)), Err(Error::Unknown));
    }

    #[test]
    fn symbol_keys_work_in_shapes() {
        let mut k = PropertyKeys::new();
        let mut shapes = Shapes::new();
        let s = k.string_key(&js("a")).unwrap_or(Key(0));
        let y = k.symbol_key(ITERATOR).unwrap_or(Key(0));
        let s1 = shapes.add_property(ROOT, s, Attrs::ALL);
        let s1 = s1.map(|(id, _)| id).unwrap_or(ROOT);
        let s2 = shapes.add_property(s1, y, Attrs::ALL);
        let s2 = s2.map(|(id, _)| id).unwrap_or(ROOT);
        assert_eq!(shapes.lookup(s2, s), Some((0, Attrs::ALL)));
        assert_eq!(shapes.lookup(s2, y), Some((1, Attrs::ALL)));
        // The same order on another object reaches the same shape.
        let t1 = shapes.add_property(ROOT, s, Attrs::ALL).map(|(i, _)| i);
        assert_eq!(t1, Ok(s1));
    }
}
