//! Executable-style specification of the IPC message schema (phase-2.md item
//! 2.3). The schema is ours: this file is the definition.
//!
//! A message is a CBOR array (`crate::cbor`) whose first element is an
//! unsigned integer tag and whose other elements are the message's fields,
//! in order. Fields are text strings, byte strings, unsigned integers,
//! booleans, or (one field, `Display`'s links) an array of text strings.
//!
//! | Tag | Direction | Message | Fields |
//! |-----|-----------|---------|--------|
//! | 1 | renderer to kernel | `CookieGet` | |
//! | 2 | renderer to kernel | `CookieSet` | cookie string (text) |
//! | 3 | renderer to kernel | `StorageGetItem` | key (text) |
//! | 4 | renderer to kernel | `StorageSetItem` | key (text), value (text) |
//! | 5 | renderer to kernel | `StorageRemoveItem` | key (text) |
//! | 6 | renderer to kernel | `StorageClear` | |
//! | 7 | renderer to kernel | `StorageKey` | index (unsigned) |
//! | 8 | renderer to kernel | `StorageLength` | |
//! | 9 | renderer to kernel | `Navigate` | url (text) |
//! | 10 | renderer to kernel | `Display` | title (text), text (text), links (array of text) |
//! | 101 | kernel to renderer | `Commit` | url (text), content type (bytes), kind (unsigned) |
//! | 102 | kernel to renderer | `CookieValue` | cookie string (text) |
//! | 103 | kernel to renderer | `StorageValue` | present (bool), then value (text) only if present |
//! | 104 | kernel to renderer | `StorageLengthValue` | length (unsigned) |
//! | 105 | kernel to renderer | `Error` | code (unsigned) |
//! | 106 | kernel to renderer | `Body` | bytes (bytes, at most [`max_body_chunk`]) |
//! | 107 | kernel to renderer | `BodyEnd` | |
//!
//! `StorageLengthValue` is not in the plan's list, which has no reply for
//! `StorageLength`; the schema needs one.
//!
//! Phase 4 (phase-4.md item 4.12) changed `Commit` and added `Body`,
//! `BodyEnd` and `Display`. A committed document is `Commit`, zero or more
//! `Body` frames and `BodyEnd`, and its body is the concatenation of the
//! `Body` frames' bytes, in order. `Commit`'s content type is the response's
//! combined `Content-Type` field value, or empty; its kind is 0 for a
//! document and 1 for a user script (the Phase 2 script path). `Display` is
//! the renderer's text rendering of its document: a title, the text, and
//! the absolute URLs of its links.
//!
//! Two rules are part of the schema's spec ([`message_fields`], and
//! `lemmas::lemma_no_identity_fields`):
//! - **No message carries a claimed identity.** No origin, renderer id, tab
//!   id or sender URL appears in any message. The kernel learns the sender
//!   from the socket. (`Navigate`'s `url` is the address to go to, not the
//!   sender's; `Display` names no tab, origin or URL of its own: its title
//!   and text are what the page says, and its links are where it points.)
//! - **Renderer ids never reach a renderer.** They are assigned in order, so
//!   showing one would let a renderer count another's spawns.
//!
//! Modelling choices:
//! - Text is the bytes of its UTF-8 encoding (`Seq<u8>`), as in a CBOR text
//!   string token; a message is well formed ([`message_ok`]) when its
//!   token sequence is one data item of the profile, i.e. text is valid
//!   UTF-8.
//! - An absent storage value is `present = false` with no value, because
//!   the profile has no null.
//! - `Commit`'s kind is any unsigned integer on the wire; 0 and 1 are the
//!   kinds the kernel sends, and a renderer refuses any other. (The schema
//!   does not narrow it, so that every message is still exactly its tokens.)
//! - `Display`'s links are a nested array: the message's array has four
//!   elements (the tag, the title, the text and the links), and its last
//!   element is an array of text strings, whose tokens follow it
//!   ([`display_tokens`]). It is the only nested field in the schema.
//! - "Failure" is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The CBOR profile's token, as this schema uses it.
pub type Token = crate::cbor::spec::Token;

/// [`crate::cbor::spec::decode`].
pub open spec fn decode(b: Seq<u8>) -> Option<Seq<Token>> {
    crate::cbor::spec::decode(b)
}

/// [`crate::cbor::spec::encode`].
pub open spec fn encode(t: Seq<Token>) -> Seq<u8> {
    crate::cbor::spec::encode(t)
}

/// [`crate::cbor::spec::is_item`].
pub open spec fn is_item(t: Seq<Token>) -> bool {
    crate::cbor::spec::is_item(t)
}

/// A message, in either direction.
pub enum Message {
    /// Renderer to kernel: read `document.cookie`.
    CookieGet,
    /// Renderer to kernel: write `document.cookie`.
    CookieSet {
        /// The cookie string.
        cookie_string: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.getItem(key)`.
    StorageGetItem {
        /// The key.
        key: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.setItem(key, value)`.
    StorageSetItem {
        /// The key.
        key: Seq<u8>,
        /// The value.
        value: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.removeItem(key)`.
    StorageRemoveItem {
        /// The key.
        key: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.clear()`.
    StorageClear,
    /// Renderer to kernel: `localStorage.key(index)`.
    StorageKey {
        /// The index.
        index: u64,
    },
    /// Renderer to kernel: `localStorage.length`.
    StorageLength,
    /// Renderer to kernel: navigate to a URL.
    Navigate {
        /// The URL to go to (not the sender's).
        url: Seq<u8>,
    },
    /// Renderer to kernel: show this text rendering of the committed
    /// document (phase-4.md item 4.12).
    Display {
        /// The document's title.
        title: Seq<u8>,
        /// The document's text, laid out.
        text: Seq<u8>,
        /// The absolute URLs of its links, in order.
        links: Seq<Seq<u8>>,
    },
    /// Kernel to renderer: a document is committed; its body follows in
    /// `Body` frames, then `BodyEnd`.
    Commit {
        /// The committed URL.
        url: Seq<u8>,
        /// The response's combined `Content-Type` field value, or empty.
        content_type: Seq<u8>,
        /// 0 a document, 1 a user script.
        kind: u64,
    },
    /// Kernel to renderer: the value of `document.cookie`.
    CookieValue {
        /// The cookie string.
        cookie_string: Seq<u8>,
    },
    /// Kernel to renderer: a storage value, if there is one.
    StorageValue {
        /// The value, or `None` if there is none.
        value: Option<Seq<u8>>,
    },
    /// Kernel to renderer: `localStorage.length`.
    StorageLengthValue {
        /// The length.
        length: u64,
    },
    /// Kernel to renderer: a request failed.
    Error {
        /// The error code.
        code: u64,
    },
    /// Kernel to renderer: the next part of the committed document's body.
    Body {
        /// The octets.
        bytes: Seq<u8>,
    },
    /// Kernel to renderer: the committed document's body is complete.
    BodyEnd,
}

/// The most octets one `Body` carries: `MAX_FRAME` minus the rest of its
/// payload, which is the array's head (1 octet), the tag 106 (2 octets) and
/// the byte string's head (at most 5 octets below 2^32), so that every `Body`
/// of at most this many octets fits one frame
/// (`lemmas::lemma_body_fits_frame`).
pub open spec fn max_body_chunk() -> nat {
    (crate::frame::spec::MAX_FRAME - 8) as nat
}

/// Whether `m` is sent by a renderer to the kernel.
pub open spec fn is_from_renderer(m: Message) -> bool {
    match m {
        Message::CookieGet
        | Message::CookieSet { .. }
        | Message::StorageGetItem { .. }
        | Message::StorageSetItem { .. }
        | Message::StorageRemoveItem { .. }
        | Message::StorageClear
        | Message::StorageKey { .. }
        | Message::StorageLength
        | Message::Navigate { .. }
        | Message::Display { .. } => true,
        _ => false,
    }
}

/// The kind of each field of a message.
pub enum Field {
    /// A cookie string.
    CookieString,
    /// A storage key.
    Key,
    /// A storage value.
    Value,
    /// A URL to navigate to or commit.
    Url,
    /// A storage index.
    Index,
    /// Whether a storage value is present.
    Present,
    /// A storage length.
    Length,
    /// An error code.
    Code,
    /// A document's content type.
    ContentType,
    /// A document's kind (a document or a user script).
    Kind,
    /// Some octets of a document's body.
    BodyBytes,
    /// A document's title.
    Title,
    /// A document's text.
    Text,
    /// The URLs a document links to.
    Links,
    /// A claimed origin. No message has one.
    Origin,
    /// A renderer id. No message has one.
    RendererId,
    /// A tab id. No message has one.
    TabId,
    /// The URL of the sender. No message has one.
    SenderUrl,
}

/// The fields a message carries, in order. The two schema rules say none of
/// them is an identity ([`is_identity`]).
pub open spec fn message_fields(m: Message) -> Seq<Field> {
    match m {
        Message::CookieGet => seq![],
        Message::CookieSet { .. } => seq![Field::CookieString],
        Message::StorageGetItem { .. } => seq![Field::Key],
        Message::StorageSetItem { .. } => seq![Field::Key, Field::Value],
        Message::StorageRemoveItem { .. } => seq![Field::Key],
        Message::StorageClear => seq![],
        Message::StorageKey { .. } => seq![Field::Index],
        Message::StorageLength => seq![],
        Message::Navigate { .. } => seq![Field::Url],
        Message::Display { .. } => seq![Field::Title, Field::Text, Field::Links],
        Message::Commit { .. } => seq![Field::Url, Field::ContentType, Field::Kind],
        Message::CookieValue { .. } => seq![Field::CookieString],
        Message::StorageValue { value } => match value {
            None => seq![Field::Present],
            Some(_) => seq![Field::Present, Field::Value],
        },
        Message::StorageLengthValue { .. } => seq![Field::Length],
        Message::Error { .. } => seq![Field::Code],
        Message::Body { .. } => seq![Field::BodyBytes],
        Message::BodyEnd => seq![],
    }
}

/// The number of tokens of a message beyond one per field: the elements of
/// `Display`'s links, which follow the links' array token.
pub open spec fn nested_len(m: Message) -> nat {
    match m {
        Message::Display { links, .. } => links.len(),
        _ => 0,
    }
}

/// A field that names who is speaking or which renderer: forbidden.
pub open spec fn is_identity(f: Field) -> bool {
    match f {
        Field::Origin | Field::RendererId | Field::TabId | Field::SenderUrl => true,
        _ => false,
    }
}

/// The tokens of a list of text strings, in order.
pub open spec fn text_tokens(ls: Seq<Seq<u8>>) -> Seq<Token> {
    ls.map_values(|l: Seq<u8>| Token::Text(l))
}

/// The tokens of `Display`: the array of the tag, the title, the text and
/// the links, the links being an array whose text strings follow it.
pub open spec fn display_tokens(title: Seq<u8>, text: Seq<u8>, links: Seq<Seq<u8>>) -> Seq<Token> {
    seq![Token::Array(4), Token::Uint(10), Token::Text(title), Token::Text(text), Token::Array(links.len() as u64)] + text_tokens(links)
}

/// The tokens of a message: an array of the tag and the fields.
pub open spec fn message_tokens(m: Message) -> Seq<Token> {
    match m {
        Message::CookieGet => seq![Token::Array(1), Token::Uint(1)],
        Message::CookieSet { cookie_string } => seq![Token::Array(2), Token::Uint(2), Token::Text(cookie_string)],
        Message::StorageGetItem { key } => seq![Token::Array(2), Token::Uint(3), Token::Text(key)],
        Message::StorageSetItem { key, value } => seq![Token::Array(3), Token::Uint(4), Token::Text(key), Token::Text(value)],
        Message::StorageRemoveItem { key } => seq![Token::Array(2), Token::Uint(5), Token::Text(key)],
        Message::StorageClear => seq![Token::Array(1), Token::Uint(6)],
        Message::StorageKey { index } => seq![Token::Array(2), Token::Uint(7), Token::Uint(index)],
        Message::StorageLength => seq![Token::Array(1), Token::Uint(8)],
        Message::Navigate { url } => seq![Token::Array(2), Token::Uint(9), Token::Text(url)],
        Message::Display { title, text, links } => display_tokens(title, text, links),
        Message::Commit { url, content_type, kind } => seq![Token::Array(4), Token::Uint(101), Token::Text(url), Token::Bytes(content_type), Token::Uint(kind)],
        Message::CookieValue { cookie_string } => seq![Token::Array(2), Token::Uint(102), Token::Text(cookie_string)],
        Message::StorageValue { value } => match value {
            None => seq![Token::Array(2), Token::Uint(103), Token::Bool(false)],
            Some(v) => seq![Token::Array(3), Token::Uint(103), Token::Bool(true), Token::Text(v)],
        },
        Message::StorageLengthValue { length } => seq![Token::Array(2), Token::Uint(104), Token::Uint(length)],
        Message::Error { code } => seq![Token::Array(2), Token::Uint(105), Token::Uint(code)],
        Message::Body { bytes } => seq![Token::Array(2), Token::Uint(106), Token::Bytes(bytes)],
        Message::BodyEnd => seq![Token::Array(1), Token::Uint(107)],
    }
}

/// Whether `m` can be sent: its tokens are one data item of the profile.
pub open spec fn message_ok(m: Message) -> bool {
    is_item(message_tokens(m))
}

/// The message with this `tag` and these field tokens.
pub open spec fn parse_fields(tag: u64, f: Seq<Token>) -> Option<Message> {
    if tag == 1 {
        if f.len() == 0 { Some(Message::CookieGet) } else { None }
    } else if tag == 2 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::CookieSet { cookie_string: s }), _ => None } } else { None }
    } else if tag == 3 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::StorageGetItem { key: s }), _ => None } } else { None }
    } else if tag == 4 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Text(k), Token::Text(v)) => Some(Message::StorageSetItem { key: k, value: v }),
                _ => None,
            }
        } else { None }
    } else if tag == 5 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::StorageRemoveItem { key: s }), _ => None } } else { None }
    } else if tag == 6 {
        if f.len() == 0 { Some(Message::StorageClear) } else { None }
    } else if tag == 7 {
        if f.len() == 1 { match f[0] { Token::Uint(i) => Some(Message::StorageKey { index: i }), _ => None } } else { None }
    } else if tag == 8 {
        if f.len() == 0 { Some(Message::StorageLength) } else { None }
    } else if tag == 9 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::Navigate { url: s }), _ => None } } else { None }
    } else if tag == 101 {
        if f.len() == 3 {
            match (f[0], f[1], f[2]) {
                (Token::Text(u), Token::Bytes(c), Token::Uint(k)) => Some(Message::Commit { url: u, content_type: c, kind: k }),
                _ => None,
            }
        } else { None }
    } else if tag == 102 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::CookieValue { cookie_string: s }), _ => None } } else { None }
    } else if tag == 103 {
        if f.len() == 1 {
            match f[0] { Token::Bool(false) => Some(Message::StorageValue { value: None }), _ => None }
        } else if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Bool(true), Token::Text(v)) => Some(Message::StorageValue { value: Some(v) }),
                _ => None,
            }
        } else { None }
    } else if tag == 104 {
        if f.len() == 1 { match f[0] { Token::Uint(n) => Some(Message::StorageLengthValue { length: n }), _ => None } } else { None }
    } else if tag == 105 {
        if f.len() == 1 { match f[0] { Token::Uint(n) => Some(Message::Error { code: n }), _ => None } } else { None }
    } else if tag == 106 {
        if f.len() == 1 { match f[0] { Token::Bytes(b) => Some(Message::Body { bytes: b }), _ => None } } else { None }
    } else if tag == 107 {
        if f.len() == 0 { Some(Message::BodyEnd) } else { None }
    } else {
        None
    }
}

/// Every token of `ts` is a text string.
pub open spec fn all_text(ts: Seq<Token>) -> bool {
    forall|j: int| 0 <= j < ts.len() ==> ts[j] is Text
}

/// The text strings of tokens that are all text strings.
pub open spec fn texts_of(ts: Seq<Token>) -> Seq<Seq<u8>> {
    ts.map_values(|t: Token| t->Text_0)
}

/// `Display` from the element count `n` of its array and the tokens after
/// the tag: four elements, two text strings, then an array of `k` text
/// strings that are the last `k` tokens.
pub open spec fn parse_display(n: u64, f: Seq<Token>) -> Option<Message> {
    if n == 4 && f.len() >= 3 {
        match (f[0], f[1], f[2]) {
            (Token::Text(title), Token::Text(text), Token::Array(k)) => {
                let rest = f.subrange(3, f.len() as int);
                if k as nat == rest.len() && all_text(rest) {
                    Some(Message::Display { title, text, links: texts_of(rest) })
                } else {
                    None
                }
            },
            _ => None,
        }
    } else {
        None
    }
}

/// The message in a token sequence: an array whose first element is the
/// tag, and which has exactly the message's fields after it (for `Display`,
/// whose last field is an array, [`parse_display`]).
pub open spec fn parse_message(t: Seq<Token>) -> Option<Message> {
    if t.len() < 2 {
        None
    } else {
        match (t[0], t[1]) {
            (Token::Array(n), Token::Uint(tag)) => {
                if tag == 10 {
                    parse_display(n, t.subrange(2, t.len() as int))
                } else if n as nat + 1 == t.len() {
                    parse_fields(tag, t.subrange(2, t.len() as int))
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// Decode one message, in either direction, from the bytes of a CBOR item.
pub open spec fn decode_message(b: Seq<u8>) -> Option<Message> {
    match decode(b) {
        Some(t) => parse_message(t),
        None => None,
    }
}

/// Decode a message the kernel receives: only renderer-to-kernel messages.
pub open spec fn decode_renderer_message(b: Seq<u8>) -> Option<Message> {
    match decode_message(b) {
        Some(m) => if is_from_renderer(m) { Some(m) } else { None },
        None => None,
    }
}

/// The bytes of a message.
pub open spec fn encode_message(m: Message) -> Seq<u8> {
    encode(message_tokens(m))
}

/// Decode a message from a whole frame: split the frame, then decode.
pub open spec fn decode_framed(frame: Seq<u8>) -> Option<Message> {
    match crate::frame::spec::decode_frame(frame) {
        Some(p) => decode_message(p),
        None => None,
    }
}

} // verus!
