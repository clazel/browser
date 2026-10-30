//! The executable message codec, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
use crate::cbor::token::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A message, in either direction; see [`Message`], whose view it is.
#[derive(Debug, PartialEq, Eq)]
pub enum Msg {
    /// Renderer to kernel: read `document.cookie`.
    CookieGet,
    /// Renderer to kernel: write `document.cookie`.
    CookieSet {
        /// The cookie string.
        cookie_string: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.getItem(key)`.
    StorageGetItem {
        /// The key.
        key: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.setItem(key, value)`.
    StorageSetItem {
        /// The key.
        key: Vec<u8>,
        /// The value.
        value: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.removeItem(key)`.
    StorageRemoveItem {
        /// The key.
        key: Vec<u8>,
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
        url: Vec<u8>,
    },
    /// Renderer to kernel: show this text rendering of the committed
    /// document.
    Display {
        /// The document's title.
        title: Vec<u8>,
        /// The document's text, laid out.
        text: Vec<u8>,
        /// The absolute URLs of its links, in order.
        links: Vec<Vec<u8>>,
    },
    /// Kernel to renderer: a document is committed; its body follows in
    /// `Body` frames, then `BodyEnd`.
    Commit {
        /// The committed URL.
        url: Vec<u8>,
        /// The response's combined `Content-Type` field value, or empty.
        content_type: Vec<u8>,
        /// 0 a document, 1 a user script.
        kind: u64,
    },
    /// Kernel to renderer: the value of `document.cookie`.
    CookieValue {
        /// The cookie string.
        cookie_string: Vec<u8>,
    },
    /// Kernel to renderer: a storage value, if there is one.
    StorageValue {
        /// The value, or `None` if there is none.
        value: Option<Vec<u8>>,
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
        bytes: Vec<u8>,
    },
    /// Kernel to renderer: the committed document's body is complete.
    BodyEnd,
}

/// [`max_body_chunk`]: the most octets one `Body` carries, `MAX_FRAME` minus
/// 8.
pub const MAX_BODY_CHUNK: usize = 1_048_568;

/// [`MAX_BODY_CHUNK`] is the spec's [`max_body_chunk`].
pub proof fn lemma_max_body_chunk()
    ensures
        MAX_BODY_CHUNK as nat == max_body_chunk(),
{
}

/// The view of a list of strings.
pub open spec fn strings_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|s: Vec<u8>| s@)
}

/// The view of an optional string.
pub open spec fn option_bytes(v: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match v {
        Some(v) => Some(v@),
        None => None,
    }
}

impl View for Msg {
    type V = Message;

    open spec fn view(&self) -> Message {
        match self {
            Msg::CookieGet => Message::CookieGet,
            Msg::CookieSet { cookie_string } => Message::CookieSet { cookie_string: cookie_string@ },
            Msg::StorageGetItem { key } => Message::StorageGetItem { key: key@ },
            Msg::StorageSetItem { key, value } => Message::StorageSetItem { key: key@, value: value@ },
            Msg::StorageRemoveItem { key } => Message::StorageRemoveItem { key: key@ },
            Msg::StorageClear => Message::StorageClear,
            Msg::StorageKey { index } => Message::StorageKey { index: *index },
            Msg::StorageLength => Message::StorageLength,
            Msg::Navigate { url } => Message::Navigate { url: url@ },
            Msg::Display { title, text, links } => Message::Display { title: title@, text: text@, links: strings_view(links@) },
            Msg::Commit { url, content_type, kind } => Message::Commit { url: url@, content_type: content_type@, kind: *kind },
            Msg::CookieValue { cookie_string } => Message::CookieValue { cookie_string: cookie_string@ },
            Msg::StorageValue { value } => Message::StorageValue { value: option_bytes(*value) },
            Msg::StorageLengthValue { length } => Message::StorageLengthValue { length: *length },
            Msg::Error { code } => Message::Error { code: *code },
            Msg::Body { bytes } => Message::Body { bytes: bytes@ },
            Msg::BodyEnd => Message::BodyEnd,
        }
    }
}

/// The view of an optional message; `None` is failure.
pub open spec fn option_msg(m: Option<Msg>) -> Option<Message> {
    match m {
        Some(m) => Some(m@),
        None => None,
    }
}

fn copy(s: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// The text at index `i`, if the token there is a text string.
fn text_at(toks: &[Tok], i: usize) -> (r: Option<Vec<u8>>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(v) => views(toks@)[i as int] == crate::cbor::spec::Token::Text(v@),
            None => !(views(toks@)[i as int] is Text),
        },
{
    match toks.get(i) {
        Some(Tok::Text(v)) => Some(copy(v.as_slice())),
        _ => None,
    }
}

/// The byte string at index `i`, if the token there is one.
fn bytes_at(toks: &[Tok], i: usize) -> (r: Option<Vec<u8>>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(v) => views(toks@)[i as int] == crate::cbor::spec::Token::Bytes(v@),
            None => !(views(toks@)[i as int] is Bytes),
        },
{
    match toks.get(i) {
        Some(Tok::Bytes(v)) => Some(copy(v.as_slice())),
        _ => None,
    }
}

/// The unsigned integer at index `i`, if the token there is one.
fn uint_at(toks: &[Tok], i: usize) -> (r: Option<u64>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(n) => views(toks@)[i as int] == crate::cbor::spec::Token::Uint(n),
            None => !(views(toks@)[i as int] is Uint),
        },
{
    match toks.get(i) {
        Some(Tok::Uint(n)) => Some(*n),
        _ => None,
    }
}

/// The boolean at index `i`, if the token there is one.
fn bool_at(toks: &[Tok], i: usize) -> (r: Option<bool>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(b) => views(toks@)[i as int] == crate::cbor::spec::Token::Bool(b),
            None => !(views(toks@)[i as int] is Bool),
        },
{
    match toks.get(i) {
        Some(Tok::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// The message with this `tag` whose fields are the tokens after the first
/// two.
fn parse_fields(tag: u64, toks: &[Tok]) -> (r: Option<Msg>)
    requires
        toks.len() >= 2,
    ensures
        option_msg(r) == super::spec::parse_fields(tag, views(toks@).subrange(2, toks.len() as int)),
{
    // Never saturates: toks.len() >= 2.
    let k = toks.len().saturating_sub(2);
    let ghost f = views(toks@).subrange(2, toks.len() as int);
    assert(f.len() == k);
    assert forall|j: int| 0 <= j < f.len() implies f[j] == views(toks@)[j + 2] by {}
    if tag == 1 {
        if k == 0 { Some(Msg::CookieGet) } else { None }
    } else if tag == 2 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::CookieSet { cookie_string: s })
        } else { None }
    } else if tag == 3 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::StorageGetItem { key: s })
        } else { None }
    } else if tag == 4 {
        if k == 2 {
            match (text_at(toks, 2), text_at(toks, 3)) {
                (Some(a), Some(b)) => Some(Msg::StorageSetItem { key: a, value: b }),
                _ => None,
            }
        } else { None }
    } else if tag == 5 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::StorageRemoveItem { key: s })
        } else { None }
    } else if tag == 6 {
        if k == 0 { Some(Msg::StorageClear) } else { None }
    } else if tag == 7 {
        if k == 1 {
            let n = uint_at(toks, 2)?;
            Some(Msg::StorageKey { index: n })
        } else { None }
    } else if tag == 8 {
        if k == 0 { Some(Msg::StorageLength) } else { None }
    } else if tag == 9 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::Navigate { url: s })
        } else { None }
    } else if tag == 101 {
        if k == 3 {
            match (text_at(toks, 2), bytes_at(toks, 3), uint_at(toks, 4)) {
                (Some(a), Some(b), Some(c)) => Some(Msg::Commit { url: a, content_type: b, kind: c }),
                _ => None,
            }
        } else { None }
    } else if tag == 102 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::CookieValue { cookie_string: s })
        } else { None }
    } else if tag == 103 {
        if k == 1 {
            match bool_at(toks, 2) {
                Some(false) => Some(Msg::StorageValue { value: None }),
                _ => None,
            }
        } else if k == 2 {
            match (bool_at(toks, 2), text_at(toks, 3)) {
                (Some(true), Some(v)) => Some(Msg::StorageValue { value: Some(v) }),
                _ => None,
            }
        } else { None }
    } else if tag == 104 {
        if k == 1 {
            let n = uint_at(toks, 2)?;
            Some(Msg::StorageLengthValue { length: n })
        } else { None }
    } else if tag == 105 {
        if k == 1 {
            let n = uint_at(toks, 2)?;
            Some(Msg::Error { code: n })
        } else { None }
    } else if tag == 106 {
        if k == 1 {
            let b = bytes_at(toks, 2)?;
            Some(Msg::Body { bytes: b })
        } else { None }
    } else if tag == 107 {
        if k == 0 { Some(Msg::BodyEnd) } else { None }
    } else {
        None
    }
}

/// `Display` from the element count `n` and the tokens: see
/// [`super::spec::parse_display`].
fn parse_display(n: u64, toks: &[Tok]) -> (r: Option<Msg>)
    requires
        toks.len() >= 2,
    ensures
        option_msg(r) == super::spec::parse_display(n, views(toks@).subrange(2, toks.len() as int)),
{
    let ghost f = views(toks@).subrange(2, toks.len() as int);
    assert forall|j: int| 0 <= j < f.len() implies f[j] == views(toks@)[j + 2] by {}
    if n != 4 || toks.len() < 5 {
        assert(super::spec::parse_display(n, f) is None);
        return None;
    }
    let title = match text_at(toks, 2) {
        Some(a) => a,
        None => {
            assert(super::spec::parse_display(n, f) is None);
            return None;
        },
    };
    let text = match text_at(toks, 3) {
        Some(b) => b,
        None => {
            assert(super::spec::parse_display(n, f) is None);
            return None;
        },
    };
    let k = match toks.get(4) {
        Some(Tok::Array(k)) => *k,
        _ => {
            assert(!(views(toks@)[4] is Array));
            assert(super::spec::parse_display(n, f) is None);
            return None;
        },
    };
    assert(f[0] == crate::cbor::spec::Token::Text(title@));
    assert(f[1] == crate::cbor::spec::Token::Text(text@));
    assert(f[2] == crate::cbor::spec::Token::Array(k));
    let ghost rest = f.subrange(3, f.len() as int);
    assert forall|j: int| 0 <= j < rest.len() implies rest[j] == views(toks@)[j + 5] by {}
    // toks.len() >= 5, so this does not saturate.
    let count = toks.len().saturating_sub(5);
    assert(count as nat == rest.len());
    if k != count as u64 {
        assert(super::spec::parse_display(n, f) is None);
        return None;
    }
    let mut links: Vec<Vec<u8>> = Vec::new();
    let mut j: usize = 5;
    while j < toks.len()
        invariant
            5 <= j <= toks.len(),
            n == 4,
            f == views(toks@).subrange(2, toks.len() as int),
            f.len() >= 3,
            f[0] == crate::cbor::spec::Token::Text(title@),
            f[1] == crate::cbor::spec::Token::Text(text@),
            f[2] == crate::cbor::spec::Token::Array(k),
            rest == f.subrange(3, f.len() as int),
            k as nat == rest.len(),
            rest.len() == toks.len() - 5,
            forall|x: int| 0 <= x < rest.len() ==> rest[x] == views(toks@)[x + 5],
            links@.len() == j - 5,
            forall|x: int| 0 <= x < j - 5 ==> (#[trigger] rest[x]) is Text && links@[x]@ == rest[x]->Text_0,
        decreases toks.len() - j,
    {
        match text_at(toks, j) {
            Some(v) => links.push(v),
            None => {
                assert(!(rest[j - 5] is Text));
                proof {
                    super::lemmas::lemma_all_text(rest);
                }
                assert(!super::spec::all_text(rest));
                assert(super::spec::parse_display(n, f) is None);
                return None;
            },
        }
        j = j.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_all_text(rest);
    }
    assert(super::spec::all_text(rest));
    assert(strings_view(links@) =~= super::spec::texts_of(rest));
    assert(super::spec::parse_display(n, f) == Some(super::spec::Message::Display { title: title@, text: text@, links: strings_view(links@) }));
    Some(Msg::Display { title, text, links })
}

/// The message in a token sequence.
fn parse_message(toks: &[Tok]) -> (r: Option<Msg>)
    ensures
        option_msg(r) == super::spec::parse_message(views(toks@)),
{
    if toks.len() < 2 {
        return None;
    }
    let n = match toks.first() {
        Some(Tok::Array(n)) => *n,
        _ => return None,
    };
    let tag = uint_at(toks, 1)?;
    if tag == 10 {
        return parse_display(n, toks);
    }
    // toks.len() >= 2, so this does not saturate.
    if n == (toks.len() as u64).saturating_sub(1) {
        parse_fields(tag, toks)
    } else {
        None
    }
}

/// Decode one message, in either direction, from the bytes of a CBOR item.
pub fn decode_message(input: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_message_ensures(input@, option_msg(output)),
{
    let toks = crate::cbor::decode::decode(input)?;
    parse_message(toks.as_slice())
}

/// Whether `m` is sent by a renderer to the kernel.
pub fn is_from_renderer(m: &Msg) -> (r: bool)
    ensures
        r == super::spec::is_from_renderer(m@),
{
    matches!(
        m,
        Msg::CookieGet
            | Msg::CookieSet { .. }
            | Msg::StorageGetItem { .. }
            | Msg::StorageSetItem { .. }
            | Msg::StorageRemoveItem { .. }
            | Msg::StorageClear
            | Msg::StorageKey { .. }
            | Msg::StorageLength
            | Msg::Navigate { .. }
            | Msg::Display { .. }
    )
}

/// Decode a message the kernel receives from a renderer: only
/// renderer-to-kernel messages.
pub fn decode_renderer_message(input: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_renderer_message_ensures(input@, option_msg(output)),
{
    let m = decode_message(input)?;
    if is_from_renderer(&m) { Some(m) } else { None }
}

/// Decode a message from a whole frame.
pub fn decode_framed(frame: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_framed_ensures(frame@, option_msg(output)),
{
    let payload = crate::frame::codec::decode_frame(frame)?;
    decode_message(payload.as_slice())
}

fn toks2(a: Tok, b: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@],
{
    let t = vec![a, b];
    assert(views(t@) =~= seq![a@, b@]);
    t
}

fn toks3(a: Tok, b: Tok, c: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@, c@],
{
    let t = vec![a, b, c];
    assert(views(t@) =~= seq![a@, b@, c@]);
    t
}

fn toks4(a: Tok, b: Tok, c: Tok, d: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@, c@, d@],
{
    let t = vec![a, b, c, d];
    assert(views(t@) =~= seq![a@, b@, c@, d@]);
    t
}

fn toks5(a: Tok, b: Tok, c: Tok, d: Tok, e: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@, c@, d@, e@],
{
    let t = vec![a, b, c, d, e];
    assert(views(t@) =~= seq![a@, b@, c@, d@, e@]);
    t
}

/// The tokens of `Display`: [`super::spec::display_tokens`].
fn display_tokens(title: &[u8], text: &[u8], links: &[Vec<u8>]) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= super::spec::display_tokens(title@, text@, strings_view(links@)),
{
    let ghost lv = strings_view(links@);
    let mut t = toks5(Tok::Array(4), Tok::Uint(10), Tok::Text(copy(title)), Tok::Text(copy(text)), Tok::Array(links.len() as u64));
    let ghost head = views(t@);
    let mut j: usize = 0;
    while j < links.len()
        invariant
            j <= links.len(),
            lv == strings_view(links@),
            lv.len() == links@.len(),
            views(t@) =~= head + super::spec::text_tokens(lv.take(j as int)),
        decreases links.len() - j,
    {
        let v = match links.get(j) {
            Some(l) => copy(l.as_slice()),
            None => Vec::new(),
        };
        proof {
            lemma_views_push(t@, Tok::Text(v));
            assert(lv.take(j as int + 1) =~= lv.take(j as int).push(lv[j as int]));
            assert(super::spec::text_tokens(lv.take(j as int + 1)) =~= super::spec::text_tokens(lv.take(j as int)).push(crate::cbor::spec::Token::Text(lv[j as int])));
        }
        t.push(Tok::Text(v));
        j = j.saturating_add(1);
    }
    assert(lv.take(links.len() as int) =~= lv);
    t
}

/// The tokens of a message.
fn message_tokens(m: &Msg) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= super::spec::message_tokens(m@),
{
    match m {
        Msg::CookieGet => toks2(Tok::Array(1), Tok::Uint(1)),
        Msg::CookieSet { cookie_string } => toks3(Tok::Array(2), Tok::Uint(2), Tok::Text(copy(cookie_string.as_slice()))),
        Msg::StorageGetItem { key } => toks3(Tok::Array(2), Tok::Uint(3), Tok::Text(copy(key.as_slice()))),
        Msg::StorageSetItem { key, value } => toks4(
            Tok::Array(3),
            Tok::Uint(4),
            Tok::Text(copy(key.as_slice())),
            Tok::Text(copy(value.as_slice())),
        ),
        Msg::StorageRemoveItem { key } => toks3(Tok::Array(2), Tok::Uint(5), Tok::Text(copy(key.as_slice()))),
        Msg::StorageClear => toks2(Tok::Array(1), Tok::Uint(6)),
        Msg::StorageKey { index } => toks3(Tok::Array(2), Tok::Uint(7), Tok::Uint(*index)),
        Msg::StorageLength => toks2(Tok::Array(1), Tok::Uint(8)),
        Msg::Navigate { url } => toks3(Tok::Array(2), Tok::Uint(9), Tok::Text(copy(url.as_slice()))),
        Msg::Display { title, text, links } => display_tokens(title.as_slice(), text.as_slice(), links.as_slice()),
        Msg::Commit { url, content_type, kind } => toks5(
            Tok::Array(4),
            Tok::Uint(101),
            Tok::Text(copy(url.as_slice())),
            Tok::Bytes(copy(content_type.as_slice())),
            Tok::Uint(*kind),
        ),
        Msg::CookieValue { cookie_string } => toks3(Tok::Array(2), Tok::Uint(102), Tok::Text(copy(cookie_string.as_slice()))),
        Msg::StorageValue { value } => match value {
            None => toks3(Tok::Array(2), Tok::Uint(103), Tok::Bool(false)),
            Some(v) => toks4(Tok::Array(3), Tok::Uint(103), Tok::Bool(true), Tok::Text(copy(v.as_slice()))),
        },
        Msg::StorageLengthValue { length } => toks3(Tok::Array(2), Tok::Uint(104), Tok::Uint(*length)),
        Msg::Error { code } => toks3(Tok::Array(2), Tok::Uint(105), Tok::Uint(*code)),
        Msg::Body { bytes } => toks3(Tok::Array(2), Tok::Uint(106), Tok::Bytes(copy(bytes.as_slice()))),
        Msg::BodyEnd => toks2(Tok::Array(1), Tok::Uint(107)),
    }
}

/// The bytes of a message.
pub fn encode_message(m: &Msg) -> (output: Vec<u8>)
    requires
        super::contract::encode_message_requires(m@),
    ensures
        super::contract::encode_message_ensures(m@, output@),
{
    let toks = message_tokens(m);
    assert(views(toks@) =~= message_tokens_spec(m@));
    crate::cbor::encode::encode(toks.as_slice())
}

/// The frame of a message; `None` if its bytes are over `MAX_FRAME`.
pub fn encode_framed(m: &Msg) -> (output: Option<Vec<u8>>)
    requires
        super::contract::encode_message_requires(m@),
    ensures
        super::contract::encode_framed_ensures(
            m@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    let payload = encode_message(m);
    crate::frame::codec::encode_frame(payload.as_slice())
}

/// The spec's tokens of a message (a name for the spec function, which the
/// exec function of the same name shadows).
spec fn message_tokens_spec(m: Message) -> Seq<crate::cbor::spec::Token> {
    super::spec::message_tokens(m)
}

} // verus!
