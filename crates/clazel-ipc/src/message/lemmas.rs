//! Facts proven about the message schema: the three lemmas of item 2.2 lifted
//! to messages and frames (decode inverts encode, encode inverts decode so no
//! two byte strings are the same message, and decoding allocates no more
//! than the input), and the two schema rules.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`all_text`] is: every token is a text string.
pub proof fn lemma_all_text(ts: Seq<Token>)
    ensures
        all_text(ts) == forall|j: int| 0 <= j < ts.len() ==> (#[trigger] ts[j]) is Text,
    decreases ts.len(),
{
    if ts.len() > 0 {
        lemma_all_text(ts.drop_first());
        if forall|j: int| 0 <= j < ts.len() ==> (#[trigger] ts[j]) is Text {
            assert forall|j: int| 0 <= j < ts.drop_first().len() implies (#[trigger] ts.drop_first()[j]) is Text by {
                assert(ts.drop_first()[j] == ts[j + 1]);
            }
            assert(ts[0] is Text);
        }
        if all_text(ts) {
            assert forall|j: int| 0 <= j < ts.len() implies (#[trigger] ts[j]) is Text by {
                if j > 0 {
                    assert(ts[j] == ts.drop_first()[j - 1]);
                }
            }
        }
    }
}

/// The tokens of text strings are all text strings, and give the strings
/// back.
pub proof fn lemma_text_tokens(ls: Seq<Seq<u8>>)
    ensures
        text_tokens(ls).len() == ls.len(),
        all_text(text_tokens(ls)),
        texts_of(text_tokens(ls)) =~= ls,
{
    lemma_all_text(text_tokens(ls));
}

/// Text tokens are the tokens of their strings.
pub proof fn lemma_texts_of(ts: Seq<Token>)
    requires
        all_text(ts),
    ensures
        text_tokens(texts_of(ts)) =~= ts,
{
    lemma_all_text(ts);
    assert forall|j: int| 0 <= j < ts.len() implies text_tokens(texts_of(ts))[j] == ts[j] by {
        assert(ts[j] is Text);
    }
}

/// `k` text strings owed `p` items are one item each: exactly `p` of them,
/// each one the profile can encode.
pub proof fn lemma_items_texts(ls: Seq<Seq<u8>>, p: nat)
    ensures
        crate::cbor::spec::is_items(text_tokens(ls), p) == (ls.len() == p && forall|j: int|
            0 <= j < ls.len() ==> crate::cbor::spec::token_ok(Token::Text(#[trigger] ls[j]))),
    decreases ls.len(),
{
    let t = text_tokens(ls);
    if ls.len() > 0 && p > 0 {
        assert(t.drop_first() =~= text_tokens(ls.drop_first()));
        assert(crate::cbor::spec::pending_after(p, t[0]) == (p - 1) as nat);
        lemma_items_texts(ls.drop_first(), (p - 1) as nat);
        if crate::cbor::spec::is_items(t, p) {
            assert forall|j: int| 0 <= j < ls.len() implies crate::cbor::spec::token_ok(Token::Text(#[trigger] ls[j])) by {
                if j > 0 {
                    assert(ls[j] == ls.drop_first()[j - 1]);
                }
            }
        }
        if ls.len() == p && forall|j: int| 0 <= j < ls.len() ==> crate::cbor::spec::token_ok(Token::Text(#[trigger] ls[j])) {
            assert forall|j: int| 0 <= j < ls.drop_first().len() implies crate::cbor::spec::token_ok(Token::Text(#[trigger] ls.drop_first()[j])) by {
                assert(ls.drop_first()[j] == ls[j + 1]);
            }
            assert(crate::cbor::spec::token_ok(Token::Text(ls[0])));
        }
    }
}

/// One step of `is_items`.
proof fn lemma_items_step(t: Seq<Token>, p: nat)
    requires
        t.len() > 0,
        p > 0,
    ensures
        crate::cbor::spec::is_items(t, p) == (crate::cbor::spec::token_ok(t[0]) && crate::cbor::spec::is_items(
            t.drop_first(),
            crate::cbor::spec::pending_after(p, t[0]),
        )),
{
}

/// `[Array(n), Uint(tag), rest...]` is one item exactly when `rest` is the
/// tokens of `n - 1` items.
pub proof fn lemma_items_head(n: u64, tag: u64, rest: Seq<Token>)
    requires
        n >= 1,
    ensures
        is_item(seq![Token::Array(n), Token::Uint(tag)] + rest) == crate::cbor::spec::is_items(rest, (n - 1) as nat),
{
    let t = seq![Token::Array(n), Token::Uint(tag)] + rest;
    let t1 = seq![Token::Uint(tag)] + rest;
    lemma_items_step(t, 1);
    assert(t[0] == Token::Array(n));
    assert(t.drop_first() =~= t1);
    assert(crate::cbor::spec::pending_after(1, Token::Array(n)) == n as nat);
    lemma_items_step(t1, n as nat);
    assert(t1[0] == Token::Uint(tag));
    assert(t1.drop_first() =~= rest);
    assert(crate::cbor::spec::pending_after(n as nat, Token::Uint(tag)) == (n - 1) as nat);
}

/// `Display` can be sent exactly when its title, its text and each link is
/// valid UTF-8 and there are fewer than 2^64 links (as for every array).
pub proof fn lemma_display_ok(title: Seq<u8>, text: Seq<u8>, links: Seq<Seq<u8>>)
    ensures
        message_ok(Message::Display { title, text, links }) == (crate::cbor::spec::token_ok(Token::Text(title))
            && crate::cbor::spec::token_ok(Token::Text(text)) && links.len() < 0x1_0000_0000_0000_0000 && forall|j: int|
            0 <= j < links.len() ==> crate::cbor::spec::token_ok(Token::Text(#[trigger] links[j]))),
{
    let k = links.len() as u64;
    let tl = text_tokens(links);
    let r0 = seq![Token::Text(title), Token::Text(text), Token::Array(k)] + tl;
    let r1 = seq![Token::Text(text), Token::Array(k)] + tl;
    let r2 = seq![Token::Array(k)] + tl;
    assert(display_tokens(title, text, links) =~= seq![Token::Array(4), Token::Uint(10)] + r0);
    lemma_items_head(4, 10, r0);
    lemma_items_step(r0, 3);
    assert(r0[0] == Token::Text(title));
    assert(r0.drop_first() =~= r1);
    lemma_items_step(r1, 2);
    assert(r1[0] == Token::Text(text));
    assert(r1.drop_first() =~= r2);
    lemma_items_step(r2, 1);
    assert(r2[0] == Token::Array(k));
    assert(r2.drop_first() =~= tl);
    assert(crate::cbor::spec::pending_after(1, Token::Array(k)) == k as nat);
    lemma_items_texts(links, k as nat);
    if links.len() < 0x1_0000_0000_0000_0000 {
        assert(k as nat == links.len());
    } else {
        assert(k as nat != links.len());
    }
}

/// A sendable message has fewer than 2^64 nested tokens.
pub proof fn lemma_nested_len_ok(m: Message)
    requires
        message_ok(m),
    ensures
        nested_len(m) < 0x1_0000_0000_0000_0000,
{
    if let Message::Display { title, text, links } = m {
        lemma_display_ok(title, text, links);
    }
}

/// A `Body` of at most [`max_body_chunk`] octets can be sent, and its bytes
/// fit one frame.
pub proof fn lemma_body_fits_frame(bytes: Seq<u8>)
    requires
        bytes.len() <= max_body_chunk(),
    ensures
        message_ok(Message::Body { bytes }),
        crate::frame::spec::payload_ok(encode_message(Message::Body { bytes })),
{
    let t = seq![Token::Array(2), Token::Uint(106), Token::Bytes(bytes)];
    assert(t =~= seq![Token::Array(2), Token::Uint(106)] + seq![Token::Bytes(bytes)]);
    lemma_items_head(2, 106, seq![Token::Bytes(bytes)]);
    lemma_items_step(seq![Token::Bytes(bytes)], 1);
    assert(seq![Token::Bytes(bytes)][0] == Token::Bytes(bytes));
    assert(seq![Token::Bytes(bytes)].drop_first() =~= Seq::<Token>::empty());
    assert(crate::cbor::spec::token_ok(Token::Bytes(bytes)));
    assert(crate::cbor::spec::is_items(Seq::<Token>::empty(), 0));
    reveal_with_fuel(crate::cbor::spec::encode, 4);
    assert(t.drop_first() =~= seq![Token::Uint(106), Token::Bytes(bytes)]);
    assert(t.drop_first().drop_first() =~= seq![Token::Bytes(bytes)]);
    assert(t.drop_first().drop_first().drop_first() =~= Seq::<Token>::empty());
    crate::cbor::lemmas::lemma_be_bytes_len(106, 1);
    crate::cbor::lemmas::lemma_be_bytes_len(bytes.len(), 1);
    crate::cbor::lemmas::lemma_be_bytes_len(bytes.len(), 2);
    crate::cbor::lemmas::lemma_be_bytes_len(bytes.len(), 4);
    assert(crate::cbor::spec::encode(Seq::<Token>::empty()) == Seq::<u8>::empty());
    assert(crate::cbor::spec::encode_head(2, bytes.len()).len() <= 5);
}

/// The tokens of a sendable message parse back to it.
pub proof fn lemma_parse_message_tokens(m: Message)
    requires
        nested_len(m) < 0x1_0000_0000_0000_0000,
    ensures
        parse_message(message_tokens(m)) == Some(m),
{
    let t = message_tokens(m);
    match m {
        Message::CookieGet => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::StorageClear => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::StorageLength => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::CookieSet { cookie_string } => { assert(t.subrange(2, 3) =~= seq![Token::Text(cookie_string)]); },
        Message::StorageGetItem { key } => { assert(t.subrange(2, 3) =~= seq![Token::Text(key)]); },
        Message::StorageSetItem { key, value } => { assert(t.subrange(2, 4) =~= seq![Token::Text(key), Token::Text(value)]); },
        Message::StorageRemoveItem { key } => { assert(t.subrange(2, 3) =~= seq![Token::Text(key)]); },
        Message::StorageKey { index } => { assert(t.subrange(2, 3) =~= seq![Token::Uint(index)]); },
        Message::Navigate { url } => { assert(t.subrange(2, 3) =~= seq![Token::Text(url)]); },
        Message::Display { title, text, links } => {
            let f = t.subrange(2, t.len() as int);
            assert(f =~= seq![Token::Text(title), Token::Text(text), Token::Array(links.len() as u64)] + text_tokens(links));
            assert(f.subrange(3, f.len() as int) =~= text_tokens(links));
            lemma_text_tokens(links);
        },
        Message::Commit { url, content_type, kind } => {
            assert(t.subrange(2, 5) =~= seq![Token::Text(url), Token::Bytes(content_type), Token::Uint(kind)]);
        },
        Message::Body { bytes } => { assert(t.subrange(2, 3) =~= seq![Token::Bytes(bytes)]); },
        Message::BodyEnd => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::CookieValue { cookie_string } => { assert(t.subrange(2, 3) =~= seq![Token::Text(cookie_string)]); },
        Message::StorageValue { value } => match value {
            None => { assert(t.subrange(2, 3) =~= seq![Token::Bool(false)]); },
            Some(v) => { assert(t.subrange(2, 4) =~= seq![Token::Bool(true), Token::Text(v)]); },
        },
        Message::StorageLengthValue { length } => { assert(t.subrange(2, 3) =~= seq![Token::Uint(length)]); },
        Message::Error { code } => { assert(t.subrange(2, 3) =~= seq![Token::Uint(code)]); },
    }
}

/// A token sequence that parses is the tokens of the message it parses to.
pub proof fn lemma_message_tokens_parse(t: Seq<Token>)
    ensures
        match parse_message(t) {
            Some(m) => message_tokens(m) =~= t,
            None => true,
        },
{
    if let Some(m) = parse_message(t) {
        let f = t.subrange(2, t.len() as int);
        if let Message::Display { title, text, links } = m {
            let n = t[0]->Array_0;
            assert(parse_display(n, f) == Some(m));
            let rest = f.subrange(3, f.len() as int);
            lemma_texts_of(rest);
            assert(t =~= seq![t[0], t[1]] + f);
            assert(f =~= seq![f[0], f[1], f[2]] + rest);
            assert(message_tokens(m) =~= t);
            return;
        }
        assert(parse_fields(match t[1] { Token::Uint(tag) => tag, _ => 0 }, f) == Some(m));
        assert(f.len() + 2 == t.len());
        assert forall|i: int| 0 <= i < f.len() implies f[i] == t[i + 2] by {}
        match m {
            Message::StorageValue { value } => match value {
                None => {},
                Some(_) => {},
            },
            _ => {},
        }
        assert(message_tokens(m) =~= t);
    }
}

/// Decode inverts encode: every sendable message decodes from its bytes.
pub proof fn lemma_decode_encode_message(m: Message)
    ensures
        message_ok(m) ==> decode_message(encode_message(m)) == Some(m),
{
    if message_ok(m) {
        crate::cbor::lemmas::lemma_decode_encode(message_tokens(m));
        lemma_nested_len_ok(m);
        lemma_parse_message_tokens(m);
    }
}

/// Encode inverts decode: a message that decodes is sendable, and its
/// bytes are exactly the input. No two byte strings are the same message.
pub proof fn lemma_encode_decode_message(b: Seq<u8>)
    ensures
        match decode_message(b) {
            Some(m) => message_ok(m) && encode_message(m) =~= b,
            None => true,
        },
{
    crate::cbor::lemmas::lemma_encode_decode(b);
    if let Some(t) = decode(b) {
        lemma_message_tokens_parse(t);
    }
}

/// Two byte strings that decode to the same message are equal: no parser
/// differential between kernel and renderer.
pub proof fn lemma_decode_message_injective(a: Seq<u8>, b: Seq<u8>)
    requires
        decode_message(a) is Some,
        decode_message(a) == decode_message(b),
    ensures
        a =~= b,
{
    lemma_encode_decode_message(a);
    lemma_encode_decode_message(b);
}

/// The kernel's decoder returns only renderer-to-kernel messages.
pub proof fn lemma_renderer_decode_direction(b: Seq<u8>)
    ensures
        match decode_renderer_message(b) {
            Some(m) => is_from_renderer(m) && decode_message(b) == Some(m),
            None => true,
        },
{
}

/// A message decoded from a few bytes has few tokens: decoding allocates no
/// more than there are input bytes.
pub proof fn lemma_decode_message_alloc_bound(b: Seq<u8>)
    ensures
        match decode_message(b) {
            Some(m) => message_tokens(m).len() <= b.len(),
            None => true,
        },
{
    crate::cbor::lemmas::lemma_decode_alloc_bound(b);
    if let Some(m) = decode_message(b) {
        let t = decode(b).unwrap();
        lemma_message_tokens_parse(t);
    }
}

/// The wire shape follows the field table: an array of the tag and the
/// fields, so a message carries exactly the fields in [`message_fields`]
/// (and `Display`'s links, which follow their array's token).
pub proof fn lemma_fields_match_tokens(m: Message)
    ensures
        message_tokens(m).len() == 2 + message_fields(m).len() + nested_len(m),
        message_tokens(m)[0] == Token::Array((1 + message_fields(m).len()) as u64),
{
    match m {
        Message::StorageValue { value } => match value {
            None => {},
            Some(_) => {},
        },
        _ => {},
    }
}

/// Schema rule 1 and 2: no message, in either direction, has a field that
/// is an origin, a renderer id, a tab id or the sender's URL. The kernel
/// learns the sender from the socket, and renderer ids never reach a
/// renderer.
pub proof fn lemma_no_identity_fields(m: Message)
    ensures
        forall|i: int| 0 <= i < message_fields(m).len() ==> !is_identity(#[trigger] message_fields(m)[i]),
{
    match m {
        Message::StorageValue { value } => match value {
            None => {},
            Some(_) => {},
        },
        _ => {},
    }
}

/// A renderer-to-kernel message carries no identity and the kernel-to-
/// renderer messages carry none either, so a renderer cannot claim, or
/// learn, who anyone is, through a message.
pub proof fn lemma_no_identity_on_the_wire(m: Message)
    ensures
        forall|i: int| 0 <= i < message_fields(m).len() ==> !is_identity(#[trigger] message_fields(m)[i]),
        message_tokens(m).len() == 2 + message_fields(m).len() + nested_len(m),
{
    lemma_no_identity_fields(m);
    lemma_fields_match_tokens(m);
}

// ---------------------------------------------------------------------------
// Frames and messages together.
// ---------------------------------------------------------------------------

/// A sendable message whose bytes fit a frame is received as itself.
pub proof fn lemma_decode_encode_framed(m: Message)
    ensures
        (message_ok(m) && crate::frame::spec::payload_ok(encode_message(m)))
            ==> decode_framed(crate::frame::spec::encode_frame(encode_message(m))) == Some(m),
{
    if message_ok(m) && crate::frame::spec::payload_ok(encode_message(m)) {
        crate::frame::lemmas::lemma_decode_encode_frame(encode_message(m));
        lemma_decode_encode_message(m);
    }
}

/// A frame that decodes to a message is exactly that message's frame.
pub proof fn lemma_encode_decode_framed(frame: Seq<u8>)
    ensures
        match decode_framed(frame) {
            Some(m) => {
                &&& message_ok(m)
                &&& crate::frame::spec::payload_ok(encode_message(m))
                &&& crate::frame::spec::encode_frame(encode_message(m)) =~= frame
            },
            None => true,
        },
{
    crate::frame::lemmas::lemma_encode_decode_frame(frame);
    if let Some(p) = crate::frame::spec::decode_frame(frame) {
        lemma_encode_decode_message(p);
    }
}

} // verus!
