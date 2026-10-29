//! The frames the kernel sends to renderers: [`crate::spec::reply_frame`],
//! [`crate::spec::error_frame`] and [`crate::spec::commit_frames`], as exec
//! functions over the IPC codec (item 2.3; the document frames, item 4.12).

use clazel_ipc::message::codec::{Msg, encode_message};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A text string the profile can encode.
pub open spec fn text_ok(s: Seq<u8>) -> bool {
    clazel_ipc::cbor::spec::token_ok(clazel_ipc::cbor::spec::Token::Text(s))
}

/// A byte string the profile can encode.
pub open spec fn bytes_ok(s: Seq<u8>) -> bool {
    clazel_ipc::cbor::spec::token_ok(clazel_ipc::cbor::spec::Token::Bytes(s))
}

/// One step of [`is_items`].
proof fn lemma_items_step(t: Seq<clazel_ipc::cbor::spec::Token>, p: nat)
    requires
        t.len() > 0,
        p > 0,
    ensures
        clazel_ipc::cbor::spec::is_items(t, p) == (clazel_ipc::cbor::spec::token_ok(t[0]) && clazel_ipc::cbor::spec::is_items(t.drop_first(), clazel_ipc::cbor::spec::pending_after(p, t[0]))),
{
}

/// The empty sequence of tokens.
proof fn lemma_items_empty(p: nat)
    ensures
        clazel_ipc::cbor::spec::is_items(Seq::<clazel_ipc::cbor::spec::Token>::empty(), p) == (p == 0),
{
}

/// `[Array(n), Uint(tag), t...]`, whatever the rest.
proof fn lemma_items_head(n: u64, tag: u64, rest: Seq<clazel_ipc::cbor::spec::Token>)
    requires
        n >= 1,
    ensures
        clazel_ipc::cbor::spec::is_item(seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest) == clazel_ipc::cbor::spec::is_items(rest, (n - 1) as nat),
{
    let t = seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest;
    lemma_items_step(t, 1);
    assert(t[0] == clazel_ipc::cbor::spec::Token::Array(n));
    assert(t.drop_first() =~= seq![clazel_ipc::cbor::spec::Token::Uint(tag)] + rest);
    assert(clazel_ipc::cbor::spec::pending_after(1, clazel_ipc::cbor::spec::Token::Array(n)) == n as nat);
    let t1 = seq![clazel_ipc::cbor::spec::Token::Uint(tag)] + rest;
    lemma_items_step(t1, n as nat);
    assert(t1[0] == clazel_ipc::cbor::spec::Token::Uint(tag));
    assert(t1.drop_first() =~= rest);
    assert(clazel_ipc::cbor::spec::pending_after(n as nat, clazel_ipc::cbor::spec::Token::Uint(tag)) == (n - 1) as nat);
}

/// The exact condition under which a message can be sent: every text string
/// in it is valid UTF-8 (and short enough, which any sequence is, as a `Vec`).
pub open spec fn message_texts_ok(m: clazel_ipc::message::spec::Message) -> bool {
    match m {
        clazel_ipc::message::spec::Message::CookieGet | clazel_ipc::message::spec::Message::StorageClear | clazel_ipc::message::spec::Message::StorageLength => true,
        clazel_ipc::message::spec::Message::StorageKey { .. } | clazel_ipc::message::spec::Message::StorageLengthValue { .. } | clazel_ipc::message::spec::Message::Error { .. } => true,
        clazel_ipc::message::spec::Message::CookieSet { cookie_string } | clazel_ipc::message::spec::Message::CookieValue { cookie_string } => text_ok(cookie_string),
        clazel_ipc::message::spec::Message::StorageGetItem { key } | clazel_ipc::message::spec::Message::StorageRemoveItem { key } => text_ok(key),
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => text_ok(key) && text_ok(value),
        clazel_ipc::message::spec::Message::Navigate { url } => text_ok(url),
        clazel_ipc::message::spec::Message::Display { title, text, links } => text_ok(title) && text_ok(text) && links.len() < 0x1_0000_0000_0000_0000
            && forall|j: int| 0 <= j < links.len() ==> text_ok(#[trigger] links[j]),
        clazel_ipc::message::spec::Message::Commit { url, content_type, .. } => text_ok(url) && bytes_ok(content_type),
        clazel_ipc::message::spec::Message::Body { bytes } => bytes_ok(bytes),
        clazel_ipc::message::spec::Message::BodyEnd => true,
        clazel_ipc::message::spec::Message::StorageValue { value } => match value {
            None => true,
            Some(v) => text_ok(v),
        },
    }
}

/// `message_ok` from the tokens after the head.
proof fn lemma_msg(m: clazel_ipc::message::spec::Message, n: u64, tag: u64, rest: Seq<clazel_ipc::cbor::spec::Token>)
    requires
        n >= 1,
        clazel_ipc::message::spec::message_tokens(m) =~= seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest,
    ensures
        clazel_ipc::message::spec::message_ok(m) == clazel_ipc::cbor::spec::is_items(rest, (n - 1) as nat),
{
    lemma_items_head(n, tag, rest);
    assert(clazel_ipc::message::spec::message_tokens(m) == seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest);
}

/// A message can be sent exactly when its texts are valid UTF-8.
pub proof fn lemma_message_ok(m: clazel_ipc::message::spec::Message)
    ensures
        clazel_ipc::message::spec::message_ok(m) == message_texts_ok(m),
{
    match m {
        clazel_ipc::message::spec::Message::CookieGet => {
            lemma_msg(m, 1, 1, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::StorageClear => {
            lemma_msg(m, 1, 6, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::StorageLength => {
            lemma_msg(m, 1, 8, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::StorageKey { index } => {
            lemma_msg(m, 2, 7, seq![clazel_ipc::cbor::spec::Token::Uint(index)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Uint(index));
        },
        clazel_ipc::message::spec::Message::StorageLengthValue { length } => {
            lemma_msg(m, 2, 104, seq![clazel_ipc::cbor::spec::Token::Uint(length)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Uint(length));
        },
        clazel_ipc::message::spec::Message::Error { code } => {
            lemma_msg(m, 2, 105, seq![clazel_ipc::cbor::spec::Token::Uint(code)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Uint(code));
        },
        clazel_ipc::message::spec::Message::CookieSet { cookie_string } => {
            lemma_msg(m, 2, 2, seq![clazel_ipc::cbor::spec::Token::Text(cookie_string)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(cookie_string));
        },
        clazel_ipc::message::spec::Message::CookieValue { cookie_string } => {
            lemma_msg(m, 2, 102, seq![clazel_ipc::cbor::spec::Token::Text(cookie_string)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(cookie_string));
        },
        clazel_ipc::message::spec::Message::StorageGetItem { key } => {
            lemma_msg(m, 2, 3, seq![clazel_ipc::cbor::spec::Token::Text(key)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(key));
        },
        clazel_ipc::message::spec::Message::StorageRemoveItem { key } => {
            lemma_msg(m, 2, 5, seq![clazel_ipc::cbor::spec::Token::Text(key)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(key));
        },
        clazel_ipc::message::spec::Message::Navigate { url } => {
            lemma_msg(m, 2, 9, seq![clazel_ipc::cbor::spec::Token::Text(url)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(url));
        },
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => {
            lemma_msg(m, 3, 4, seq![clazel_ipc::cbor::spec::Token::Text(key), clazel_ipc::cbor::spec::Token::Text(value)]);
            lemma_two(clazel_ipc::cbor::spec::Token::Text(key), clazel_ipc::cbor::spec::Token::Text(value));
        },
        clazel_ipc::message::spec::Message::Commit { url, content_type, kind } => {
            lemma_msg(
                m,
                4,
                101,
                seq![clazel_ipc::cbor::spec::Token::Text(url), clazel_ipc::cbor::spec::Token::Bytes(content_type), clazel_ipc::cbor::spec::Token::Uint(kind)],
            );
            lemma_three(clazel_ipc::cbor::spec::Token::Text(url), clazel_ipc::cbor::spec::Token::Bytes(content_type), clazel_ipc::cbor::spec::Token::Uint(kind));
        },
        clazel_ipc::message::spec::Message::Body { bytes } => {
            lemma_msg(m, 2, 106, seq![clazel_ipc::cbor::spec::Token::Bytes(bytes)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Bytes(bytes));
        },
        clazel_ipc::message::spec::Message::BodyEnd => {
            lemma_msg(m, 1, 107, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::Display { title, text, links } => {
            clazel_ipc::message::lemmas::lemma_display_ok(title, text, links);
        },
        clazel_ipc::message::spec::Message::StorageValue { value } => match value {
            None => {
                lemma_msg(m, 2, 103, seq![clazel_ipc::cbor::spec::Token::Bool(false)]);
                lemma_one(clazel_ipc::cbor::spec::Token::Bool(false));
            },
            Some(v) => {
                lemma_msg(m, 3, 103, seq![clazel_ipc::cbor::spec::Token::Bool(true), clazel_ipc::cbor::spec::Token::Text(v)]);
                lemma_two(clazel_ipc::cbor::spec::Token::Bool(true), clazel_ipc::cbor::spec::Token::Text(v));
            },
        },
    }
}

/// One non-array token owed once.
proof fn lemma_one(a: clazel_ipc::cbor::spec::Token)
    requires
        !(a is Array),
    ensures
        clazel_ipc::cbor::spec::is_items(seq![a], 1) == clazel_ipc::cbor::spec::token_ok(a),
{
    lemma_items_step(seq![a], 1);
    assert(seq![a].drop_first() =~= Seq::<clazel_ipc::cbor::spec::Token>::empty());
    lemma_items_empty(0);
}

/// Three non-array tokens owed three times.
proof fn lemma_three(a: clazel_ipc::cbor::spec::Token, b: clazel_ipc::cbor::spec::Token, c: clazel_ipc::cbor::spec::Token)
    requires
        !(a is Array),
        !(b is Array),
        !(c is Array),
    ensures
        clazel_ipc::cbor::spec::is_items(seq![a, b, c], 3) == (clazel_ipc::cbor::spec::token_ok(a) && clazel_ipc::cbor::spec::token_ok(b)
            && clazel_ipc::cbor::spec::token_ok(c)),
{
    lemma_items_step(seq![a, b, c], 3);
    assert(seq![a, b, c].drop_first() =~= seq![b, c]);
    lemma_two(b, c);
}

/// Two non-array tokens owed twice.
proof fn lemma_two(a: clazel_ipc::cbor::spec::Token, b: clazel_ipc::cbor::spec::Token)
    requires
        !(a is Array),
        !(b is Array),
    ensures
        clazel_ipc::cbor::spec::is_items(seq![a, b], 2) == (clazel_ipc::cbor::spec::token_ok(a) && clazel_ipc::cbor::spec::token_ok(b)),
{
    lemma_items_step(seq![a, b], 2);
    assert(seq![a, b].drop_first() =~= seq![b]);
    lemma_one(b);
}

/// The length of a slice as a `u64` (a `usize` is at most 64 bits).
fn len_u64(s: &[u8]) -> (n: u64)
    ensures
        n as nat == s@.len(),
{
    s.len() as u64
}

/// The text string `s` can be sent (`utf8_valid`, as a `Vec` is short).
fn text_ok_exec(s: &[u8]) -> (r: bool)
    ensures
        r == text_ok(s@),
{
    let ok = clazel_encoding::utf8::decode::decode_without_bom_or_fail(s).is_some();
    let _n = len_u64(s);
    assert(_n as nat == s@.len());
    assert(ok == clazel_ipc::cbor::spec::utf8_valid(s@));
    assert(s@.len() < 0x1_0000_0000_0000_0000);
    ok
}

/// The byte string `s` can be sent (as a `Vec`, it is short).
fn bytes_ok_exec(s: &[u8]) -> (r: bool)
    ensures
        r == bytes_ok(s@),
{
    let _n = len_u64(s);
    assert(s@.len() < 0x1_0000_0000_0000_0000);
    true
}

/// Every one of a list of text strings can be sent, and the list can.
fn texts_ok_exec(links: &[Vec<u8>]) -> (r: bool)
    ensures
        r == (clazel_ipc::message::codec::strings_view(links@).len() < 0x1_0000_0000_0000_0000 && forall|j: int|
            0 <= j < clazel_ipc::message::codec::strings_view(links@).len() ==> text_ok(
                #[trigger] clazel_ipc::message::codec::strings_view(links@)[j],
            )),
{
    let ghost lv = clazel_ipc::message::codec::strings_view(links@);
    let _n = links.len() as u64;
    assert(lv.len() < 0x1_0000_0000_0000_0000);
    let mut j: usize = 0;
    while j < links.len()
        invariant
            j <= links.len(),
            lv == clazel_ipc::message::codec::strings_view(links@),
            forall|x: int| 0 <= x < j ==> text_ok(#[trigger] lv[x]),
        decreases links.len() - j,
    {
        let ok = match links.get(j) {
            Some(l) => text_ok_exec(l.as_slice()),
            None => true,
        };
        if !ok {
            assert(!text_ok(lv[j as int]));
            return false;
        }
        j = j.saturating_add(1);
    }
    true
}

/// [`message_ok`] of an exec message.
pub fn message_ok_exec(m: &Msg) -> (r: bool)
    ensures
        r == clazel_ipc::message::spec::message_ok(m@),
{
    proof {
        lemma_message_ok(m@);
    }
    match m {
        Msg::CookieGet | Msg::StorageClear | Msg::StorageLength => true,
        Msg::StorageKey { .. } | Msg::StorageLengthValue { .. } | Msg::Error { .. } => true,
        Msg::CookieSet { cookie_string } | Msg::CookieValue { cookie_string } => text_ok_exec(cookie_string.as_slice()),
        Msg::StorageGetItem { key } | Msg::StorageRemoveItem { key } => text_ok_exec(key.as_slice()),
        Msg::StorageSetItem { key, value } => text_ok_exec(key.as_slice()) && text_ok_exec(value.as_slice()),
        Msg::Navigate { url } => text_ok_exec(url.as_slice()),
        Msg::Display { title, text, links } => text_ok_exec(title.as_slice()) && text_ok_exec(text.as_slice()) && texts_ok_exec(links.as_slice()),
        Msg::Commit { url, content_type, .. } => text_ok_exec(url.as_slice()) && bytes_ok_exec(content_type.as_slice()),
        Msg::Body { bytes } => bytes_ok_exec(bytes.as_slice()),
        Msg::BodyEnd => true,
        Msg::StorageValue { value } => match value {
            None => true,
            Some(v) => text_ok_exec(v.as_slice()),
        },
    }
}

/// [`error_frame`]: the frame of `Error { code }`, for `code` the kernel
/// uses (all are below 24, so the frame is 8 octets).
pub fn error_frame_exec(code: u64) -> (r: Vec<u8>)
    requires
        code < 24,
    ensures
        r@ == crate::spec::error_frame(code as u64),
{
    let m = Msg::Error { code };
    proof {
        lemma_message_ok(m@);
    }
    let payload = encode_message(&m);
    assert(payload@.len() <= clazel_ipc::frame::spec::MAX_FRAME as nat) by {
        assert(payload@ == clazel_ipc::message::spec::encode_message(m@));
        lemma_error_payload_len(code);
    }
    match clazel_ipc::frame::codec::encode_frame(payload.as_slice()) {
        Some(f) => f,
        None => {
            assert(false);
            Vec::new()
        },
    }
}

/// The payload of `Error { code }` for a small code is at most 3 tokens of
/// at most 2 octets.
proof fn lemma_error_payload_len(code: u64)
    requires
        code < 24,
    ensures
        clazel_ipc::message::spec::encode_message(clazel_ipc::message::spec::Message::Error { code }).len() <= 4,
{
    // encode_head(0, 105) is 2 octets, the others one.
    let t = clazel_ipc::message::spec::message_tokens(clazel_ipc::message::spec::Message::Error { code });
    assert(t == seq![clazel_ipc::cbor::spec::Token::Array(2), clazel_ipc::cbor::spec::Token::Uint(105), clazel_ipc::cbor::spec::Token::Uint(code)]);
    let e = clazel_ipc::cbor::spec::encode(t);
    assert(clazel_ipc::message::spec::encode_message(clazel_ipc::message::spec::Message::Error { code }) == e);
    reveal_with_fuel(clazel_ipc::cbor::spec::encode, 4);
    assert(t.drop_first() =~= seq![clazel_ipc::cbor::spec::Token::Uint(105), clazel_ipc::cbor::spec::Token::Uint(code)]);
    assert(t.drop_first().drop_first() =~= seq![clazel_ipc::cbor::spec::Token::Uint(code)]);
    assert(t.drop_first().drop_first().drop_first() =~= Seq::<clazel_ipc::cbor::spec::Token>::empty());
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(105, 1);
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(code as nat, 1);
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(2, 1);
    assert(clazel_ipc::cbor::spec::encode(Seq::<clazel_ipc::cbor::spec::Token>::empty()) == Seq::<u8>::empty());
}

/// [`reply_frame`] of an exec message.
pub fn reply_frame_exec(m: &Msg) -> (r: Vec<u8>)
    ensures
        r@ == crate::spec::reply_frame(m@),
{
    if message_ok_exec(m) {
        let payload = encode_message(m);
        match clazel_ipc::frame::codec::encode_frame(payload.as_slice()) {
            Some(f) => f,
            None => error_frame_exec(4),
        }
    } else {
        error_frame_exec(4)
    }
}

/// One more step of [`body_frames`]: the frames of `b` from `pos` are the
/// frame of the next piece, then the frames from where it ends.
proof fn lemma_body_frames_step(b: Seq<u8>, pos: nat)
    requires
        pos < b.len(),
    ensures
        crate::spec::body_frames(b.skip(pos as int)) == if b.len() - pos <= clazel_ipc::message::spec::max_body_chunk() {
            crate::spec::reply_frame(clazel_ipc::message::spec::Message::Body { bytes: b.skip(pos as int) })
        } else {
            crate::spec::reply_frame(
                clazel_ipc::message::spec::Message::Body {
                    bytes: b.subrange(pos as int, (pos + clazel_ipc::message::spec::max_body_chunk()) as int),
                },
            ) + crate::spec::body_frames(b.skip((pos + clazel_ipc::message::spec::max_body_chunk()) as int))
        },
{
    let r = b.skip(pos as int);
    let c = clazel_ipc::message::spec::max_body_chunk();
    assert(r.len() == b.len() - pos);
    if r.len() > c {
        assert(r.take(c as int) =~= b.subrange(pos as int, (pos + c) as int));
        assert(r.skip(c as int) =~= b.skip((pos + c) as int));
    }
}

/// [`commit_frames`]: the frames that commit the document of this content
/// type, kind and body at `url` (UTF-8 encoded): `Commit`, the `Body`
/// frames, each of at most `MAX_BODY_CHUNK` octets, and `BodyEnd`.
pub fn commit_frames_exec(url: &[u32], content_type: &[u8], kind: u64, body: &[u8]) -> (r: Vec<u8>)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(url@),
    ensures
        crate::contract::commit_frames_ensures(url@, content_type@, kind, body@, r@),
{
    let encoded = clazel_encoding::utf8::encode::encode(url);
    let m = Msg::Commit { url: encoded, content_type: vstd::slice::slice_to_vec(content_type), kind };
    let mut out = reply_frame_exec(&m);
    let ghost head = out@;
    let ghost c = clazel_ipc::message::spec::max_body_chunk();
    proof {
        clazel_ipc::message::codec::lemma_max_body_chunk();
        assert(body@.skip(0) =~= body@);
    }
    let chunk = clazel_ipc::message::codec::MAX_BODY_CHUNK;
    let mut pos: usize = 0;
    while pos < body.len()
        invariant
            pos <= body.len(),
            c == clazel_ipc::message::spec::max_body_chunk(),
            chunk as nat == c,
            head + crate::spec::body_frames(body@) == out@ + crate::spec::body_frames(body@.skip(pos as int)),
        decreases body.len() - pos,
    {
        proof {
            lemma_body_frames_step(body@, pos as nat);
        }
        let rest = body.len().saturating_sub(pos);
        if rest <= chunk {
            let piece = reply_frame_exec(&Msg::Body { bytes: vstd::slice::slice_to_vec(slice_subrange(body, pos, body.len())) });
            proof {
                assert(body@.subrange(pos as int, body.len() as int) =~= body@.skip(pos as int));
                assert(body@.skip(body.len() as int) =~= Seq::<u8>::empty());
                assert(crate::spec::body_frames(Seq::<u8>::empty()) == Seq::<u8>::empty());
            }
            let ghost before = out@;
            out.extend_from_slice(piece.as_slice());
            assert(out@ =~= before + piece@);
            pos = body.len();
            assert(out@ + crate::spec::body_frames(body@.skip(pos as int)) =~= out@);
        } else {
            let end = pos.saturating_add(chunk);
            let piece = reply_frame_exec(&Msg::Body { bytes: vstd::slice::slice_to_vec(slice_subrange(body, pos, end)) });
            let ghost before = out@;
            out.extend_from_slice(piece.as_slice());
            assert(out@ =~= before + piece@);
            pos = end;
        }
    }
    let ghost before = out@;
    let tail = reply_frame_exec(&Msg::BodyEnd);
    out.extend_from_slice(tail.as_slice());
    proof {
        assert(body@.skip(body.len() as int) =~= Seq::<u8>::empty());
        assert(out@ =~= before + tail@);
        assert(out@ =~= head + crate::spec::body_frames(body@) + tail@);
    }
    out
}

/// The octets `s[from..to]`.
fn slice_subrange(s: &[u8], from: usize, to: usize) -> (r: &[u8])
    requires
        from <= to <= s.len(),
    ensures
        r@ == s@.subrange(from as int, to as int),
{
    vstd::slice::slice_subrange(s, from, to)
}

} // verus!
