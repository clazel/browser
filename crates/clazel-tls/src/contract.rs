//! Contracts the executable functions must be proven to meet. Each exec
//! function's `ensures` clause is exactly one of these predicates, so
//! reviewing these (and [`super::spec`]) is enough to know what the
//! implementation guarantees.
//!
//! An exec value is related to its spec value by `View`: a byte slice or
//! `Vec<u8>` to its `Seq<u8>`, a [`Cur`](super::reader::Cur) to the bytes
//! it has not yet consumed, a message struct to the spec struct of the
//! same name.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §3: the cursor.
// ---------------------------------------------------------------------------

/// `Cur::uint(w)`: `before` is the cursor's bytes when called, `after` its
/// bytes after. A value is returned exactly when [`read_uint`] reads one,
/// and then `after` is what it leaves.
pub open spec fn uint_ensures(before: Seq<u8>, w: nat, r: Option<u64>, after: Seq<u8>) -> bool {
    match r {
        Some(v) => read_uint(before, w) == Some((v as nat, after)),
        None => read_uint(before, w) is None,
    }
}

/// `Cur::fixed(n)`: the `n` bytes returned, as [`read_fixed`] reads them.
pub open spec fn fixed_ensures(before: Seq<u8>, n: nat, r: Option<Seq<u8>>, after: Seq<u8>) -> bool {
    match r {
        Some(s) => read_fixed(before, n) == Some((s, after)),
        None => read_fixed(before, n) is None,
    }
}

/// `Cur::vec(floor, ceil)`: the cursor returned holds the vector's
/// contents, as [`read_vec`] reads them; the cursor called on is left
/// after them.
pub open spec fn vec_ensures(
    before: Seq<u8>,
    floor: nat,
    ceil: nat,
    r: Option<Seq<u8>>,
    after: Seq<u8>,
) -> bool {
    match r {
        Some(c) => read_vec(before, floor, ceil) == Some((c, after)),
        None => read_vec(before, floor, ceil) is None,
    }
}

// ---------------------------------------------------------------------------
// §5.1 to §5.3: records.
// ---------------------------------------------------------------------------

/// `read_record(input, protected)`: the outcome is [`read_record`]'s.
pub open spec fn read_record_ensures(input: Seq<u8>, protected: bool, out: Read<Frame>) -> bool {
    out == read_record(input, protected)
}

/// Appending a record header: `after` is `before` and [`write_record_header`].
pub open spec fn write_record_header_ensures(
    before: Seq<u8>,
    ctype: u8,
    version: u16,
    length: nat,
    after: Seq<u8>,
) -> bool {
    after == before + write_record_header(ctype, version, length)
}

/// Appending a `TLSPlaintext`: `after` is `before` and [`write_plaintext`].
pub open spec fn write_plaintext_ensures(
    before: Seq<u8>,
    ctype: u8,
    version: u16,
    fragment: Seq<u8>,
    after: Seq<u8>,
) -> bool {
    after == before + write_plaintext(ctype, version, fragment)
}

/// `additional_data(length)`: the five bytes of [`additional_data`].
pub open spec fn additional_data_ensures(length: nat, out: Seq<u8>) -> bool {
    out == additional_data(length)
}

/// `per_record_nonce(iv, seqno)`: [`per_record_nonce`].
pub open spec fn per_record_nonce_ensures(iv: Seq<u8>, seqno: u64, out: Seq<u8>) -> bool {
    out == per_record_nonce(iv, seqno)
}

/// `split_inner_plaintext(p)`: the content length and type
/// [`split_inner_plaintext`] finds (the content is the first `n` bytes).
pub open spec fn split_inner_ensures(p: Seq<u8>, out: Option<(usize, u8)>) -> bool {
    match out {
        Some((n, t)) => split_inner_plaintext(p) == Some((p.take(n as int), t)),
        None => split_inner_plaintext(p) is None,
    }
}

/// §5.4: full inner plaintext includes the content type and all padding.
pub open spec fn inner_length_requires(content: Seq<u8>, padding: nat) -> bool {
    content.len() + 1 + padding <= MAX_PLAINTEXT + 1
}

/// `open_inner_plaintext(p)`: [`open_inner_plaintext`].
pub open spec fn open_inner_ensures(p: Seq<u8>, out: Res<Record>) -> bool {
    out == open_inner_plaintext(p)
}

/// `Reassembler::feed_record` and `feed_ccs`: the result and the new
/// state are the spec's, and the state obeys its bound (an error leaves
/// the connection dead, so the state after one is not specified).
pub open spec fn feed_ensures(before: Reasm, out: Res<(Event, Reasm)>, after: Reasm) -> bool {
    match out {
        Res::Ok((ev, st)) => st == after,
        Res::Err(_) => true,
    }
}

/// The invariant the reassembler keeps: it never holds a whole message
/// header's length of a message above the limit, so it is bounded.
pub open spec fn reasm_inv(st: Reasm) -> bool {
    st.buf.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY
}

// ---------------------------------------------------------------------------
// §4.2: extensions.
// ---------------------------------------------------------------------------

/// `check_extensions(es, m)`: [`check_extensions`].
pub open spec fn check_extensions_ensures(es: Seq<Ext>, m: MsgKind, out: Option<ErrKind>) -> bool {
    out == check_extensions(es, m)
}

/// A reader of a list never produces more elements than it was given
/// bytes: a declared length cannot make it reserve memory for elements
/// that are not there.
pub open spec fn alloc_ensures(input_len: nat, output_len: Option<nat>) -> bool {
    match output_len {
        Some(n) => n <= input_len,
        None => true,
    }
}

// ---------------------------------------------------------------------------
// §4: handshake messages.
// ---------------------------------------------------------------------------

/// `parse_handshake(msg, hash_len)`: [`parse_handshake`].
pub open spec fn parse_handshake_ensures(msg: Seq<u8>, hash_len: nat, out: Res<HsMsg>) -> bool {
    out == parse_handshake(msg, hash_len)
}

/// Appending a ClientHello's body: `after` is `before` and
/// [`write_client_hello`]. The precondition is that the hello is one the
/// encoding can hold.
pub open spec fn client_hello_requires(ch: ClientHello) -> bool {
    &&& ch.random.len() == 32
    &&& vec_in_bounds(ch.session_id, 0, 32)
    &&& 1 <= ch.cipher_suites.len() <= 32767
    &&& vec_in_bounds(ch.compression, 1, 255)
    &&& forall|i: int| 0 <= i < ch.extensions.len() ==> (#[trigger] ch.extensions[i]).data.len() <= 65535
    &&& vec_in_bounds(write_list(ch.extensions, |e: Ext| write_ext(e)), 8, 65535)
}

/// `write_client_hello(out, ch)`.
pub open spec fn write_client_hello_ensures(before: Seq<u8>, ch: ClientHello, after: Seq<u8>) -> bool {
    after == before + write_client_hello(ch)
}

/// `write_handshake(out, t, body)` (the header, then the body); the body
/// is below 2^24 bytes.
pub open spec fn write_handshake_ensures(before: Seq<u8>, t: u8, body: Seq<u8>, after: Seq<u8>) -> bool {
    after == before + write_handshake(t, body)
}

/// `write_alert(out, a)`.
pub open spec fn write_alert_ensures(before: Seq<u8>, a: Alert, after: Seq<u8>) -> bool {
    after == before + write_alert(a)
}

/// `read_alert(b)`: [`read_alert`].
pub open spec fn read_alert_ensures(b: Seq<u8>, out: Option<Alert>) -> bool {
    out == read_alert(b)
}

} // verus!
