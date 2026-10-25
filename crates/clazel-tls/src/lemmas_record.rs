//! Facts proven about the record layer of [`super::spec`] (RFC 8446 §5).
//! The ones that matter:
//!
//! - the record header round-trips ([`lemma_read_record_write_plaintext`])
//!   and what [`read_record`] accepts is one encoding
//!   ([`lemma_read_record_canonical`]);
//! - no over-read, and no decision before the data
//!   ([`lemma_read_record_extend`], [`lemma_read_record_prefix`]);
//! - the nonce ([`lemma_nonce_zero`], [`lemma_nonce_injective`]);
//! - protecting a record and reading it back gives the record, if the AEAD
//!   opens what it seals ([`lemma_encrypt_decrypt`]);
//! - the reassembler never buffers more than its bound
//!   ([`lemma_feed_bound`]), emits a message only when all its bytes have
//!   arrived and never loses or invents a byte
//!   ([`lemma_extract_conserves`], [`lemma_extract_prefix`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §5.1: the record header.
// ---------------------------------------------------------------------------

/// The header of a record is five bytes: the type, the version and the
/// length, in that order.
proof fn lemma_header_shape(t: u8, v: u16, len: nat)
    requires
        len < 65536,
    ensures
        write_record_header(t, v, len).len() == 5,
        write_record_header(t, v, len)[0] == t,
        write_record_header(t, v, len).subrange(1, 3) =~= be_bytes(v as nat, 2),
        write_record_header(t, v, len).subrange(3, 5) =~= be_bytes(len, 2),
{
    super::lemmas_pl::lemma_be_bytes_len(v as nat, 2);
    super::lemmas_pl::lemma_be_bytes_len(len, 2);
}

/// A record we write is read back as the record, whatever follows it, as
/// long as it is one the standard allows: an `alert` or `handshake`
/// fragment of 1 to 2^14 bytes, with a version [`legacy_record_version_ok`]
/// accepts.
pub proof fn lemma_read_record_write_plaintext(t: u8, v: u16, fragment: Seq<u8>, rest: Seq<u8>)
    requires
        t == CT_ALERT || t == CT_HANDSHAKE,
        legacy_record_version_ok(v, false),
        1 <= fragment.len() <= MAX_PLAINTEXT,
    ensures
        read_record(write_plaintext(t, v, fragment) + rest, false) == Read::Done(
            Frame::Plain(Record { ctype: t, fragment }),
            rest,
        ),
{
    super::lemmas_pl::lemma_pow256_widths();
    let len = fragment.len();
    lemma_header_shape(t, v, len);
    let hdr = write_record_header(t, v, len);
    let b = write_plaintext(t, v, fragment) + rest;
    assert(b =~= hdr + (fragment + rest));
    assert(b.subrange(1, 3) =~= be_bytes(v as nat, 2));
    assert(b.subrange(3, 5) =~= be_bytes(len, 2));
    super::lemmas_pl::lemma_be_value_of_be_bytes(v as nat, 2);
    super::lemmas_pl::lemma_be_value_of_be_bytes(len, 2);
    assert(b.subrange(5, (5 + len) as int) =~= fragment);
    assert(b.skip((5 + len) as int) =~= rest);
}

/// An unprotected change_cipher_spec record, as a middlebox-compatible
/// server sends it, is read as [`Frame::Ccs`].
pub proof fn lemma_read_record_ccs(v: u16, rest: Seq<u8>)
    requires
        legacy_record_version_ok(v, false),
    ensures
        read_record(write_plaintext(CT_CHANGE_CIPHER_SPEC, v, seq![1u8]) + rest, false) == Read::Done(Frame::Ccs, rest),
{
    super::lemmas_pl::lemma_pow256_widths();
    let fragment = seq![1u8];
    let len = fragment.len();
    lemma_header_shape(CT_CHANGE_CIPHER_SPEC, v, len);
    let hdr = write_record_header(CT_CHANGE_CIPHER_SPEC, v, len);
    let b = write_plaintext(CT_CHANGE_CIPHER_SPEC, v, fragment) + rest;
    assert(b =~= hdr + (fragment + rest));
    assert(b.subrange(1, 3) =~= be_bytes(v as nat, 2));
    assert(b.subrange(3, 5) =~= be_bytes(len, 2));
    super::lemmas_pl::lemma_be_value_of_be_bytes(v as nat, 2);
    super::lemmas_pl::lemma_be_value_of_be_bytes(len, 2);
    assert(b.subrange(5, (5 + len) as int) =~= fragment);
    assert(b.skip((5 + len) as int) =~= rest);
}

/// What [`read_record`] accepts is what the writers write: an unprotected
/// `alert` or `handshake` record is [`write_plaintext`] of its fragment, a
/// change_cipher_spec is that of `[1]`, and a protected record's header
/// is exactly the additional data of §5.2 for its length. In every case
/// the input is the record's bytes and the rest.
pub proof fn lemma_read_record_canonical(b: Seq<u8>, protected: bool)
    ensures
        match read_record(b, protected) {
            Read::Done(f, rest) => match f {
                Frame::Plain(rec) => {
                    &&& !protected
                    &&& (rec.ctype == CT_ALERT || rec.ctype == CT_HANDSHAKE)
                    &&& 1 <= rec.fragment.len() <= MAX_PLAINTEXT
                    &&& exists|v: u16| legacy_record_version_ok(v, protected) && b =~= write_plaintext(
                        rec.ctype,
                        v,
                        rec.fragment,
                    ) + rest
                },
                Frame::Ccs => {
                    exists|v: u16| legacy_record_version_ok(v, protected) && b =~= write_plaintext(
                        CT_CHANGE_CIPHER_SPEC,
                        v,
                        seq![1u8],
                    ) + rest
                },
                Frame::Protected(h, body) => {
                    &&& protected
                    &&& body.len() <= MAX_CIPHERTEXT
                    &&& h =~= additional_data(body.len())
                    &&& b =~= h + body + rest
                },
            },
            _ => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Read::Done(f, rest) = read_record(b, protected) {
        let t = b[0];
        let vn = be_value(b.subrange(1, 3));
        let v = vn as u16;
        let len = be_value(b.subrange(3, 5));
        super::lemmas_pl::lemma_be_value_bound(b.subrange(1, 3));
        super::lemmas_pl::lemma_be_value_bound(b.subrange(3, 5));
        super::lemmas_pl::lemma_be_bytes_of_be_value(b.subrange(1, 3));
        super::lemmas_pl::lemma_be_bytes_of_be_value(b.subrange(3, 5));
        assert(v as nat == vn);
        let hdr = write_record_header(t, v, len);
        lemma_header_shape(t, v, len);
        assert(b.take(5) =~= hdr) by {
            assert(b.take(5).subrange(1, 3) =~= b.subrange(1, 3));
            assert(b.take(5).subrange(3, 5) =~= b.subrange(3, 5));
            assert(hdr.subrange(1, 3) =~= be_bytes(vn, 2));
            assert(hdr.subrange(3, 5) =~= be_bytes(len, 2));
            assert(b.take(5)[0] == hdr[0]);
            assert forall|i: int| 0 <= i < 5 implies b.take(5)[i] == hdr[i] by {
                if i == 0 {
                } else if i < 3 {
                    assert(b.take(5).subrange(1, 3)[i - 1] == hdr.subrange(1, 3)[i - 1]);
                } else {
                    assert(b.take(5).subrange(3, 5)[i - 3] == hdr.subrange(3, 5)[i - 3]);
                }
            }
        }
        let body = b.subrange(5, (5 + len) as int);
        assert(b =~= b.take(5) + body + b.skip((5 + len) as int));
        match f {
            Frame::Plain(rec) => {
                assert(b =~= write_plaintext(rec.ctype, v, rec.fragment) + rest);
            },
            Frame::Ccs => {
                assert(b =~= write_plaintext(CT_CHANGE_CIPHER_SPEC, v, seq![1u8]) + rest);
            },
            Frame::Protected(h, bd) => {
                assert(h =~= additional_data(bd.len()));
            },
        }
    }
}

/// No over-read: the outcome of [`read_record`] on a stream does not
/// depend on the bytes after the record it finds, or after the point it
/// refuses it.
pub proof fn lemma_read_record_extend(b: Seq<u8>, protected: bool, extra: Seq<u8>)
    ensures
        match read_record(b, protected) {
            Read::Done(f, rest) => read_record(b + extra, protected) == Read::Done(f, rest + extra),
            Read::Fail(k) => read_record(b + extra, protected) == Read::Fail(k),
            Read::NeedMore => true,
        },
{
    if b.len() >= RECORD_HEADER {
        let bb = b + extra;
        assert(bb.subrange(1, 3) =~= b.subrange(1, 3));
        assert(bb.subrange(3, 5) =~= b.subrange(3, 5));
        assert(bb[0] == b[0]);
        let len = be_value(b.subrange(3, 5));
        if b.len() >= RECORD_HEADER + len {
            assert(bb.subrange(5, (5 + len) as int) =~= b.subrange(5, (5 + len) as int));
            assert(bb.skip((5 + len) as int) =~= b.skip((5 + len) as int) + extra);
            assert(bb.take(5) =~= b.take(5));
        }
    }
}

/// No decision before the data: if a record is complete in `b`, every
/// proper prefix of it is "need more", never a record and never an error.
/// (An error that the five header bytes already settle is made when they
/// are there, and a complete record has none.)
pub proof fn lemma_read_record_prefix(b: Seq<u8>, protected: bool, n: nat)
    requires
        read_record(b, protected) is Done,
        n < b.len() - (match read_record(b, protected) {
            Read::Done(_, rest) => rest.len(),
            _ => 0,
        }),
    ensures
        read_record(b.take(n as int), protected) is NeedMore,
{
    let p = b.take(n as int);
    if n >= RECORD_HEADER {
        assert(p.subrange(1, 3) =~= b.subrange(1, 3));
        assert(p.subrange(3, 5) =~= b.subrange(3, 5));
        assert(p[0] == b[0]);
    }
}

// ---------------------------------------------------------------------------
// §5.3: the nonce.
// ---------------------------------------------------------------------------

/// XOR with zero is the identity.
proof fn lemma_xor_zero(x: u8)
    ensures
        (x ^ 0u8) == x,
{
    assert((x ^ 0u8) == x) by (bit_vector);
}

/// XOR with a fixed byte is injective.
proof fn lemma_xor_cancel(a: u8, b: u8, c: u8)
    requires
        (a ^ b) == (a ^ c),
    ensures
        b == c,
{
    assert(((a ^ b) == (a ^ c)) ==> b == c) by (bit_vector);
}

/// The nonce is as long as the IV.
pub proof fn lemma_nonce_len(iv: Seq<u8>, seqno: u64)
    ensures
        per_record_nonce(iv, seqno).len() == iv.len(),
{
}

/// "the first record transmitted under a particular traffic key MUST use
/// sequence number 0": the nonce of record 0 is the IV.
pub proof fn lemma_nonce_zero(iv: Seq<u8>)
    ensures
        per_record_nonce(iv, 0) =~= iv,
{
    lemma_be_bytes_zero(iv.len());
    let n = per_record_nonce(iv, 0);
    assert forall|i: int| 0 <= i < iv.len() implies n[i] == iv[i] by {
        assert(be_bytes(0, iv.len())[i] == 0u8);
        lemma_xor_zero(iv[i]);
    }
}

/// Zero spelled in any width is all zero bytes.
proof fn lemma_be_bytes_zero(w: nat)
    ensures
        be_bytes(0, w).len() == w,
        forall|i: int| 0 <= i < w ==> be_bytes(0, w)[i] == 0u8,
    decreases w,
{
    super::lemmas_pl::lemma_be_bytes_len(0, w);
    if w > 0 {
        lemma_be_bytes_zero((w - 1) as nat);
        let s = be_bytes(0, (w - 1) as nat);
        assert(be_bytes(0, w) =~= s.push(0u8));
    }
}

/// "padded to the left with zeros to iv_length": with a 12 byte IV, the
/// first four bytes of the nonce are the IV's, and the last eight are the
/// IV's XORed with the sequence number, most significant byte first.
pub proof fn lemma_nonce_prefix(iv: Seq<u8>, seqno: u64)
    requires
        iv.len() >= 8,
    ensures
        forall|i: int| 0 <= i < iv.len() - 8 ==> per_record_nonce(iv, seqno)[i] == iv[i],
{
    super::lemmas_pl::lemma_pow256_widths();
    let w = iv.len();
    let padded = be_bytes(seqno as nat, w);
    lemma_be_bytes_high_zero(seqno as nat, w, 8);
    assert forall|i: int| 0 <= i < iv.len() - 8 implies per_record_nonce(iv, seqno)[i] == iv[i] by {
        assert(padded[i] == 0u8);
        lemma_xor_zero(iv[i]);
    }
}

/// A number below 256^k, spelled in `w >= k` bytes, has zeros in all but
/// the last `k` of them.
proof fn lemma_be_bytes_high_zero(v: nat, w: nat, k: nat)
    requires
        v < super::spec::pow256(k),
        w >= k,
    ensures
        forall|i: int| 0 <= i < w - k ==> be_bytes(v, w)[i] == 0u8,
    decreases w,
{
    super::lemmas_pl::lemma_be_bytes_len(v, w);
    if w > 0 {
        let s = be_bytes(v / 256, (w - 1) as nat);
        assert(be_bytes(v, w) =~= s.push((v % 256) as u8));
        if k == 0 {
            assert(super::spec::pow256(0) == 1);
            assert(v == 0);
            assert(v / 256 < super::spec::pow256(0));
            lemma_be_bytes_high_zero(v / 256, (w - 1) as nat, 0);
            assert(v % 256 == 0);
        } else {
            assert(super::spec::pow256(k) == 256 * super::spec::pow256((k - 1) as nat));
            assert(v / 256 < super::spec::pow256((k - 1) as nat)) by (nonlinear_arith)
                requires
                    v < 256 * super::spec::pow256((k - 1) as nat),
            ;
            lemma_be_bytes_high_zero(v / 256, (w - 1) as nat, (k - 1) as nat);
        }
    }
}

/// 256^w is at least 256^8 for w at least 8.
pub proof fn lemma_pow256_at_least_8(w: nat)
    requires
        w >= 8,
    ensures
        super::spec::pow256(w) >= 0x1_0000_0000_0000_0000,
    decreases w,
{
    super::lemmas_pl::lemma_pow256_widths();
    if w > 8 {
        lemma_pow256_at_least_8((w - 1) as nat);
        assert(super::spec::pow256(w) == 256 * super::spec::pow256((w - 1) as nat));
    }
}

/// Distinct sequence numbers give distinct nonces under one IV: a nonce
/// is never reused within a key's lifetime.
pub proof fn lemma_nonce_injective(iv: Seq<u8>, a: u64, b: u64)
    requires
        iv.len() >= 8,
        a != b,
    ensures
        per_record_nonce(iv, a) != per_record_nonce(iv, b),
{
    super::lemmas_pl::lemma_pow256_widths();
    let w = iv.len();
    // Pigeonhole on the tail is a detour: compare the be_bytes, which are
    // injective, byte by byte through the XOR with the same IV.
    let pa = be_bytes(a as nat, w);
    let pb = be_bytes(b as nat, w);
    assert(a as nat != b as nat);
    if per_record_nonce(iv, a) == per_record_nonce(iv, b) {
        assert forall|i: int| 0 <= i < w implies pa[i] == pb[i] by {
            assert(per_record_nonce(iv, a)[i] == (iv[i] ^ pa[i]) as u8);
            assert(per_record_nonce(iv, b)[i] == (iv[i] ^ pb[i]) as u8);
            lemma_xor_cancel(iv[i], pa[i], pb[i]);
        }
        super::lemmas_pl::lemma_be_bytes_len(a as nat, w);
        super::lemmas_pl::lemma_be_bytes_len(b as nat, w);
        assert(pa =~= pb);
        lemma_pow256_at_least_8(w);
        lemma_be_bytes_inj(a as nat, b as nat, w);
    }
}

/// [`be_bytes`] is injective on the numbers below 256^w.
proof fn lemma_be_bytes_inj(a: nat, b: nat, w: nat)
    requires
        a < super::spec::pow256(w),
        b < super::spec::pow256(w),
        be_bytes(a, w) =~= be_bytes(b, w),
    ensures
        a == b,
{
    super::lemmas_pl::lemma_be_value_of_be_bytes(a, w);
    super::lemmas_pl::lemma_be_value_of_be_bytes(b, w);
}

// ---------------------------------------------------------------------------
// §5.2 and §5.4: TLSInnerPlaintext.
// ---------------------------------------------------------------------------

/// The padding is `padding` zero bytes.
proof fn lemma_zeros_len(n: nat)
    ensures
        Seq::new(n, |i: int| 0u8).len() == n,
{
}

/// Splitting what [`write_inner_plaintext`] wrote finds the content and
/// the type, whatever the padding, provided the type is not zero.
pub proof fn lemma_split_write_inner(content: Seq<u8>, ctype: u8, padding: nat)
    requires
        ctype != 0,
    ensures
        split_inner_plaintext(write_inner_plaintext(content, ctype, padding)) == Some((content, ctype)),
    decreases padding,
{
    let p = write_inner_plaintext(content, ctype, padding);
    if padding == 0 {
        assert(p =~= content + seq![ctype]);
        assert(p.drop_last() =~= content);
        assert(p.last() == ctype);
    } else {
        assert(p.last() == 0u8);
        assert(p.drop_last() =~= write_inner_plaintext(content, ctype, (padding - 1) as nat));
        lemma_split_write_inner(content, ctype, (padding - 1) as nat);
    }
}

/// What [`split_inner_plaintext`] finds is a content, a non-zero type and
/// then only zeros: the input is [`write_inner_plaintext`] of them.
pub proof fn lemma_split_inner_canonical(p: Seq<u8>)
    ensures
        match split_inner_plaintext(p) {
            Some((c, t)) => {
                &&& t != 0
                &&& c.len() < p.len()
                &&& p =~= write_inner_plaintext(c, t, (p.len() - c.len() - 1) as nat)
            },
            None => forall|i: int| 0 <= i < p.len() ==> p[i] == 0u8,
        },
    decreases p.len(),
{
    if p.len() > 0 {
        if p.last() != 0 {
            let c = p.drop_last();
            assert(p =~= write_inner_plaintext(c, p.last(), 0));
        } else {
            lemma_split_inner_canonical(p.drop_last());
            match split_inner_plaintext(p.drop_last()) {
                Some((c, t)) => {
                    let d = p.drop_last();
                    assert(d =~= write_inner_plaintext(c, t, (d.len() - c.len() - 1) as nat));
                    assert(p =~= write_inner_plaintext(c, t, (p.len() - c.len() - 1) as nat)) by {
                        assert(p =~= d.push(0u8));
                        assert(write_inner_plaintext(c, t, (p.len() - c.len() - 1) as nat) =~= write_inner_plaintext(
                            c,
                            t,
                            (d.len() - c.len() - 1) as nat,
                        ).push(0u8));
                    }
                },
                None => {
                    assert forall|i: int| 0 <= i < p.len() implies p[i] == 0u8 by {
                        if i < p.len() - 1 {
                            assert(p.drop_last()[i] == 0u8);
                        }
                    }
                },
            }
        }
    }
}

/// The inner plaintext of a record we protect is opened to the record:
/// any type of `alert`, `handshake` or `application_data`, bounded padding,
/// content of at most 2^14 bytes, non-empty unless it is application data.
pub proof fn lemma_open_write_inner(content: Seq<u8>, ctype: u8, padding: nat)
    requires
        ctype == CT_ALERT || ctype == CT_HANDSHAKE || ctype == CT_APPLICATION_DATA,
        content.len() <= MAX_PLAINTEXT,
        content.len() + 1 + padding <= MAX_PLAINTEXT + 1,
        ctype == CT_APPLICATION_DATA || content.len() > 0,
    ensures
        open_inner_plaintext(write_inner_plaintext(content, ctype, padding)) == Res::Ok(
            Record { ctype, fragment: content },
        ),
{
    lemma_split_write_inner(content, ctype, padding);
}

// ---------------------------------------------------------------------------
// §5.2: protecting and unprotecting a record.
// ---------------------------------------------------------------------------

/// Protecting a record, reading the `TLSCiphertext` off the wire and
/// unprotecting it gives the record back, whatever follows it in the
/// stream, as long as the AEAD opens what it seals and the record is one
/// the standard allows.
pub proof fn lemma_encrypt_decrypt(
    seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    tag_len: nat,
    iv: Seq<u8>,
    seqno: u64,
    ctype: u8,
    content: Seq<u8>,
    padding: nat,
    rest: Seq<u8>,
)
    requires
        ctype == CT_ALERT || ctype == CT_HANDSHAKE || ctype == CT_APPLICATION_DATA,
        content.len() <= MAX_PLAINTEXT,
        content.len() + 1 + padding <= MAX_PLAINTEXT + 1,
        ctype == CT_APPLICATION_DATA || content.len() > 0,
        content.len() + 1 + padding + tag_len <= MAX_CIPHERTEXT,
        forall|n: Seq<u8>, a: Seq<u8>, p: Seq<u8>| #[trigger] seal(n, a, p).len() == p.len() + tag_len,
        forall|n: Seq<u8>, a: Seq<u8>, p: Seq<u8>| #[trigger] open(n, a, seal(n, a, p)) == Some(p),
    ensures
        ({
            let record = encrypt_record(seal, tag_len, iv, seqno, ctype, content, padding);
            match read_record(record + rest, true) {
                Read::Done(Frame::Protected(h, body), r) => {
                    &&& r == rest
                    &&& decrypt_record(open, iv, seqno, h, body) == Res::Ok(Record { ctype, fragment: content })
                },
                _ => false,
            }
        }),
{
    super::lemmas_pl::lemma_pow256_widths();
    let inner = write_inner_plaintext(content, ctype, padding);
    assert(inner.len() == content.len() + 1 + padding);
    let nonce = per_record_nonce(iv, seqno);
    let ct_len = inner.len() + tag_len;
    let ad = additional_data(ct_len);
    let ct = seal(nonce, ad, inner);
    assert(ct.len() == ct_len);
    let record = encrypt_record(seal, tag_len, iv, seqno, ctype, content, padding);
    assert(record == ad + ct);
    // The header of a TLSCiphertext is the additional data.
    lemma_header_shape(CT_APPLICATION_DATA, 0x0303, ct_len);
    let b = record + rest;
    assert(b =~= ad + (ct + rest));
    assert(b.subrange(1, 3) =~= be_bytes(0x0303, 2));
    assert(b.subrange(3, 5) =~= be_bytes(ct_len, 2));
    super::lemmas_pl::lemma_be_value_of_be_bytes(0x0303, 2);
    super::lemmas_pl::lemma_be_value_of_be_bytes(ct_len, 2);
    assert(b.subrange(5, (5 + ct_len) as int) =~= ct);
    assert(b.skip((5 + ct_len) as int) =~= rest);
    assert(b.take(5) =~= ad);
    lemma_open_write_inner(content, ctype, padding);
}

// ---------------------------------------------------------------------------
// §5.1: reassembly.
// ---------------------------------------------------------------------------

/// The concatenation of a list of messages.
pub open spec fn concat_messages(ms: Seq<Seq<u8>>) -> Seq<u8>
    decreases ms.len(),
{
    if ms.len() == 0 {
        seq![]
    } else {
        ms[0] + concat_messages(ms.skip(1))
    }
}

/// Whether `m` is the encoding of a whole handshake message whose body is
/// within the limit: four bytes of header whose `uint24` is the length of
/// the rest.
pub open spec fn is_message(m: Seq<u8>) -> bool {
    &&& m.len() >= HANDSHAKE_HEADER
    &&& m.len() == HANDSHAKE_HEADER + be_value(m.subrange(1, 4))
    &&& be_value(m.subrange(1, 4)) <= MAX_HANDSHAKE_BODY
}

/// Conservation: what [`extract_messages`] takes off the front, with what
/// it keeps, is exactly its input. No byte is dropped, invented or
/// reordered, every message it emits is a whole message, and it keeps
/// fewer bytes than the header and the largest body.
pub proof fn lemma_extract_conserves(buf: Seq<u8>)
    ensures
        match extract_messages(buf) {
            Res::Ok((ms, rest)) => {
                &&& buf =~= concat_messages(ms) + rest
                &&& forall|i: int| 0 <= i < ms.len() ==> is_message(#[trigger] ms[i])
                &&& rest.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY
                &&& rest.len() <= buf.len()
            },
            Res::Err(_) => true,
        },
    decreases buf.len(),
{
    if buf.len() >= HANDSHAKE_HEADER {
        let len = be_value(buf.subrange(1, 4));
        if len <= MAX_HANDSHAKE_BODY && buf.len() >= HANDSHAKE_HEADER + len {
            let n = (HANDSHAKE_HEADER + len) as int;
            let tail = buf.skip(n);
            lemma_extract_conserves(tail);
            if let Res::Ok((ms, rest)) = extract_messages(tail) {
                let m = buf.take(n);
                let all = seq![m] + ms;
                assert(all.skip(1) =~= ms);
                assert(concat_messages(all) =~= m + concat_messages(ms));
                assert(buf =~= m + tail);
                assert(m.subrange(1, 4) =~= buf.subrange(1, 4));
                assert(is_message(m));
                assert forall|i: int| 0 <= i < all.len() implies is_message(#[trigger] all[i]) by {
                    if i > 0 {
                        assert(all[i] == ms[i - 1]);
                    }
                }
            }
        }
    }
}

/// No decision before the data: a proper prefix of a whole message
/// produces no message and is kept whole.
pub proof fn lemma_extract_prefix(buf: Seq<u8>, m: Seq<u8>)
    requires
        is_message(m),
        buf.len() < m.len(),
        buf =~= m.take(buf.len() as int),
    ensures
        extract_messages(buf) == Res::Ok((seq![], buf)),
{
    if buf.len() >= HANDSHAKE_HEADER {
        assert(buf.subrange(1, 4) =~= m.subrange(1, 4));
    }
}

/// A whole message is emitted as soon as its last byte is in the buffer,
/// and is the first message emitted.
pub proof fn lemma_extract_complete(m: Seq<u8>, extra: Seq<u8>)
    requires
        is_message(m),
    ensures
        match extract_messages(m + extra) {
            Res::Ok((ms, rest)) => ms.len() >= 1 && ms[0] == m,
            Res::Err(_) => true,
        },
{
    let b = m + extra;
    assert(b.subrange(1, 4) =~= m.subrange(1, 4));
    assert(b.take(m.len() as int) =~= m);
    assert(b.skip(m.len() as int) =~= extra);
}

/// The reassembler's buffer is bounded: starting from a buffer within the
/// bound and a record of at most 2^14 bytes, the buffer being extended
/// never reaches [`REASSEMBLY_BOUND`], and the state after a record is
/// within the bound again.
pub proof fn lemma_feed_bound(st: Reasm, rec: Record)
    requires
        st.buf.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY,
        rec.fragment.len() <= MAX_PLAINTEXT,
    ensures
        (st.buf + rec.fragment).len() < REASSEMBLY_BOUND,
        match feed_record(st, rec) {
            Res::Ok((_, st2)) => st2.buf.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY,
            Res::Err(_) => true,
        },
{
    lemma_extract_conserves(st.buf + rec.fragment);
}

/// The unprotected change_cipher_spec path keeps the state.
pub proof fn lemma_feed_ccs_bound(st: Reasm)
    requires
        st.buf.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY,
    ensures
        match feed_ccs(st) {
            Res::Ok((_, st2)) => st2.buf.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY,
            Res::Err(_) => true,
        },
{
}

/// The reassembler never loses a byte across a handshake record: what it
/// emits and what it keeps is what it had and what arrived.
pub proof fn lemma_feed_conserves(st: Reasm, rec: Record)
    requires
        rec.ctype == CT_HANDSHAKE,
    ensures
        match feed_record(st, rec) {
            Res::Ok((Event::Messages(ms), st2)) => st.buf + rec.fragment =~= concat_messages(ms) + st2.buf,
            _ => true,
        },
{
    lemma_extract_conserves(st.buf + rec.fragment);
}

/// No decision before the data, at the level of a record: if the bytes
/// that have arrived (the buffer and this fragment) are a proper prefix of
/// a whole message, the record gives no message and the state keeps them.
pub proof fn lemma_feed_prefix(st: Reasm, rec: Record, m: Seq<u8>)
    requires
        rec.ctype == CT_HANDSHAKE,
        rec.fragment.len() > 0,
        is_message(m),
        (st.buf + rec.fragment).len() < m.len(),
        st.buf + rec.fragment =~= m.take((st.buf + rec.fragment).len() as int),
    ensures
        feed_record(st, rec) == Res::<(Event, Reasm)>::Ok((Event::Messages(seq![]), Reasm { buf: st.buf + rec.fragment })),
{
    lemma_extract_prefix(st.buf + rec.fragment, m);
}

/// The reassembler fed a list of handshake fragments in turn.
pub open spec fn feed_all(st: Reasm, frags: Seq<Seq<u8>>) -> Res<(Seq<Seq<u8>>, Reasm)>
    decreases frags.len(),
{
    if frags.len() == 0 {
        Res::Ok((seq![], st))
    } else {
        match feed_record(st, Record { ctype: CT_HANDSHAKE, fragment: frags[0] }) {
            Res::Err(e) => Res::Err(e),
            Res::Ok((Event::Messages(ms), st2)) => {
                match feed_all(st2, frags.skip(1)) {
                    Res::Err(e) => Res::Err(e),
                    Res::Ok((ms2, st3)) => Res::Ok((ms + ms2, st3)),
                }
            },
            Res::Ok((_, st2)) => feed_all(st2, frags.skip(1)),
        }
    }
}

/// The concatenation of a list of fragments.
pub open spec fn concat_fragments(frags: Seq<Seq<u8>>) -> Seq<u8>
    decreases frags.len(),
{
    if frags.len() == 0 {
        seq![]
    } else {
        frags[0] + concat_fragments(frags.skip(1))
    }
}

/// No decision before the data, across any number of records: if the
/// non-empty fragments that arrive, one record each and together with the
/// buffer, are a proper prefix of one whole message, no message is
/// emitted and the buffer holds exactly what arrived.
pub proof fn lemma_feed_all_prefix(st: Reasm, frags: Seq<Seq<u8>>, m: Seq<u8>)
    requires
        is_message(m),
        forall|i: int| 0 <= i < frags.len() ==> (#[trigger] frags[i]).len() > 0,
        (st.buf + concat_fragments(frags)).len() < m.len(),
        st.buf + concat_fragments(frags) =~= m.take((st.buf + concat_fragments(frags)).len() as int),
    ensures
        feed_all(st, frags) == Res::<(Seq<Seq<u8>>, Reasm)>::Ok(
            (seq![], Reasm { buf: st.buf + concat_fragments(frags) }),
        ),
    decreases frags.len(),
{
    if frags.len() > 0 {
        let f = frags[0];
        let tail = frags.skip(1);
        let all = st.buf + concat_fragments(frags);
        assert(concat_fragments(frags) == f + concat_fragments(tail));
        let st1 = st.buf + f;
        assert(st1.len() <= all.len());
        assert(st1 =~= all.take(st1.len() as int));
        assert(st1 =~= m.take(st1.len() as int)) by {
            assert(all.take(st1.len() as int) =~= m.take(all.len() as int).take(st1.len() as int));
            assert(m.take(all.len() as int).take(st1.len() as int) =~= m.take(st1.len() as int));
        }
        // st1 is a proper prefix of m (it is no longer than all).
        lemma_feed_prefix(st, Record { ctype: CT_HANDSHAKE, fragment: f }, m);
        let st2 = Reasm { buf: st1 };
        assert forall|i: int| 0 <= i < tail.len() implies (#[trigger] tail[i]).len() > 0 by {
            assert(tail[i] == frags[i + 1]);
        }
        assert(st2.buf + concat_fragments(tail) =~= all) by {
            assert(st.buf + (f + concat_fragments(tail)) =~= (st.buf + f) + concat_fragments(tail));
        }
        lemma_feed_all_prefix(st2, tail, m);
    }
}

// ---------------------------------------------------------------------------
// §6: alerts.
// ---------------------------------------------------------------------------

/// An alert we write is read back, and what is read is what is written.
pub proof fn lemma_alert_round_trip(a: Alert)
    ensures
        read_alert(write_alert(a)) == Some(a),
{
}

/// What [`read_alert`] accepts is one encoding.
pub proof fn lemma_alert_canonical(b: Seq<u8>)
    ensures
        match read_alert(b) {
            Some(a) => write_alert(a) =~= b,
            None => b.len() != 2,
        },
{
}

} // verus!
