//! The executable record layer (RFC 8446 §5), proven to meet
//! [`super::contract`]: reading a record off a byte stream, writing one,
//! the per-record nonce, the additional data, the padding scan of
//! `TLSInnerPlaintext`, and protecting and unprotecting a record over an
//! AEAD given as a trait ([`Aead`]), which the cryptography instantiates
//! (phase-3.md item 3.5f).

use super::reader::byte_at;
use super::spec::{
    CT_ALERT, CT_APPLICATION_DATA, CT_CHANGE_CIPHER_SPEC, CT_HANDSHAKE, ErrKind, MAX_CIPHERTEXT,
    MAX_PLAINTEXT, RECORD_HEADER,
};
use super::writer::{push_be, push_u16};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What [`read_record`] found on the wire: [`super::spec::Frame`].
#[derive(Debug, PartialEq, Eq)]
pub enum Frame<'a> {
    /// An unprotected `handshake` or `alert` record: its type and fragment.
    Plain(u8, &'a [u8]),
    /// An unprotected change_cipher_spec record that is to be dropped (§5).
    Ccs,
    /// A `TLSCiphertext`: its header, which is the AEAD's additional data,
    /// and its `encrypted_record`.
    Protected(&'a [u8], &'a [u8]),
}

impl<'a> View for Frame<'a> {
    type V = super::spec::Frame;

    open spec fn view(&self) -> super::spec::Frame {
        match self {
            Frame::Plain(t, f) => super::spec::Frame::Plain(super::spec::Record { ctype: *t, fragment: f@ }),
            Frame::Ccs => super::spec::Frame::Ccs,
            Frame::Protected(h, b) => super::spec::Frame::Protected(h@, b@),
        }
    }
}

/// The outcome of [`read_record`]: [`super::spec::Read`].
#[derive(Debug, PartialEq, Eq)]
pub enum ReadOut<'a> {
    /// More bytes are needed.
    NeedMore,
    /// The record is refused.
    Fail(ErrKind),
    /// A record, and the bytes after it.
    Done(Frame<'a>, &'a [u8]),
}

impl<'a> View for ReadOut<'a> {
    type V = super::spec::Read<super::spec::Frame>;

    open spec fn view(&self) -> super::spec::Read<super::spec::Frame> {
        match self {
            ReadOut::NeedMore => super::spec::Read::NeedMore,
            ReadOut::Fail(k) => super::spec::Read::Fail(*k),
            ReadOut::Done(f, r) => super::spec::Read::Done(f@, r@),
        }
    }
}

/// §5.1 and §5.2: read one record from the front of `input`
/// ([`super::spec::read_record`]).
pub fn read_record<'a>(input: &'a [u8], protected: bool) -> (out: ReadOut<'a>)
    ensures
        super::contract::read_record_ensures(input@, protected, out@),
{
    if input.len() < RECORD_HEADER {
        return ReadOut::NeedMore;
    }
    let t = byte_at(input, 0);
    let v_hi = byte_at(input, 1);
    let v_lo = byte_at(input, 2);
    let l_hi = byte_at(input, 3);
    let l_lo = byte_at(input, 4);
    proof {
        super::lemmas_pl::lemma_be_value_2(input@.subrange(1, 3));
        super::lemmas_pl::lemma_be_value_2(input@.subrange(3, 5));
    }
    // v_hi * 256 + v_lo and l_hi * 256 + l_lo are below 2^16: no saturation.
    let v: u16 = (v_hi as u16).saturating_mul(256).saturating_add(v_lo as u16);
    let len: usize = (l_hi as usize).saturating_mul(256).saturating_add(l_lo as usize);
    // 1.
    let ok_type = if protected {
        t == CT_APPLICATION_DATA || t == CT_CHANGE_CIPHER_SPEC
    } else {
        t == CT_CHANGE_CIPHER_SPEC || t == CT_ALERT || t == CT_HANDSHAKE
    };
    if !ok_type {
        return ReadOut::Fail(ErrKind::UnexpectedContentType);
    }
    // 2.
    if !(v == 0x0303 || (!protected && v == 0x0301)) {
        return ReadOut::Fail(ErrKind::BadLegacyRecordVersion);
    }
    // 3.
    let limit = if protected && t == CT_APPLICATION_DATA {
        MAX_CIPHERTEXT
    } else {
        MAX_PLAINTEXT
    };
    if len > limit {
        return ReadOut::Fail(ErrKind::RecordOverflow);
    }
    // 4.
    if len == 0 && (t == CT_HANDSHAKE || t == CT_ALERT) {
        return ReadOut::Fail(ErrKind::ZeroLengthFragment);
    }
    // len <= 2^14 + 256, so this does not saturate.
    let total = RECORD_HEADER.saturating_add(len);
    if input.len() < total {
        return ReadOut::NeedMore;
    }
    let body = vstd::slice::slice_subrange(input, RECORD_HEADER, total);
    let rest = vstd::slice::slice_subrange(input, total, input.len());
    if t == CT_CHANGE_CIPHER_SPEC {
        // 5.
        if body.len() == 1 && byte_at(body, 0) == 1 {
            proof {
                assert(body@ =~= seq![1u8]);
            }
            ReadOut::Done(Frame::Ccs, rest)
        } else {
            proof {
                assert(body@ != seq![1u8]);
            }
            ReadOut::Fail(ErrKind::BadChangeCipherSpec)
        }
    } else if t == CT_APPLICATION_DATA {
        let header = vstd::slice::slice_subrange(input, 0, RECORD_HEADER);
        ReadOut::Done(Frame::Protected(header, body), rest)
    } else {
        ReadOut::Done(Frame::Plain(t, body), rest)
    }
}

/// §5.1: append a record header ([`super::spec::write_record_header`]).
pub fn write_record_header(out: &mut Vec<u8>, ctype: u8, version: u16, length: usize)
    requires
        length < 65536,
    ensures
        super::contract::write_record_header_ensures(old(out)@, ctype, version, length as nat, final(out)@),
{
    out.push(ctype);
    push_u16(out, version);
    proof {
        super::lemmas_pl::lemma_pow256_widths();
    }
    push_be(out, length as u64, 2);
    assert(out@ =~= old(out)@ + super::spec::write_record_header(ctype, version, length as nat));
}

/// §5.1: append a `TLSPlaintext` ([`super::spec::write_plaintext`]).
pub fn write_plaintext(out: &mut Vec<u8>, ctype: u8, version: u16, fragment: &[u8])
    requires
        fragment.len() < 65536,
    ensures
        super::contract::write_plaintext_ensures(old(out)@, ctype, version, fragment@, final(out)@),
{
    write_record_header(out, ctype, version, fragment.len());
    out.extend_from_slice(fragment);
    assert(out@ =~= old(out)@ + super::spec::write_plaintext(ctype, version, fragment@));
}

/// §5.2: the additional data of a `TLSCiphertext` whose `encrypted_record`
/// is `length` bytes ([`super::spec::additional_data`]).
pub fn additional_data(length: usize) -> (out: Vec<u8>)
    requires
        length < 65536,
    ensures
        super::contract::additional_data_ensures(length as nat, out@),
{
    let mut out: Vec<u8> = Vec::new();
    write_record_header(&mut out, CT_APPLICATION_DATA, 0x0303, length);
    proof {
        assert(out@ =~= Seq::<u8>::empty() + super::spec::write_record_header(CT_APPLICATION_DATA, 0x0303, length as nat));
        assert(out@ =~= super::spec::additional_data(length as nat));
    }
    out
}

/// §5.3: the per-record nonce ([`super::spec::per_record_nonce`]): the
/// sequence number in network byte order, padded on the left with zeros to
/// the length of the IV, XORed with the IV.
pub fn per_record_nonce(iv: &[u8], seqno: u64) -> (out: Vec<u8>)
    requires
        iv.len() >= 8,
    ensures
        super::contract::per_record_nonce_ensures(iv@, seqno, out@),
{
    let mut padded: Vec<u8> = Vec::new();
    proof {
        super::lemmas_record::lemma_pow256_at_least_8(iv.len() as nat);
    }
    push_be(&mut padded, seqno, iv.len());
    proof {
        assert(padded@ =~= Seq::<u8>::empty() + super::spec::be_bytes(seqno as nat, iv.len() as nat));
        super::lemmas_pl::lemma_be_bytes_len(seqno as nat, iv.len() as nat);
    }
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < iv.len()
        invariant
            i <= iv.len(),
            padded@.len() == iv.len(),
            padded@ == super::spec::be_bytes(seqno as nat, iv.len() as nat),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> out@[j] == (iv@[j] ^ padded@[j]) as u8,
        decreases iv.len() - i,
    {
        let a = byte_at(iv, i);
        let b = byte_at(padded.as_slice(), i);
        out.push(a ^ b);
        // Never saturates: i < iv.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= super::spec::per_record_nonce(iv@, seqno));
    }
    out
}

/// §5.4: the content length and the type of a `TLSInnerPlaintext`, found
/// by scanning from the end for the first non-zero octet
/// ([`super::spec::split_inner_plaintext`]).
pub fn split_inner_plaintext(p: &[u8]) -> (out: Option<(usize, u8)>)
    ensures
        super::contract::split_inner_ensures(p@, out),
        match out {
            Some((n, _)) => n < p.len(),
            None => true,
        },
{
    let mut i: usize = p.len();
    proof {
        assert(p@.take(p.len() as int) =~= p@);
    }
    while i > 0
        invariant
            i <= p.len(),
            super::spec::split_inner_plaintext(p@) == super::spec::split_inner_plaintext(p@.take(i as int)),
        decreases i,
    {
        // i >= 1, so this does not saturate.
        let j = i.saturating_sub(1);
        let b = byte_at(p, j);
        proof {
            let t = p@.take(i as int);
            assert(t.last() == p@[j as int]);
            assert(t.drop_last() =~= p@.take(j as int));
        }
        if b != 0 {
            proof {
                assert(super::spec::split_inner_plaintext(p@.take(i as int)) == Some((p@.take(j as int), b)));
            }
            return Some((j, b));
        }
        i = j;
    }
    proof {
        assert(p@.take(0) =~= Seq::<u8>::empty());
    }
    None
}

/// The exec form of a [`super::spec::Res`] holding a record: the content
/// type and the content.
pub open spec fn res_record(r: Result<(u8, Vec<u8>), ErrKind>) -> super::spec::Res<super::spec::Record> {
    match r {
        Ok((t, v)) => super::spec::Res::Ok(super::spec::Record { ctype: t, fragment: v@ }),
        Err(k) => super::spec::Res::Err(k),
    }
}

/// §5.2 and §5.4: the record a decrypted `TLSInnerPlaintext` holds, or
/// why it is refused ([`super::spec::open_inner_plaintext`]).
pub fn open_inner_plaintext(p: Vec<u8>) -> (out: Result<(u8, Vec<u8>), ErrKind>)
    ensures
        super::contract::open_inner_ensures(p@, res_record(out)),
{
    if p.len() > MAX_PLAINTEXT.saturating_add(1) { return Err(ErrKind::RecordOverflow); }
    let (n, t) = match split_inner_plaintext(p.as_slice()) {
        Some(x) => x,
        None => return Err(ErrKind::AllZeroInnerPlaintext),
    };
    proof {
        assert(p@.take(n as int).len() == n);
    }
    if t == CT_CHANGE_CIPHER_SPEC {
        return Err(ErrKind::BadChangeCipherSpec);
    }
    if !(t == CT_ALERT || t == CT_HANDSHAKE || t == CT_APPLICATION_DATA) {
        return Err(ErrKind::UnexpectedContentType);
    }
    if n > MAX_PLAINTEXT {
        return Err(ErrKind::RecordOverflow);
    }
    if n == 0 && (t == CT_HANDSHAKE || t == CT_ALERT) {
        return Err(ErrKind::ZeroLengthFragment);
    }
    let mut content = p;
    content.truncate(n);
    Ok((t, content))
}

/// §5.2: the AEAD of a cipher suite, as the record layer needs it. The
/// specification functions are what the standard writes as
/// `AEAD-Encrypt(write_key, nonce, additional_data, plaintext)` and
/// `AEAD-Decrypt(...)` with the key inside `self`; the executable
/// methods are proven to compute them. Nothing about the cipher is
/// assumed except that its output is `tag_len` bytes longer than its
/// input ("An AEAD algorithm used in TLS 1.3 MUST NOT produce an
/// expansion greater than 255 octets").
pub trait Aead {
    /// `AEAD-Encrypt`.
    spec fn seal_spec(&self, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>) -> Seq<u8>;

    /// `AEAD-Decrypt`.
    spec fn open_spec(&self, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>) -> Option<Seq<u8>>;

    /// The expansion of the AEAD, in bytes (at most 255).
    spec fn tag_len_spec(&self) -> nat;

    /// The length of the nonce the AEAD takes, which is `iv_length` of §5.3.
    spec fn nonce_len_spec(&self) -> nat;

    /// The expansion.
    fn tag_len(&self) -> (n: usize)
        ensures
            n == self.tag_len_spec(),
            n <= 255,
    ;

    /// The nonce length.
    fn nonce_len(&self) -> (n: usize)
        ensures
            n == self.nonce_len_spec(),
            n >= 8,
    ;

    /// Encrypt.
    fn seal(&self, nonce: &[u8], ad: &[u8], plaintext: &[u8]) -> (ciphertext: Vec<u8>)
        requires
            nonce@.len() == self.nonce_len_spec(),
        ensures
            ciphertext@ == self.seal_spec(nonce@, ad@, plaintext@),
    ;

    /// Decrypt, or refuse.
    fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> (plaintext: Option<Vec<u8>>)
        requires
            nonce@.len() == self.nonce_len_spec(),
        ensures
            match plaintext {
                Some(p) => self.open_spec(nonce@, ad@, ciphertext@) == Some(p@),
                None => self.open_spec(nonce@, ad@, ciphertext@) is None,
            },
    ;

    /// The output is `tag_len` bytes longer than the input.
    proof fn lemma_seal_len(&self, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>)
        ensures
            self.seal_spec(nonce, ad, plaintext).len() == plaintext.len() + self.tag_len_spec(),
    ;
}

/// §5.2: unprotect a `TLSCiphertext` that [`read_record`] returned
/// ([`super::spec::decrypt_record`]): `header` is the additional data and
/// `encrypted` the `encrypted_record`.
pub fn decrypt_record<A: Aead>(aead: &A, iv: &[u8], seqno: u64, header: &[u8], encrypted: &[u8]) -> (out: Result<
    (u8, Vec<u8>),
    ErrKind,
>)
    requires
        iv.len() >= 8,
        iv@.len() == aead.nonce_len_spec(),
    ensures
        res_record(out) == super::spec::decrypt_record(
            |n: Seq<u8>, a: Seq<u8>, c: Seq<u8>| aead.open_spec(n, a, c),
            iv@,
            seqno,
            header@,
            encrypted@,
        ),
{
    let nonce = per_record_nonce(iv, seqno);
    proof {
        assert(nonce@.len() == iv@.len());
    }
    match aead.open(nonce.as_slice(), header, encrypted) {
        None => Err(ErrKind::BadRecordMac),
        Some(p) => open_inner_plaintext(p),
    }
}

/// §5.2: protect a record ([`super::spec::encrypt_record`]): the
/// `TLSInnerPlaintext` of `content`, `ctype` and `padding` zeros, sealed
/// under the additional data of its own length, behind that header.
pub fn encrypt_record<A: Aead>(aead: &A, iv: &[u8], seqno: u64, ctype: u8, content: &[u8], padding: usize) -> (record:
    Vec<u8>)
    requires
        iv.len() >= 8,
        iv@.len() == aead.nonce_len_spec(),
        super::contract::inner_length_requires(content@, padding as nat),
        content.len() + 1 + padding + aead.tag_len_spec() <= MAX_CIPHERTEXT,
    ensures
        record@ == super::spec::encrypt_record(
            |n: Seq<u8>, a: Seq<u8>, p: Seq<u8>| aead.seal_spec(n, a, p),
            aead.tag_len_spec(),
            iv@,
            seqno,
            ctype,
            content@,
            padding as nat,
        ),
{
    let mut inner: Vec<u8> = Vec::new();
    inner.extend_from_slice(content);
    inner.push(ctype);
    let mut k: usize = 0;
    proof {
        assert(inner@ =~= content@ + seq![ctype]);
        assert(Seq::new(0, |i: int| 0u8) =~= Seq::<u8>::empty());
    }
    while k < padding
        invariant
            k <= padding,
            inner@ =~= content@ + seq![ctype] + Seq::new(k as nat, |i: int| 0u8),
            super::contract::inner_length_requires(content@, padding as nat),
        content.len() + 1 + padding + aead.tag_len_spec() <= MAX_CIPHERTEXT,
        decreases padding - k,
    {
        inner.push(0);
        proof {
            assert(Seq::new(k as nat + 1, |i: int| 0u8) =~= Seq::new(k as nat, |i: int| 0u8).push(0u8));
        }
        // Never saturates: k < padding.
        k = k.saturating_add(1);
    }
    let tag = aead.tag_len();
    // inner.len() + tag <= 2^14 + 256, so these do not saturate.
    let ct_len = inner.len().saturating_add(tag);
    let ad = additional_data(ct_len);
    let nonce = per_record_nonce(iv, seqno);
    proof {
        assert(nonce@.len() == iv@.len());
    }
    let ct = aead.seal(nonce.as_slice(), ad.as_slice(), inner.as_slice());
    let mut record = ad;
    record.extend_from_slice(ct.as_slice());
    proof {
        assert(inner@ =~= super::spec::write_inner_plaintext(content@, ctype, padding as nat));
    }
    record
}

} // verus!
