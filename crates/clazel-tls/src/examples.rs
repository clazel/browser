//! Concrete facts about [`super::spec`], each proven by evaluating the
//! spec on a concrete input. They are evidence that the transcription says
//! what the standard says (every one can be checked against the quoted
//! text), and each is a theorem that a deliberately broken spec fails
//! (`mutations.json`): a certificate there calls one of these lemmas on
//! the mutant and shows its statement false.
//!
//! One lemma per table row of RFC 8446 §4.2 (`lemma_ext_row_*`), one per
//! length rule, one per record rule, one per rule of the reassembler and
//! of the handshake checks.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §3.4: the length field and the bounds of a vector.
// ---------------------------------------------------------------------------

/// §3.4: "The length will be in the form of a number consuming as many
/// bytes as required to hold the vector's specified maximum (ceiling)
/// length": 255 fits one byte, 256 needs two, 65535 fits two, 65536 needs
/// three.
pub proof fn lemma_len_width_table()
    ensures
        len_width(0) == 1,
        len_width(255) == 1,
        len_width(256) == 2,
        len_width(65535) == 2,
        len_width(65536) == 3,
        len_width(16777215) == 3,
{
    assert(len_width(0) == 1) by (compute_only);
    assert(len_width(255) == 1) by (compute_only);
    assert(len_width(256) == 2) by (compute_only);
    assert(len_width(65535) == 2) by (compute_only);
    assert(len_width(65536) == 3) by (compute_only);
    assert(len_width(16777215) == 3) by (compute_only);
}

/// §3.4, `opaque x<floor..ceiling>`: a vector of 3 bytes with ceiling 3
/// is read, one of 3 bytes with floor 3 is read, and the bytes after it
/// are left.
pub proof fn lemma_read_vec_bounds()
    ensures
        read_vec(seq![3u8, 1, 2, 3, 9], 0, 3) == Some((seq![1u8, 2, 3], seq![9u8])),
        read_vec(seq![3u8, 1, 2, 3], 3, 255) == Some((seq![1u8, 2, 3], Seq::<u8>::empty())),
        read_vec(seq![0u8], 0, 255) == Some((Seq::<u8>::empty(), Seq::<u8>::empty())),
        read_vec(seq![4u8, 1, 2, 3, 4], 0, 3) is None,
        read_vec(seq![2u8, 1, 2], 3, 255) is None,
        read_vec(seq![0u8], 1, 255) is None,
        read_vec(seq![3u8, 1, 2], 0, 255) is None,
        read_vec(seq![1u8, 9], 0, 3) == Some((seq![9u8], Seq::<u8>::empty())),
        read_vec(seq![1u8, 9], 1, 3) == Some((seq![9u8], Seq::<u8>::empty())),
        read_vec(seq![1u8, 9, 8], 0, 3) == Some((seq![9u8], seq![8u8])),
        read_vec(seq![0u8, 3, 1, 2, 3], 0, 300) == Some((seq![1u8, 2, 3], Seq::<u8>::empty())),
{
    assert(read_vec(seq![3u8, 1, 2, 3, 9], 0, 3) == Some((seq![1u8, 2, 3], seq![9u8]))) by (compute_only);
    assert(read_vec(seq![3u8, 1, 2, 3], 3, 255) == Some((seq![1u8, 2, 3], Seq::<u8>::empty()))) by (compute_only);
    assert(read_vec(seq![0u8], 0, 255) == Some((Seq::<u8>::empty(), Seq::<u8>::empty()))) by (compute_only);
    assert(read_vec(seq![4u8, 1, 2, 3, 4], 0, 3) is None) by (compute_only);
    assert(read_vec(seq![2u8, 1, 2], 3, 255) is None) by (compute_only);
    assert(read_vec(seq![0u8], 1, 255) is None) by (compute_only);
    assert(read_vec(seq![3u8, 1, 2], 0, 255) is None) by (compute_only);
    assert(read_vec(seq![1u8, 9], 0, 3) == Some((seq![9u8], Seq::<u8>::empty()))) by (compute_only);
    assert(read_vec(seq![1u8, 9], 1, 3) == Some((seq![9u8], Seq::<u8>::empty()))) by (compute_only);
    assert(read_vec(seq![1u8, 9, 8], 0, 3) == Some((seq![9u8], seq![8u8]))) by (compute_only);
    assert(read_vec(seq![0u8, 3, 1, 2, 3], 0, 300) == Some((seq![1u8, 2, 3], Seq::<u8>::empty()))) by (compute_only);
}

/// §3.4: "The length of an encoded vector must be an exact multiple of
/// the length of a single element (e.g., a 17-byte vector of uint16 would
/// be illegal)."
pub proof fn lemma_read_u16s_multiple()
    ensures
        read_u16s(seq![0u8, 1, 3, 4]) == Some(seq![1u16, 772]),
        read_u16s(Seq::<u8>::empty()) == Some(Seq::<u16>::empty()),
        read_u16s(seq![0u8, 1, 3]) is None,
{
    assert(read_u16s(seq![0u8, 1, 3, 4]) == Some(seq![1u16, 772])) by (compute_only);
    assert(read_u16s(Seq::<u8>::empty()) == Some(Seq::<u16>::empty())) by (compute_only);
    assert(read_u16s(seq![0u8, 1, 3]) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §5.1 and §5.2: records.
// ---------------------------------------------------------------------------

/// §5.1: "The length MUST NOT exceed 2^14 bytes" (16384 = 0x4000). A
/// record of length 0x4001 is refused as soon as its header is read, with
/// `record_overflow`, and one of 0x4000 is waited for.
pub proof fn lemma_plaintext_limit()
    ensures
        read_record(seq![22u8, 3, 3, 0x40, 0x01], false) == Read::<Frame>::Fail(ErrKind::RecordOverflow),
        read_record(seq![22u8, 3, 3, 0x40, 0x00], false) == Read::<Frame>::NeedMore,
        read_record(seq![21u8, 3, 3, 0x40, 0x01], false) == Read::<Frame>::Fail(ErrKind::RecordOverflow),
        read_record(seq![20u8, 3, 3, 0x40, 0x01], false) == Read::<Frame>::Fail(ErrKind::RecordOverflow),
        read_record(seq![20u8, 3, 3, 0x40, 0x01], true) == Read::<Frame>::Fail(ErrKind::RecordOverflow),
{
    assert(read_record(seq![22u8, 3, 3, 0x40, 0x01], false) == Read::<Frame>::Fail(ErrKind::RecordOverflow)) by (compute_only);
    assert(read_record(seq![22u8, 3, 3, 0x40, 0x00], false) == Read::<Frame>::NeedMore) by (compute_only);
    assert(read_record(seq![21u8, 3, 3, 0x40, 0x01], false) == Read::<Frame>::Fail(ErrKind::RecordOverflow)) by (compute_only);
    assert(read_record(seq![20u8, 3, 3, 0x40, 0x01], false) == Read::<Frame>::Fail(ErrKind::RecordOverflow)) by (compute_only);
    assert(read_record(seq![20u8, 3, 3, 0x40, 0x01], true) == Read::<Frame>::Fail(ErrKind::RecordOverflow)) by (compute_only);
}

/// §5.2: "The length MUST NOT exceed 2^14 + 256 bytes" (16640 = 0x4100).
pub proof fn lemma_ciphertext_limit()
    ensures
        read_record(seq![23u8, 3, 3, 0x41, 0x01], true) == Read::<Frame>::Fail(ErrKind::RecordOverflow),
        read_record(seq![23u8, 3, 3, 0x41, 0x00], true) == Read::<Frame>::NeedMore,
        read_record(seq![23u8, 3, 3, 0x40, 0x01], true) == Read::<Frame>::NeedMore,
{
    assert(read_record(seq![23u8, 3, 3, 0x41, 0x01], true) == Read::<Frame>::Fail(ErrKind::RecordOverflow)) by (compute_only);
    assert(read_record(seq![23u8, 3, 3, 0x41, 0x00], true) == Read::<Frame>::NeedMore) by (compute_only);
    assert(read_record(seq![23u8, 3, 3, 0x40, 0x01], true) == Read::<Frame>::NeedMore) by (compute_only);
}

/// §5.1: a handshake record and an alert record are read, with the
/// versions 0x0303 and (before protection) 0x0301; "MUST NOT" ones are
/// refused.
pub proof fn lemma_record_versions()
    ensures
        read_record(seq![22u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Done(
            Frame::Plain(Record { ctype: 22, fragment: seq![7u8] }),
            Seq::<u8>::empty(),
        ),
        read_record(seq![22u8, 3, 1, 0, 1, 7], false) == Read::<Frame>::Done(
            Frame::Plain(Record { ctype: 22, fragment: seq![7u8] }),
            Seq::<u8>::empty(),
        ),
        read_record(seq![21u8, 3, 3, 0, 2, 2, 40, 9], false) == Read::<Frame>::Done(
            Frame::Plain(Record { ctype: 21, fragment: seq![2u8, 40] }),
            seq![9u8],
        ),
        read_record(seq![22u8, 3, 4, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::BadLegacyRecordVersion),
        read_record(seq![22u8, 3, 2, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::BadLegacyRecordVersion),
        read_record(seq![23u8, 3, 1, 0, 1, 7], true) == Read::<Frame>::Fail(ErrKind::BadLegacyRecordVersion),
        read_record(seq![23u8, 3, 3, 0, 1, 7], true) == Read::<Frame>::Done(
            Frame::Protected(seq![23u8, 3, 3, 0, 1], seq![7u8]),
            Seq::<u8>::empty(),
        ),
{
    assert(read_record(seq![22u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Done(
        Frame::Plain(Record { ctype: 22, fragment: seq![7u8] }),
        Seq::<u8>::empty(),
    )) by (compute_only);
    assert(read_record(seq![22u8, 3, 1, 0, 1, 7], false) == Read::<Frame>::Done(
        Frame::Plain(Record { ctype: 22, fragment: seq![7u8] }),
        Seq::<u8>::empty(),
    )) by (compute_only);
    assert(read_record(seq![21u8, 3, 3, 0, 2, 2, 40, 9], false) == Read::<Frame>::Done(
        Frame::Plain(Record { ctype: 21, fragment: seq![2u8, 40] }),
        seq![9u8],
    )) by (compute_only);
    assert(read_record(seq![22u8, 3, 4, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::BadLegacyRecordVersion)) by (compute_only);
    assert(read_record(seq![22u8, 3, 2, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::BadLegacyRecordVersion)) by (compute_only);
    assert(read_record(seq![23u8, 3, 1, 0, 1, 7], true) == Read::<Frame>::Fail(ErrKind::BadLegacyRecordVersion)) by (compute_only);
    assert(read_record(seq![23u8, 3, 3, 0, 1, 7], true) == Read::<Frame>::Done(
        Frame::Protected(seq![23u8, 3, 3, 0, 1], seq![7u8]),
        Seq::<u8>::empty(),
    )) by (compute_only);
}

/// §5: "If a TLS implementation receives an unexpected record type, it
/// MUST terminate the connection with an "unexpected_message" alert":
/// invalid(0), heartbeat(24) and anything else; application data before
/// protection; a handshake or alert record after it.
pub proof fn lemma_record_types()
    ensures
        read_record(seq![0u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType),
        read_record(seq![24u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType),
        read_record(seq![23u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType),
        read_record(seq![22u8, 3, 3, 0, 1, 7], true) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType),
        read_record(seq![21u8, 3, 3, 0, 2, 2, 40], true) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType),
{
    assert(read_record(seq![0u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType)) by (compute_only);
    assert(read_record(seq![24u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType)) by (compute_only);
    assert(read_record(seq![23u8, 3, 3, 0, 1, 7], false) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType)) by (compute_only);
    assert(read_record(seq![22u8, 3, 3, 0, 1, 7], true) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType)) by (compute_only);
    assert(read_record(seq![21u8, 3, 3, 0, 2, 2, 40], true) == Read::<Frame>::Fail(ErrKind::UnexpectedContentType)) by (compute_only);
}

/// §5.1: "Implementations MUST NOT send zero-length fragments of
/// Handshake types"; an Alert record "MUST contain exactly one message";
/// "Zero-length fragments of Application Data MAY be sent".
pub proof fn lemma_zero_length_fragments()
    ensures
        read_record(seq![22u8, 3, 3, 0, 0], false) == Read::<Frame>::Fail(ErrKind::ZeroLengthFragment),
        read_record(seq![21u8, 3, 3, 0, 0], false) == Read::<Frame>::Fail(ErrKind::ZeroLengthFragment),
        read_record(seq![23u8, 3, 3, 0, 0], true) == Read::<Frame>::Done(
            Frame::Protected(seq![23u8, 3, 3, 0, 0], Seq::<u8>::empty()),
            Seq::<u8>::empty(),
        ),
{
    assert(read_record(seq![22u8, 3, 3, 0, 0], false) == Read::<Frame>::Fail(ErrKind::ZeroLengthFragment)) by (compute_only);
    assert(read_record(seq![21u8, 3, 3, 0, 0], false) == Read::<Frame>::Fail(ErrKind::ZeroLengthFragment)) by (compute_only);
    assert(read_record(seq![23u8, 3, 3, 0, 0], true) == Read::<Frame>::Done(
        Frame::Protected(seq![23u8, 3, 3, 0, 0], Seq::<u8>::empty()),
        Seq::<u8>::empty(),
    )) by (compute_only);
}

/// §5: "An implementation may receive an unencrypted record of type
/// change_cipher_spec consisting of the single byte value 0x01 ... and
/// MUST simply drop it ... An implementation which receives any other
/// change_cipher_spec value ... MUST abort the handshake with an
/// "unexpected_message" alert."
pub proof fn lemma_change_cipher_spec()
    ensures
        read_record(seq![20u8, 3, 3, 0, 1, 1], false) == Read::<Frame>::Done(Frame::Ccs, Seq::<u8>::empty()),
        read_record(seq![20u8, 3, 3, 0, 1, 1], true) == Read::<Frame>::Done(Frame::Ccs, Seq::<u8>::empty()),
        read_record(seq![20u8, 3, 3, 0, 1, 2], false) == Read::<Frame>::Fail(ErrKind::BadChangeCipherSpec),
        read_record(seq![20u8, 3, 3, 0, 2, 1, 1], false) == Read::<Frame>::Fail(ErrKind::BadChangeCipherSpec),
        read_record(seq![20u8, 3, 3, 0, 0], false) == Read::<Frame>::Fail(ErrKind::BadChangeCipherSpec),
{
    assert(read_record(seq![20u8, 3, 3, 0, 1, 1], false) == Read::<Frame>::Done(Frame::Ccs, Seq::<u8>::empty())) by (compute_only);
    assert(read_record(seq![20u8, 3, 3, 0, 1, 1], true) == Read::<Frame>::Done(Frame::Ccs, Seq::<u8>::empty())) by (compute_only);
    assert(read_record(seq![20u8, 3, 3, 0, 1, 2], false) == Read::<Frame>::Fail(ErrKind::BadChangeCipherSpec)) by (compute_only);
    assert(read_record(seq![20u8, 3, 3, 0, 2, 1, 1], false) == Read::<Frame>::Fail(ErrKind::BadChangeCipherSpec)) by (compute_only);
    assert(read_record(seq![20u8, 3, 3, 0, 0], false) == Read::<Frame>::Fail(ErrKind::BadChangeCipherSpec)) by (compute_only);
}

/// §5.4: "scans the field from the end toward the beginning until it
/// finds a non-zero octet. This non-zero octet is the content type": the
/// content is what precedes it, whatever the padding.
pub proof fn lemma_inner_plaintext()
    ensures
        split_inner_plaintext(seq![5u8, 22]) == Some((seq![5u8], 22u8)),
        split_inner_plaintext(seq![5u8, 22, 0, 0, 0]) == Some((seq![5u8], 22u8)),
        split_inner_plaintext(seq![0u8, 5, 23, 0]) == Some((seq![0u8, 5], 23u8)),
        split_inner_plaintext(seq![22u8]) == Some((Seq::<u8>::empty(), 22u8)),
        split_inner_plaintext(seq![0u8, 0, 0]) is None,
        split_inner_plaintext(Seq::<u8>::empty()) is None,
{
    assert(split_inner_plaintext(seq![5u8, 22]) == Some((seq![5u8], 22u8))) by (compute_only);
    assert(split_inner_plaintext(seq![5u8, 22, 0, 0, 0]) == Some((seq![5u8], 22u8))) by (compute_only);
    assert(split_inner_plaintext(seq![0u8, 5, 23, 0]) == Some((seq![0u8, 5], 23u8))) by (compute_only);
    assert(split_inner_plaintext(seq![22u8]) == Some((Seq::<u8>::empty(), 22u8))) by (compute_only);
    assert(split_inner_plaintext(seq![0u8, 0, 0]) is None) by (compute_only);
    assert(split_inner_plaintext(Seq::<u8>::empty()) is None) by (compute_only);
}

/// §5.2 and §5.4 on a decrypted `TLSInnerPlaintext`: all zeros has no
/// type (`unexpected_message`); a protected change_cipher_spec is an
/// error; an unknown type is an unexpected record type; a handshake or
/// alert record with no content is an error ("MUST NOT send Handshake and
/// Alert records that have a zero-length TLSInnerPlaintext.content");
/// empty application data is fine.
pub proof fn lemma_open_inner_plaintext()
    ensures
        open_inner_plaintext(seq![0u8, 0]) == Res::<Record>::Err(ErrKind::AllZeroInnerPlaintext),
        open_inner_plaintext(seq![1u8, 22]) == Res::<Record>::Ok(Record { ctype: 22, fragment: seq![1u8] }),
        open_inner_plaintext(seq![1u8, 21, 0]) == Res::<Record>::Ok(Record { ctype: 21, fragment: seq![1u8] }),
        open_inner_plaintext(seq![1u8, 20]) == Res::<Record>::Err(ErrKind::BadChangeCipherSpec),
        open_inner_plaintext(seq![1u8, 24]) == Res::<Record>::Err(ErrKind::UnexpectedContentType),
        open_inner_plaintext(seq![22u8]) == Res::<Record>::Err(ErrKind::ZeroLengthFragment),
        open_inner_plaintext(seq![21u8, 0]) == Res::<Record>::Err(ErrKind::ZeroLengthFragment),
        open_inner_plaintext(seq![23u8]) == Res::<Record>::Ok(Record { ctype: 23, fragment: Seq::<u8>::empty() }),
{
    assert(open_inner_plaintext(seq![0u8, 0]) == Res::<Record>::Err(ErrKind::AllZeroInnerPlaintext)) by (compute_only);
    assert(open_inner_plaintext(seq![1u8, 22]) == Res::<Record>::Ok(Record { ctype: 22, fragment: seq![1u8] })) by (compute_only);
    assert(open_inner_plaintext(seq![1u8, 21, 0]) == Res::<Record>::Ok(Record { ctype: 21, fragment: seq![1u8] })) by (compute_only);
    assert(open_inner_plaintext(seq![1u8, 20]) == Res::<Record>::Err(ErrKind::BadChangeCipherSpec)) by (compute_only);
    assert(open_inner_plaintext(seq![1u8, 24]) == Res::<Record>::Err(ErrKind::UnexpectedContentType)) by (compute_only);
    assert(open_inner_plaintext(seq![22u8]) == Res::<Record>::Err(ErrKind::ZeroLengthFragment)) by (compute_only);
    assert(open_inner_plaintext(seq![21u8, 0]) == Res::<Record>::Err(ErrKind::ZeroLengthFragment)) by (compute_only);
    assert(open_inner_plaintext(seq![23u8]) == Res::<Record>::Ok(Record { ctype: 23, fragment: Seq::<u8>::empty() })) by (compute_only);
}

/// §5.2: "additional_data = TLSCiphertext.opaque_type ||
/// TLSCiphertext.legacy_record_version || TLSCiphertext.length": type 23,
/// version 0x0303, the length in two bytes.
pub proof fn lemma_additional_data()
    ensures
        additional_data(0x4100) == seq![23u8, 3, 3, 0x41, 0],
        additional_data(5) == seq![23u8, 3, 3, 0, 5],
        write_record_header(22, 0x0301, 0x0102) == seq![22u8, 3, 1, 1, 2],
{
    assert(additional_data(0x4100) == seq![23u8, 3, 3, 0x41, 0]) by (compute_only);
    assert(additional_data(5) == seq![23u8, 3, 3, 0, 5]) by (compute_only);
    assert(write_record_header(22, 0x0301, 0x0102) == seq![22u8, 3, 1, 1, 2]) by (compute_only);
}

/// §5.3: "1. The 64-bit record sequence number is encoded in network byte
/// order and padded to the left with zeros to iv_length. 2. The padded
/// sequence number is XORed with ... the static client_write_iv or
/// server_write_iv." With a twelve-byte IV that ends in 5 and sequence
/// number 3, the last byte is 5 xor 3 = 6; with sequence number 0x0102
/// the last two bytes are 0x0102 xor the IV's.
pub proof fn lemma_nonce_examples()
    ensures
        per_record_nonce(seq![0xA0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5], 3) == seq![0xA0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6],
        per_record_nonce(seq![1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], 0x0102) == seq![1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 14],
        per_record_nonce(seq![0u8, 0, 0, 0, 0, 0, 0, 0], 0x0100000000000000) == seq![1u8, 0, 0, 0, 0, 0, 0, 0],
{
    assert(per_record_nonce(seq![0xA0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5], 3) == seq![0xA0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6])
        by (compute_only);
    assert(per_record_nonce(seq![1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], 0x0102) == seq![1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 14])
        by (compute_only);
    assert(per_record_nonce(seq![0u8, 0, 0, 0, 0, 0, 0, 0], 0x0100000000000000) == seq![1u8, 0, 0, 0, 0, 0, 0, 0])
        by (compute_only);
}

// ---------------------------------------------------------------------------
// §5.1: the reassembly of handshake messages.
// ---------------------------------------------------------------------------

/// §4 and §5.1: messages are coalesced in a record and fragmented across
/// records; a message is emitted when its last byte arrives and not
/// before.
pub proof fn lemma_extract_examples()
    ensures
        extract_messages(seq![1u8, 0, 0, 1, 9, 2, 0, 0, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (seq![seq![1u8, 0, 0, 1, 9], seq![2u8, 0, 0, 0]], Seq::<u8>::empty()),
        ),
        extract_messages(seq![1u8, 0, 0, 2, 9]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (Seq::<Seq<u8>>::empty(), seq![1u8, 0, 0, 2, 9]),
        ),
        extract_messages(seq![1u8, 0, 0, 1, 9]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (seq![seq![1u8, 0, 0, 1, 9]], Seq::<u8>::empty()),
        ),
        extract_messages(seq![1u8, 0, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (Seq::<Seq<u8>>::empty(), seq![1u8, 0, 0]),
        ),
        extract_messages(seq![1u8, 0, 0, 0, 2, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (seq![seq![1u8, 0, 0, 0]], seq![2u8, 0]),
        ),
        extract_messages(Seq::<u8>::empty()) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (Seq::<Seq<u8>>::empty(), Seq::<u8>::empty()),
        ),
{
    assert(extract_messages(seq![1u8, 0, 0, 1, 9, 2, 0, 0, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (seq![seq![1u8, 0, 0, 1, 9], seq![2u8, 0, 0, 0]], Seq::<u8>::empty()),
    )) by (compute_only);
    assert(extract_messages(seq![1u8, 0, 0, 2, 9]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (Seq::<Seq<u8>>::empty(), seq![1u8, 0, 0, 2, 9]),
    )) by (compute_only);
    assert(extract_messages(seq![1u8, 0, 0, 1, 9]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (seq![seq![1u8, 0, 0, 1, 9]], Seq::<u8>::empty()),
    )) by (compute_only);
    assert(extract_messages(seq![1u8, 0, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (Seq::<Seq<u8>>::empty(), seq![1u8, 0, 0]),
    )) by (compute_only);
    assert(extract_messages(seq![1u8, 0, 0, 0, 2, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (seq![seq![1u8, 0, 0, 0]], seq![2u8, 0]),
    )) by (compute_only);
    assert(extract_messages(Seq::<u8>::empty()) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (Seq::<Seq<u8>>::empty(), Seq::<u8>::empty()),
    )) by (compute_only);
}

/// The limit on a handshake message: a body of 2^18 octets (262144 =
/// 0x040000) is waited for, one of 0x040001 is refused at its header.
pub proof fn lemma_handshake_limit()
    ensures
        extract_messages(seq![1u8, 4, 0, 1]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(ErrKind::HandshakeTooLarge),
        extract_messages(seq![1u8, 4, 0, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
            (Seq::<Seq<u8>>::empty(), seq![1u8, 4, 0, 0]),
        ),
        extract_messages(seq![1u8, 0xFF, 0xFF, 0xFF]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(ErrKind::HandshakeTooLarge),
{
    assert(extract_messages(seq![1u8, 4, 0, 1]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(ErrKind::HandshakeTooLarge))
        by (compute_only);
    assert(extract_messages(seq![1u8, 4, 0, 0]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Ok(
        (Seq::<Seq<u8>>::empty(), seq![1u8, 4, 0, 0]),
    )) by (compute_only);
    assert(extract_messages(seq![1u8, 0xFF, 0xFF, 0xFF]) == Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(ErrKind::HandshakeTooLarge))
        by (compute_only);
}

/// §5.1: records of other types do not interleave with a handshake
/// message; a zero-length handshake or alert fragment is an error; an
/// alert is exactly one message.
pub proof fn lemma_feed_examples()
    ensures
        feed_record(Reasm { buf: seq![1u8, 0, 0, 5] }, Record { ctype: 23, fragment: seq![1u8] })
            == Res::<(Event, Reasm)>::Err(ErrKind::Interleaved),
        feed_record(Reasm { buf: seq![1u8, 0, 0, 5] }, Record { ctype: 21, fragment: seq![2u8, 40] })
            == Res::<(Event, Reasm)>::Err(ErrKind::Interleaved),
        feed_ccs(Reasm { buf: seq![1u8] }) == Res::<(Event, Reasm)>::Err(ErrKind::Interleaved),
        feed_ccs(Reasm { buf: Seq::<u8>::empty() }) == Res::<(Event, Reasm)>::Ok(
            (Event::Ignored, Reasm { buf: Seq::<u8>::empty() }),
        ),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 22, fragment: Seq::<u8>::empty() })
            == Res::<(Event, Reasm)>::Err(ErrKind::ZeroLengthFragment),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: Seq::<u8>::empty() })
            == Res::<(Event, Reasm)>::Err(ErrKind::ZeroLengthFragment),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: seq![2u8, 40] })
            == Res::<(Event, Reasm)>::Ok((Event::Alert(Alert { level: 2, description: 40 }), Reasm { buf: Seq::<u8>::empty() })),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: seq![2u8, 40, 2, 40] })
            == Res::<(Event, Reasm)>::Err(ErrKind::Decode),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: seq![2u8] })
            == Res::<(Event, Reasm)>::Err(ErrKind::Decode),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 23, fragment: seq![7u8] })
            == Res::<(Event, Reasm)>::Ok((Event::AppData(seq![7u8]), Reasm { buf: Seq::<u8>::empty() })),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 20, fragment: seq![1u8] })
            == Res::<(Event, Reasm)>::Err(ErrKind::BadChangeCipherSpec),
        feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 0, fragment: seq![1u8] })
            == Res::<(Event, Reasm)>::Err(ErrKind::UnexpectedContentType),
        feed_record(Reasm { buf: seq![1u8, 0] }, Record { ctype: 22, fragment: seq![0u8, 1, 9, 2, 0] })
            == Res::<(Event, Reasm)>::Ok(
            (Event::Messages(seq![seq![1u8, 0, 0, 1, 9]]), Reasm { buf: seq![2u8, 0] }),
        ),
{
    assert(feed_record(Reasm { buf: seq![1u8, 0, 0, 5] }, Record { ctype: 23, fragment: seq![1u8] })
        == Res::<(Event, Reasm)>::Err(ErrKind::Interleaved)) by (compute_only);
    assert(feed_record(Reasm { buf: seq![1u8, 0, 0, 5] }, Record { ctype: 21, fragment: seq![2u8, 40] })
        == Res::<(Event, Reasm)>::Err(ErrKind::Interleaved)) by (compute_only);
    assert(feed_ccs(Reasm { buf: seq![1u8] }) == Res::<(Event, Reasm)>::Err(ErrKind::Interleaved)) by (compute_only);
    assert(feed_ccs(Reasm { buf: Seq::<u8>::empty() }) == Res::<(Event, Reasm)>::Ok(
        (Event::Ignored, Reasm { buf: Seq::<u8>::empty() }),
    )) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 22, fragment: Seq::<u8>::empty() })
        == Res::<(Event, Reasm)>::Err(ErrKind::ZeroLengthFragment)) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: Seq::<u8>::empty() })
        == Res::<(Event, Reasm)>::Err(ErrKind::ZeroLengthFragment)) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: seq![2u8, 40] })
        == Res::<(Event, Reasm)>::Ok((Event::Alert(Alert { level: 2, description: 40 }), Reasm { buf: Seq::<u8>::empty() })))
        by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: seq![2u8, 40, 2, 40] })
        == Res::<(Event, Reasm)>::Err(ErrKind::Decode)) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 21, fragment: seq![2u8] })
        == Res::<(Event, Reasm)>::Err(ErrKind::Decode)) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 23, fragment: seq![7u8] })
        == Res::<(Event, Reasm)>::Ok((Event::AppData(seq![7u8]), Reasm { buf: Seq::<u8>::empty() }))) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 20, fragment: seq![1u8] })
        == Res::<(Event, Reasm)>::Err(ErrKind::BadChangeCipherSpec)) by (compute_only);
    assert(feed_record(Reasm { buf: Seq::<u8>::empty() }, Record { ctype: 0, fragment: seq![1u8] })
        == Res::<(Event, Reasm)>::Err(ErrKind::UnexpectedContentType)) by (compute_only);
    assert(feed_record(Reasm { buf: seq![1u8, 0] }, Record { ctype: 22, fragment: seq![0u8, 1, 9, 2, 0] })
        == Res::<(Event, Reasm)>::Ok((Event::Messages(seq![seq![1u8, 0, 0, 1, 9]]), Reasm { buf: seq![2u8, 0] })))
        by (compute_only);
}

// ---------------------------------------------------------------------------
// §6: alerts.
// ---------------------------------------------------------------------------

/// §6.2: the alert each kind of error maps to.
pub proof fn lemma_alert_mapping()
    ensures
        alert_of(ErrKind::Decode) == 50,
        alert_of(ErrKind::RecordOverflow) == 22,
        alert_of(ErrKind::UnexpectedContentType) == 10,
        alert_of(ErrKind::UnexpectedHandshakeType) == 10,
        alert_of(ErrKind::ZeroLengthFragment) == 10,
        alert_of(ErrKind::Interleaved) == 10,
        alert_of(ErrKind::AllZeroInnerPlaintext) == 10,
        alert_of(ErrKind::BadChangeCipherSpec) == 10,
        alert_of(ErrKind::BadLegacyRecordVersion) == 50,
        alert_of(ErrKind::HandshakeTooLarge) == 47,
        alert_of(ErrKind::DuplicateExtension) == 47,
        alert_of(ErrKind::ExtensionNotAllowed) == 47,
        alert_of(ErrKind::InvalidEnum) == 47,
        alert_of(ErrKind::NonEmptyContext) == 47,
        alert_of(ErrKind::MissingExtension) == 109,
        alert_of(ErrKind::BadRecordMac) == 20,
        alert_for(ErrKind::Decode) == (Alert { level: 2, description: 50 }),
{
    assert(alert_of(ErrKind::Decode) == 50) by (compute_only);
    assert(alert_of(ErrKind::RecordOverflow) == 22) by (compute_only);
    assert(alert_of(ErrKind::UnexpectedContentType) == 10) by (compute_only);
    assert(alert_of(ErrKind::UnexpectedHandshakeType) == 10) by (compute_only);
    assert(alert_of(ErrKind::ZeroLengthFragment) == 10) by (compute_only);
    assert(alert_of(ErrKind::Interleaved) == 10) by (compute_only);
    assert(alert_of(ErrKind::AllZeroInnerPlaintext) == 10) by (compute_only);
    assert(alert_of(ErrKind::BadChangeCipherSpec) == 10) by (compute_only);
    assert(alert_of(ErrKind::BadLegacyRecordVersion) == 50) by (compute_only);
    assert(alert_of(ErrKind::HandshakeTooLarge) == 47) by (compute_only);
    assert(alert_of(ErrKind::DuplicateExtension) == 47) by (compute_only);
    assert(alert_of(ErrKind::ExtensionNotAllowed) == 47) by (compute_only);
    assert(alert_of(ErrKind::InvalidEnum) == 47) by (compute_only);
    assert(alert_of(ErrKind::NonEmptyContext) == 47) by (compute_only);
    assert(alert_of(ErrKind::MissingExtension) == 109) by (compute_only);
    assert(alert_of(ErrKind::BadRecordMac) == 20) by (compute_only);
    assert(alert_for(ErrKind::Decode) == Alert { level: 2, description: 50 }) by (compute_only);
}

/// §6, §6.1: `close_notify` closes; `user_canceled` closes when it is a
/// warning; every other alert is an error whatever its level says, and
/// "Unknown Alert types MUST be treated as error alerts."
pub proof fn lemma_alert_closure()
    ensures
        alert_is_closure(Alert { level: 1, description: 0 }),
        alert_is_closure(Alert { level: 2, description: 0 }),
        alert_is_closure(Alert { level: 1, description: 90 }),
        !alert_is_closure(Alert { level: 2, description: 90 }),
        !alert_is_closure(Alert { level: 1, description: 40 }),
        !alert_is_closure(Alert { level: 1, description: 200 }),
{
    assert(alert_is_closure(Alert { level: 1, description: 0 })) by (compute_only);
    assert(alert_is_closure(Alert { level: 2, description: 0 })) by (compute_only);
    assert(alert_is_closure(Alert { level: 1, description: 90 })) by (compute_only);
    assert(!alert_is_closure(Alert { level: 2, description: 90 })) by (compute_only);
    assert(!alert_is_closure(Alert { level: 1, description: 40 })) by (compute_only);
    assert(!alert_is_closure(Alert { level: 1, description: 200 })) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.2: the table of which extension may appear in which message, one
// lemma per row.
// ---------------------------------------------------------------------------

/// §4.2 table row `server_name`: CH, EE.
pub proof fn lemma_ext_row_server_name()
    ensures
        extension_allowed(0, MsgKind::Ch),
        extension_allowed(0, MsgKind::Ee),
        !extension_allowed(0, MsgKind::Sh),
        !extension_allowed(0, MsgKind::Ct),
        !extension_allowed(0, MsgKind::Cr),
        !extension_allowed(0, MsgKind::Nst),
        !extension_allowed(0, MsgKind::Hrr),
{
    assert(extension_allowed(0, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(0, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(0, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(0, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(0, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(0, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(0, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `max_fragment_length`: CH, EE.
pub proof fn lemma_ext_row_max_fragment_length()
    ensures
        extension_allowed(1, MsgKind::Ch),
        extension_allowed(1, MsgKind::Ee),
        !extension_allowed(1, MsgKind::Sh),
        !extension_allowed(1, MsgKind::Ct),
        !extension_allowed(1, MsgKind::Cr),
        !extension_allowed(1, MsgKind::Nst),
        !extension_allowed(1, MsgKind::Hrr),
{
    assert(extension_allowed(1, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(1, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(1, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(1, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(1, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(1, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(1, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `status_request`: CH, CR, CT.
pub proof fn lemma_ext_row_status_request()
    ensures
        extension_allowed(5, MsgKind::Ch),
        extension_allowed(5, MsgKind::Cr),
        extension_allowed(5, MsgKind::Ct),
        !extension_allowed(5, MsgKind::Sh),
        !extension_allowed(5, MsgKind::Ee),
        !extension_allowed(5, MsgKind::Nst),
        !extension_allowed(5, MsgKind::Hrr),
{
    assert(extension_allowed(5, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(5, MsgKind::Cr)) by (compute_only);
    assert(extension_allowed(5, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(5, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(5, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(5, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(5, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `supported_groups`: CH, EE.
pub proof fn lemma_ext_row_supported_groups()
    ensures
        extension_allowed(10, MsgKind::Ch),
        extension_allowed(10, MsgKind::Ee),
        !extension_allowed(10, MsgKind::Sh),
        !extension_allowed(10, MsgKind::Ct),
        !extension_allowed(10, MsgKind::Cr),
        !extension_allowed(10, MsgKind::Nst),
        !extension_allowed(10, MsgKind::Hrr),
{
    assert(extension_allowed(10, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(10, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(10, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(10, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(10, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(10, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(10, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `signature_algorithms`: CH, CR.
pub proof fn lemma_ext_row_signature_algorithms()
    ensures
        extension_allowed(13, MsgKind::Ch),
        extension_allowed(13, MsgKind::Cr),
        !extension_allowed(13, MsgKind::Sh),
        !extension_allowed(13, MsgKind::Ee),
        !extension_allowed(13, MsgKind::Ct),
        !extension_allowed(13, MsgKind::Nst),
        !extension_allowed(13, MsgKind::Hrr),
{
    assert(extension_allowed(13, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(13, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(13, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(13, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(13, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(13, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(13, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `use_srtp`: CH, EE.
pub proof fn lemma_ext_row_use_srtp()
    ensures
        extension_allowed(14, MsgKind::Ch),
        extension_allowed(14, MsgKind::Ee),
        !extension_allowed(14, MsgKind::Sh),
        !extension_allowed(14, MsgKind::Ct),
        !extension_allowed(14, MsgKind::Cr),
        !extension_allowed(14, MsgKind::Nst),
        !extension_allowed(14, MsgKind::Hrr),
{
    assert(extension_allowed(14, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(14, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(14, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(14, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(14, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(14, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(14, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `heartbeat`: CH, EE.
pub proof fn lemma_ext_row_heartbeat()
    ensures
        extension_allowed(15, MsgKind::Ch),
        extension_allowed(15, MsgKind::Ee),
        !extension_allowed(15, MsgKind::Sh),
        !extension_allowed(15, MsgKind::Ct),
        !extension_allowed(15, MsgKind::Cr),
        !extension_allowed(15, MsgKind::Nst),
        !extension_allowed(15, MsgKind::Hrr),
{
    assert(extension_allowed(15, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(15, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(15, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(15, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(15, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(15, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(15, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `application_layer_protocol_negotiation`: CH, EE.
pub proof fn lemma_ext_row_alpn()
    ensures
        extension_allowed(16, MsgKind::Ch),
        extension_allowed(16, MsgKind::Ee),
        !extension_allowed(16, MsgKind::Sh),
        !extension_allowed(16, MsgKind::Ct),
        !extension_allowed(16, MsgKind::Cr),
        !extension_allowed(16, MsgKind::Nst),
        !extension_allowed(16, MsgKind::Hrr),
{
    assert(extension_allowed(16, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(16, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(16, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(16, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(16, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(16, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(16, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `signed_certificate_timestamp`: CH, CR, CT.
pub proof fn lemma_ext_row_signed_certificate_timestamp()
    ensures
        extension_allowed(18, MsgKind::Ch),
        extension_allowed(18, MsgKind::Cr),
        extension_allowed(18, MsgKind::Ct),
        !extension_allowed(18, MsgKind::Sh),
        !extension_allowed(18, MsgKind::Ee),
        !extension_allowed(18, MsgKind::Nst),
        !extension_allowed(18, MsgKind::Hrr),
{
    assert(extension_allowed(18, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(18, MsgKind::Cr)) by (compute_only);
    assert(extension_allowed(18, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(18, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(18, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(18, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(18, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `client_certificate_type`: CH, EE.
pub proof fn lemma_ext_row_client_certificate_type()
    ensures
        extension_allowed(19, MsgKind::Ch),
        extension_allowed(19, MsgKind::Ee),
        !extension_allowed(19, MsgKind::Sh),
        !extension_allowed(19, MsgKind::Ct),
        !extension_allowed(19, MsgKind::Cr),
        !extension_allowed(19, MsgKind::Nst),
        !extension_allowed(19, MsgKind::Hrr),
{
    assert(extension_allowed(19, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(19, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(19, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(19, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(19, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(19, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(19, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `server_certificate_type`: CH, EE.
pub proof fn lemma_ext_row_server_certificate_type()
    ensures
        extension_allowed(20, MsgKind::Ch),
        extension_allowed(20, MsgKind::Ee),
        !extension_allowed(20, MsgKind::Sh),
        !extension_allowed(20, MsgKind::Ct),
        !extension_allowed(20, MsgKind::Cr),
        !extension_allowed(20, MsgKind::Nst),
        !extension_allowed(20, MsgKind::Hrr),
{
    assert(extension_allowed(20, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(20, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(20, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(20, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(20, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(20, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(20, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `padding`: CH.
pub proof fn lemma_ext_row_padding()
    ensures
        extension_allowed(21, MsgKind::Ch),
        !extension_allowed(21, MsgKind::Sh),
        !extension_allowed(21, MsgKind::Ee),
        !extension_allowed(21, MsgKind::Ct),
        !extension_allowed(21, MsgKind::Cr),
        !extension_allowed(21, MsgKind::Nst),
        !extension_allowed(21, MsgKind::Hrr),
{
    assert(extension_allowed(21, MsgKind::Ch)) by (compute_only);
    assert(!extension_allowed(21, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(21, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(21, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(21, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(21, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(21, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `key_share`: CH, SH, HRR.
pub proof fn lemma_ext_row_key_share()
    ensures
        extension_allowed(51, MsgKind::Ch),
        extension_allowed(51, MsgKind::Sh),
        extension_allowed(51, MsgKind::Hrr),
        !extension_allowed(51, MsgKind::Ee),
        !extension_allowed(51, MsgKind::Ct),
        !extension_allowed(51, MsgKind::Cr),
        !extension_allowed(51, MsgKind::Nst),
{
    assert(extension_allowed(51, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(51, MsgKind::Sh)) by (compute_only);
    assert(extension_allowed(51, MsgKind::Hrr)) by (compute_only);
    assert(!extension_allowed(51, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(51, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(51, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(51, MsgKind::Nst)) by (compute_only);
}

/// §4.2 table row `pre_shared_key`: CH, SH.
pub proof fn lemma_ext_row_pre_shared_key()
    ensures
        extension_allowed(41, MsgKind::Ch),
        extension_allowed(41, MsgKind::Sh),
        !extension_allowed(41, MsgKind::Ee),
        !extension_allowed(41, MsgKind::Ct),
        !extension_allowed(41, MsgKind::Cr),
        !extension_allowed(41, MsgKind::Nst),
        !extension_allowed(41, MsgKind::Hrr),
{
    assert(extension_allowed(41, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(41, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(41, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(41, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(41, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(41, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(41, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `psk_key_exchange_modes`: CH.
pub proof fn lemma_ext_row_psk_key_exchange_modes()
    ensures
        extension_allowed(45, MsgKind::Ch),
        !extension_allowed(45, MsgKind::Sh),
        !extension_allowed(45, MsgKind::Ee),
        !extension_allowed(45, MsgKind::Ct),
        !extension_allowed(45, MsgKind::Cr),
        !extension_allowed(45, MsgKind::Nst),
        !extension_allowed(45, MsgKind::Hrr),
{
    assert(extension_allowed(45, MsgKind::Ch)) by (compute_only);
    assert(!extension_allowed(45, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(45, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(45, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(45, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(45, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(45, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `early_data`: CH, EE, NST.
pub proof fn lemma_ext_row_early_data()
    ensures
        extension_allowed(42, MsgKind::Ch),
        extension_allowed(42, MsgKind::Ee),
        extension_allowed(42, MsgKind::Nst),
        !extension_allowed(42, MsgKind::Sh),
        !extension_allowed(42, MsgKind::Ct),
        !extension_allowed(42, MsgKind::Cr),
        !extension_allowed(42, MsgKind::Hrr),
{
    assert(extension_allowed(42, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(42, MsgKind::Ee)) by (compute_only);
    assert(extension_allowed(42, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(42, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(42, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(42, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(42, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `cookie`: CH, HRR.
pub proof fn lemma_ext_row_cookie()
    ensures
        extension_allowed(44, MsgKind::Ch),
        extension_allowed(44, MsgKind::Hrr),
        !extension_allowed(44, MsgKind::Sh),
        !extension_allowed(44, MsgKind::Ee),
        !extension_allowed(44, MsgKind::Ct),
        !extension_allowed(44, MsgKind::Cr),
        !extension_allowed(44, MsgKind::Nst),
{
    assert(extension_allowed(44, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(44, MsgKind::Hrr)) by (compute_only);
    assert(!extension_allowed(44, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(44, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(44, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(44, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(44, MsgKind::Nst)) by (compute_only);
}

/// §4.2 table row `supported_versions`: CH, SH, HRR.
pub proof fn lemma_ext_row_supported_versions()
    ensures
        extension_allowed(43, MsgKind::Ch),
        extension_allowed(43, MsgKind::Sh),
        extension_allowed(43, MsgKind::Hrr),
        !extension_allowed(43, MsgKind::Ee),
        !extension_allowed(43, MsgKind::Ct),
        !extension_allowed(43, MsgKind::Cr),
        !extension_allowed(43, MsgKind::Nst),
{
    assert(extension_allowed(43, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(43, MsgKind::Sh)) by (compute_only);
    assert(extension_allowed(43, MsgKind::Hrr)) by (compute_only);
    assert(!extension_allowed(43, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(43, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(43, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(43, MsgKind::Nst)) by (compute_only);
}

/// §4.2 table row `certificate_authorities`: CH, CR.
pub proof fn lemma_ext_row_certificate_authorities()
    ensures
        extension_allowed(47, MsgKind::Ch),
        extension_allowed(47, MsgKind::Cr),
        !extension_allowed(47, MsgKind::Sh),
        !extension_allowed(47, MsgKind::Ee),
        !extension_allowed(47, MsgKind::Ct),
        !extension_allowed(47, MsgKind::Nst),
        !extension_allowed(47, MsgKind::Hrr),
{
    assert(extension_allowed(47, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(47, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(47, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(47, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(47, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(47, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(47, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `oid_filters`: CR.
pub proof fn lemma_ext_row_oid_filters()
    ensures
        extension_allowed(48, MsgKind::Cr),
        !extension_allowed(48, MsgKind::Ch),
        !extension_allowed(48, MsgKind::Sh),
        !extension_allowed(48, MsgKind::Ee),
        !extension_allowed(48, MsgKind::Ct),
        !extension_allowed(48, MsgKind::Nst),
        !extension_allowed(48, MsgKind::Hrr),
{
    assert(extension_allowed(48, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(48, MsgKind::Ch)) by (compute_only);
    assert(!extension_allowed(48, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(48, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(48, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(48, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(48, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `post_handshake_auth`: CH.
pub proof fn lemma_ext_row_post_handshake_auth()
    ensures
        extension_allowed(49, MsgKind::Ch),
        !extension_allowed(49, MsgKind::Sh),
        !extension_allowed(49, MsgKind::Ee),
        !extension_allowed(49, MsgKind::Ct),
        !extension_allowed(49, MsgKind::Cr),
        !extension_allowed(49, MsgKind::Nst),
        !extension_allowed(49, MsgKind::Hrr),
{
    assert(extension_allowed(49, MsgKind::Ch)) by (compute_only);
    assert(!extension_allowed(49, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(49, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(49, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(49, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(49, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(49, MsgKind::Hrr)) by (compute_only);
}

/// §4.2 table row `signature_algorithms_cert`: CH, CR.
pub proof fn lemma_ext_row_signature_algorithms_cert()
    ensures
        extension_allowed(50, MsgKind::Ch),
        extension_allowed(50, MsgKind::Cr),
        !extension_allowed(50, MsgKind::Sh),
        !extension_allowed(50, MsgKind::Ee),
        !extension_allowed(50, MsgKind::Ct),
        !extension_allowed(50, MsgKind::Nst),
        !extension_allowed(50, MsgKind::Hrr),
{
    assert(extension_allowed(50, MsgKind::Ch)) by (compute_only);
    assert(extension_allowed(50, MsgKind::Cr)) by (compute_only);
    assert(!extension_allowed(50, MsgKind::Sh)) by (compute_only);
    assert(!extension_allowed(50, MsgKind::Ee)) by (compute_only);
    assert(!extension_allowed(50, MsgKind::Ct)) by (compute_only);
    assert(!extension_allowed(50, MsgKind::Nst)) by (compute_only);
    assert(!extension_allowed(50, MsgKind::Hrr)) by (compute_only);
}

/// §4.2: a type that is not a row of the table (here 40 and 46, "Used
/// but never assigned" in Appendix B, and 0xFFFF) is not restricted by it.
pub proof fn lemma_ext_unknown_rows()
    ensures
        !extension_known(40),
        !extension_known(46),
        !extension_known(0xFFFF),
        extension_known(0),
        extension_known(51),
        extension_allowed(40, MsgKind::Sh),
        extension_allowed(0xFFFF, MsgKind::Ct),
{
    assert(!extension_known(40)) by (compute_only);
    assert(!extension_known(46)) by (compute_only);
    assert(!extension_known(0xFFFF)) by (compute_only);
    assert(extension_known(0)) by (compute_only);
    assert(extension_known(51)) by (compute_only);
    assert(extension_allowed(40, MsgKind::Sh)) by (compute_only);
    assert(extension_allowed(0xFFFF, MsgKind::Ct)) by (compute_only);
}

/// RFC 8446 §5.4: padding counts toward the complete 2^14+1 inner bound.
pub proof fn lemma_inner_full_length()
    ensures open_inner_plaintext(Seq::new(16384, |i: int| 42u8) + seq![23u8, 0u8]) == Res::<Record>::Err(ErrKind::RecordOverflow),
{
    assert(open_inner_plaintext(Seq::new(16384, |i: int| 42u8) + seq![23u8, 0u8]) == Res::<Record>::Err(ErrKind::RecordOverflow)) by (compute_only);
}

} // verus!
