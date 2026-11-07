//! RFC 8446 §5: the wire forms of the record layer, the limits, the per-record
//! nonce and the AEAD inputs. Receiving is in `connection`.
//!
//! Modelling choices:
//! - `ContentType` is a `nat` with prefix `ct_`, so unknown types survive to
//!   "receives an unexpected record type".
//! - A record's `legacy_record_version` is read and kept only as bytes for the
//!   AEAD: "TLSPlaintext.legacy_record_version MUST be ignored by all
//!   implementations", and Appendix D says of the ciphertext one that it "is
//!   included in the additional data for deprotection but MAY otherwise be
//!   ignored". So [`additional_data`] uses the received value, which gives a
//!   different result from the §5.2 constant only if a peer sent another value,
//!   when decryption fails anyway.
//! - The model's sender never pads ([`write_inner_plaintext`] takes the length,
//!   and the sender passes 0): "Implementations MAY choose to pad". The receiver
//!   accepts any padding.
//! - The model's sender does not fragment what fits one record, and does not
//!   coalesce handshake messages: both are allowed (§5.1).
//! - Sequence numbers are `nat`. "they should not wrap": [`max_sequence_number`]
//!   is where §5.3's rule applies.
//! - AEAD's expansion in TLSCiphertext.length is `aead_expansion()`, the tag.
//! - The nonce's step 1 pads to the length of `iv`, which is iv_length here;
//!   `encode_uint` keeps the low bytes, which is everything when the number fits
//!   64 bits.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;

verus! {

/// §5.1 invalid(0).
pub open spec fn ct_invalid() -> nat { 0 }
/// §5.1 change_cipher_spec(20).
pub open spec fn ct_change_cipher_spec() -> nat { 20 }
/// §5.1 alert(21).
pub open spec fn ct_alert() -> nat { 21 }
/// §5.1 handshake(22).
pub open spec fn ct_handshake() -> nat { 22 }
/// §5.1 application_data(23).
pub open spec fn ct_application_data() -> nat { 23 }

/// §5.1: "The length MUST NOT exceed 2^14 bytes."
pub open spec fn max_plaintext_length() -> nat { 0x4000 }

/// §5.2: "The length MUST NOT exceed 2^14 + 256 bytes."
pub open spec fn max_ciphertext_length() -> nat { 0x4000 + 256 }

/// §5.4: "the full encoded TLSInnerPlaintext MUST NOT exceed 2^14 + 1 octets."
pub open spec fn max_inner_plaintext_length() -> nat { 0x4000 + 1 }

/// §5.3: "A 64-bit sequence number": the largest there is.
pub open spec fn max_sequence_number() -> nat { 0xffff_ffff_ffff_ffff }

/// §5.1: the header shared by TLSPlaintext and TLSCiphertext: `ContentType type;
/// ProtocolVersion legacy_record_version; uint16 length;`.
pub struct RecordHeader {
    /// §5.1 type; §5.2 opaque_type.
    pub content_type: nat,
    /// §5.1, §5.2 legacy_record_version.
    pub legacy_record_version: nat,
    /// §5.1, §5.2 length.
    pub length: nat,
}

/// §5.1: the header at the start of `stream`, if five bytes are there.
pub open spec fn read_record_header(stream: Seq<u8>) -> Option<RecordHeader> {
    if stream.len() < 5 {
        None
    } else {
        Some(RecordHeader {
            content_type: stream[0] as nat,
            legacy_record_version: read_uint(stream.subrange(1, 3), 2),
            length: read_uint(stream.subrange(3, 5), 2),
        })
    }
}

/// §5.1: the encoded header.
pub open spec fn write_record_header(content_type: nat, legacy_record_version: nat, length: nat) -> Seq<u8> {
    uint8(content_type) + uint16(legacy_record_version) + uint16(length)
}

/// §5.1: an encoded TLSPlaintext.
pub open spec fn write_tls_plaintext(content_type: nat, legacy_record_version: nat, fragment: Seq<u8>) -> Seq<u8> {
    write_record_header(content_type, legacy_record_version, fragment.len()) + fragment
}

/// §5.2: `struct { opaque content[TLSPlaintext.length]; ContentType type; uint8
/// zeros[length_of_padding]; } TLSInnerPlaintext;`
pub open spec fn write_inner_plaintext(content: Seq<u8>, content_type: nat, length_of_padding: nat) -> Seq<u8> {
    content + uint8(content_type) + repeat_byte(0, length_of_padding)
}

/// §5.4: "upon successful decryption of a TLSCiphertext.encrypted_record, the
/// receiving implementation scans the field from the end toward the beginning
/// until it finds a non-zero octet. This non-zero octet is the content type of the
/// message." The result is (content, type), or `None` if there is no non-zero
/// octet ("MUST limit their scanning to the cleartext returned").
pub open spec fn read_inner_plaintext(cleartext: Seq<u8>) -> Option<(Seq<u8>, nat)>
    decreases cleartext.len(),
{
    if cleartext.len() == 0 {
        None
    } else {
        let before_last = cleartext.subrange(0, cleartext.len() - 1);
        if cleartext[cleartext.len() - 1] != 0 {
            Some((before_last, cleartext[cleartext.len() - 1] as nat))
        } else {
            read_inner_plaintext(before_last)
        }
    }
}

/// §5.2: `additional_data = TLSCiphertext.opaque_type ||
/// TLSCiphertext.legacy_record_version || TLSCiphertext.length`.
pub open spec fn additional_data(opaque_type: nat, legacy_record_version: nat, length: nat) -> Seq<u8> {
    write_record_header(opaque_type, legacy_record_version, length)
}

/// Byte-wise XOR of two sequences of the same length.
pub open spec fn xor_bytes(a: Seq<u8>, b: Seq<u8>) -> Seq<u8>
    decreases a.len(),
{
    if a.len() == 0 || b.len() == 0 {
        seq![]
    } else {
        seq![a[0] ^ b[0]] + xor_bytes(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

/// §5.3: "The per-record nonce for the AEAD construction is formed as follows".
pub open spec fn per_record_nonce(write_iv: Seq<u8>, sequence_number: nat) -> Seq<u8> {
    // 1. "The 64-bit record sequence number is encoded in network byte order and
    //    padded to the left with zeros to iv_length."
    let padded = encode_uint(sequence_number, write_iv.len());
    // 2. "The padded sequence number is XORed with either the static
    //    client_write_iv or server_write_iv (depending on the role)."
    xor_bytes(padded, write_iv)
}

/// The traffic secret of a direction, its §7.3 traffic keys, and its §5.3 sequence
/// number.
pub struct TrafficState {
    /// §7.3: the "Secret" of the table.
    pub secret: Seq<u8>,
    /// §7.3: [sender]_write_key.
    pub key: Seq<u8>,
    /// §7.3: [sender]_write_iv.
    pub iv: Seq<u8>,
    /// §5.3: "Each sequence number is set to zero at the beginning of a connection
    /// and whenever the key is changed".
    pub sequence_number: nat,
}

/// §7.3: "All the traffic keying material is recomputed whenever the underlying
/// Secret changes". §5.3: "the first record transmitted under a particular traffic
/// key MUST use sequence number 0".
pub open spec fn traffic_state(p: Primitives, secret: Seq<u8>) -> TrafficState {
    TrafficState { secret, key: write_key(p, secret), iv: write_iv(p, secret), sequence_number: 0 }
}

/// §5.2: "The record protection functions translate a TLSPlaintext structure into a
/// TLSCiphertext structure": the encoded TLSCiphertext of `content` of
/// `content_type`, with no padding, under `traffic` at its sequence number.
pub open spec fn protect_record(p: Primitives, traffic: TrafficState, content_type: nat, content: Seq<u8>) -> Seq<u8> {
    let plaintext = write_inner_plaintext(content, content_type, 0);
    // §5.2 length: "the sum of the lengths of the content and the padding, plus one
    // for the inner content type, plus any expansion added by the AEAD algorithm".
    let length = plaintext.len() + aead_expansion();
    // §5.2: opaque_type = application_data; legacy_record_version = 0x0303.
    let header = write_record_header(ct_application_data(), 0x0303, length);
    let nonce = per_record_nonce(traffic.iv, traffic.sequence_number);
    // AEADEncrypted = AEAD-Encrypt(write_key, nonce, additional_data, plaintext)
    header + (p.aead_encrypt)(traffic.key, nonce, additional_data(ct_application_data(), 0x0303, length), plaintext)
}

/// §5.1: the record layer "fragments information blocks into TLSPlaintext records
/// carrying data in chunks of 2^14 bytes or less". Handshake and application data
/// only: "Alert messages MUST NOT be fragmented".
pub open spec fn fragment_blocks(data: Seq<u8>) -> Seq<Seq<u8>>
    decreases data.len(),
{
    if data.len() <= max_plaintext_length() {
        seq![data]
    } else {
        seq![data.subrange(0, max_plaintext_length() as int)]
            + fragment_blocks(data.subrange(max_plaintext_length() as int, data.len() as int))
    }
}

} // verus!
