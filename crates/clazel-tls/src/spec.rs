//! RFC 8446 "The Transport Layer Security (TLS) Protocol Version 1.3"
//! (August 2018, <https://www.rfc-editor.org/rfc/rfc8446>), transcribed as
//! executable functions over `Seq<u8>`, with RFC 6066 §3 (`server_name`,
//! <https://www.rfc-editor.org/rfc/rfc6066#section-3>). An RFC is
//! immutable, so there is no commit to pin. Nothing here runs; it defines
//! what "correct" means. Each `///` comment cites the section it
//! transcribes and quotes the text it follows.
//!
//! Sections, in order: §3 the presentation language, §6 alerts and the
//! errors of this crate, §5 the record layer and the reassembly of
//! handshake messages, §4.2 extensions, §4 handshake messages.
//!
//! ## What is in and out
//!
//! In: `TLSPlaintext`, `TLSCiphertext`, `TLSInnerPlaintext`, the nonce and
//! additional data, handshake reassembly; `Handshake`, ClientHello,
//! ServerHello, HelloRetryRequest, EncryptedExtensions, CertificateRequest
//! (read, so it can be refused), Certificate, CertificateVerify, Finished,
//! NewSessionTicket (read, then ignored: no resumption in this phase),
//! KeyUpdate, EndOfEarlyData (empty); the extensions of §4.2.1 to §4.2.3,
//! §4.2.7, §4.2.8 and RFC 6066 §3. Out: the key schedule (§7), the
//! handshake state machine (Appendix A) and the cryptography, which are
//! phase-3.md items 3.5e and 3.5f; the contents of a certificate (item
//! 3.5b), `pre_shared_key`, `early_data`, `psk_key_exchange_modes`,
//! `certificate_authorities`, `oid_filters` and the rest, which are
//! `opaque` (their type is kept, their `extension_data` is not read).
//!
//! ## Modelling choices
//!
//! Each is a deviation in form or in strictness, and the argument is given
//! here once.
//!
//! - **A reader returns what is left.** A reader takes the bytes not yet
//!   consumed and returns the value with the bytes after it, so the
//!   standard's "next field" is the next reader applied to the rest.
//!   "Failure" is `None` (a syntax error) or, where the standard names the
//!   rule, an [`ErrKind`] in a [`Res`]. A record reader returns
//!   [`Read::NeedMore`] when the bytes so far are a proper prefix of a
//!   record, which a byte stream needs and the standard leaves to the
//!   transport.
//! - **Enums are numbers.** §3.5 enums are kept as the number read
//!   (`u8` or `u16`); which values are defined is a predicate where the
//!   standard makes it matter (content types, handshake types, the
//!   `KeyUpdateRequest`, alert descriptions). `uint32` is read as a
//!   number.
//! - **Lists end when their bytes do.** `T T'<floor..ceiling>` with a
//!   variable-length `T` is a [`read_vec`] followed by elements until the
//!   bytes are used up ([`read_list`]), as §3.4 says ("the length of an
//!   encoded vector must be an exact multiple of the length of a single
//!   element").
//! - **Ceilings below 2^24.** [`len_width`] covers 1, 2 and 3 byte length
//!   fields, which is every vector in RFC 8446 Appendix B (the largest
//!   ceiling is 2^24-1).
//! - **The AEAD is a parameter.** §5.2's `AEAD-Encrypt` and `AEAD-Decrypt`
//!   are spec functions given to [`encrypt_record`] and
//!   [`decrypt_record`], with the key inside them. The exec functions take
//!   a trait with the same shape. Nothing about the cipher is assumed
//!   except where a lemma says so in its premise.
//! - **Limits.** Handshake messages: a body above [`MAX_HANDSHAKE_BODY`]
//!   (2^18 = 262144 octets) is refused when its four-byte header is read,
//!   although `uint24 length` allows 2^24-1; the reassembly buffer never
//!   holds [`REASSEMBLY_BOUND`] (2^14 + 4 + 2^18 = 278532) bytes or more.
//!   Records: 2^14 content bytes, 2^14 + 1 full inner-plaintext bytes
//!   including type/padding (§5.4), and 2^14 + 256 ciphertext bytes (§5.2).
//!   Extensions: 2^16-1
//!   octets of `extension_data` and of the whole block, as declared.
//! - **`legacy_record_version`.** §5.1 also says the field "MUST be
//!   ignored for all purposes"; the reader here refuses a value that is
//!   not one a TLS 1.3 implementation generates (0x0303, or 0x0301 in an
//!   unprotected record, §5.1; always 0x0303 once protected, §5.2) with
//!   `decode_error`, so that a stream that is not TLS framing at all is
//!   refused at its first record. The cost is a server that sends another
//!   value, which §5.1 forbids it to.
//! - **Unknown record and handshake types are errors**, as §5 and
//!   Appendix B.3 leave no other reading: `unexpected_message`.
//! - **Unrecognized extensions pass the §4.2 table.** The table binds
//!   "an extension which it recognizes"; [`extension_allowed`] is true for
//!   a type that is not a row. The handshake refuses one that was not
//!   offered (`unsupported_extension`, §4.2), which needs the offer, so it
//!   is item 3.5e's.
//! - **Checks in a fixed order.** [`check_extensions`] reports the first
//!   rule broken in the order duplicates, not allowed, malformed body,
//!   missing `supported_versions`; the standard does not order them.
//! - **No client certificates.** CertificateRequest is read and then
//!   refused by the handshake: the client sends a [`Certificate`] with
//!   no entries (§4.4.2) and no CertificateVerify.
//! - **`legacy_version` is read, not checked**, in ClientHello and
//!   ServerHello: §4.2.1 says a client "MUST ignore the
//!   ServerHello.legacy_version value" when `supported_versions` is there.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// RFC 8446 §3, "Presentation Language"
// RFC 8446 §3, "Presentation Language": the one core codec that every
// message in the sections below is
// defined in terms of.
//
// A reader takes the bytes not yet consumed (`b`) and returns what it
// read together with the bytes that remain, or `None` when the bytes do
// not hold the value ("the length of the message was incorrect",
// RFC 8446 §6, which gives `decode_error`). A writer is the inverse.
//
// - §3.3 "Numeric": an unsigned integer of 1, 2, 3 or 4 bytes, "stored in
//   network byte order" (most significant byte first): [`read_uint`].
// - §3.4 "Vectors": a fixed-length vector `T T'[n]` occupies `n` bytes
//   and has no length field ([`read_fixed`]); a variable-length vector
//   `T T'<floor..ceiling>` is "the actual length" followed by the
//   contents, "in the form of a number consuming as many bytes as
//   required to hold the vector's specified maximum (ceiling) length"
//   ([`len_width`], [`read_vec`], [`write_vec`]); "the length of an
//   encoded vector must be an exact multiple of the length of a single
//   element" ([`read_list`] reads elements until the contents are used
//   up exactly, so a partial element fails).
// - §3.5 "Enumerateds": an enum is a number whose width is that of the
//   largest value its declaration lists, `(255)` for one byte and
//   `(65535)` for two. Every enum here is kept as the number read
//   ([`read_uint`] of 1 or 2 bytes); which values are defined is a
//   separate predicate where the standard makes it matter.
// - §3.6 "Constructed types": a struct is its fields in order, with no
//   padding or separator; each struct is a chain of readers in the
//   message's own spec function.
// ===========================================================================



/// 256 to the power `n`: the number of values `n` bytes can hold.
pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * pow256((n - 1) as nat)
    }
}

/// §3.3: the number `s` spells in network byte order, most significant
/// byte first.
pub open spec fn be_value(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        be_value(s.drop_last()) * 256 + s.last() as nat
    }
}

/// The `width` bytes spelling `value` in network byte order, most
/// significant byte first (the inverse of [`be_value`] for
/// `value < 256^width`).
pub open spec fn be_bytes(value: nat, width: nat) -> Seq<u8>
    decreases width,
{
    if width == 0 {
        seq![]
    } else {
        be_bytes(value / 256, (width - 1) as nat).push((value % 256) as u8)
    }
}

/// §3.4: the number of bytes of the length field of a vector whose
/// ceiling is `ceil`: "as many bytes as required to hold the vector's
/// specified maximum (ceiling) length". One byte holds 0 to 255 (§3.3
/// `uint8`), two bytes 0 to 65535, three bytes 0 to 2^24-1. (No vector in
/// this crate has a ceiling of 2^24 or more.)
pub open spec fn len_width(ceil: nat) -> nat {
    if ceil <= 255 {
        1
    } else if ceil <= 65535 {
        2
    } else {
        3
    }
}

/// §3.3: read a `w`-byte unsigned integer. Returns its value and the
/// bytes after it.
pub open spec fn read_uint(b: Seq<u8>, w: nat) -> Option<(nat, Seq<u8>)> {
    if b.len() < w {
        None
    } else {
        Some((be_value(b.take(w as int)), b.skip(w as int)))
    }
}

/// §3.4, `opaque T[n]`: read exactly `n` bytes.
pub open spec fn read_fixed(b: Seq<u8>, n: nat) -> Option<(Seq<u8>, Seq<u8>)> {
    if b.len() < n {
        None
    } else {
        Some((b.take(n as int), b.skip(n as int)))
    }
}

/// §3.4, `opaque T[floor..ceiling]` as `T<floor..ceiling>`: read the
/// length field, check it is within the declared bounds ("the length ...
/// out of range" is a `decode_error`, §6) and read that many bytes.
/// Returns the contents and the bytes after them.
pub open spec fn read_vec(b: Seq<u8>, floor: nat, ceil: nat) -> Option<(Seq<u8>, Seq<u8>)> {
    match read_uint(b, len_width(ceil)) {
        None => None,
        Some((n, r)) => {
            if n < floor || n > ceil || r.len() < n {
                None
            } else {
                Some((r.take(n as int), r.skip(n as int)))
            }
        },
    }
}

/// §3.4: the contents of a vector with ceiling `ceil` are within its
/// bounds.
pub open spec fn vec_in_bounds(content: Seq<u8>, floor: nat, ceil: nat) -> bool {
    floor <= content.len() <= ceil
}

/// §3.4: the encoding of a variable-length vector: its length in
/// `len_width(ceil)` bytes, then its contents.
pub open spec fn write_vec(content: Seq<u8>, ceil: nat) -> Seq<u8> {
    be_bytes(content.len(), len_width(ceil)) + content
}

/// §3.4, `T T'<floor..ceiling>` where `T` is not a single byte: read the
/// vector's bytes with [`read_vec`], then read elements with `f` until
/// the contents are used up exactly ("the length of an encoded vector must
/// be an exact multiple of the length of a single element"). Each element
/// must consume at least one byte, which makes the loop terminate (every
/// element in this crate is at least two bytes).
pub open spec fn read_list<E>(b: Seq<u8>, f: spec_fn(Seq<u8>) -> Option<(E, Seq<u8>)>) -> Option<Seq<E>>
    decreases b.len(),
{
    if b.len() == 0 {
        Some(seq![])
    } else {
        match f(b) {
            None => None,
            Some((e, rest)) => {
                if rest.len() >= b.len() {
                    None
                } else {
                    match read_list(rest, f) {
                        None => None,
                        Some(es) => Some(seq![e] + es),
                    }
                }
            },
        }
    }
}

/// The bytes of a list of elements: each element's encoding `w(e)`, in
/// order.
pub open spec fn write_list<E>(es: Seq<E>, w: spec_fn(E) -> Seq<u8>) -> Seq<u8>
    decreases es.len(),
{
    if es.len() == 0 {
        seq![]
    } else {
        w(es[0]) + write_list(es.skip(1), w)
    }
}

/// `uint16` as an element of a list (a `ProtocolVersion`, `CipherSuite`,
/// `NamedGroup` or `SignatureScheme`).
pub open spec fn read_u16(b: Seq<u8>) -> Option<(u16, Seq<u8>)> {
    match read_uint(b, 2) {
        None => None,
        Some((v, r)) => Some((v as u16, r)),
    }
}

/// The two bytes of a `uint16`.
pub open spec fn write_u16(v: u16) -> Seq<u8> {
    be_bytes(v as nat, 2)
}

/// A list of `uint16` read from the contents of a vector.
pub open spec fn read_u16s(b: Seq<u8>) -> Option<Seq<u16>> {
    read_list(b, |x: Seq<u8>| read_u16(x))
}

/// The bytes of a list of `uint16`.
pub open spec fn write_u16s(vs: Seq<u16>) -> Seq<u8> {
    write_list(vs, |v: u16| write_u16(v))
}

/// §3.3: the three bytes of a `uint24`.
pub open spec fn write_u24(v: nat) -> Seq<u8> {
    be_bytes(v, 3)
}


// ===========================================================================
// RFC 8446 §6, "Alert Protocol"
// RFC 8446 §6, "Alert Protocol", and the mapping from each parse error in
// this crate to the alert §6.2 names for it.
//
// §6 gives the two generic rules that decide most cases: "Peers which
// receive a message which cannot be parsed according to the syntax (e.g.,
// have a length extending beyond the message boundary or contain an
// out-of-range length) MUST terminate the connection with a
// "decode_error" alert. Peers which receive a message which is
// syntactically correct but semantically invalid (e.g., a DHE share of
// p - 1, or an invalid enum) MUST terminate the connection with an
// "illegal_parameter" alert." The rest are the specific rules quoted at
// each [`ErrKind`].
// ===========================================================================



/// §6, `AlertLevel`: `warning(1)`.
pub const LEVEL_WARNING: u8 = 1;

/// §6, `AlertLevel`: `fatal(2)`.
pub const LEVEL_FATAL: u8 = 2;

/// §6, `close_notify(0)`.
pub const CLOSE_NOTIFY: u8 = 0;

/// §6, `unexpected_message(10)`.
pub const UNEXPECTED_MESSAGE: u8 = 10;

/// §6, `bad_record_mac(20)`.
pub const BAD_RECORD_MAC: u8 = 20;

/// §6, `record_overflow(22)`.
pub const RECORD_OVERFLOW: u8 = 22;

/// §6, `handshake_failure(40)`.
pub const HANDSHAKE_FAILURE: u8 = 40;

/// §6, `bad_certificate(42)`.
pub const BAD_CERTIFICATE: u8 = 42;

/// §6, `unsupported_certificate(43)`.
pub const UNSUPPORTED_CERTIFICATE: u8 = 43;

/// §6, `certificate_revoked(44)`.
pub const CERTIFICATE_REVOKED: u8 = 44;

/// §6, `certificate_expired(45)`.
pub const CERTIFICATE_EXPIRED: u8 = 45;

/// §6, `certificate_unknown(46)`.
pub const CERTIFICATE_UNKNOWN: u8 = 46;

/// §6, `illegal_parameter(47)`.
pub const ILLEGAL_PARAMETER: u8 = 47;

/// §6, `unknown_ca(48)`.
pub const UNKNOWN_CA: u8 = 48;

/// §6, `access_denied(49)`.
pub const ACCESS_DENIED: u8 = 49;

/// §6, `decode_error(50)`.
pub const DECODE_ERROR: u8 = 50;

/// §6, `decrypt_error(51)`.
pub const DECRYPT_ERROR: u8 = 51;

/// §6, `protocol_version(70)`.
pub const PROTOCOL_VERSION: u8 = 70;

/// §6, `insufficient_security(71)`.
pub const INSUFFICIENT_SECURITY: u8 = 71;

/// §6, `internal_error(80)`.
pub const INTERNAL_ERROR: u8 = 80;

/// §6, `inappropriate_fallback(86)`.
pub const INAPPROPRIATE_FALLBACK: u8 = 86;

/// §6, `user_canceled(90)`.
pub const USER_CANCELED: u8 = 90;

/// §6, `missing_extension(109)`.
pub const MISSING_EXTENSION: u8 = 109;

/// §6, `unsupported_extension(110)`.
pub const UNSUPPORTED_EXTENSION: u8 = 110;

/// §6, `unrecognized_name(112)`.
pub const UNRECOGNIZED_NAME: u8 = 112;

/// §6, `bad_certificate_status_response(113)`.
pub const BAD_CERTIFICATE_STATUS_RESPONSE: u8 = 113;

/// §6, `unknown_psk_identity(115)`.
pub const UNKNOWN_PSK_IDENTITY: u8 = 115;

/// §6, `certificate_required(116)`.
pub const CERTIFICATE_REQUIRED: u8 = 116;

/// §6, `no_application_protocol(120)`.
pub const NO_APPLICATION_PROTOCOL: u8 = 120;

/// §6, `struct { AlertLevel level; AlertDescription description; } Alert`.
/// Both enums are one byte, and any value may arrive (`(255)`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Alert {
    /// `AlertLevel`: `warning(1)`, `fatal(2)`, or any other byte.
    pub level: u8,
    /// `AlertDescription`.
    pub description: u8,
}

/// §6 `Alert`: exactly two bytes. "A record with an Alert type MUST
/// contain exactly one message" (§5.1), so any other length is not an
/// alert.
pub open spec fn read_alert(b: Seq<u8>) -> Option<Alert> {
    if b.len() == 2 {
        Some(Alert { level: b[0], description: b[1] })
    } else {
        None
    }
}

/// The two bytes of an alert.
pub open spec fn write_alert(a: Alert) -> Seq<u8> {
    seq![a.level, a.description]
}

/// §6.2: whether the code is one of the `AlertDescription` values the
/// standard defines (the list in §6, which leaves out the `_RESERVED`
/// values of Appendix B.2).
pub open spec fn alert_description_defined(d: u8) -> bool {
    d == 0 || d == 10 || d == 20 || d == 22 || d == 40 || d == 42 || d == 43 || d == 44 || d == 45
        || d == 46 || d == 47 || d == 48 || d == 49 || d == 50 || d == 51 || d == 70 || d == 71
        || d == 80 || d == 86 || d == 90 || d == 109 || d == 110 || d == 112 || d == 113
        || d == 115 || d == 116 || d == 120
}

/// §6 and §6.1: whether a received alert closes a direction without being
/// an error. In TLS 1.3 the level is ignored; closure semantics follow the
/// alert description. Unknown alerts and the §6.2 error alerts are fatal.
pub open spec fn alert_is_closure(a: Alert) -> bool {
    a.description == CLOSE_NOTIFY || a.description == USER_CANCELED
}

/// What went wrong, as a parse or record-layer error. Each kind names the
/// rule that was broken and maps to exactly one alert ([`alert_of`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrKind {
    /// §6 "cannot be parsed according to the syntax": a length that runs
    /// past the message, a vector length outside its `<floor..ceiling>`,
    /// a fixed-size field of the wrong size, bytes left over. Alert
    /// `decode_error` (§6.2: "some field was out of the specified range or
    /// the length of the message was incorrect").
    Decode,
    /// §5.1: "The length MUST NOT exceed 2^14 bytes. An endpoint that
    /// receives a record that exceeds this length MUST terminate the
    /// connection with a "record_overflow" alert"; §5.2: the same for
    /// 2^14 + 256 on a TLSCiphertext; §5.2: a record that decrypts to
    /// more than 2^14 bytes of content. Alert `record_overflow`.
    RecordOverflow,
    /// §5: "If a TLS implementation receives an unexpected record type, it
    /// MUST terminate the connection with an "unexpected_message" alert":
    /// a content type other than change_cipher_spec, alert, handshake or
    /// application_data, or one that is not allowed here.
    UnexpectedContentType,
    /// §4 `HandshakeType`: a type that Appendix B.3's `select` does not
    /// list (including the `_RESERVED` values and `message_hash`).
    /// Alert `unexpected_message` (§6.2: "the wrong handshake message").
    UnexpectedHandshakeType,
    /// §5.1: "Implementations MUST NOT send zero-length fragments of
    /// Handshake types"; §5.4: "if such a message is received, the
    /// receiving implementation MUST terminate the connection with an
    /// "unexpected_message" alert". Also an Alert record with no alert.
    ZeroLengthFragment,
    /// §5.1: "Handshake messages MUST NOT be interleaved with other record
    /// types" (and an Alert, being one message, cannot be fragmented).
    /// Alert `unexpected_message`.
    Interleaved,
    /// §5.4: a TLSInnerPlaintext with no non-zero octet has no content
    /// type. Alert `unexpected_message`.
    AllZeroInnerPlaintext,
    /// §5: a change_cipher_spec record that is not the single byte 0x01,
    /// or is protected: "MUST abort the handshake with an
    /// "unexpected_message" alert".
    BadChangeCipherSpec,
    /// A `legacy_record_version` that no TLS 1.3 implementation sends
    /// (see the modelling choices at the top of this file). Alert `decode_error`.
    BadLegacyRecordVersion,
    /// A handshake message longer than this crate's stated limit (see
    /// [`MAX_HANDSHAKE_BODY`]). RFC 8446 names no alert for
    /// this; `illegal_parameter` is what OpenSSL and BoringSSL send for
    /// an excessive message size.
    HandshakeTooLarge,
    /// §4.2: "There MUST NOT be more than one extension of the same type
    /// in a given extension block." Alert `illegal_parameter` (the rule is
    /// not given an alert; §6's generic rule for a syntactically correct
    /// but invalid message applies, as the §4.2 table's rule does).
    DuplicateExtension,
    /// §4.2: "If an implementation receives an extension which it
    /// recognizes and which is not specified for the message in which it
    /// appears, it MUST abort the handshake with an "illegal_parameter"
    /// alert."
    ExtensionNotAllowed,
    /// §6: "syntactically correct but semantically invalid (e.g., ... an
    /// invalid enum)": an undefined `KeyUpdateRequest` (§4.6.3), a
    /// `legacy_compression_method` that is not 0 (§4.1.3), or compression
    /// methods other than the single null method in a ClientHello (§4.1.2:
    /// "MUST abort the handshake with an "illegal_parameter" alert").
    /// Alert `illegal_parameter`.
    InvalidEnum,
    /// §4.4.2: in the case of server authentication the
    /// `certificate_request_context` "SHALL be zero length". Alert
    /// `illegal_parameter` (§6 generic rule).
    NonEmptyContext,
    /// §4.1.3: "All TLS 1.3 ServerHello messages MUST contain the
    /// "supported_versions" extension" (and §4.1.4 for a
    /// HelloRetryRequest). Alert `missing_extension` (§6.2: "sent by
    /// endpoints that receive a handshake message not containing an
    /// extension that is mandatory to send for the offered TLS version").
    MissingExtension,
    /// §5.2: "If the decryption fails, the receiver MUST terminate the
    /// connection with a "bad_record_mac" alert."
    BadRecordMac,
}

/// The alert §6.2 names for each kind of error: the description to send.
pub open spec fn alert_of(k: ErrKind) -> u8 {
    match k {
        ErrKind::Decode => DECODE_ERROR,
        ErrKind::RecordOverflow => RECORD_OVERFLOW,
        ErrKind::UnexpectedContentType => UNEXPECTED_MESSAGE,
        ErrKind::UnexpectedHandshakeType => UNEXPECTED_MESSAGE,
        ErrKind::ZeroLengthFragment => UNEXPECTED_MESSAGE,
        ErrKind::Interleaved => UNEXPECTED_MESSAGE,
        ErrKind::AllZeroInnerPlaintext => UNEXPECTED_MESSAGE,
        ErrKind::BadChangeCipherSpec => UNEXPECTED_MESSAGE,
        ErrKind::BadLegacyRecordVersion => DECODE_ERROR,
        ErrKind::HandshakeTooLarge => ILLEGAL_PARAMETER,
        ErrKind::DuplicateExtension => ILLEGAL_PARAMETER,
        ErrKind::ExtensionNotAllowed => ILLEGAL_PARAMETER,
        ErrKind::InvalidEnum => ILLEGAL_PARAMETER,
        ErrKind::NonEmptyContext => ILLEGAL_PARAMETER,
        ErrKind::MissingExtension => MISSING_EXTENSION,
        ErrKind::BadRecordMac => BAD_RECORD_MAC,
    }
}

/// The alert a peer sends on a fatal error: "All the alerts listed in
/// Section 6.2 MUST be sent with AlertLevel=fatal" (§6).
pub open spec fn alert_for(k: ErrKind) -> Alert {
    Alert { level: LEVEL_FATAL, description: alert_of(k) }
}

/// The result of a parser that can fail with a rule of the standard: a
/// value, or the kind of error.
pub enum Res<T> {
    /// Parsed.
    Ok(T),
    /// Refused, for this reason.
    Err(ErrKind),
}

/// Whether a result is a success.
pub open spec fn is_ok<T>(r: Res<T>) -> bool {
    r is Ok
}


// ===========================================================================
// RFC 8446 §5, "Record Protocol"
// RFC 8446 §5, "Record Protocol": §5.1 `TLSPlaintext`, §5.2
// `TLSCiphertext` and `TLSInnerPlaintext`, §5.3 the per-record nonce, and
// the reassembly of handshake messages from records.
//
// The AEAD itself is not here. §5.2's `AEAD-Encrypt` and `AEAD-Decrypt`
// are parameters of the functions that need them, given as spec
// functions of the nonce, the additional data and the text, so the key
// they close over never appears (phase-3.md item 3.5f instantiates them
// with ChaCha20-Poly1305).
// ===========================================================================



// ---------------------------------------------------------------------------
// §5, §5.1 and §5.2: constants.
// ---------------------------------------------------------------------------

/// §5.1 `ContentType`: `invalid(0)`.
pub const CT_INVALID: u8 = 0;

/// §5.1 `ContentType`: `change_cipher_spec(20)`.
pub const CT_CHANGE_CIPHER_SPEC: u8 = 20;

/// §5.1 `ContentType`: `alert(21)`.
pub const CT_ALERT: u8 = 21;

/// §5.1 `ContentType`: `handshake(22)`.
pub const CT_HANDSHAKE: u8 = 22;

/// §5.1 `ContentType`: `application_data(23)`.
pub const CT_APPLICATION_DATA: u8 = 23;

/// §5.1: "The length MUST NOT exceed 2^14 bytes."
pub const MAX_PLAINTEXT: usize = 16384;

/// §5.2: "The length MUST NOT exceed 2^14 + 256 bytes."
pub const MAX_CIPHERTEXT: usize = 16640;

/// The largest handshake message body this crate reassembles: 2^18 octets
/// (262144). §4 `uint24 length` allows up to 2^24 - 1; a longer message is
/// refused as soon as its four-byte header is read, so the reassembly
/// buffer is bounded ([`REASSEMBLY_BOUND`]). A certificate chain is the
/// largest message in practice and is a few tens of kilobytes.
pub const MAX_HANDSHAKE_BODY: usize = 262144;

/// The size of a handshake message header (§4: one byte `msg_type` and a
/// `uint24 length`).
pub const HANDSHAKE_HEADER: usize = 4;

/// The most bytes the reassembly buffer ever holds, including the record
/// being appended: the unfinished message (fewer than
/// `HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY` bytes) plus one record's
/// fragment (at most 2^14 bytes).
pub const REASSEMBLY_BOUND: usize = 16384 + 4 + 262144;

/// The size of a record header (§5.1: one byte `type`, two bytes
/// `legacy_record_version`, two bytes `length`).
pub const RECORD_HEADER: usize = 5;

// ---------------------------------------------------------------------------
// §5.1: TLSPlaintext.
// ---------------------------------------------------------------------------

/// §5.1: the `legacy_record_version` values a TLS 1.3 implementation
/// generates: "MUST be set to 0x0303 for all records generated by a TLS
/// 1.3 implementation other than an initial ClientHello (i.e., one not
/// generated after a HelloRetryRequest), where it MAY also be 0x0301 for
/// compatibility purposes." The standard also says the field "MUST be
/// ignored for all purposes"; this crate is stricter and refuses any other
/// value (a modelling choice, listed at the top of this file): a record that carries
/// neither is not TLS 1.3 framing. `protected` is true once record
/// protection has started, when §5.2 fixes it: "The legacy_record_version
/// field is always 0x0303."
pub open spec fn legacy_record_version_ok(v: u16, protected: bool) -> bool {
    v == 0x0303 || (!protected && v == 0x0301)
}

/// §5.1 `TLSPlaintext`'s header: `type`, `legacy_record_version`,
/// `length`.
pub open spec fn write_record_header(ctype: u8, version: u16, length: nat) -> Seq<u8> {
    seq![ctype] + write_u16(version) + be_bytes(length, 2)
}

/// §5.1 `TLSPlaintext`: the header and the fragment.
pub open spec fn write_plaintext(ctype: u8, version: u16, fragment: Seq<u8>) -> Seq<u8> {
    write_record_header(ctype, version, fragment.len()) + fragment
}

/// The outcome of reading one record from a byte stream.
pub enum Read<T> {
    /// More bytes are needed; nothing has been decided.
    NeedMore,
    /// The record is refused, for this reason.
    Fail(ErrKind),
    /// A record, and the bytes after it.
    Done(T, Seq<u8>),
}

/// A record as the layer above sees it (§5.1 `TLSPlaintext`, or the
/// result of removing §5.2's protection): its content type and fragment.
pub struct Record {
    /// `ContentType`.
    pub ctype: u8,
    /// The fragment (`TLSPlaintext.fragment`, or `TLSInnerPlaintext.content`).
    pub fragment: Seq<u8>,
}

/// What [`read_record`] found on the wire.
pub enum Frame {
    /// An unprotected `handshake` or `alert` record.
    Plain(Record),
    /// §5: "an unencrypted record of type change_cipher_spec consisting of
    /// the single byte value 0x01", which the receiver "MUST simply drop".
    Ccs,
    /// A `TLSCiphertext`: its header (which is the AEAD's additional data,
    /// §5.2: "additional_data = TLSCiphertext.opaque_type ||
    /// TLSCiphertext.legacy_record_version || TLSCiphertext.length") and
    /// its `encrypted_record`.
    Protected(Seq<u8>, Seq<u8>),
}

/// §5.1 and §5.2: read one record from the front of `b`. `protected` is
/// true once record protection has started (after the ServerHello has been
/// processed). All the decisions that need only the five header bytes are
/// made as soon as they are there, before the body arrives.
///
/// 1. "If a TLS implementation receives an unexpected record type, it MUST
///    terminate the connection with an "unexpected_message" alert" (§5):
///    unprotected, only `change_cipher_spec`, `alert` and `handshake`
///    records may arrive ("Application Data messages are always
///    protected", §5.1); protected, only `application_data` (the outer
///    type of every `TLSCiphertext`, §5.2) and the unprotected
///    `change_cipher_spec` of the middlebox compatibility mode (§5,
///    Appendix D.4).
/// 2. `legacy_record_version` ([`legacy_record_version_ok`]).
/// 3. "The length MUST NOT exceed 2^14 bytes" (2^14 + 256 for a
///    `TLSCiphertext`); otherwise `record_overflow`.
/// 4. "Implementations MUST NOT send zero-length fragments of Handshake
///    types" (§5.1), and an Alert record "MUST contain exactly one
///    message": an empty `handshake` or `alert` fragment is an error.
/// 5. Once the body is there, a `change_cipher_spec` must be the single
///    byte 0x01 (§5).
pub open spec fn read_record(b: Seq<u8>, protected: bool) -> Read<Frame> {
    if b.len() < RECORD_HEADER {
        Read::NeedMore
    } else {
        let t = b[0];
        let v = be_value(b.subrange(1, 3)) as u16;
        let len = be_value(b.subrange(3, 5));
        let ok_type = if protected {
            t == CT_APPLICATION_DATA || t == CT_CHANGE_CIPHER_SPEC
        } else {
            t == CT_CHANGE_CIPHER_SPEC || t == CT_ALERT || t == CT_HANDSHAKE
        };
        if !ok_type {
            // 1.
            Read::Fail(ErrKind::UnexpectedContentType)
        } else if !legacy_record_version_ok(v, protected) {
            // 2.
            Read::Fail(ErrKind::BadLegacyRecordVersion)
        } else if len > (if protected && t == CT_APPLICATION_DATA {
            MAX_CIPHERTEXT
        } else {
            MAX_PLAINTEXT
        }) {
            // 3.
            Read::Fail(ErrKind::RecordOverflow)
        } else if len == 0 && (t == CT_HANDSHAKE || t == CT_ALERT) {
            // 4.
            Read::Fail(ErrKind::ZeroLengthFragment)
        } else if b.len() < RECORD_HEADER + len {
            Read::NeedMore
        } else {
            let body = b.subrange(5, (5 + len) as int);
            let rest = b.skip((5 + len) as int);
            if t == CT_CHANGE_CIPHER_SPEC {
                // 5.
                if body == seq![1u8] {
                    Read::Done(Frame::Ccs, rest)
                } else {
                    Read::Fail(ErrKind::BadChangeCipherSpec)
                }
            } else if t == CT_APPLICATION_DATA {
                // Protected (an unprotected one was refused in step 1).
                Read::Done(Frame::Protected(b.take(5), body), rest)
            } else {
                Read::Done(Frame::Plain(Record { ctype: t, fragment: body }), rest)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §5.2: TLSInnerPlaintext and the protection of a record.
// ---------------------------------------------------------------------------

/// §5.2 `TLSInnerPlaintext`: the content, the real content type, and
/// `padding` zero octets (§5.4: "Padding is a string of zero-valued bytes
/// appended to the ContentType field before encryption").
pub open spec fn write_inner_plaintext(content: Seq<u8>, ctype: u8, padding: nat) -> Seq<u8> {
    content + seq![ctype] + Seq::new(padding, |i: int| 0u8)
}

/// §5.4: "the receiving implementation scans the field from the end
/// toward the beginning until it finds a non-zero octet. This non-zero
/// octet is the content type of the message." Returns the content (what
/// precedes that octet) and the type, or `None` when every octet is zero.
pub open spec fn split_inner_plaintext(p: Seq<u8>) -> Option<(Seq<u8>, u8)>
    decreases p.len(),
{
    if p.len() == 0 {
        None
    } else if p.last() != 0 {
        Some((p.drop_last(), p.last()))
    } else {
        split_inner_plaintext(p.drop_last())
    }
}

/// §5.2 and §5.4 applied to the decrypted `TLSInnerPlaintext` `p`:
///
/// 0. §5.4: reject a full encoded inner plaintext above 2^14 + 1,
///    including content type and padding, with `record_overflow`.
/// 1. Find the content type from the end; "all-zero" has none, which is
///    `unexpected_message`.
/// 2. A `change_cipher_spec` record must not be protected (§5: "which
///    receives a protected change_cipher_spec record MUST abort the
///    handshake with an "unexpected_message" alert"); any other value than
///    `alert`, `handshake` and `application_data` is an unexpected record
///    type.
/// 3. "A record decrypted to a TLSPlaintext record with more than 2^14
///    bytes" is `record_overflow` (§6.2).
/// 4. "Implementations MUST NOT send Handshake and Alert records that have
///    a zero-length TLSInnerPlaintext.content; if such a message is
///    received, the receiving implementation MUST terminate the
///    connection with an "unexpected_message" alert." (§5.4)
pub open spec fn open_inner_plaintext(p: Seq<u8>) -> Res<Record> {
    if p.len() > MAX_PLAINTEXT + 1 { Res::Err(ErrKind::RecordOverflow) }
    else { match split_inner_plaintext(p) {
        None => Res::Err(ErrKind::AllZeroInnerPlaintext),
        Some((content, t)) => {
            if t == CT_CHANGE_CIPHER_SPEC {
                Res::Err(ErrKind::BadChangeCipherSpec)
            } else if !(t == CT_ALERT || t == CT_HANDSHAKE || t == CT_APPLICATION_DATA) {
                Res::Err(ErrKind::UnexpectedContentType)
            } else if content.len() > MAX_PLAINTEXT {
                Res::Err(ErrKind::RecordOverflow)
            } else if content.len() == 0 && (t == CT_HANDSHAKE || t == CT_ALERT) {
                Res::Err(ErrKind::ZeroLengthFragment)
            } else {
                Res::Ok(Record { ctype: t, fragment: content })
            }
        },
    }
    }
}

/// §5.2: the additional data of a `TLSCiphertext` whose
/// `encrypted_record` is `length` bytes: "TLSCiphertext.opaque_type ||
/// TLSCiphertext.legacy_record_version || TLSCiphertext.length", where the
/// type is 23 and the version is 0x0303.
pub open spec fn additional_data(length: nat) -> Seq<u8> {
    write_record_header(CT_APPLICATION_DATA, 0x0303, length)
}

/// §5.3 "Per-Record Nonce": "1. The 64-bit record sequence number is
/// encoded in network byte order and padded to the left with zeros to
/// iv_length. 2. The padded sequence number is XORed with either the
/// static client_write_iv or server_write_iv." `iv` is that IV, so its
/// length is `iv_length`, which §5.3 sets "to the larger of 8 bytes and
/// N_MIN" (12 for the cipher suite of this crate).
pub open spec fn per_record_nonce(iv: Seq<u8>, seqno: u64) -> Seq<u8> {
    let padded = be_bytes(seqno as nat, iv.len());
    Seq::new(iv.len(), |i: int| (iv[i] ^ padded[i]) as u8)
}

/// §5.2: `AEAD-Encrypt(write_key, nonce, additional_data, plaintext)` and
/// `AEAD-Decrypt(...)`, as parameters. `seal(nonce, ad, plaintext)` is the
/// `AEADEncrypted` value, which is `tag_len` bytes longer than the
/// plaintext ("An AEAD algorithm used in TLS 1.3 MUST NOT produce an
/// expansion greater than 255 octets"). `open(nonce, ad, ciphertext)` is
/// the plaintext, or `None` when the decryption fails.
///
/// §5.2 protection of one record: the `TLSInnerPlaintext` is the content,
/// the type and `padding` zeros; its `TLSCiphertext` has the additional
/// data above, whose `length` is the length of the AEAD output; the
/// record is that header and the output.
pub open spec fn encrypt_record(
    seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    tag_len: nat,
    iv: Seq<u8>,
    seqno: u64,
    ctype: u8,
    content: Seq<u8>,
    padding: nat,
) -> Seq<u8> {
    let inner = write_inner_plaintext(content, ctype, padding);
    let ad = additional_data(inner.len() + tag_len);
    ad + seal(per_record_nonce(iv, seqno), ad, inner)
}

/// §5.2 deprotection of a `TLSCiphertext` read by [`read_record`]
/// (`header` is the additional data): "If the decryption fails, the
/// receiver MUST terminate the connection with a "bad_record_mac" alert",
/// then §5.4 on the plaintext ([`open_inner_plaintext`]).
pub open spec fn decrypt_record(
    open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    iv: Seq<u8>,
    seqno: u64,
    header: Seq<u8>,
    encrypted_record: Seq<u8>,
) -> Res<Record> {
    match open(per_record_nonce(iv, seqno), header, encrypted_record) {
        None => Res::Err(ErrKind::BadRecordMac),
        Some(p) => open_inner_plaintext(p),
    }
}

// ---------------------------------------------------------------------------
// §5.1: handshake messages across records.
// ---------------------------------------------------------------------------

/// The reassembly state: the bytes of a handshake message that has begun
/// and not yet ended (empty at a message boundary). "Handshake messages
/// MAY be coalesced into a single TLSPlaintext record or fragmented
/// across several records" (§5.1).
pub struct Reasm {
    /// The unfinished message's bytes so far: fewer than
    /// `HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY`.
    pub buf: Seq<u8>,
}

/// What a record gave to the layer above.
pub enum Event {
    /// Zero or more complete handshake messages, each as its whole
    /// encoding (the four-byte header and the body), in order. (The
    /// transcript hash of §4.4.1 is over exactly these bytes.)
    Messages(Seq<Seq<u8>>),
    /// An alert (§6; one per record, §5.1).
    Alert(Alert),
    /// Application data (§5.1), possibly empty.
    AppData(Seq<u8>),
    /// A dropped change_cipher_spec record (§5).
    Ignored,
}

/// §4: split `buf` into the complete handshake messages at its front and
/// the bytes of an unfinished one: while there are four bytes, the
/// message is `1 + 3 + uint24 length` bytes; stop when its bytes have not
/// all arrived. A length above [`MAX_HANDSHAKE_BODY`] is refused as soon
/// as it is read.
pub open spec fn extract_messages(buf: Seq<u8>) -> Res<(Seq<Seq<u8>>, Seq<u8>)>
    decreases buf.len(),
{
    if buf.len() < HANDSHAKE_HEADER {
        Res::Ok((seq![], buf))
    } else {
        let len = be_value(buf.subrange(1, 4));
        if len > MAX_HANDSHAKE_BODY {
            Res::Err(ErrKind::HandshakeTooLarge)
        } else if buf.len() < HANDSHAKE_HEADER + len {
            Res::Ok((seq![], buf))
        } else {
            match extract_messages(buf.skip((HANDSHAKE_HEADER + len) as int)) {
                Res::Err(e) => Res::Err(e),
                Res::Ok((ms, rest)) => Res::Ok((seq![buf.take((HANDSHAKE_HEADER + len) as int)] + ms, rest)),
            }
        }
    }
}

/// §5.1: feed one record (as [`read_record`] and [`decrypt_record`] give
/// it) to the reassembler.
///
/// - `handshake`: "Implementations MUST NOT send zero-length fragments of
///   Handshake types, even if those fragments contain padding", so an
///   empty one is an error; otherwise the fragment is appended and every
///   complete message is taken off the front ([`extract_messages`]).
/// - `alert`: "Alert messages MUST NOT be fragmented across records, and
///   multiple alert messages MUST NOT be coalesced into a single
///   TLSPlaintext record. In other words, a record with an Alert type MUST
///   contain exactly one message": exactly two bytes ([`read_alert`]),
///   and not in the middle of a handshake message ("Handshake messages
///   MUST NOT be interleaved with other record types").
/// - `application_data`: not in the middle of a handshake message either;
///   its content is passed on.
/// - Any other type, `change_cipher_spec` included, is not a record the
///   layer above receives: a protected change_cipher_spec is an error
///   (§5), and an unprotected one is [`Frame::Ccs`], handled by
///   [`feed_ccs`].
pub open spec fn feed_record(st: Reasm, rec: Record) -> Res<(Event, Reasm)> {
    if rec.ctype == CT_HANDSHAKE {
        if rec.fragment.len() == 0 {
            Res::Err(ErrKind::ZeroLengthFragment)
        } else {
            match extract_messages(st.buf + rec.fragment) {
                Res::Err(e) => Res::Err(e),
                Res::Ok((ms, rest)) => Res::Ok((Event::Messages(ms), Reasm { buf: rest })),
            }
        }
    } else if rec.ctype == CT_ALERT {
        if st.buf.len() > 0 {
            Res::Err(ErrKind::Interleaved)
        } else if rec.fragment.len() == 0 {
            Res::Err(ErrKind::ZeroLengthFragment)
        } else {
            match read_alert(rec.fragment) {
                None => Res::Err(ErrKind::Decode),
                Some(a) => Res::Ok((Event::Alert(a), st)),
            }
        }
    } else if rec.ctype == CT_APPLICATION_DATA {
        if st.buf.len() > 0 {
            Res::Err(ErrKind::Interleaved)
        } else {
            Res::Ok((Event::AppData(rec.fragment), st))
        }
    } else if rec.ctype == CT_CHANGE_CIPHER_SPEC {
        Res::Err(ErrKind::BadChangeCipherSpec)
    } else {
        Res::Err(ErrKind::UnexpectedContentType)
    }
}

/// §5: an unprotected change_cipher_spec record is dropped ("MUST simply
/// drop it without further processing"), except in the middle of a
/// handshake message, where it would interleave ("Handshake messages MUST
/// NOT be interleaved with other record types").
pub open spec fn feed_ccs(st: Reasm) -> Res<(Event, Reasm)> {
    if st.buf.len() > 0 {
        Res::Err(ErrKind::Interleaved)
    } else {
        Res::Ok((Event::Ignored, st))
    }
}

/// §5.1: "Handshake messages MUST NOT span key changes. Implementations
/// MUST verify that all messages immediately preceding a key change align
/// with a record boundary; if not, then they MUST terminate the connection
/// with an "unexpected_message" alert." The check: no message has begun.
pub open spec fn at_message_boundary(st: Reasm) -> bool {
    st.buf.len() == 0
}

/// The state before any record.
pub open spec fn reasm_new() -> Reasm {
    Reasm { buf: seq![] }
}


// ===========================================================================
// RFC 8446 §4.2, "Extensions"
// RFC 8446 §4.2, "Extensions", and the extensions this crate reads or
// writes: §4.2.1 `supported_versions`, §4.2.2 `cookie`, §4.2.3
// `signature_algorithms` and `signature_algorithms_cert`, §4.2.7
// `supported_groups`, §4.2.8 `key_share`, and RFC 6066 §3 `server_name`
// (<https://www.rfc-editor.org/rfc/rfc6066#section-3>). Every other
// extension is `opaque`: its type is kept, and its `extension_data` is
// not read.
// ===========================================================================



// ---------------------------------------------------------------------------
// §4.2: ExtensionType.
// ---------------------------------------------------------------------------

/// §4.2 `ExtensionType`: `server_name(0)`, RFC 6066.
pub const EXT_SERVER_NAME: u16 = 0;

/// `max_fragment_length(1)`, RFC 6066.
pub const EXT_MAX_FRAGMENT_LENGTH: u16 = 1;

/// `status_request(5)`, RFC 6066.
pub const EXT_STATUS_REQUEST: u16 = 5;

/// `supported_groups(10)`.
pub const EXT_SUPPORTED_GROUPS: u16 = 10;

/// `signature_algorithms(13)`.
pub const EXT_SIGNATURE_ALGORITHMS: u16 = 13;

/// `use_srtp(14)`, RFC 5764.
pub const EXT_USE_SRTP: u16 = 14;

/// `heartbeat(15)`, RFC 6520.
pub const EXT_HEARTBEAT: u16 = 15;

/// `application_layer_protocol_negotiation(16)`, RFC 7301.
pub const EXT_ALPN: u16 = 16;

/// `signed_certificate_timestamp(18)`, RFC 6962.
pub const EXT_SCT: u16 = 18;

/// `client_certificate_type(19)`, RFC 7250.
pub const EXT_CLIENT_CERTIFICATE_TYPE: u16 = 19;

/// `server_certificate_type(20)`, RFC 7250.
pub const EXT_SERVER_CERTIFICATE_TYPE: u16 = 20;

/// `padding(21)`, RFC 7685.
pub const EXT_PADDING: u16 = 21;

/// `pre_shared_key(41)`.
pub const EXT_PRE_SHARED_KEY: u16 = 41;

/// `early_data(42)`.
pub const EXT_EARLY_DATA: u16 = 42;

/// `supported_versions(43)`.
pub const EXT_SUPPORTED_VERSIONS: u16 = 43;

/// `cookie(44)`.
pub const EXT_COOKIE: u16 = 44;

/// `psk_key_exchange_modes(45)`.
pub const EXT_PSK_KEY_EXCHANGE_MODES: u16 = 45;

/// `certificate_authorities(47)`.
pub const EXT_CERTIFICATE_AUTHORITIES: u16 = 47;

/// `oid_filters(48)`.
pub const EXT_OID_FILTERS: u16 = 48;

/// `post_handshake_auth(49)`.
pub const EXT_POST_HANDSHAKE_AUTH: u16 = 49;

/// `signature_algorithms_cert(50)`.
pub const EXT_SIGNATURE_ALGORITHMS_CERT: u16 = 50;

/// `key_share(51)`.
pub const EXT_KEY_SHARE: u16 = 51;

/// §4.2: `struct { ExtensionType extension_type; opaque
/// extension_data<0..2^16-1>; } Extension`. The data is opaque here;
/// [`ext_body_ok`] says which are read further.
pub struct Ext {
    /// `extension_type`.
    pub etype: u16,
    /// `extension_data`.
    pub data: Seq<u8>,
}

/// §4.2: read one `Extension`.
pub open spec fn read_ext(b: Seq<u8>) -> Option<(Ext, Seq<u8>)> {
    match read_uint(b, 2) {
        None => None,
        Some((t, r)) => {
            match read_vec(r, 0, 65535) {
                None => None,
                Some((data, rest)) => Some((Ext { etype: t as u16, data }, rest)),
            }
        },
    }
}

/// §4.2: the bytes of one `Extension`.
pub open spec fn write_ext(e: Ext) -> Seq<u8> {
    write_u16(e.etype) + write_vec(e.data, 65535)
}

/// `Extension extensions<floor..ceil>`: read the vector and its elements.
/// Returns the extensions and the bytes after the vector.
pub open spec fn read_exts(b: Seq<u8>, floor: nat, ceil: nat) -> Option<(Seq<Ext>, Seq<u8>)> {
    match read_vec(b, floor, ceil) {
        None => None,
        Some((c, r)) => {
            match read_list(c, |x: Seq<u8>| read_ext(x)) {
                None => None,
                Some(es) => Some((es, r)),
            }
        },
    }
}

/// The bytes of `Extension extensions<_..ceil>`.
pub open spec fn write_exts(es: Seq<Ext>, ceil: nat) -> Seq<u8> {
    write_vec(write_list(es, |e: Ext| write_ext(e)), ceil)
}

/// §4.2: "There MUST NOT be more than one extension of the same type in a
/// given extension block."
pub open spec fn no_duplicates(es: Seq<Ext>) -> bool {
    forall|i: int, j: int| 0 <= i < j < es.len() ==> (#[trigger] es[i]).etype != (#[trigger] es[j]).etype
}

/// Whether an extension of type `t` is in the list. (Written as a recursion
/// over the list so that it can be evaluated; [`super::lemmas_ext::lemma_has_ext_iff`]
/// proves it is "some extension has type `t`".)
pub open spec fn has_ext(es: Seq<Ext>, t: u16) -> bool
    decreases es.len(),
{
    if es.len() == 0 {
        false
    } else {
        es[0].etype == t || has_ext(es.skip(1), t)
    }
}

/// §4.2: no two extensions of the block have the same type, as a recursion
/// (the first one's type is not among the rest, and the rest are unique);
/// [`super::lemmas_ext::lemma_exts_unique_iff`] proves it is
/// [`no_duplicates`].
pub open spec fn exts_unique(es: Seq<Ext>) -> bool
    decreases es.len(),
{
    if es.len() == 0 {
        true
    } else {
        !has_ext(es.skip(1), es[0].etype) && exts_unique(es.skip(1))
    }
}

// ---------------------------------------------------------------------------
// §4.2: which extension may appear in which message.
// ---------------------------------------------------------------------------

/// The messages of the §4.2 table: "CH (ClientHello), SH (ServerHello),
/// EE (EncryptedExtensions), CT (Certificate), CR (CertificateRequest),
/// NST (NewSessionTicket), and HRR (HelloRetryRequest)".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MsgKind {
    /// ClientHello.
    Ch,
    /// ServerHello.
    Sh,
    /// EncryptedExtensions.
    Ee,
    /// Certificate (the extensions of a `CertificateEntry`).
    Ct,
    /// CertificateRequest.
    Cr,
    /// NewSessionTicket.
    Nst,
    /// HelloRetryRequest.
    Hrr,
}

/// §4.2: the extensions the table lists.
pub open spec fn extension_known(t: u16) -> bool {
    t == 0 || t == 1 || t == 5 || t == 10 || t == 13 || t == 14 || t == 15 || t == 16 || t == 18
        || t == 19 || t == 20 || t == 21 || t == 41 || t == 42 || t == 43 || t == 44 || t == 45
        || t == 47 || t == 48 || t == 49 || t == 50 || t == 51
}

/// §4.2, the table of the messages where a given extension may appear
/// ("TLS 1.3" column), one case per row, in the table's order:
///
/// | Extension                                | TLS 1.3     |
/// |------------------------------------------|-------------|
/// | server_name (RFC 6066)                   | CH, EE      |
/// | max_fragment_length (RFC 6066)           | CH, EE      |
/// | status_request (RFC 6066)                | CH, CR, CT  |
/// | supported_groups (RFC 7919)              | CH, EE      |
/// | signature_algorithms (RFC 8446)          | CH, CR      |
/// | use_srtp (RFC 5764)                      | CH, EE      |
/// | heartbeat (RFC 6520)                     | CH, EE      |
/// | application_layer_protocol_negotiation   | CH, EE      |
/// | signed_certificate_timestamp (RFC 6962)  | CH, CR, CT  |
/// | client_certificate_type (RFC 7250)       | CH, EE      |
/// | server_certificate_type (RFC 7250)       | CH, EE      |
/// | padding (RFC 7685)                       | CH          |
/// | key_share (RFC 8446)                     | CH, SH, HRR |
/// | pre_shared_key (RFC 8446)                | CH, SH      |
/// | psk_key_exchange_modes (RFC 8446)        | CH          |
/// | early_data (RFC 8446)                    | CH, EE, NST |
/// | cookie (RFC 8446)                        | CH, HRR     |
/// | supported_versions (RFC 8446)            | CH, SH, HRR |
/// | certificate_authorities (RFC 8446)       | CH, CR      |
/// | oid_filters (RFC 8446)                   | CR          |
/// | post_handshake_auth (RFC 8446)           | CH          |
/// | signature_algorithms_cert (RFC 8446)     | CH, CR      |
///
/// The table binds extensions the implementation "recognizes": a type that
/// is not a row ([`extension_known`] is false) is not restricted by it, so
/// it is allowed here; whether it was offered, and so whether it may be
/// answered, is the handshake's check (§4.2: "Implementations MUST NOT
/// send extension responses if the remote endpoint did not send the
/// corresponding extension requests ... Upon receiving such an extension,
/// an endpoint MUST abort the handshake with an "unsupported_extension"
/// alert").
pub open spec fn extension_allowed(t: u16, m: MsgKind) -> bool {
    if t == EXT_SERVER_NAME {
        m is Ch || m is Ee
    } else if t == EXT_MAX_FRAGMENT_LENGTH {
        m is Ch || m is Ee
    } else if t == EXT_STATUS_REQUEST {
        m is Ch || m is Cr || m is Ct
    } else if t == EXT_SUPPORTED_GROUPS {
        m is Ch || m is Ee
    } else if t == EXT_SIGNATURE_ALGORITHMS {
        m is Ch || m is Cr
    } else if t == EXT_USE_SRTP {
        m is Ch || m is Ee
    } else if t == EXT_HEARTBEAT {
        m is Ch || m is Ee
    } else if t == EXT_ALPN {
        m is Ch || m is Ee
    } else if t == EXT_SCT {
        m is Ch || m is Cr || m is Ct
    } else if t == EXT_CLIENT_CERTIFICATE_TYPE {
        m is Ch || m is Ee
    } else if t == EXT_SERVER_CERTIFICATE_TYPE {
        m is Ch || m is Ee
    } else if t == EXT_PADDING {
        m is Ch
    } else if t == EXT_KEY_SHARE {
        m is Ch || m is Sh || m is Hrr
    } else if t == EXT_PRE_SHARED_KEY {
        m is Ch || m is Sh
    } else if t == EXT_PSK_KEY_EXCHANGE_MODES {
        m is Ch
    } else if t == EXT_EARLY_DATA {
        m is Ch || m is Ee || m is Nst
    } else if t == EXT_COOKIE {
        m is Ch || m is Hrr
    } else if t == EXT_SUPPORTED_VERSIONS {
        m is Ch || m is Sh || m is Hrr
    } else if t == EXT_CERTIFICATE_AUTHORITIES {
        m is Ch || m is Cr
    } else if t == EXT_OID_FILTERS {
        m is Cr
    } else if t == EXT_POST_HANDSHAKE_AUTH {
        m is Ch
    } else if t == EXT_SIGNATURE_ALGORITHMS_CERT {
        m is Ch || m is Cr
    } else {
        // Not a row of the table.
        true
    }
}

// ---------------------------------------------------------------------------
// The extensions that are read.
// ---------------------------------------------------------------------------

/// §4.2.8 `KeyShareEntry`: `NamedGroup group; opaque key_exchange<1..2^16-1>`.
pub struct KeyShare {
    /// `group`.
    pub group: u16,
    /// `key_exchange`.
    pub key_exchange: Seq<u8>,
}

/// RFC 6066 §3 `ServerName`: `NameType name_type; select (name_type) {
/// case host_name: HostName; }`, with `HostName` an `opaque
/// HostName<1..2^16-1>` and `NameType` `host_name(0)`. Only `host_name`
/// is defined, so no other `name_type` has a body that can be read.
pub struct ServerName {
    /// The `HostName` bytes.
    pub host_name: Seq<u8>,
}

/// §4.2.8: read one `KeyShareEntry`.
pub open spec fn read_key_share(b: Seq<u8>) -> Option<(KeyShare, Seq<u8>)> {
    match read_uint(b, 2) {
        None => None,
        Some((g, r)) => {
            match read_vec(r, 1, 65535) {
                None => None,
                Some((kx, rest)) => Some((KeyShare { group: g as u16, key_exchange: kx }, rest)),
            }
        },
    }
}

/// §4.2.8: the bytes of a `KeyShareEntry`.
pub open spec fn write_key_share(k: KeyShare) -> Seq<u8> {
    write_u16(k.group) + write_vec(k.key_exchange, 65535)
}

/// RFC 6066 §3: read one `ServerName`.
pub open spec fn read_server_name(b: Seq<u8>) -> Option<(ServerName, Seq<u8>)> {
    match read_uint(b, 1) {
        None => None,
        Some((nt, r)) => {
            if nt != 0 {
                None
            } else {
                match read_vec(r, 1, 65535) {
                    None => None,
                    Some((h, rest)) => Some((ServerName { host_name: h }, rest)),
                }
            }
        },
    }
}

/// RFC 6066 §3: the bytes of a `ServerName` (`name_type` 0, then the
/// `HostName`).
pub open spec fn write_server_name(s: ServerName) -> Seq<u8> {
    seq![0u8] + write_vec(s.host_name, 65535)
}

/// §4.2.1, `SupportedVersions` in a ClientHello: `ProtocolVersion
/// versions<2..254>`, the whole of `extension_data`.
pub open spec fn read_supported_versions_ch(data: Seq<u8>) -> Option<Seq<u16>> {
    match read_vec(data, 2, 254) {
        None => None,
        Some((c, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                read_u16s(c)
            }
        },
    }
}

/// §4.2.1, the bytes of `SupportedVersions` in a ClientHello.
pub open spec fn write_supported_versions_ch(vs: Seq<u16>) -> Seq<u8> {
    write_vec(write_u16s(vs), 254)
}

/// §4.2.1, `SupportedVersions` in a ServerHello or HelloRetryRequest:
/// `ProtocolVersion selected_version`, the whole of `extension_data`.
pub open spec fn read_supported_versions_sh(data: Seq<u8>) -> Option<u16> {
    match read_u16(data) {
        None => None,
        Some((v, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                Some(v)
            }
        },
    }
}

/// §4.2.2: `struct { opaque cookie<1..2^16-1>; } Cookie`, the whole of
/// `extension_data`.
pub open spec fn read_cookie(data: Seq<u8>) -> Option<Seq<u8>> {
    match read_vec(data, 1, 65535) {
        None => None,
        Some((c, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                Some(c)
            }
        },
    }
}

/// §4.2.2: the bytes of `Cookie`.
pub open spec fn write_cookie(c: Seq<u8>) -> Seq<u8> {
    write_vec(c, 65535)
}

/// §4.2.3: `struct { SignatureScheme supported_signature_algorithms<2..2^16-2>;
/// } SignatureSchemeList`, the whole of `extension_data`. The same
/// structure serves `signature_algorithms` and `signature_algorithms_cert`.
pub open spec fn read_signature_schemes(data: Seq<u8>) -> Option<Seq<u16>> {
    match read_vec(data, 2, 65534) {
        None => None,
        Some((c, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                read_u16s(c)
            }
        },
    }
}

/// §4.2.3: the bytes of a `SignatureSchemeList`.
pub open spec fn write_signature_schemes(ss: Seq<u16>) -> Seq<u8> {
    write_vec(write_u16s(ss), 65534)
}

/// §4.2.7: `struct { NamedGroup named_group_list<2..2^16-1>; }
/// NamedGroupList`, the whole of `extension_data`.
pub open spec fn read_named_groups(data: Seq<u8>) -> Option<Seq<u16>> {
    match read_vec(data, 2, 65535) {
        None => None,
        Some((c, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                read_u16s(c)
            }
        },
    }
}

/// §4.2.7: the bytes of a `NamedGroupList`.
pub open spec fn write_named_groups(gs: Seq<u16>) -> Seq<u8> {
    write_vec(write_u16s(gs), 65535)
}

/// §4.2.8, `KeyShareClientHello`: `KeyShareEntry client_shares<0..2^16-1>`,
/// the whole of `extension_data`.
pub open spec fn read_key_share_ch(data: Seq<u8>) -> Option<Seq<KeyShare>> {
    match read_vec(data, 0, 65535) {
        None => None,
        Some((c, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                read_list(c, |x: Seq<u8>| read_key_share(x))
            }
        },
    }
}

/// §4.2.8: the bytes of a `KeyShareClientHello`.
pub open spec fn write_key_share_ch(shares: Seq<KeyShare>) -> Seq<u8> {
    write_vec(write_list(shares, |k: KeyShare| write_key_share(k)), 65535)
}

/// §4.2.8, `KeyShareHelloRetryRequest`: `NamedGroup selected_group`, the
/// whole of `extension_data`.
pub open spec fn read_key_share_hrr(data: Seq<u8>) -> Option<u16> {
    read_supported_versions_sh(data)
}

/// §4.2.8, `KeyShareServerHello`: `KeyShareEntry server_share`, the whole
/// of `extension_data`.
pub open spec fn read_key_share_sh(data: Seq<u8>) -> Option<KeyShare> {
    match read_key_share(data) {
        None => None,
        Some((k, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                Some(k)
            }
        },
    }
}

/// RFC 6066 §3, in a ClientHello: `ServerName server_name_list<1..2^16-1>`,
/// the whole of `extension_data`.
pub open spec fn read_server_name_ch(data: Seq<u8>) -> Option<Seq<ServerName>> {
    match read_vec(data, 1, 65535) {
        None => None,
        Some((c, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                read_list(c, |x: Seq<u8>| read_server_name(x))
            }
        },
    }
}

/// RFC 6066 §3: the bytes of a `ServerNameList`.
pub open spec fn write_server_name_ch(names: Seq<ServerName>) -> Seq<u8> {
    write_vec(write_list(names, |s: ServerName| write_server_name(s)), 65535)
}

/// RFC 6066 §3: "the server SHALL include an extension of type
/// "server_name" in the (extended) server hello. The "extension_data"
/// field of this extension SHALL be empty." (In TLS 1.3 it is in
/// EncryptedExtensions.)
pub open spec fn server_name_ee_ok(data: Seq<u8>) -> bool {
    data.len() == 0
}

/// Whether the `extension_data` of `e`, which appears in a message of
/// kind `m`, is well formed for the extensions this crate reads. Any other
/// extension is opaque and always well formed.
pub open spec fn ext_body_ok(e: Ext, m: MsgKind) -> bool {
    if e.etype == EXT_SUPPORTED_VERSIONS {
        if m is Ch {
            read_supported_versions_ch(e.data) is Some
        } else {
            read_supported_versions_sh(e.data) is Some
        }
    } else if e.etype == EXT_COOKIE {
        read_cookie(e.data) is Some
    } else if e.etype == EXT_SIGNATURE_ALGORITHMS || e.etype == EXT_SIGNATURE_ALGORITHMS_CERT {
        read_signature_schemes(e.data) is Some
    } else if e.etype == EXT_SUPPORTED_GROUPS {
        read_named_groups(e.data) is Some
    } else if e.etype == EXT_KEY_SHARE {
        if m is Ch {
            read_key_share_ch(e.data) is Some
        } else if m is Hrr {
            read_key_share_hrr(e.data) is Some
        } else {
            read_key_share_sh(e.data) is Some
        }
    } else if e.etype == EXT_SERVER_NAME {
        if m is Ch {
            read_server_name_ch(e.data) is Some
        } else {
            server_name_ee_ok(e.data)
        }
    } else {
        true
    }
}

/// Every extension of the block is allowed in a message of kind `m`
/// ([`extension_allowed`]), as a recursion;
/// [`super::lemmas_ext::lemma_all_allowed_iff`] proves it is "for every
/// extension".
pub open spec fn all_allowed(es: Seq<Ext>, m: MsgKind) -> bool
    decreases es.len(),
{
    es.len() == 0 || (extension_allowed(es[0].etype, m) && all_allowed(es.skip(1), m))
}

/// Every extension of the block has the structure its type calls for
/// ([`ext_body_ok`]), as a recursion;
/// [`super::lemmas_ext::lemma_all_bodies_ok_iff`] proves it is "for every
/// extension".
pub open spec fn all_bodies_ok(es: Seq<Ext>, m: MsgKind) -> bool
    decreases es.len(),
{
    es.len() == 0 || (ext_body_ok(es[0], m) && all_bodies_ok(es.skip(1), m))
}

/// The checks §4.2 puts on an extension block `es` of a message of kind
/// `m`, in this order, giving the first rule broken:
///
/// 1. "There MUST NOT be more than one extension of the same type in a
///    given extension block" (`illegal_parameter`);
/// 2. "If an implementation receives an extension which it recognizes and
///    which is not specified for the message in which it appears, it MUST
///    abort the handshake with an "illegal_parameter" alert"
///    ([`extension_allowed`]);
/// 3. an extension this crate reads whose `extension_data` does not have
///    its structure ([`ext_body_ok`]): `decode_error` (§6);
/// 4. Protocol-version negotiation is checked by the hello layer, which can
///    return `protocol_version` for a legacy ServerHello without extensions.
pub open spec fn check_extensions(es: Seq<Ext>, m: MsgKind) -> Option<ErrKind> {
    if !exts_unique(es) {
        Some(ErrKind::DuplicateExtension)
    } else if !all_allowed(es, m) {
        Some(ErrKind::ExtensionNotAllowed)
    } else if !all_bodies_ok(es, m) {
        Some(ErrKind::Decode)
    } else {
        None
    }
}


// ===========================================================================
// RFC 8446 §4, "Handshake Protocol"
// RFC 8446 §4, "Handshake Protocol": the `Handshake` header, and the
// messages of §4.1 to §4.6 (the client sends ClientHello, Certificate,
// Finished and KeyUpdate; it receives the rest).
//
// Each message is a struct of [`read_uint`] and the other presentation-language readers, written as the
// standard's `struct` declares it (Appendix B.3). A syntax error is
// `None`; [`parse_handshake`] adds the rules that need the message's
// meaning and gives the error kind ([`ErrKind`]).
// ===========================================================================



// ---------------------------------------------------------------------------
// §4: HandshakeType and the Handshake header.
// ---------------------------------------------------------------------------

/// §4 `HandshakeType`: `client_hello(1)`.
pub const HS_CLIENT_HELLO: u8 = 1;

/// `server_hello(2)`.
pub const HS_SERVER_HELLO: u8 = 2;

/// `new_session_ticket(4)`.
pub const HS_NEW_SESSION_TICKET: u8 = 4;

/// `end_of_early_data(5)`.
pub const HS_END_OF_EARLY_DATA: u8 = 5;

/// `encrypted_extensions(8)`.
pub const HS_ENCRYPTED_EXTENSIONS: u8 = 8;

/// `certificate(11)`.
pub const HS_CERTIFICATE: u8 = 11;

/// `certificate_request(13)`.
pub const HS_CERTIFICATE_REQUEST: u8 = 13;

/// `certificate_verify(15)`.
pub const HS_CERTIFICATE_VERIFY: u8 = 15;

/// `finished(20)`.
pub const HS_FINISHED: u8 = 20;

/// `key_update(24)`.
pub const HS_KEY_UPDATE: u8 = 24;

/// Appendix B.3: the `HandshakeType` values that `Handshake`'s `select`
/// has a case for. The others (`hello_request_RESERVED(0)`,
/// `hello_verify_request_RESERVED(3)`, `hello_retry_request_RESERVED(6)`,
/// the other reserved values and `message_hash(254)`, which only appears
/// in the transcript hash of §4.4.1, and every value the standard does not
/// list) are not messages.
pub open spec fn handshake_type_known(t: u8) -> bool {
    t == 1 || t == 2 || t == 4 || t == 5 || t == 8 || t == 11 || t == 13 || t == 15 || t == 20 || t == 24
}

/// §4 `Handshake`: the bytes of a message of type `t` whose body is
/// `body` (`msg_type`, a `uint24 length` "bytes in message", the body).
pub open spec fn write_handshake(t: u8, body: Seq<u8>) -> Seq<u8> {
    seq![t] + write_u24(body.len()) + body
}

/// §4 `Handshake`: the type and the length of the body, read from the
/// first four bytes.
pub open spec fn read_handshake_header(b: Seq<u8>) -> Option<(u8, nat)> {
    if b.len() < HANDSHAKE_HEADER {
        None
    } else {
        Some((b[0], be_value(b.subrange(1, 4))))
    }
}

// ---------------------------------------------------------------------------
// §4.1.2 ClientHello, §4.1.3 ServerHello, §4.1.4 HelloRetryRequest.
// ---------------------------------------------------------------------------

/// §4.1.2 `ClientHello`.
pub struct ClientHello {
    /// `legacy_version` ("MUST be set to 0x0303").
    pub legacy_version: u16,
    /// `random`: `opaque Random[32]`.
    pub random: Seq<u8>,
    /// `legacy_session_id<0..32>`.
    pub session_id: Seq<u8>,
    /// `CipherSuite cipher_suites<2..2^16-2>`, each `uint8 CipherSuite[2]`
    /// kept as a `uint16`.
    pub cipher_suites: Seq<u16>,
    /// `legacy_compression_methods<1..2^8-1>`.
    pub compression: Seq<u8>,
    /// `Extension extensions<8..2^16-1>`.
    pub extensions: Seq<Ext>,
}

/// §4.1.3 `ServerHello`, which is also a HelloRetryRequest when its
/// `random` is [`hrr_random`].
pub struct ServerHello {
    /// `legacy_version`.
    pub legacy_version: u16,
    /// `random`.
    pub random: Seq<u8>,
    /// `legacy_session_id_echo<0..32>`.
    pub session_id_echo: Seq<u8>,
    /// `CipherSuite cipher_suite`.
    pub cipher_suite: u16,
    /// `legacy_compression_method` ("MUST have the value 0").
    pub compression: u8,
    /// `Extension extensions<6..2^16-1>`.
    pub extensions: Seq<Ext>,
}

/// §4.1.3: "the HelloRetryRequest message uses the same structure as the
/// ServerHello, but with Random set to the special value of the SHA-256 of
/// "HelloRetryRequest": CF 21 AD 74 E5 9A 61 11 BE 1D 8C 02 1E 65 B8 91 C2
/// A2 11 16 7A BB 8C 5E 07 9E 09 E2 C8 A8 33 9C".
pub open spec fn hrr_random() -> Seq<u8> {
    seq![
        0xCFu8, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91,
        0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E, 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C,
    ]
}

/// §4.1.3: "Upon receiving a message with type server_hello,
/// implementations MUST first examine the Random value and, if it matches
/// this value, process it as described in Section 4.1.4": whether the
/// message is a HelloRetryRequest.
pub open spec fn is_hello_retry_request(sh: ServerHello) -> bool {
    sh.random == hrr_random()
}

/// The kind of message a ServerHello is for the extension table of §4.2.
pub open spec fn server_hello_kind(sh: ServerHello) -> MsgKind {
    if is_hello_retry_request(sh) {
        MsgKind::Hrr
    } else {
        MsgKind::Sh
    }
}

/// §4.1.2, the structure of a ClientHello (Appendix B.3.1), as the whole
/// of a message body.
pub open spec fn read_client_hello(b: Seq<u8>) -> Option<ClientHello> {
    match read_uint(b, 2) {
        None => None,
        Some((ver, r1)) => {
            match read_fixed(r1, 32) {
                None => None,
                Some((random, r2)) => {
                    match read_vec(r2, 0, 32) {
                        None => None,
                        Some((sid, r3)) => {
                            match read_vec(r3, 2, 65534) {
                                None => None,
                                Some((cs_bytes, r4)) => {
                                    match read_u16s(cs_bytes) {
                                        None => None,
                                        Some(cs) => {
                                            match read_vec(r4, 1, 255) {
                                                None => None,
                                                Some((comp, r5)) => {
                                                    match read_exts(r5, 8, 65535) {
                                                        None => None,
                                                        Some((exts, r6)) => {
                                                            if r6.len() != 0 {
                                                                None
                                                            } else {
                                                                Some(
                                                                    ClientHello {
                                                                        legacy_version: ver as u16,
                                                                        random,
                                                                        session_id: sid,
                                                                        cipher_suites: cs,
                                                                        compression: comp,
                                                                        extensions: exts,
                                                                    },
                                                                )
                                                            }
                                                        },
                                                    }
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

/// §4.1.2: the bytes of a ClientHello's body, as the client sends it.
pub open spec fn write_client_hello(ch: ClientHello) -> Seq<u8> {
    write_u16(ch.legacy_version) + (ch.random + (write_vec(ch.session_id, 32) + (write_vec(
        write_u16s(ch.cipher_suites),
        65534,
    ) + (write_vec(ch.compression, 255) + write_exts(ch.extensions, 65535)))))
}

/// §4.1.3, the structure of a ServerHello (Appendix B.3.1), as the whole
/// of a message body.
pub open spec fn read_server_hello(b: Seq<u8>) -> Option<ServerHello> {
    match read_uint(b, 2) {
        None => None,
        Some((ver, r1)) => {
            match read_fixed(r1, 32) {
                None => None,
                Some((random, r2)) => {
                    match read_vec(r2, 0, 32) {
                        None => None,
                        Some((sid, r3)) => {
                            match read_uint(r3, 2) {
                                None => None,
                                Some((cs, r4)) => {
                                    match read_uint(r4, 1) {
                                        None => None,
                                        Some((comp, r5)) => {
                                            if r5.len() == 0 {
                                                Some(ServerHello {
                                                    legacy_version: ver as u16,
                                                    random,
                                                    session_id_echo: sid,
                                                    cipher_suite: cs as u16,
                                                    compression: comp as u8,
                                                    extensions: Seq::empty(),
                                                })
                                            } else { match read_exts(r5, 0, 65535) {
                                                None => None,
                                                Some((exts, r6)) => {
                                                    if r6.len() != 0 {
                                                        None
                                                    } else {
                                                        Some(
                                                            ServerHello {
                                                                legacy_version: ver as u16,
                                                                random,
                                                                session_id_echo: sid,
                                                                cipher_suite: cs as u16,
                                                                compression: comp as u8,
                                                                extensions: exts,
                                                            },
                                                        )
                                                    }
                                                },
                                            } }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

/// §4.1.3: the bytes of a ServerHello's body.
pub open spec fn write_server_hello(sh: ServerHello) -> Seq<u8> {
    write_u16(sh.legacy_version) + (sh.random + (write_vec(sh.session_id_echo, 32) + (write_u16(sh.cipher_suite) + (seq![
        sh.compression,
    ] + write_exts(sh.extensions, 65535)))))
}

// ---------------------------------------------------------------------------
// §4.3 and §4.4: server parameters and authentication.
// ---------------------------------------------------------------------------

/// §4.3.1 `EncryptedExtensions`: `Extension extensions<0..2^16-1>`, the
/// whole of a message body.
pub open spec fn read_encrypted_extensions(b: Seq<u8>) -> Option<Seq<Ext>> {
    match read_exts(b, 0, 65535) {
        None => None,
        Some((es, rest)) => {
            if rest.len() != 0 {
                None
            } else {
                Some(es)
            }
        },
    }
}

/// §4.3.2 `CertificateRequest`.
pub struct CertificateRequest {
    /// `certificate_request_context<0..2^8-1>`.
    pub context: Seq<u8>,
    /// `Extension extensions<2..2^16-1>`.
    pub extensions: Seq<Ext>,
}

/// §4.3.2: the structure of a CertificateRequest, the whole of a message
/// body.
pub open spec fn read_certificate_request(b: Seq<u8>) -> Option<CertificateRequest> {
    match read_vec(b, 0, 255) {
        None => None,
        Some((ctx, r1)) => {
            match read_exts(r1, 2, 65535) {
                None => None,
                Some((es, rest)) => {
                    if rest.len() != 0 {
                        None
                    } else {
                        Some(CertificateRequest { context: ctx, extensions: es })
                    }
                },
            }
        },
    }
}

/// §4.4.2 `CertificateEntry` for the `X509` certificate type: `opaque
/// cert_data<1..2^24-1>; Extension extensions<0..2^16-1>`.
pub struct CertificateEntry {
    /// `cert_data`, a DER certificate (read by phase-3.md item 3.5b).
    pub cert_data: Seq<u8>,
    /// `extensions`.
    pub extensions: Seq<Ext>,
}

/// §4.4.2 `Certificate`.
pub struct Certificate {
    /// `certificate_request_context<0..2^8-1>`.
    pub context: Seq<u8>,
    /// `CertificateEntry certificate_list<0..2^24-1>`.
    pub entries: Seq<CertificateEntry>,
}

/// §4.4.2: read one `CertificateEntry`.
pub open spec fn read_certificate_entry(b: Seq<u8>) -> Option<(CertificateEntry, Seq<u8>)> {
    match read_vec(b, 1, 16777215) {
        None => None,
        Some((cert, r1)) => {
            match read_exts(r1, 0, 65535) {
                None => None,
                Some((es, rest)) => Some((CertificateEntry { cert_data: cert, extensions: es }, rest)),
            }
        },
    }
}

/// §4.4.2: the bytes of a `CertificateEntry`.
pub open spec fn write_certificate_entry(e: CertificateEntry) -> Seq<u8> {
    write_vec(e.cert_data, 16777215) + write_exts(e.extensions, 65535)
}

/// §4.4.2: the structure of a Certificate, the whole of a message body.
pub open spec fn read_certificate(b: Seq<u8>) -> Option<Certificate> {
    match read_vec(b, 0, 255) {
        None => None,
        Some((ctx, r1)) => {
            match read_vec(r1, 0, 16777215) {
                None => None,
                Some((list, rest)) => {
                    if rest.len() != 0 {
                        None
                    } else {
                        match read_list(list, |x: Seq<u8>| read_certificate_entry(x)) {
                            None => None,
                            Some(es) => Some(Certificate { context: ctx, entries: es }),
                        }
                    }
                },
            }
        },
    }
}

/// §4.4.2: the bytes of a Certificate's body. A client that has no
/// certificate to answer a CertificateRequest with sends this with no
/// entries (§4.4.2: "the client MUST send a Certificate message
/// containing no certificates (i.e., with the "certificate_list" field
/// having length 0)").
pub open spec fn write_certificate(c: Certificate) -> Seq<u8> {
    write_vec(c.context, 255) + write_vec(
        write_list(c.entries, |e: CertificateEntry| write_certificate_entry(e)),
        16777215,
    )
}

/// §4.4.3 `CertificateVerify`: `SignatureScheme algorithm; opaque
/// signature<0..2^16-1>`.
pub struct CertificateVerify {
    /// `algorithm`.
    pub algorithm: u16,
    /// `signature`.
    pub signature: Seq<u8>,
}

/// §4.4.3: the structure of a CertificateVerify, the whole of a body.
pub open spec fn read_certificate_verify(b: Seq<u8>) -> Option<CertificateVerify> {
    match read_uint(b, 2) {
        None => None,
        Some((alg, r1)) => {
            match read_vec(r1, 0, 65535) {
                None => None,
                Some((sig, rest)) => {
                    if rest.len() != 0 {
                        None
                    } else {
                        Some(CertificateVerify { algorithm: alg as u16, signature: sig })
                    }
                },
            }
        },
    }
}

/// §4.4.3: the bytes of a CertificateVerify's body.
pub open spec fn write_certificate_verify(c: CertificateVerify) -> Seq<u8> {
    write_u16(c.algorithm) + write_vec(c.signature, 65535)
}

/// §4.3.1: the bytes of an EncryptedExtensions body.
pub open spec fn write_encrypted_extensions(es: Seq<Ext>) -> Seq<u8> {
    write_exts(es, 65535)
}

/// §4.3.2: the bytes of a CertificateRequest's body.
pub open spec fn write_certificate_request(c: CertificateRequest) -> Seq<u8> {
    write_vec(c.context, 255) + write_exts(c.extensions, 65535)
}

/// §4.4.4 `Finished`: `opaque verify_data[Hash.length]`, the whole of a
/// body, for a hash of `hash_len` bytes (32 for SHA-256).
pub open spec fn read_finished(b: Seq<u8>, hash_len: nat) -> Option<Seq<u8>> {
    if b.len() == hash_len {
        Some(b)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// §4.6: post-handshake messages.
// ---------------------------------------------------------------------------

/// §4.6.1 `NewSessionTicket`.
pub struct NewSessionTicket {
    /// `uint32 ticket_lifetime`.
    pub ticket_lifetime: u32,
    /// `uint32 ticket_age_add`.
    pub ticket_age_add: u32,
    /// `opaque ticket_nonce<0..255>`.
    pub ticket_nonce: Seq<u8>,
    /// `opaque ticket<1..2^16-1>`.
    pub ticket: Seq<u8>,
    /// `Extension extensions<0..2^16-2>`.
    pub extensions: Seq<Ext>,
}

/// §4.6.1: the structure of a NewSessionTicket, the whole of a body. This
/// crate parses it and the layer above ignores it (no resumption in this
/// phase).
pub open spec fn read_new_session_ticket(b: Seq<u8>) -> Option<NewSessionTicket> {
    match read_uint(b, 4) {
        None => None,
        Some((life, r1)) => {
            match read_uint(r1, 4) {
                None => None,
                Some((add, r2)) => {
                    match read_vec(r2, 0, 255) {
                        None => None,
                        Some((nonce, r3)) => {
                            match read_vec(r3, 1, 65535) {
                                None => None,
                                Some((ticket, r4)) => {
                                    match read_exts(r4, 0, 65534) {
                                        None => None,
                                        Some((es, rest)) => {
                                            if rest.len() != 0 {
                                                None
                                            } else {
                                                Some(
                                                    NewSessionTicket {
                                                        ticket_lifetime: life as u32,
                                                        ticket_age_add: add as u32,
                                                        ticket_nonce: nonce,
                                                        ticket: ticket,
                                                        extensions: es,
                                                    },
                                                )
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

/// §4.6.1: the bytes of a NewSessionTicket's body.
pub open spec fn write_new_session_ticket(n: NewSessionTicket) -> Seq<u8> {
    be_bytes(n.ticket_lifetime as nat, 4) + (be_bytes(n.ticket_age_add as nat, 4) + (write_vec(n.ticket_nonce, 255) + (write_vec(
        n.ticket,
        65535,
    ) + write_exts(n.extensions, 65534))))
}

/// §4.6.3 `KeyUpdateRequest`: `update_not_requested(0)`.
pub const UPDATE_NOT_REQUESTED: u8 = 0;

/// `update_requested(1)`.
pub const UPDATE_REQUESTED: u8 = 1;

/// §4.6.3: the bytes of a KeyUpdate's body.
pub open spec fn write_key_update(request_update: u8) -> Seq<u8> {
    seq![request_update]
}

/// §4.6.3: the structure of a KeyUpdate, the whole of a body: one byte,
/// `KeyUpdateRequest request_update`.
pub open spec fn read_key_update(b: Seq<u8>) -> Option<u8> {
    if b.len() == 1 {
        Some(b[0])
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// A parsed message, and the rules that need its meaning.
// ---------------------------------------------------------------------------

/// A handshake message this crate reads.
pub enum HsMsg {
    /// §4.1.2.
    ClientHello(ClientHello),
    /// §4.1.3 and §4.1.4 (a HelloRetryRequest is a ServerHello with
    /// [`hrr_random`]).
    ServerHello(ServerHello),
    /// §4.6.1.
    NewSessionTicket(NewSessionTicket),
    /// §4.5, with an empty body.
    EndOfEarlyData,
    /// §4.3.1.
    EncryptedExtensions(Seq<Ext>),
    /// §4.4.2.
    Certificate(Certificate),
    /// §4.3.2.
    CertificateRequest(CertificateRequest),
    /// §4.4.3.
    CertificateVerify(CertificateVerify),
    /// §4.4.4: `verify_data`.
    Finished(Seq<u8>),
    /// §4.6.3: `request_update`.
    KeyUpdate(u8),
}

/// §4.2 on the extensions of each entry of a Certificate: the first error
/// in the entries' order.
pub open spec fn certificate_entries_error(es: Seq<CertificateEntry>) -> Option<ErrKind>
    decreases es.len(),
{
    if es.len() == 0 {
        None
    } else {
        match check_extensions(es[0].extensions, MsgKind::Ct) {
            Some(k) => Some(k),
            None => certificate_entries_error(es.skip(1)),
        }
    }
}

/// §4: the message of type `t` with body `body`, read and checked.
/// `hash_len` is the length of the cipher suite's hash (for `Finished`).
///
/// 1. `t` is a type Appendix B.3 lists, else `unexpected_message`.
/// 2. The body has the structure of the message (a syntax error is
///    `decode_error`, §6).
/// 3. The rules of §4.1 to §4.6 that read its fields:
///    - ClientHello (§4.1.2): "legacy_compression_methods ... MUST contain
///      exactly one byte, set to zero ... If a TLS 1.3 ClientHello is
///      received with any other value in this field, the server MUST abort
///      the handshake with an "illegal_parameter" alert"; the extensions
///      ([`check_extensions`], kind CH).
///    - ServerHello (§4.1.3): "legacy_compression_method: A single byte
///      which MUST have the value 0"; the extensions ([`check_extensions`],
///      kind SH, or HRR for a HelloRetryRequest).
///    - EncryptedExtensions, CertificateRequest, NewSessionTicket: the
///      extensions (kinds EE, CR, NST).
///    - Certificate (§4.4.2): in the case of server authentication the
///      context "SHALL be zero length"; the extensions of each entry
///      (kind CT).
///    - KeyUpdate (§4.6.3): "If the request_update field is set to any
///      other value than the defined ones, the receiver MUST terminate the
///      connection with an "illegal_parameter" alert."
pub open spec fn parse_handshake_body(t: u8, body: Seq<u8>, hash_len: nat) -> Res<HsMsg> {
    if !handshake_type_known(t) {
        // 1.
        Res::Err(ErrKind::UnexpectedHandshakeType)
    } else if t == HS_CLIENT_HELLO {
        match read_client_hello(body) {
            None => Res::Err(ErrKind::Decode),
            Some(ch) => {
                if ch.compression != seq![0u8] {
                    Res::Err(ErrKind::InvalidEnum)
                } else {
                    match check_extensions(ch.extensions, MsgKind::Ch) {
                        Some(k) => Res::Err(k),
                        None => Res::Ok(HsMsg::ClientHello(ch)),
                    }
                }
            },
        }
    } else if t == HS_SERVER_HELLO {
        match read_server_hello(body) {
            None => Res::Err(ErrKind::Decode),
            Some(sh) => {
                if sh.compression != 0 {
                    Res::Err(ErrKind::InvalidEnum)
                } else {
                    match check_extensions(sh.extensions, server_hello_kind(sh)) {
                        Some(k) => Res::Err(k),
                        None => Res::Ok(HsMsg::ServerHello(sh)),
                    }
                }
            },
        }
    } else if t == HS_NEW_SESSION_TICKET {
        match read_new_session_ticket(body) {
            None => Res::Err(ErrKind::Decode),
            Some(n) => {
                match check_extensions(n.extensions, MsgKind::Nst) {
                    Some(k) => Res::Err(k),
                    None => Res::Ok(HsMsg::NewSessionTicket(n)),
                }
            },
        }
    } else if t == HS_END_OF_EARLY_DATA {
        if body.len() == 0 {
            Res::Ok(HsMsg::EndOfEarlyData)
        } else {
            Res::Err(ErrKind::Decode)
        }
    } else if t == HS_ENCRYPTED_EXTENSIONS {
        match read_encrypted_extensions(body) {
            None => Res::Err(ErrKind::Decode),
            Some(es) => {
                match check_extensions(es, MsgKind::Ee) {
                    Some(k) => Res::Err(k),
                    None => Res::Ok(HsMsg::EncryptedExtensions(es)),
                }
            },
        }
    } else if t == HS_CERTIFICATE {
        match read_certificate(body) {
            None => Res::Err(ErrKind::Decode),
            Some(c) => {
                match certificate_entries_error(c.entries) {
                    Some(k) => Res::Err(k),
                    None => Res::Ok(HsMsg::Certificate(c)),
                }
            },
        }
    } else if t == HS_CERTIFICATE_REQUEST {
        match read_certificate_request(body) {
            None => Res::Err(ErrKind::Decode),
            Some(c) => {
                match check_extensions(c.extensions, MsgKind::Cr) {
                    Some(k) => Res::Err(k),
                    None => Res::Ok(HsMsg::CertificateRequest(c)),
                }
            },
        }
    } else if t == HS_CERTIFICATE_VERIFY {
        match read_certificate_verify(body) {
            None => Res::Err(ErrKind::Decode),
            Some(c) => Res::Ok(HsMsg::CertificateVerify(c)),
        }
    } else if t == HS_FINISHED {
        match read_finished(body, hash_len) {
            None => Res::Err(ErrKind::Decode),
            Some(v) => Res::Ok(HsMsg::Finished(v)),
        }
    } else {
        // t == HS_KEY_UPDATE: the only type left.
        match read_key_update(body) {
            None => Res::Err(ErrKind::Decode),
            Some(r) => {
                if r == UPDATE_NOT_REQUESTED || r == UPDATE_REQUESTED {
                    Res::Ok(HsMsg::KeyUpdate(r))
                } else {
                    Res::Err(ErrKind::InvalidEnum)
                }
            },
        }
    }
}

/// §4: one whole handshake message `msg` (what [`extract_messages`] emits),
/// read and checked: the header, then the body ([`parse_handshake_body`]).
/// A type that is not a message is refused before the length is compared,
/// as the type is the first thing read.
pub open spec fn parse_handshake(msg: Seq<u8>, hash_len: nat) -> Res<HsMsg> {
    match read_handshake_header(msg) {
        None => Res::Err(ErrKind::Decode),
        Some((t, len)) => {
            if !handshake_type_known(t) {
                Res::Err(ErrKind::UnexpectedHandshakeType)
            } else if msg.len() != HANDSHAKE_HEADER + len {
                Res::Err(ErrKind::Decode)
            } else {
                parse_handshake_body(t, msg.skip(4), hash_len)
            }
        },
    }
}

} // verus!
