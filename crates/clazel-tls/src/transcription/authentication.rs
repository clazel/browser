//! RFC 8446 §4.3 and §4.4: EncryptedExtensions, CertificateRequest, the
//! transcript hash, Certificate, CertificateVerify and Finished.
//!
//! Modelling choices:
//! - **The transcript** is the list of the raw handshake messages exchanged so
//!   far with a flag for whether the first was retried. [`transcript_hash`] is
//!   §4.4.1's two equations. It takes the flag explicitly, because the rule is
//!   stated of "when the server responds to a ClientHello with a
//!   HelloRetryRequest", not of the bytes; the state machine sets it.
//! - Only `certificate_type` X509 is modelled: the client does not offer the
//!   certificate-type extensions (§4.4.2: "If the corresponding certificate type
//!   extension ... was not negotiated"), so `RawPublicKey` cannot be selected.
//! - "The server's certificate_list MUST always be non-empty", and §4.4.2.4 gives
//!   the alert, `decode_error`, even though the struct's floor is 0. So the
//!   decoder accepts the empty list and the check is separate.
//! - Certificate validation (§4.4.2.2, §4.4.2.4) and the meaning of the OCSP
//!   and SCT contents (§4.4.2.1) are `Primitives::validate_certificate_chain`,
//!   which sees the entries, extensions included. MD5 and SHA-1 rejection is
//!   part of that. Their TLS syntax (CertificateStatus,
//!   SignedCertificateTimestampList) is checked first, in `extension_bodies`.
//! - **Client certificates**: the model has none. A CertificateRequest in the
//!   main handshake is checked, and §4.4.2's "If the server requests client
//!   authentication but no suitable certificate is available, the client MUST
//!   send a Certificate message containing no certificates" is what is answered,
//!   with the request's context echoed. Therefore no client CertificateVerify
//!   ever exists: "Clients MUST send this message whenever authenticating via a
//!   certificate (i.e., when the Certificate message is non-empty)".
//! - **§4.4.3's "unless".** "the signature algorithm MUST be one offered in the
//!   client's 'signature_algorithms' extension unless no valid certificate chain
//!   can be produced without unsupported algorithms" is a rule for the server.
//!   It gives the client nothing to verify with: §4.2.3 says each value is one
//!   "that the client is willing to verify". So a client rejects an un-offered
//!   scheme, always. See `docs/ERRATA.md`.
//! - In a CertificateRequest, the contents of extensions other than
//!   signature_algorithms are decoded for their syntax only
//!   (`extension_bodies`), since a client that always answers with no
//!   certificate does nothing with them. The same file checks the syntax of the
//!   bodies of EncryptedExtensions and of each CertificateEntry.
//! - EncryptedExtensions' "forbidden extensions" (§4.3.1) are those §4.2's table
//!   does not specify for EE.

#[allow(unused_imports)]
use vstd::prelude::*;

use super::extensions::Extension;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::extension_bodies::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;

verus! {

// --------------------------------------------------------------------------
// §4.3.1 Encrypted Extensions.
// --------------------------------------------------------------------------

/// §4.3.1: `struct { Extension extensions<0..2^16-1>; } EncryptedExtensions;`
pub struct EncryptedExtensions {
    /// §4.3.1 extensions.
    pub extensions: Seq<Extension>,
}

/// §4.3.1: the structure, from exactly its bytes.
pub open spec fn read_encrypted_extensions(body: Seq<u8>) -> Option<EncryptedExtensions> {
    match read_extensions(body, 0, 0xffff) {
        Some((extensions, rest)) => if rest.len() == 0 { Some(EncryptedExtensions { extensions }) } else { None },
        None => None,
    }
}

/// §4.3.1: the encoded message.
pub open spec fn write_encrypted_extensions(message: EncryptedExtensions) -> Seq<u8> {
    write_handshake(ht_encrypted_extensions(), write_extensions(message.extensions))
}

/// §4.3.1: "The client MUST check EncryptedExtensions for the presence of any
/// forbidden extensions and if any are found MUST abort the handshake with an
/// 'illegal_parameter' alert." And §4.2's responses rule.
pub open spec fn encrypted_extensions_failures(sent: ClientHello, message: EncryptedExtensions) -> Seq<ClientError> {
    response_block_failures(message.extensions, extension_types(sent.extensions), TableMessage::Ee)
        // §4.2: the bodies (`extension_bodies`), RFC 6066 §3's server_name among them.
        + extension_body_failures(sent.extensions, message.extensions, TableMessage::Ee)
}

// --------------------------------------------------------------------------
// §4.3.2 Certificate Request.
// --------------------------------------------------------------------------

/// §4.3.2's struct CertificateRequest.
pub struct CertificateRequest {
    /// `opaque certificate_request_context<0..2^8-1>;`
    pub certificate_request_context: Seq<u8>,
    /// `Extension extensions<2..2^16-1>;`
    pub extensions: Seq<Extension>,
}

/// §4.3.2: the structure, from exactly its bytes.
pub open spec fn read_certificate_request(body: Seq<u8>) -> Option<CertificateRequest> {
    match read_vector(body, 0, 0xff) {
        None => None,
        Some((certificate_request_context, rest)) => match read_extensions(rest, 2, 0xffff) {
            None => None,
            Some((extensions, rest)) =>
                if rest.len() == 0 { Some(CertificateRequest { certificate_request_context, extensions }) } else { None },
        },
    }
}

/// §4.3.2: the encoded message.
pub open spec fn write_certificate_request(message: CertificateRequest) -> Seq<u8> {
    write_handshake(ht_certificate_request(),
        write_vector(message.certificate_request_context, 0xff) + write_extensions(message.extensions))
}

/// §4.3.2: every failure of a CertificateRequest in the main handshake.
pub open spec fn certificate_request_failures(message: CertificateRequest) -> Seq<ClientError> {
    // "This field SHALL be zero length unless used for the post-handshake
    // authentication exchanges".
    fails_if(message.certificate_request_context.len() != 0, ClientError::RequestContextNotEmpty)
    // §4.2: table and duplicates. "Clients MUST ignore unrecognized extensions."
    + block_rules_failures(message.extensions, TableMessage::Cr)
    // "The 'signature_algorithms' extension MUST be specified".
    + match find_extension(message.extensions, ext_signature_algorithms()) {
        None => seq![ClientError::SignatureAlgorithmsMissing],
        Some(data) => fails_if(read_signature_scheme_list(data) is None, ClientError::Malformed),
    }
    // §4.2: the bodies (`extension_bodies`). Requests, so no offer is consulted.
    + extension_body_failures(seq![], message.extensions, TableMessage::Cr)
}

// --------------------------------------------------------------------------
// §4.4.1 The Transcript Hash.
// --------------------------------------------------------------------------

/// §4.4.1: the special synthetic handshake message: "Hash(message_hash ||
/// /* Handshake type */ 00 00 Hash.length || /* Handshake message length (bytes)
/// */ Hash(ClientHello1) /* Hash of ClientHello1 */ ...".
pub open spec fn synthetic_message_hash(p: Primitives, client_hello1: Seq<u8>) -> Seq<u8> {
    seq![ht_message_hash() as u8, 0u8, 0u8, hash_length() as u8] + (p.hash)(client_hello1)
}

/// §4.4.1: `Transcript-Hash(M1, M2, ... Mn) = Hash(M1 || M2 || ... || Mn)`, and,
/// `retried`, `Transcript-Hash(ClientHello1, HelloRetryRequest, ... Mn) =
/// Hash(message_hash || 00 00 Hash.length || Hash(ClientHello1) ||
/// HelloRetryRequest || ... || Mn)`.
pub open spec fn transcript_hash(p: Primitives, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    if retried && messages.len() > 0 {
        (p.hash)(synthetic_message_hash(p, messages[0])
            + concatenate(messages.subrange(1, messages.len() as int)))
    } else {
        (p.hash)(concatenate(messages))
    }
}

// --------------------------------------------------------------------------
// §4.4.2 Certificate.
// --------------------------------------------------------------------------

/// §4.4.2: `struct { opaque cert_data<1..2^24-1>; Extension extensions<0..2^16-1>; } CertificateEntry;`
/// with `certificate_type` X509.
pub struct CertificateEntry {
    /// `opaque cert_data<1..2^24-1>;`
    pub cert_data: Seq<u8>,
    /// `Extension extensions<0..2^16-1>;`
    pub extensions: Seq<Extension>,
}

/// §4.4.2's struct Certificate.
pub struct Certificate {
    /// `opaque certificate_request_context<0..2^8-1>;`
    pub certificate_request_context: Seq<u8>,
    /// `CertificateEntry certificate_list<0..2^24-1>;`
    pub certificate_list: Seq<CertificateEntry>,
}

/// The body of `certificate_list` as its entries.
pub open spec fn read_certificate_entries(body: Seq<u8>) -> Option<Seq<CertificateEntry>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else {
        match read_vector(body, 1, 0xff_ffff) {
            None => None,
            Some((cert_data, after_data)) => match read_vector(after_data, 0, 0xffff) {
                None => None,
                Some((extension_bytes, _)) =>
                    if body.len() < 3 + cert_data.len() + 2 + extension_bytes.len() {
                        None
                    } else {
                        match read_extension_list(extension_bytes) {
                            None => None,
                            Some(extensions) => match read_certificate_entries(
                                body.subrange((3 + cert_data.len() + 2 + extension_bytes.len()) as int, body.len() as int)) {
                                None => None,
                                Some(tail) => Some(seq![CertificateEntry { cert_data, extensions }] + tail),
                            },
                        }
                    },
            },
        }
    }
}

/// §4.4.2: the structure, from exactly its bytes.
pub open spec fn read_certificate(body: Seq<u8>) -> Option<Certificate> {
    match read_vector(body, 0, 0xff) {
        None => None,
        Some((certificate_request_context, rest)) => match read_vector(rest, 0, 0xff_ffff) {
            None => None,
            Some((list, rest)) =>
                if rest.len() != 0 {
                    None
                } else {
                    match read_certificate_entries(list) {
                        None => None,
                        Some(certificate_list) => Some(Certificate { certificate_request_context, certificate_list }),
                    }
                },
        },
    }
}

/// The encoded elements of `certificate_list`.
pub open spec fn write_certificate_entries(entries: Seq<CertificateEntry>) -> Seq<u8>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        write_vector(entries[0].cert_data, 0xff_ffff) + write_extensions(entries[0].extensions)
            + write_certificate_entries(entries.subrange(1, entries.len() as int))
    }
}

/// §4.4.2: the encoded message.
pub open spec fn write_certificate(message: Certificate) -> Seq<u8> {
    write_handshake(ht_certificate(),
        write_vector(message.certificate_request_context, 0xff)
            + write_vector(write_certificate_entries(message.certificate_list), 0xff_ffff))
}

/// §4.4.2: "Extensions in the Certificate message from the server MUST correspond
/// to ones from the ClientHello message", with §4.2's rules, per entry.
pub open spec fn certificate_entries_failures(sent: ClientHello, entries: Seq<CertificateEntry>) -> Seq<ClientError>
    decreases entries.len(),
{
    if entries.len() == 0 {
        seq![]
    } else {
        response_block_failures(entries[0].extensions, extension_types(sent.extensions), TableMessage::Ct)
            // §4.4.2.1 and §4.2: the bodies (`extension_bodies`).
            + extension_body_failures(sent.extensions, entries[0].extensions, TableMessage::Ct)
            + certificate_entries_failures(sent, entries.subrange(1, entries.len() as int))
    }
}

/// §4.4.2 and §4.4.2.4: every failure of a server's Certificate before
/// certificate validation.
pub open spec fn certificate_failures(sent: ClientHello, message: Certificate) -> Seq<ClientError> {
    // "Otherwise (in the case of server authentication), this field SHALL be zero
    // length." A client without post-handshake authentication always is.
    fails_if(message.certificate_request_context.len() != 0, ClientError::CertificateContextNotEmpty)
    // §4.4.2.4: "If the server supplies an empty Certificate message, the client
    // MUST abort the handshake with a 'decode_error' alert."
    + fails_if(message.certificate_list.len() == 0, ClientError::EmptyServerCertificate)
    + certificate_entries_failures(sent, message.certificate_list)
}

// --------------------------------------------------------------------------
// §4.4.3 Certificate Verify.
// --------------------------------------------------------------------------

/// §4.4.3's struct CertificateVerify.
pub struct CertificateVerify {
    /// `SignatureScheme algorithm;`
    pub algorithm: nat,
    /// `opaque signature<0..2^16-1>;`
    pub signature: Seq<u8>,
}

/// §4.4.3: the structure, from exactly its bytes.
pub open spec fn read_certificate_verify(body: Seq<u8>) -> Option<CertificateVerify> {
    if body.len() < 2 {
        None
    } else {
        match read_vector(body.subrange(2, body.len() as int), 0, 0xffff) {
            Some((signature, rest)) =>
                if rest.len() == 0 { Some(CertificateVerify { algorithm: read_uint(body, 2), signature }) } else { None },
            None => None,
        }
    }
}

/// §4.4.3: the encoded message.
pub open spec fn write_certificate_verify(message: CertificateVerify) -> Seq<u8> {
    write_handshake(ht_certificate_verify(), uint16(message.algorithm) + write_vector(message.signature, 0xffff))
}

/// §4.4.3: 'The context string for a server signature is "TLS 1.3, server
/// CertificateVerify".'
pub open spec fn server_certificate_verify_context() -> Seq<u8> {
    seq![0x54u8, 0x4c, 0x53, 0x20, 0x31, 0x2e, 0x33, 0x2c, 0x20,
         0x73, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20,
         0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65,
         0x56, 0x65, 0x72, 0x69, 0x66, 0x79]
}

/// §4.4.3: 'The context string for a client signature is "TLS 1.3, client
/// CertificateVerify".' Kept for completeness; a client without certificates
/// never signs.
pub open spec fn client_certificate_verify_context() -> Seq<u8> {
    seq![0x54u8, 0x4c, 0x53, 0x20, 0x31, 0x2e, 0x33, 0x2c, 0x20,
         0x63, 0x6c, 0x69, 0x65, 0x6e, 0x74, 0x20,
         0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65,
         0x56, 0x65, 0x72, 0x69, 0x66, 0x79]
}

/// §4.4.3: "The digital signature is then computed over the concatenation of: A
/// string that consists of octet 32 (0x20) repeated 64 times; The context string;
/// A single 0 byte which serves as the separator; The content to be signed".
pub open spec fn certificate_verify_content(context: Seq<u8>, content_to_be_signed: Seq<u8>) -> Seq<u8> {
    repeat_byte(0x20, 64) + context + seq![0u8] + content_to_be_signed
}

/// §4.4.3: every failure of a server's CertificateVerify, given the transcript
/// through its Certificate and the end-entity public key.
pub open spec fn certificate_verify_failures(p: Primitives, sent: ClientHello, message: CertificateVerify,
    transcript: Seq<Seq<u8>>, retried: bool, public_key: Seq<u8>) -> Seq<ClientError>
{
    // "If the CertificateVerify message is sent by a server, the signature algorithm
    // MUST be one offered in the client's 'signature_algorithms' extension".
    fails_if(!list_has(offered_signature_schemes(sent), message.algorithm), ClientError::SignatureSchemeNotOffered)
    // "RSA signatures MUST use an RSASSA-PSS algorithm, regardless of whether
    // RSASSA-PKCS1-v1_5 algorithms appear in 'signature_algorithms'. The SHA-1
    // algorithm MUST NOT be used".
    + fails_if(scheme_refers_solely_to_certificates(message.algorithm), ClientError::SignatureSchemeForbidden)
    // "the signature algorithm MUST be compatible with the key".
    + fails_if(!(p.key_compatible)(message.algorithm, public_key), ClientError::SignatureSchemeKeyMismatch)
    // "If the verification fails, the receiver MUST terminate the handshake with a
    // 'decrypt_error' alert."
    + fails_if(!(p.verify_signature)(message.algorithm, public_key,
            certificate_verify_content(server_certificate_verify_context(),
                // "Transcript-Hash(Handshake Context, Certificate)"
                transcript_hash(p, transcript, retried)),
            message.signature),
        ClientError::CertificateVerifyFailed)
}

// --------------------------------------------------------------------------
// §4.4.4 Finished.
// --------------------------------------------------------------------------

/// §4.4.4: `struct { opaque verify_data[Hash.length]; } Finished;`
pub struct Finished {
    /// §4.4.4 verify_data.
    pub verify_data: Seq<u8>,
}

/// §4.4.4: the structure, from exactly its bytes.
pub open spec fn read_finished(body: Seq<u8>) -> Option<Finished> {
    if body.len() == hash_length() { Some(Finished { verify_data: body }) } else { None }
}

/// §4.4.4: the encoded message.
pub open spec fn write_finished(verify_data: Seq<u8>) -> Seq<u8> {
    write_handshake(ht_finished(), verify_data)
}

/// §4.4.4: `finished_key = HKDF-Expand-Label(BaseKey, "finished", "", Hash.length)`.
pub open spec fn finished_key(p: Primitives, base_key: Seq<u8>) -> Seq<u8> {
    hkdf_expand_label(p, base_key, label_finished(), seq![], hash_length())
}

/// §4.4.4: `verify_data = HMAC(finished_key, Transcript-Hash(Handshake Context,
/// Certificate*, CertificateVerify*))`. `transcript` is those messages, and §4.4's
/// table gives the Base Key.
pub open spec fn verify_data(p: Primitives, base_key: Seq<u8>, transcript: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    (p.hmac)(finished_key(p, base_key), transcript_hash(p, transcript, retried))
}

} // verus!
