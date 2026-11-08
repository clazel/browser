//! RFC 8446 §4 and §4.1: the Handshake structure and its `select`, the key
//! exchange messages, and the client's obligations for each.
//!
//! Modelling choices:
//! - `HandshakeType` values are `nat` with prefix `ht_`. `select` (§3.8, §4) is
//!   [`select_handshake`]; its enum holds the RFC's ten arms. `message_hash` has
//!   no arm in the RFC's `select`: it only exists inside the transcript, so on
//!   the wire it is treated as any other type with no arm, unexpected.
//! - What the client sends is a parameter, not a choice of this file: the
//!   initial [`ClientHello`] is a value the caller provides, with
//!   [`client_hello_conforms`] saying what it must satisfy. The profile's three
//!   decisions are in that predicate, and [`build_client_hello`] is one way to
//!   meet it.
//! - **Two readers of a server's hello.** §4.1.3 defines `Extension
//!   extensions<6..2^16-1>`, but the client must recognize a TLS 1.2 or older
//!   ServerHello in order to run §4.1.3's downgrade check and Appendix D.1, and
//!   that older message may have fewer bytes of extensions or none (§4.1.2:
//!   "All versions of TLS allow an extensions field to optionally follow the
//!   compression_methods field"). So [`read_server_hello_any_version`] reads
//!   the optional block with no floor, and is used only to find the version;
//!   [`read_server_hello`] is §4.1.3's struct, used once the message
//!   is known to be TLS 1.3 or a HelloRetryRequest. See `docs/ERRATA.md`.
//! - **The check on `legacy_version`.** §4.2.1 says "If this extension is
//!   present, clients MUST ignore the ServerHello.legacy_version value". §4.1.4
//!   says of a HelloRetryRequest "the client MUST check the legacy_version ...
//!   as specified in Section 4.1.3". Appendix D.5 says "Any endpoint receiving a
//!   Hello message with ... ServerHello.legacy_version set to 0x0300 MUST abort
//!   the handshake with a 'protocol_version' alert". These are reconciled by
//!   specificity: 0x0300 always aborts (D.5); a HelloRetryRequest's value must
//!   be 0x0303 (§4.1.4); otherwise, with supported_versions, it is ignored
//!   (§4.2.1). See `docs/ERRATA.md`.
//! - A ServerHello with no supported_versions and legacy_version above 0x0303
//!   indicates no version the RFC defines a way to reach: all TLS 1.3 ServerHello
//!   messages "MUST contain" the extension, so it is `missing_extension`.
//! - The HelloRetryRequest in A.1 goes from WAIT_SH to START and then, sending the
//!   ClientHello, to WAIT_SH. [`second_client_hello`] and the state machine
//!   fold those two arrows into one step.
//! - A second ClientHello's padding: "Optionally adding, removing, or changing
//!   the length of the 'padding' extension". [`second_client_hello_conforms`]
//!   allows it, and [`second_client_hello`] keeps the padding as it was.
//! - §4.1.2's "MUST send the same ClientHello without modification" includes
//!   `random` and `legacy_session_id`. RFC 8448 §5's trace agrees.
//! - A client that "requests additional functionality using extensions and
//!   this functionality is not supplied by the server" "MAY abort": it does not
//!   here (a MAY, with nothing that depends on it in this RFC).
//! - Checks of a server's own MUSTs not listed here have no client action in the
//!   text: "MUST only include extensions which are required to establish the
//!   cryptographic context" (§4.1.3) is not separately enforced beyond §4.2's
//!   table, which says the same of the extensions this RFC defines.

#[allow(unused_imports)]
use vstd::prelude::*;

use super::authentication::{
    Certificate, CertificateRequest, CertificateVerify, EncryptedExtensions, Finished,
};
use super::extensions::Extension;
use super::post_handshake::{KeyUpdate, NewSessionTicket};

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::authentication::*;
#[cfg(verus_only)]
use super::extension_bodies::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::post_handshake::*;
#[cfg(verus_only)]
use super::presentation::*;

verus! {

// --------------------------------------------------------------------------
// §4 Handshake protocol.
// --------------------------------------------------------------------------

/// §4 client_hello(1).
pub open spec fn ht_client_hello() -> nat { 1 }
/// §4 server_hello(2).
pub open spec fn ht_server_hello() -> nat { 2 }
/// §4 new_session_ticket(4).
pub open spec fn ht_new_session_ticket() -> nat { 4 }
/// §4 end_of_early_data(5).
pub open spec fn ht_end_of_early_data() -> nat { 5 }
/// §4 encrypted_extensions(8).
pub open spec fn ht_encrypted_extensions() -> nat { 8 }
/// §4 certificate(11).
pub open spec fn ht_certificate() -> nat { 11 }
/// §4 certificate_request(13).
pub open spec fn ht_certificate_request() -> nat { 13 }
/// §4 certificate_verify(15).
pub open spec fn ht_certificate_verify() -> nat { 15 }
/// §4 finished(20).
pub open spec fn ht_finished() -> nat { 20 }
/// §4 key_update(24).
pub open spec fn ht_key_update() -> nat { 24 }
/// §4 message_hash(254).
pub open spec fn ht_message_hash() -> nat { 254 }

/// §4: the `select (Handshake.msg_type)` arms.
pub enum HandshakeBody {
    /// `case client_hello: ClientHello;`
    ClientHello(ClientHello),
    /// `case server_hello: ServerHello;`
    ServerHello(ServerHello),
    /// `case end_of_early_data: EndOfEarlyData;`
    EndOfEarlyData,
    /// `case encrypted_extensions: EncryptedExtensions;`
    EncryptedExtensions(EncryptedExtensions),
    /// `case certificate_request: CertificateRequest;`
    CertificateRequest(CertificateRequest),
    /// `case certificate: Certificate;`
    Certificate(Certificate),
    /// `case certificate_verify: CertificateVerify;`
    CertificateVerify(CertificateVerify),
    /// `case finished: Finished;`
    Finished(Finished),
    /// `case new_session_ticket: NewSessionTicket;`
    NewSessionTicket(NewSessionTicket),
    /// `case key_update: KeyUpdate;`
    KeyUpdate(KeyUpdate),
}

/// §4: `select (Handshake.msg_type)`: the body of each type, or `None` if the
/// type has no arm or its body does not meet its structure.
pub open spec fn select_handshake(msg_type: nat, body: Seq<u8>) -> Option<HandshakeBody> {
    if msg_type == ht_client_hello() {
        match read_client_hello(body) { Some(m) => Some(HandshakeBody::ClientHello(m)), None => None }
    } else if msg_type == ht_server_hello() {
        match read_server_hello(body) { Some(m) => Some(HandshakeBody::ServerHello(m)), None => None }
    } else if msg_type == ht_end_of_early_data() {
        // §4.5: struct {} EndOfEarlyData;
        if body.len() == 0 { Some(HandshakeBody::EndOfEarlyData) } else { None }
    } else if msg_type == ht_encrypted_extensions() {
        match read_encrypted_extensions(body) { Some(m) => Some(HandshakeBody::EncryptedExtensions(m)), None => None }
    } else if msg_type == ht_certificate_request() {
        match read_certificate_request(body) { Some(m) => Some(HandshakeBody::CertificateRequest(m)), None => None }
    } else if msg_type == ht_certificate() {
        match read_certificate(body) { Some(m) => Some(HandshakeBody::Certificate(m)), None => None }
    } else if msg_type == ht_certificate_verify() {
        match read_certificate_verify(body) { Some(m) => Some(HandshakeBody::CertificateVerify(m)), None => None }
    } else if msg_type == ht_finished() {
        match read_finished(body) { Some(m) => Some(HandshakeBody::Finished(m)), None => None }
    } else if msg_type == ht_new_session_ticket() {
        match read_new_session_ticket(body) { Some(m) => Some(HandshakeBody::NewSessionTicket(m)), None => None }
    } else if msg_type == ht_key_update() {
        match read_key_update(body) { Some(m) => Some(HandshakeBody::KeyUpdate(m)), None => None }
    } else {
        None
    }
}

/// §4: the header of Handshake, `msg_type` and `uint24 length`.
pub struct HandshakeHeader {
    /// §4 msg_type.
    pub msg_type: nat,
    /// §4 length: "remaining bytes in message".
    pub length: nat,
}

/// §4: the header at the start of `input`, if four bytes are there.
pub open spec fn read_handshake_header(input: Seq<u8>) -> Option<HandshakeHeader> {
    if input.len() < 4 {
        None
    } else {
        Some(HandshakeHeader { msg_type: input[0] as nat, length: read_uint(input.subrange(1, 4), 3) })
    }
}

/// §4: `struct { msg_type; length; select ... } Handshake;`, from exactly its
/// bytes, as (msg_type, body).
pub open spec fn read_handshake(message: Seq<u8>) -> Option<(nat, HandshakeBody)> {
    match read_handshake_header(message) {
        None => None,
        Some(header) =>
            if message.len() != 4 + header.length {
                None
            } else {
                match select_handshake(header.msg_type, message.subrange(4, message.len() as int)) {
                    None => None,
                    Some(body) => Some((header.msg_type, body)),
                }
            },
    }
}

/// §4: the encoded Handshake of the body bytes.
pub open spec fn write_handshake(msg_type: nat, body: Seq<u8>) -> Seq<u8> {
    uint8(msg_type) + uint24(body.len()) + body
}

// --------------------------------------------------------------------------
// §4.1.2 Client Hello.
// --------------------------------------------------------------------------

/// §4.1.2's struct ClientHello.
pub struct ClientHello {
    /// `ProtocolVersion legacy_version = 0x0303;`
    pub legacy_version: nat,
    /// `Random random;`, `opaque Random[32];`
    pub random: Seq<u8>,
    /// `opaque legacy_session_id<0..32>;`
    pub legacy_session_id: Seq<u8>,
    /// `CipherSuite cipher_suites<2..2^16-2>;`, each `uint8 CipherSuite[2]` as a
    /// number.
    pub cipher_suites: Seq<nat>,
    /// `opaque legacy_compression_methods<1..2^8-1>;`
    pub legacy_compression_methods: Seq<u8>,
    /// `Extension extensions<8..2^16-1>;`
    pub extensions: Seq<Extension>,
}

/// Appendix B.4: TLS_CHACHA20_POLY1305_SHA256 {0x13,0x03}, the profile's suite.
pub open spec fn tls_chacha20_poly1305_sha256() -> nat { 0x1303 }

/// §4.1.2: the ClientHello structure, from exactly its bytes.
pub open spec fn read_client_hello(body: Seq<u8>) -> Option<ClientHello> {
    match read_uint_and_random(body) {
        None => None,
        Some((legacy_version, random, rest)) => match read_vector(rest, 0, 32) {
            None => None,
            Some((legacy_session_id, rest)) => match read_vector(rest, 2, 0xfffe) {
                None => None,
                Some((suites, rest)) => match read_uint16_list(suites) {
                    None => None,
                    Some(cipher_suites) => match read_vector(rest, 1, 0xff) {
                        None => None,
                        Some((legacy_compression_methods, rest)) => match read_extensions(rest, 8, 0xffff) {
                            None => None,
                            Some((extensions, rest)) =>
                                if rest.len() != 0 {
                                    None
                                } else {
                                    Some(ClientHello {
                                        legacy_version, random, legacy_session_id, cipher_suites,
                                        legacy_compression_methods, extensions,
                                    })
                                },
                        },
                    },
                },
            },
        },
    }
}

/// The first two fields of both hellos: `legacy_version` and `random`.
pub open spec fn read_uint_and_random(body: Seq<u8>) -> Option<(nat, Seq<u8>, Seq<u8>)> {
    if body.len() < 34 {
        None
    } else {
        Some((read_uint(body, 2), body.subrange(2, 34), body.subrange(34, body.len() as int)))
    }
}

/// §4.1.2: the encoded ClientHello as a Handshake.
pub open spec fn write_client_hello(hello: ClientHello) -> Seq<u8> {
    write_handshake(ht_client_hello(),
        uint16(hello.legacy_version)
            + hello.random
            + write_vector(hello.legacy_session_id, 32)
            + write_vector(write_uint16_list(hello.cipher_suites), 0xfffe)
            + write_vector(hello.legacy_compression_methods, 0xff)
            + write_extensions(hello.extensions))
}

/// The shares of the ClientHello's key_share extension; none if it has none or
/// they do not decode.
pub open spec fn offered_shares(hello: ClientHello) -> Seq<KeyShareEntry> {
    match find_extension(hello.extensions, ext_key_share()) {
        None => seq![],
        Some(data) => match read_key_share_client_hello(data) {
            None => seq![],
            Some(shares) => shares,
        },
    }
}

/// The groups of the ClientHello's supported_groups extension.
pub open spec fn offered_groups(hello: ClientHello) -> Seq<nat> {
    match find_extension(hello.extensions, ext_supported_groups()) {
        None => seq![],
        Some(data) => match read_named_group_list(data) {
            None => seq![],
            Some(groups) => groups,
        },
    }
}

/// The versions of the ClientHello's supported_versions extension.
pub open spec fn offered_versions(hello: ClientHello) -> Seq<nat> {
    match find_extension(hello.extensions, ext_supported_versions()) {
        None => seq![],
        Some(data) => match read_supported_versions_client(data) {
            None => seq![],
            Some(versions) => versions,
        },
    }
}

/// The schemes of the ClientHello's signature_algorithms extension.
pub open spec fn offered_signature_schemes(hello: ClientHello) -> Seq<nat> {
    match find_extension(hello.extensions, ext_signature_algorithms()) {
        None => seq![],
        Some(data) => match read_signature_scheme_list(data) {
            None => seq![],
            Some(schemes) => schemes,
        },
    }
}

/// §4.1.2, §4.2.1, §4.2.3, §4.2.7, §4.2.8, §9.2: what the client's first
/// ClientHello must satisfy in this profile. `schemes` is the parameter of
/// offered signature schemes.
pub open spec fn client_hello_conforms(hello: ClientHello, schemes: Seq<nat>) -> bool {
    let shares = offered_shares(hello);
    // §4.1.2 legacy_version: "MUST be set to 0x0303".
    &&& hello.legacy_version == 0x0303
    // §4.1.2 random: "32 bytes".
    &&& hello.random.len() == 32
    // §4.1.2 legacy_session_id: in compatibility mode "a new 32-byte value",
    // "Otherwise, it MUST be set as a zero-length vector".
    &&& hello.legacy_session_id.len() == 0 || hello.legacy_session_id.len() == 32
    // The profile: one cipher suite.
    &&& hello.cipher_suites == seq![tls_chacha20_poly1305_sha256()]
    // §4.1.2 legacy_compression_methods: "exactly one byte, set to zero".
    &&& hello.legacy_compression_methods == seq![0u8]
    // §4.2: "not more than one extension of the same type".
    &&& !has_duplicate_extension(hello.extensions)
    // §4.2's table: nothing recognized that is not for a ClientHello.
    &&& !any_not_specified(hello.extensions, TableMessage::Ch)
    // §4.2.1: "Implementations of this specification MUST send this extension
    // in the ClientHello containing all versions of TLS which they are prepared
    // to negotiate"; the profile is TLS 1.3 only.
    &&& offered_versions(hello) == seq![tls13_version()]
    // §4.2.3: "Clients which desire the server to authenticate itself via a
    // certificate MUST send the 'signature_algorithms' extension". §9.2 likewise.
    &&& offered_signature_schemes(hello) == schemes
    &&& legacy_schemes_are_last(schemes)
    // §4.2.7 with §9.2 ("it MUST contain ... a 'supported_groups' extension");
    // the profile is X25519 only.
    &&& offered_groups(hello) == seq![group_x25519()]
    // §9.2: "If containing a 'supported_groups' extension, it MUST also contain
    // a 'key_share' extension, and vice versa. An empty KeyShare.client_shares
    // vector is permitted."
    &&& find_extension(hello.extensions, ext_key_share()) is Some
    &&& read_key_share_client_hello(find_extension(hello.extensions, ext_key_share())->0) is Some
    // §4.2.8: shares follow supported_groups' order, one per group, and "32 bytes
    // for X25519" (§4.2.8.2).
    &&& is_subsequence(share_groups(shares), offered_groups(hello))
    &&& has_no_repeats(share_groups(shares))
    &&& shares.len() == 0 || shares[0].key_exchange.len() == 32
    // §4.2.2: "Clients MUST NOT use cookies in their initial ClientHello".
    &&& find_extension(hello.extensions, ext_cookie()) is None
    // Modelling choice 1 of `mod.rs`: no PSK, no early data, no client
    // certificates, and only X.509 certificates (§4.4.2).
    &&& find_extension(hello.extensions, ext_pre_shared_key()) is None
    &&& find_extension(hello.extensions, ext_psk_key_exchange_modes()) is None
    &&& find_extension(hello.extensions, ext_early_data()) is None
    &&& find_extension(hello.extensions, ext_post_handshake_auth()) is None
    &&& find_extension(hello.extensions, ext_client_certificate_type()) is None
    &&& find_extension(hello.extensions, ext_server_certificate_type()) is None
}

/// One ClientHello that meets [`client_hello_conforms`]: the required extensions
/// in the order of §9.2's list, after whatever else the client sends.
/// `share` is its public value, or `None` for "an empty KeyShare.client_shares".
pub open spec fn build_client_hello(random: Seq<u8>, legacy_session_id: Seq<u8>, schemes: Seq<nat>,
    share: Option<Seq<u8>>, other_extensions: Seq<Extension>) -> ClientHello
{
    ClientHello {
        legacy_version: 0x0303,
        random,
        legacy_session_id,
        cipher_suites: seq![tls_chacha20_poly1305_sha256()],
        legacy_compression_methods: seq![0u8],
        extensions: other_extensions + seq![
            Extension {
                extension_type: ext_supported_versions(),
                extension_data: write_supported_versions_client(seq![tls13_version()]),
            },
            Extension {
                extension_type: ext_signature_algorithms(),
                extension_data: write_signature_scheme_list(schemes),
            },
            Extension {
                extension_type: ext_supported_groups(),
                extension_data: write_named_group_list(seq![group_x25519()]),
            },
            Extension {
                extension_type: ext_key_share(),
                extension_data: write_key_share_client_hello(match share {
                    None => seq![],
                    Some(key_exchange) => seq![KeyShareEntry { group: group_x25519(), key_exchange }],
                }),
            },
        ],
    }
}

/// The extensions a second ClientHello may change (§4.1.2), removed, with the
/// order of the rest kept. `key_share` only stays fixed if the HelloRetryRequest
/// supplied none.
pub open spec fn without_retry_changes(extensions: Seq<Extension>) -> Seq<Extension>
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        seq![]
    } else {
        let tail = without_retry_changes(extensions.subrange(1, extensions.len() as int));
        let t = extensions[0].extension_type;
        if t == ext_key_share() || t == ext_cookie() || t == ext_padding() {
            tail
        } else {
            seq![extensions[0]] + tail
        }
    }
}

/// §4.1.2: "the client MUST send the same ClientHello without modification,
/// except as follows", the three of those bullets a client without PSK or early
/// data can reach. §4.2.2 and §4.2.8 say the same of the cookie and key share.
pub open spec fn second_client_hello_conforms(first: ClientHello, retry_extensions: Seq<Extension>, second: ClientHello) -> bool {
    &&& second.legacy_version == first.legacy_version
    &&& second.random == first.random
    &&& second.legacy_session_id == first.legacy_session_id
    &&& second.cipher_suites == first.cipher_suites
    &&& second.legacy_compression_methods == first.legacy_compression_methods
    // Everything else, in the same order. Padding may change ("Optionally adding,
    // removing, or changing the length of the 'padding' extension").
    &&& without_retry_changes(second.extensions) == without_retry_changes(first.extensions)
    // "If a 'key_share' extension was supplied in the HelloRetryRequest, replacing
    // the list of shares with a list containing a single KeyShareEntry from the
    // indicated group."
    &&& match find_extension(retry_extensions, ext_key_share()) {
        None => find_extension(second.extensions, ext_key_share()) == find_extension(first.extensions, ext_key_share()),
        Some(data) => match read_key_share_hello_retry_request(data) {
            None => false,
            Some(selected_group) => share_groups(offered_shares(second)) == seq![selected_group],
        },
    }
    // "Including a 'cookie' extension if one was provided in the HelloRetryRequest."
    // §4.2.2: "the client MUST copy the contents of the extension".
    &&& find_extension(second.extensions, ext_cookie()) == find_extension(retry_extensions, ext_cookie())
}

/// The extensions of a second ClientHello, with key_share's data replaced if
/// `new_key_share` is given.
pub open spec fn replace_key_share(extensions: Seq<Extension>, new_key_share: Option<Seq<u8>>) -> Seq<Extension>
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        seq![]
    } else {
        let tail = replace_key_share(extensions.subrange(1, extensions.len() as int), new_key_share);
        match new_key_share {
            Some(extension_data) =>
                if extensions[0].extension_type == ext_key_share() {
                    seq![Extension { extension_type: ext_key_share(), extension_data }] + tail
                } else {
                    seq![extensions[0]] + tail
                },
            None => seq![extensions[0]] + tail,
        }
    }
}

/// §4.1.2: the second ClientHello this model sends in response to the extensions
/// of a HelloRetryRequest. `public_key` is the new share's public value, used
/// only if the request selected a group. The cookie goes last: "MAY appear in any
/// order" (§4.2), and only pre_shared_key's place is fixed, which the profile
/// does not offer.
pub open spec fn second_client_hello(first: ClientHello, retry_extensions: Seq<Extension>, public_key: Seq<u8>) -> ClientHello {
    let new_key_share = match find_extension(retry_extensions, ext_key_share()) {
        None => None,
        Some(data) => match read_key_share_hello_retry_request(data) {
            None => None,
            Some(selected_group) => Some(write_key_share_client_hello(
                seq![KeyShareEntry { group: selected_group, key_exchange: public_key }])),
        },
    };
    let replaced = replace_key_share(first.extensions, new_key_share);
    ClientHello {
        extensions: match find_extension(retry_extensions, ext_cookie()) {
            None => replaced,
            Some(extension_data) =>
                replaced + seq![Extension { extension_type: ext_cookie(), extension_data }],
        },
        ..first
    }
}

// --------------------------------------------------------------------------
// §4.1.3 Server Hello.
// --------------------------------------------------------------------------

/// §4.1.3's struct ServerHello, which HelloRetryRequest shares.
pub struct ServerHello {
    /// `ProtocolVersion legacy_version = 0x0303;`
    pub legacy_version: nat,
    /// `Random random;`
    pub random: Seq<u8>,
    /// `opaque legacy_session_id_echo<0..32>;`
    pub legacy_session_id_echo: Seq<u8>,
    /// `CipherSuite cipher_suite;`
    pub cipher_suite: nat,
    /// `uint8 legacy_compression_method = 0;`
    pub legacy_compression_method: nat,
    /// `Extension extensions<6..2^16-1>;`
    pub extensions: Seq<Extension>,
}

/// The fields of a server's hello before `extensions`, and the bytes after.
pub open spec fn read_server_hello_prefix(body: Seq<u8>) -> Option<(ServerHello, Seq<u8>)> {
    match read_uint_and_random(body) {
        None => None,
        Some((legacy_version, random, rest)) => match read_vector(rest, 0, 32) {
            None => None,
            Some((legacy_session_id_echo, rest)) =>
                if rest.len() < 3 {
                    None
                } else {
                    Some((ServerHello {
                        legacy_version,
                        random,
                        legacy_session_id_echo,
                        cipher_suite: read_uint(rest, 2),
                        legacy_compression_method: rest[2] as nat,
                        extensions: seq![],
                    }, rest.subrange(3, rest.len() as int)))
                },
        },
    }
}

/// §4.1.3: the ServerHello structure, from exactly its bytes.
pub open spec fn read_server_hello(body: Seq<u8>) -> Option<ServerHello> {
    match read_server_hello_prefix(body) {
        None => None,
        Some((hello, rest)) => match read_extensions(rest, 6, 0xffff) {
            None => None,
            Some((extensions, rest)) =>
                if rest.len() == 0 { Some(ServerHello { extensions, ..hello }) } else { None },
        },
    }
}

/// A server's hello of any version, for version detection only: the extensions
/// are optional and have no floor. See the modelling choices.
pub open spec fn read_server_hello_any_version(body: Seq<u8>) -> Option<ServerHello> {
    match read_server_hello_prefix(body) {
        None => None,
        Some((hello, rest)) =>
            if rest.len() == 0 {
                Some(hello)
            } else {
                match read_extensions(rest, 0, 0xffff) {
                    None => None,
                    Some((extensions, rest)) =>
                        if rest.len() == 0 { Some(ServerHello { extensions, ..hello }) } else { None },
                }
            },
    }
}

/// §4.1.3: the encoded ServerHello as a Handshake.
pub open spec fn write_server_hello(hello: ServerHello) -> Seq<u8> {
    write_handshake(ht_server_hello(),
        uint16(hello.legacy_version)
            + hello.random
            + write_vector(hello.legacy_session_id_echo, 32)
            + uint16(hello.cipher_suite)
            + uint8(hello.legacy_compression_method)
            + write_extensions(hello.extensions))
}

/// §4.1.3: 'Random set to the special value of the SHA-256 of
/// "HelloRetryRequest"'.
pub open spec fn hello_retry_request_random() -> Seq<u8> {
    seq![0xCFu8, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91,
         0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E, 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C]
}

/// §4.1.3: the last 8 bytes when "negotiating TLS 1.2".
pub open spec fn downgrade_tls12() -> Seq<u8> {
    seq![0x44u8, 0x4F, 0x57, 0x4E, 0x47, 0x52, 0x44, 0x01]
}

/// §4.1.3: the last 8 bytes when "negotiating TLS 1.1 or below".
pub open spec fn downgrade_tls11() -> Seq<u8> {
    seq![0x44u8, 0x4F, 0x57, 0x4E, 0x47, 0x52, 0x44, 0x00]
}

/// §4.1.3: "TLS 1.3 clients receiving a ServerHello indicating TLS 1.2 or below
/// MUST check that the last 8 bytes are not equal to either of these values."
pub open spec fn has_downgrade_sentinel(random: Seq<u8>) -> bool {
    random.len() == 32 && {
        let last_8 = random.subrange(24, 32);
        last_8 == downgrade_tls12() || last_8 == downgrade_tls11()
    }
}

/// §4.1.3 and Appendix D.1: a server's hello with no supported_versions. Such a
/// message cannot continue, since this profile offers only TLS 1.3: the list
/// always has an entry.
pub open spec fn older_server_hello_failures(hello: ServerHello) -> Seq<ClientError> {
    if hello.legacy_version <= 0x0303 {
        // §4.1.3: indicating TLS 1.2 or below.
        fails_if(has_downgrade_sentinel(hello.random), ClientError::DowngradeSentinel)
            // D.1: "not supported by the client"; D.5 for 0x0300.
            + seq![ClientError::VersionNotSupported]
    } else {
        // §4.1.3: "All TLS 1.3 ServerHello messages MUST contain the
        // 'supported_versions' extension."
        seq![ClientError::SupportedVersionsMissing]
    }
}

/// §4.2.1: "If the 'supported_versions' extension in the ServerHello contains a
/// version not offered by the client or contains a version prior to TLS 1.3, the
/// client MUST abort the handshake with an 'illegal_parameter' alert." A body
/// that is not one uint16 is a decode failure. The second list entry never fires
/// in this profile, whose only offer is 0x0304, and is kept for the text's sake.
pub open spec fn selected_version_failures(hello: ClientHello, data: Seq<u8>) -> Seq<ClientError> {
    match read_supported_versions_server(data) {
        None => seq![ClientError::Malformed],
        Some(selected_version) =>
            fails_if(!list_has(offered_versions(hello), selected_version), ClientError::SelectedVersionNotAcceptable)
                + fails_if(selected_version < tls13_version(), ClientError::SelectedVersionNotAcceptable),
    }
}

/// What a client keeps of a HelloRetryRequest to check the ServerHello against.
pub struct RetryRecord {
    /// §4.1.4: "the same as that in the HelloRetryRequest".
    pub cipher_suite: nat,
    /// §4.1.4: "The value of selected_version in the HelloRetryRequest
    /// 'supported_versions' extension MUST be retained in the ServerHello".
    pub selected_version: nat,
    /// §4.2.8: "the selected NamedGroup in the ServerHello is the same as that in
    /// the HelloRetryRequest", if that had a key_share.
    pub selected_group: Option<nat>,
}

/// §4.1.3: the fields both a ServerHello and a HelloRetryRequest are checked on
/// ("legacy_session_id_echo, cipher_suite, and legacy_compression_method").
pub open spec fn hello_field_failures(sent: ClientHello, hello: ServerHello) -> Seq<ClientError> {
    fails_if(hello.legacy_session_id_echo != sent.legacy_session_id, ClientError::SessionIdEchoMismatch)
        + fails_if(!list_has(sent.cipher_suites, hello.cipher_suite), ClientError::CipherSuiteNotOffered)
        + fails_if(hello.legacy_compression_method != 0, ClientError::CompressionMethodNotZero)
}

/// §4.2.8: the checks on a ServerHello's key_share.
pub open spec fn server_share_failures(sent: ClientHello, hello: ServerHello, retry: Option<RetryRecord>) -> Seq<ClientError> {
    match find_extension(hello.extensions, ext_key_share()) {
        // §4.1.3, §9.2. PSK is not offered, so (EC)DHE is the only exchange.
        None => seq![ClientError::KeyShareMissing],
        Some(data) => match read_key_share_server_hello(data) {
            None => seq![ClientError::Malformed],
            Some(server_share) =>
                fails_if(!list_has(share_groups(offered_shares(sent)), server_share.group),
                    ClientError::ServerShareGroupNotOffered)
                + match retry {
                    Some(RetryRecord { selected_group: Some(selected_group), .. }) =>
                        fails_if(server_share.group != selected_group, ClientError::ServerShareGroupChanged),
                    _ => seq![],
                }
                + fails_if(server_share.group == group_x25519() && server_share.key_exchange.len() != 32, ClientError::ServerShareWrongLength),
        },
    }
}

/// §4.1.3, §4.1.4, §4.2.1, §4.2.8: every failure of a ServerHello that carries
/// supported_versions, given what was sent, in the order of the text.
pub open spec fn server_hello_failures(sent: ClientHello, hello: ServerHello, retry: Option<RetryRecord>) -> Seq<ClientError> {
    // D.5: "Any endpoint receiving a Hello message with ...
    // ServerHello.legacy_version set to 0x0300 MUST abort".
    fails_if(hello.legacy_version == 0x0300, ClientError::VersionNotSupported)
    // §4.2.1: "Clients MUST check for this extension prior to processing the
    // rest of the ServerHello". The caller knows it is present.
    + match find_extension(hello.extensions, ext_supported_versions()) {
        None => seq![ClientError::SupportedVersionsMissing],
        Some(data) => selected_version_failures(sent, data)
            // §4.1.4: "a client MUST abort ... if the value changes."
            + match (retry, read_supported_versions_server(data)) {
                (Some(r), Some(selected_version)) =>
                    fails_if(selected_version != r.selected_version, ClientError::SelectedVersionChanged),
                _ => seq![],
            },
    }
    // §4.1.3.
    + hello_field_failures(sent, hello)
    // §4.1.4: "clients MUST check that the cipher suite supplied in the ServerHello
    // is the same as that in the HelloRetryRequest".
    + match retry {
        Some(r) => fails_if(hello.cipher_suite != r.cipher_suite, ClientError::CipherSuiteChanged),
        None => seq![],
    }
    // §4.2. "ServerHello MUST only include extensions which are required to
    // establish the cryptographic context".
    + response_block_failures(hello.extensions, extension_types(sent.extensions), TableMessage::Sh)
    // §4.2.8.
    + server_share_failures(sent, hello, retry)
    // §4.2: the bodies of the block (`extension_bodies`), pre_shared_key's among them.
    + extension_body_failures(sent.extensions, hello.extensions, TableMessage::Sh)
}

// --------------------------------------------------------------------------
// §4.1.4 Hello Retry Request.
// --------------------------------------------------------------------------

/// §4.1.3: "if it matches this value, process it as described in Section 4.1.4".
pub open spec fn is_hello_retry_request(hello: ServerHello) -> bool {
    hello.random == hello_retry_request_random()
}

/// §4.1.4: "Clients MUST abort the handshake with an 'illegal_parameter' alert if
/// the HelloRetryRequest would not result in any change in the ClientHello." In a
/// client with no PSK or early data, the only changes it can cause are §4.1.2's
/// key_share and cookie bullets.
pub open spec fn retry_changes_nothing(hello: ServerHello) -> bool {
    find_extension(hello.extensions, ext_key_share()) is None
    && find_extension(hello.extensions, ext_cookie()) is None
}

/// §4.1.4, §4.2.2, §4.2.8: every failure of a first HelloRetryRequest, in the
/// order of §4.1.4: "check the legacy_version, legacy_session_id_echo,
/// cipher_suite, and legacy_compression_method as specified in Section 4.1.3 and
/// then process the extensions, starting with determining the version using
/// 'supported_versions'". (A second one is `ClientError::SecondHelloRetryRequest`,
/// which the state machine checks first.)
pub open spec fn hello_retry_request_failures(sent: ClientHello, hello: ServerHello) -> Seq<ClientError> {
    fails_if(hello.legacy_version == 0x0300, ClientError::VersionNotSupported)
    + fails_if(hello.legacy_version != 0x0303, ClientError::RetryLegacyVersion)
    + hello_field_failures(sent, hello)
    // §4.1.4: "The server's extensions MUST contain 'supported_versions'."
    + match find_extension(hello.extensions, ext_supported_versions()) {
        None => seq![ClientError::SupportedVersionsMissing],
        Some(data) => selected_version_failures(sent, data),
    }
    // §4.1.4: "MUST NOT contain any extensions that were not first offered by the
    // client in its ClientHello, with the exception of optionally the 'cookie'".
    + response_block_failures(hello.extensions, extension_types(sent.extensions), TableMessage::Hrr)
    // §4.2.2: `opaque cookie<1..2^16-1>`.
    + match find_extension(hello.extensions, ext_cookie()) {
        None => seq![],
        Some(data) => fails_if(read_cookie(data) is None, ClientError::Malformed),
    }
    // §4.2.8: "the client MUST verify that (1) ... (2) ...".
    + match find_extension(hello.extensions, ext_key_share()) {
        None => seq![],
        Some(data) => match read_key_share_hello_retry_request(data) {
            None => seq![ClientError::Malformed],
            Some(selected_group) =>
                fails_if(!list_has(offered_groups(sent), selected_group), ClientError::RetryGroupNotOffered)
                + fails_if(list_has(share_groups(offered_shares(sent)), selected_group), ClientError::RetryGroupAlreadyShared),
        },
    }
    + fails_if(retry_changes_nothing(hello), ClientError::RetryWithoutChange)
}

/// What a client keeps of a HelloRetryRequest that passed its checks.
pub open spec fn retry_record(hello: ServerHello) -> RetryRecord {
    RetryRecord {
        cipher_suite: hello.cipher_suite,
        selected_version: match find_extension(hello.extensions, ext_supported_versions()) {
            Some(data) => match read_supported_versions_server(data) {
                Some(selected_version) => selected_version,
                None => 0,
            },
            None => 0,
        },
        selected_group: match find_extension(hello.extensions, ext_key_share()) {
            Some(data) => read_key_share_hello_retry_request(data),
            None => None,
        },
    }
}

} // verus!
