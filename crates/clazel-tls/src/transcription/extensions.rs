//! RFC 8446 §4.2, extensions, as far as a client needs them.
//!
//! Modelling choices:
//! - The table of §4.2 is transcribed row for row ([`extension_table`]).
//!   "recognizes" in "an extension which it recognizes" is read as "has a row
//!   in that table": the RFC cannot mean a smaller set for a client that
//!   implements the mandatory extensions of §9.2, since the rule protects the
//!   table itself, and a larger set would be some other RFC's table.
//! - `ExtensionType` is a `nat`, so an unknown one survives decoding: "Servers
//!   MUST ignore unrecognized extensions"; "Clients MUST ignore unrecognized
//!   extensions" (§4.3.2, §4.6.1). In a response the same extension falls
//!   under "MUST NOT send extension responses if the remote endpoint did not
//!   send the corresponding extension requests", since the client cannot have
//!   requested what it does not recognize.
//! - **§4.2 against §6.2.** §4.2 says an extension "which it recognizes and
//!   which is not specified for the message" is `illegal_parameter`. §6.2 says
//!   `unsupported_extension` is "Sent by endpoints receiving any handshake
//!   message containing an extension known to be prohibited for inclusion in
//!   the given handshake message". The specific MUST of §4.2, which §4.3.1
//!   repeats, is followed; see `docs/ERRATA.md`. If an extension is both not
//!   specified for the message and not offered, both are in the failure list,
//!   table rule first.
//! - This file decodes the contents the client acts on: supported_versions,
//!   cookie, signature_algorithms, supported_groups, key_share. The syntax of
//!   every body a server may send, in each message §4.2's table allows it in,
//!   including the other RFCs' extensions, is in `extension_bodies`; RFC 6066
//!   §3's server_name is in `server_name`. What the contents of status_request
//!   and signed_certificate_timestamp mean is certificate validation's.
//! - supported_groups in EncryptedExtensions is not acted on ("Clients MUST NOT
//!   act upon any information found in 'supported_groups' prior to successful
//!   completion of the handshake"); its syntax is checked
//!   (`extension_bodies`).
//! - signature_algorithms_cert is the certificate validator's concern, with the
//!   rest of chain validation; the model only carries it in the offer.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::presentation::*;

verus! {

/// §4.2: `struct { ExtensionType extension_type; opaque extension_data<0..2^16-1>; } Extension;`
pub struct Extension {
    /// §4.2 extension_type.
    pub extension_type: nat,
    /// §4.2 extension_data.
    pub extension_data: Seq<u8>,
}

/// §4.2 server_name(0).
pub open spec fn ext_server_name() -> nat { 0 }
/// §4.2 max_fragment_length(1).
pub open spec fn ext_max_fragment_length() -> nat { 1 }
/// §4.2 status_request(5).
pub open spec fn ext_status_request() -> nat { 5 }
/// §4.2 supported_groups(10).
pub open spec fn ext_supported_groups() -> nat { 10 }
/// §4.2 signature_algorithms(13).
pub open spec fn ext_signature_algorithms() -> nat { 13 }
/// §4.2 use_srtp(14).
pub open spec fn ext_use_srtp() -> nat { 14 }
/// §4.2 heartbeat(15).
pub open spec fn ext_heartbeat() -> nat { 15 }
/// §4.2 application_layer_protocol_negotiation(16).
pub open spec fn ext_application_layer_protocol_negotiation() -> nat { 16 }
/// §4.2 signed_certificate_timestamp(18).
pub open spec fn ext_signed_certificate_timestamp() -> nat { 18 }
/// §4.2 client_certificate_type(19).
pub open spec fn ext_client_certificate_type() -> nat { 19 }
/// §4.2 server_certificate_type(20).
pub open spec fn ext_server_certificate_type() -> nat { 20 }
/// §4.2 padding(21).
pub open spec fn ext_padding() -> nat { 21 }
/// §4.2 pre_shared_key(41).
pub open spec fn ext_pre_shared_key() -> nat { 41 }
/// §4.2 early_data(42).
pub open spec fn ext_early_data() -> nat { 42 }
/// §4.2 supported_versions(43).
pub open spec fn ext_supported_versions() -> nat { 43 }
/// §4.2 cookie(44).
pub open spec fn ext_cookie() -> nat { 44 }
/// §4.2 psk_key_exchange_modes(45).
pub open spec fn ext_psk_key_exchange_modes() -> nat { 45 }
/// §4.2 certificate_authorities(47).
pub open spec fn ext_certificate_authorities() -> nat { 47 }
/// §4.2 oid_filters(48).
pub open spec fn ext_oid_filters() -> nat { 48 }
/// §4.2 post_handshake_auth(49).
pub open spec fn ext_post_handshake_auth() -> nat { 49 }
/// §4.2 signature_algorithms_cert(50).
pub open spec fn ext_signature_algorithms_cert() -> nat { 50 }
/// §4.2 key_share(51).
pub open spec fn ext_key_share() -> nat { 51 }

/// §4.2's notation: CH, SH, EE, CT, CR, NST, HRR.
pub enum TableMessage {
    /// CH (ClientHello).
    Ch,
    /// SH (ServerHello).
    Sh,
    /// EE (EncryptedExtensions).
    Ee,
    /// CT (Certificate).
    Ct,
    /// CR (CertificateRequest).
    Cr,
    /// NST (NewSessionTicket).
    Nst,
    /// HRR (HelloRetryRequest).
    Hrr,
}

/// §4.2's table: the messages where a given extension may appear; `None` if it
/// has no row, which is what "recognizes" means here.
pub open spec fn extension_table(extension_type: nat) -> Option<Seq<TableMessage>> {
    let (ch, sh, ee, ct, cr, nst, hrr) = (TableMessage::Ch, TableMessage::Sh, TableMessage::Ee,
        TableMessage::Ct, TableMessage::Cr, TableMessage::Nst, TableMessage::Hrr);
    if extension_type == ext_server_name() { Some(seq![ch, ee]) }
    else if extension_type == ext_max_fragment_length() { Some(seq![ch, ee]) }
    else if extension_type == ext_status_request() { Some(seq![ch, cr, ct]) }
    else if extension_type == ext_supported_groups() { Some(seq![ch, ee]) }
    else if extension_type == ext_signature_algorithms() { Some(seq![ch, cr]) }
    else if extension_type == ext_use_srtp() { Some(seq![ch, ee]) }
    else if extension_type == ext_heartbeat() { Some(seq![ch, ee]) }
    else if extension_type == ext_application_layer_protocol_negotiation() { Some(seq![ch, ee]) }
    else if extension_type == ext_signed_certificate_timestamp() { Some(seq![ch, cr, ct]) }
    else if extension_type == ext_client_certificate_type() { Some(seq![ch, ee]) }
    else if extension_type == ext_server_certificate_type() { Some(seq![ch, ee]) }
    else if extension_type == ext_padding() { Some(seq![ch]) }
    else if extension_type == ext_key_share() { Some(seq![ch, sh, hrr]) }
    else if extension_type == ext_pre_shared_key() { Some(seq![ch, sh]) }
    else if extension_type == ext_psk_key_exchange_modes() { Some(seq![ch]) }
    else if extension_type == ext_early_data() { Some(seq![ch, ee, nst]) }
    else if extension_type == ext_cookie() { Some(seq![ch, hrr]) }
    else if extension_type == ext_supported_versions() { Some(seq![ch, sh, hrr]) }
    else if extension_type == ext_certificate_authorities() { Some(seq![ch, cr]) }
    else if extension_type == ext_oid_filters() { Some(seq![cr]) }
    else if extension_type == ext_post_handshake_auth() { Some(seq![ch]) }
    else if extension_type == ext_signature_algorithms_cert() { Some(seq![ch, cr]) }
    else { None }
}

/// §4.2: "an extension which it recognizes and which is not specified for the
/// message in which it appears".
pub open spec fn recognized_but_not_specified(extension_type: nat, message: TableMessage) -> bool {
    match extension_table(extension_type) {
        None => false,
        Some(messages) => !list_has(messages, message),
    }
}

/// The extensions of a block, decoded from the body of `Extension
/// extensions<..>`.
pub open spec fn read_extension_list(body: Seq<u8>) -> Option<Seq<Extension>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else if body.len() < 4 {
        None
    } else {
        let extension_type = read_uint(body, 2);
        match read_vector(body.subrange(2, body.len() as int), 0, 0xffff) {
            None => None,
            Some((extension_data, _)) =>
                if body.len() < 4 + extension_data.len() {
                    None
                } else {
                    match read_extension_list(body.subrange((4 + extension_data.len()) as int, body.len() as int)) {
                        None => None,
                        Some(tail) => Some(seq![Extension { extension_type, extension_data }] + tail),
                    }
                },
        }
    }
}

/// `Extension extensions<floor..ceiling>` at the start of `input`, with the bytes
/// after it. The ceiling is 2^16-1 or 2^16-2, both a two-byte length.
pub open spec fn read_extensions(input: Seq<u8>, floor: nat, ceiling: nat) -> Option<(Seq<Extension>, Seq<u8>)> {
    match read_vector(input, floor, ceiling) {
        None => None,
        Some((body, rest)) => match read_extension_list(body) {
            None => None,
            Some(extensions) => Some((extensions, rest)),
        },
    }
}

/// The encoded elements of an extension block.
pub open spec fn write_extension_list(extensions: Seq<Extension>) -> Seq<u8>
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        seq![]
    } else {
        uint16(extensions[0].extension_type)
            + write_vector(extensions[0].extension_data, 0xffff)
            + write_extension_list(extensions.subrange(1, extensions.len() as int))
    }
}

/// The encoded `Extension extensions<..>` with a two-byte length.
pub open spec fn write_extensions(extensions: Seq<Extension>) -> Seq<u8> {
    write_vector(write_extension_list(extensions), 0xffff)
}

/// The data of the first extension of the type. A second one is a failure of
/// its own ([`has_duplicate_extension`]).
pub open spec fn find_extension(extensions: Seq<Extension>, extension_type: nat) -> Option<Seq<u8>>
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        None
    } else if extensions[0].extension_type == extension_type {
        Some(extensions[0].extension_data)
    } else {
        find_extension(extensions.subrange(1, extensions.len() as int), extension_type)
    }
}

/// The types of an extension block, in order.
pub open spec fn extension_types(extensions: Seq<Extension>) -> Seq<nat>
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        seq![]
    } else {
        seq![extensions[0].extension_type] + extension_types(extensions.subrange(1, extensions.len() as int))
    }
}

/// §4.2: "There MUST NOT be more than one extension of the same type in a given
/// extension block."
pub open spec fn has_duplicate_extension(extensions: Seq<Extension>) -> bool
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        false
    } else {
        let tail = extensions.subrange(1, extensions.len() as int);
        list_has(extension_types(tail), extensions[0].extension_type) || has_duplicate_extension(tail)
    }
}

/// Whether any extension of the block breaks §4.2's table rule.
pub open spec fn any_not_specified(extensions: Seq<Extension>, message: TableMessage) -> bool
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        false
    } else {
        recognized_but_not_specified(extensions[0].extension_type, message)
            || any_not_specified(extensions.subrange(1, extensions.len() as int), message)
    }
}

/// §4.2: whether any response of the block has no request among `offered`.
/// "with the exception of the 'cookie' extension in the HelloRetryRequest".
pub open spec fn any_not_offered(extensions: Seq<Extension>, offered: Seq<nat>, message: TableMessage) -> bool
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        false
    } else {
        let exempt = message == TableMessage::Hrr && extensions[0].extension_type == ext_cookie();
        (!exempt && !list_has(offered, extensions[0].extension_type))
            || any_not_offered(extensions.subrange(1, extensions.len() as int), offered, message)
    }
}

/// §4.2's two rules on any extension block a client receives.
pub open spec fn block_rules_failures(extensions: Seq<Extension>, message: TableMessage) -> Seq<ClientError> {
    fails_if(has_duplicate_extension(extensions), ClientError::DuplicateExtension)
        + fails_if(any_not_specified(extensions, message), ClientError::ExtensionNotSpecifiedForMessage)
}

/// §4.2's rules on a block of *responses* to `offered`: ServerHello,
/// HelloRetryRequest, EncryptedExtensions and Certificate. (A
/// CertificateRequest's and a NewSessionTicket's are requests and "unsolicited
/// extensions", and their unrecognized ones are ignored.)
pub open spec fn response_block_failures(extensions: Seq<Extension>, offered: Seq<nat>, message: TableMessage) -> Seq<ClientError> {
    block_rules_failures(extensions, message)
        + fails_if(any_not_offered(extensions, offered, message), ClientError::ExtensionNotOffered)
}

// --------------------------------------------------------------------------
// §4.2.1 Supported Versions.
// --------------------------------------------------------------------------

/// §4.2.1: TLS 1.3's version value.
pub open spec fn tls13_version() -> nat { 0x0304 }

/// §4.2.1: `ProtocolVersion versions<2..254>` of a ClientHello.
pub open spec fn read_supported_versions_client(data: Seq<u8>) -> Option<Seq<nat>> {
    match read_vector(data, 2, 254) {
        Some((body, rest)) => if rest.len() == 0 { read_uint16_list(body) } else { None },
        None => None,
    }
}

/// §4.2.1: the encoded `versions<2..254>`.
pub open spec fn write_supported_versions_client(versions: Seq<nat>) -> Seq<u8> {
    write_vector(write_uint16_list(versions), 254)
}

/// §4.2.1: `ProtocolVersion selected_version` of a ServerHello or a
/// HelloRetryRequest.
pub open spec fn read_supported_versions_server(data: Seq<u8>) -> Option<nat> {
    if data.len() == 2 { Some(read_uint(data, 2)) } else { None }
}

// --------------------------------------------------------------------------
// §4.2.2 Cookie.
// --------------------------------------------------------------------------

/// §4.2.2: `struct { opaque cookie<1..2^16-1>; } Cookie;`, its body.
pub open spec fn read_cookie(data: Seq<u8>) -> Option<Seq<u8>> {
    match read_vector(data, 1, 0xffff) {
        Some((cookie, rest)) => if rest.len() == 0 { Some(cookie) } else { None },
        None => None,
    }
}

// --------------------------------------------------------------------------
// §4.2.3 Signature Algorithms.
// --------------------------------------------------------------------------

/// §4.2.3 rsa_pkcs1_sha256(0x0401).
pub open spec fn rsa_pkcs1_sha256() -> nat { 0x0401 }
/// §4.2.3 rsa_pkcs1_sha384(0x0501).
pub open spec fn rsa_pkcs1_sha384() -> nat { 0x0501 }
/// §4.2.3 rsa_pkcs1_sha512(0x0601).
pub open spec fn rsa_pkcs1_sha512() -> nat { 0x0601 }
/// §4.2.3 ecdsa_secp256r1_sha256(0x0403).
pub open spec fn ecdsa_secp256r1_sha256() -> nat { 0x0403 }
/// §4.2.3 ecdsa_secp384r1_sha384(0x0503).
pub open spec fn ecdsa_secp384r1_sha384() -> nat { 0x0503 }
/// §4.2.3 ecdsa_secp521r1_sha512(0x0603).
pub open spec fn ecdsa_secp521r1_sha512() -> nat { 0x0603 }
/// §4.2.3 rsa_pss_rsae_sha256(0x0804).
pub open spec fn rsa_pss_rsae_sha256() -> nat { 0x0804 }
/// §4.2.3 rsa_pss_rsae_sha384(0x0805).
pub open spec fn rsa_pss_rsae_sha384() -> nat { 0x0805 }
/// §4.2.3 rsa_pss_rsae_sha512(0x0806).
pub open spec fn rsa_pss_rsae_sha512() -> nat { 0x0806 }
/// §4.2.3 ed25519(0x0807).
pub open spec fn ed25519() -> nat { 0x0807 }
/// §4.2.3 ed448(0x0808).
pub open spec fn ed448() -> nat { 0x0808 }
/// §4.2.3 rsa_pss_pss_sha256(0x0809).
pub open spec fn rsa_pss_pss_sha256() -> nat { 0x0809 }
/// §4.2.3 rsa_pss_pss_sha384(0x080a).
pub open spec fn rsa_pss_pss_sha384() -> nat { 0x080a }
/// §4.2.3 rsa_pss_pss_sha512(0x080b).
pub open spec fn rsa_pss_pss_sha512() -> nat { 0x080b }
/// §4.2.3 rsa_pkcs1_sha1(0x0201).
pub open spec fn rsa_pkcs1_sha1() -> nat { 0x0201 }
/// §4.2.3 ecdsa_sha1(0x0203).
pub open spec fn ecdsa_sha1() -> nat { 0x0203 }

/// §4.2.3: the "Legacy algorithms": "SHA-1 ... with either (1) RSA using
/// RSASSA-PKCS1-v1_5 or (2) ECDSA".
pub open spec fn is_legacy_scheme(scheme: nat) -> bool {
    scheme == rsa_pkcs1_sha1() || scheme == ecdsa_sha1()
}

/// §4.2.3: "These values refer solely to signatures which appear in
/// certificates ... and are not defined for use in signed TLS handshake
/// messages" (RSASSA-PKCS1-v1_5 and the legacy algorithms); §4.4.3 repeats it
/// for CertificateVerify.
pub open spec fn scheme_refers_solely_to_certificates(scheme: nat) -> bool {
    scheme == rsa_pkcs1_sha256() || scheme == rsa_pkcs1_sha384() || scheme == rsa_pkcs1_sha512()
        || is_legacy_scheme(scheme)
}

/// §4.2.3: `struct { SignatureScheme supported_signature_algorithms<2..2^16-2>; } SignatureSchemeList;`
pub open spec fn read_signature_scheme_list(data: Seq<u8>) -> Option<Seq<nat>> {
    match read_vector(data, 2, 0xfffe) {
        Some((body, rest)) => if rest.len() == 0 { read_uint16_list(body) } else { None },
        None => None,
    }
}

/// §4.2.3: the encoded SignatureSchemeList.
pub open spec fn write_signature_scheme_list(schemes: Seq<nat>) -> Seq<u8> {
    write_vector(write_uint16_list(schemes), 0xfffe)
}

/// §4.2.3: "Clients offering these values MUST list them as the lowest priority
/// (listed after all other algorithms in SignatureSchemeList)".
pub open spec fn legacy_schemes_are_last(schemes: Seq<nat>) -> bool
    decreases schemes.len(),
{
    if schemes.len() == 0 {
        true
    } else {
        let tail = schemes.subrange(1, schemes.len() as int);
        (is_legacy_scheme(schemes[0]) ==> all_legacy(tail)) && legacy_schemes_are_last(tail)
    }
}

/// Whether every scheme of the list is a legacy one.
pub open spec fn all_legacy(schemes: Seq<nat>) -> bool
    decreases schemes.len(),
{
    if schemes.len() == 0 {
        true
    } else {
        is_legacy_scheme(schemes[0]) && all_legacy(schemes.subrange(1, schemes.len() as int))
    }
}

// --------------------------------------------------------------------------
// §4.2.7 Supported Groups.
// --------------------------------------------------------------------------

/// §4.2.7 x25519(0x001D). The one group of the profile. The enum's others are
/// values a peer may name, and need no name here.
pub open spec fn group_x25519() -> nat { 0x001D }

/// §4.2.7: `struct { NamedGroup named_group_list<2..2^16-1>; } NamedGroupList;`
pub open spec fn read_named_group_list(data: Seq<u8>) -> Option<Seq<nat>> {
    match read_vector(data, 2, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_uint16_list(body) } else { None },
        None => None,
    }
}

/// §4.2.7: the encoded NamedGroupList.
pub open spec fn write_named_group_list(groups: Seq<nat>) -> Seq<u8> {
    write_vector(write_uint16_list(groups), 0xffff)
}

// --------------------------------------------------------------------------
// §4.2.8 Key Share.
// --------------------------------------------------------------------------

/// §4.2.8: `struct { NamedGroup group; opaque key_exchange<1..2^16-1>; } KeyShareEntry;`
pub struct KeyShareEntry {
    /// §4.2.8 group.
    pub group: nat,
    /// §4.2.8 key_exchange.
    pub key_exchange: Seq<u8>,
}

/// §4.2.8: one KeyShareEntry at the start of `input`, with the bytes after it.
pub open spec fn read_key_share_entry(input: Seq<u8>) -> Option<(KeyShareEntry, Seq<u8>)> {
    if input.len() < 2 {
        None
    } else {
        match read_vector(input.subrange(2, input.len() as int), 1, 0xffff) {
            None => None,
            Some((key_exchange, rest)) =>
                Some((KeyShareEntry { group: read_uint(input, 2), key_exchange }, rest)),
        }
    }
}

/// The body of `KeyShareEntry client_shares<0..2^16-1>` as its entries.
pub open spec fn read_key_share_list(body: Seq<u8>) -> Option<Seq<KeyShareEntry>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else if body.len() < 4 {
        None
    } else {
        let width = read_uint(body.subrange(2, body.len() as int), 2);
        if width < 1 || body.len() < 4 + width {
            None
        } else {
            let entry = KeyShareEntry { group: read_uint(body, 2), key_exchange: body.subrange(4, (4 + width) as int) };
            match read_key_share_list(body.subrange((4 + width) as int, body.len() as int)) {
                None => None,
                Some(tail) => Some(seq![entry] + tail),
            }
        }
    }
}

/// §4.2.8: KeyShareClientHello, `struct { KeyShareEntry client_shares<0..2^16-1>; }`.
pub open spec fn read_key_share_client_hello(data: Seq<u8>) -> Option<Seq<KeyShareEntry>> {
    match read_vector(data, 0, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_key_share_list(body) } else { None },
        None => None,
    }
}

/// §4.2.8: the encoded elements of `client_shares`.
pub open spec fn write_key_share_list(shares: Seq<KeyShareEntry>) -> Seq<u8>
    decreases shares.len(),
{
    if shares.len() == 0 {
        seq![]
    } else {
        uint16(shares[0].group) + write_vector(shares[0].key_exchange, 0xffff)
            + write_key_share_list(shares.subrange(1, shares.len() as int))
    }
}

/// §4.2.8: the encoded KeyShareClientHello.
pub open spec fn write_key_share_client_hello(shares: Seq<KeyShareEntry>) -> Seq<u8> {
    write_vector(write_key_share_list(shares), 0xffff)
}

/// §4.2.8: KeyShareHelloRetryRequest, `struct { NamedGroup selected_group; }`.
pub open spec fn read_key_share_hello_retry_request(data: Seq<u8>) -> Option<nat> {
    if data.len() == 2 { Some(read_uint(data, 2)) } else { None }
}

/// §4.2.8: KeyShareServerHello, `struct { KeyShareEntry server_share; }`.
pub open spec fn read_key_share_server_hello(data: Seq<u8>) -> Option<KeyShareEntry> {
    match read_key_share_entry(data) {
        Some((server_share, rest)) => if rest.len() == 0 { Some(server_share) } else { None },
        None => None,
    }
}

/// The groups of a list of key shares, in order.
pub open spec fn share_groups(shares: Seq<KeyShareEntry>) -> Seq<nat>
    decreases shares.len(),
{
    if shares.len() == 0 {
        seq![]
    } else {
        seq![shares[0].group] + share_groups(shares.subrange(1, shares.len() as int))
    }
}

/// §4.2.8: "Each KeyShareEntry value MUST correspond to a group offered in the
/// 'supported_groups' extension and MUST appear in the same order", as: `shares`
/// is a (possibly non-contiguous) subsequence of `groups`. "Clients MUST NOT
/// offer multiple KeyShareEntry values for the same group" follows if `groups`
/// has no repeats, and [`has_no_repeats`] is checked alongside.
pub open spec fn is_subsequence(shares: Seq<nat>, groups: Seq<nat>) -> bool
    decreases groups.len(),
{
    if shares.len() == 0 {
        true
    } else if groups.len() == 0 {
        false
    } else if shares[0] == groups[0] {
        is_subsequence(shares.subrange(1, shares.len() as int), groups.subrange(1, groups.len() as int))
    } else {
        is_subsequence(shares, groups.subrange(1, groups.len() as int))
    }
}

/// Whether no value of the list appears twice.
pub open spec fn has_no_repeats(values: Seq<nat>) -> bool
    decreases values.len(),
{
    if values.len() == 0 {
        true
    } else {
        let tail = values.subrange(1, values.len() as int);
        !list_has(tail, values[0]) && has_no_repeats(tail)
    }
}

} // verus!
