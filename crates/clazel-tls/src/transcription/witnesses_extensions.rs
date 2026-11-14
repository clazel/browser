//! Witnesses for [`server_name`](super::server_name),
//! [`middlebox`](super::middlebox) and
//! [`extension_bodies`](super::extension_bodies), in the style of
//! [`witnesses`](super::witnesses), whose toy primitives and toy server they
//! reuse. Each is a concrete evaluation (`by (compute)`): it shows a definition
//! on one input, and proves nothing for all inputs.
//!
//! Modelling choices: as `witnesses`, the toy server's messages are built with
//! this transcription's own encoders. The RFC 8448 comparison of the
//! server_name encoder is the one independent check here.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::authentication::*;
#[cfg(verus_only)]
use super::connection::*;
#[cfg(verus_only)]
use super::extension_bodies::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::middlebox::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;
#[cfg(verus_only)]
use super::record::*;
#[cfg(verus_only)]
use super::server_name::*;
#[cfg(verus_only)]
use super::state_machine::*;
#[cfg(verus_only)]
use super::witnesses::*;

verus! {

// ==========================================================================
// RFC 6066 §3.
// ==========================================================================

/// "example.com".
pub open spec fn example_com() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d]
}

/// "server", RFC 8448 §3's host.
pub open spec fn server_bytes() -> Seq<u8> {
    seq![0x73u8, 0x65, 0x72, 0x76, 0x65, 0x72]
}

/// "192.0.2.1".
pub open spec fn ipv4_literal() -> Seq<u8> {
    seq![0x31u8, 0x39, 0x32, 0x2e, 0x30, 0x2e, 0x32, 0x2e, 0x31]
}

/// Four labels of 63 "a" each, joined by dots: 255 octets of text.
pub open spec fn too_long_name() -> Seq<u8> {
    repeat_byte(0x61, 63) + seq![0x2Eu8] + repeat_byte(0x61, 63) + seq![0x2Eu8]
        + repeat_byte(0x61, 63) + seq![0x2Eu8] + repeat_byte(0x61, 63)
}

/// RFC 6066 §3, RFC 2181 §11, RFC 1123 §2.1, RFC 1035 §2.3.4: which hosts have
/// a HostName, and what it is.
proof fn host_names()
    ensures
        host_name_for(example_com()) == Some(example_com()),
        // "without a trailing dot": one is removed, a second is not a hostname.
        host_name_for(example_com() + seq![0x2Eu8]) == Some(example_com()),
        host_name_for(example_com() + seq![0x2Eu8, 0x2E]) is None,
        // "Literal IPv4 and IPv6 addresses are not permitted".
        host_name_for(ipv4_literal()) is None,
        host_name_for(seq![0x31u8, 0x32, 0x37, 0x2e, 0x31]) is None,
        host_name_for(seq![0x3au8, 0x3a, 0x31]) is None,
        host_name_for(seq![0x5bu8, 0x3a, 0x3a, 0x31, 0x5d]) is None,
        // RFC 2181 §11: labels of any octets (here ASCII, RFC 6066 §3), not only
        // LDH, so a hyphen at either end and an underscore are kept; no empty
        // label, no octet outside ASCII.
        host_name_for(seq![0x2du8, 0x61, 0x2e, 0x63, 0x6f]) == Some(seq![0x2du8, 0x61, 0x2e, 0x63, 0x6f]),
        host_name_for(seq![0x61u8, 0x2d, 0x2e, 0x63, 0x6f]) == Some(seq![0x61u8, 0x2d, 0x2e, 0x63, 0x6f]),
        host_name_for(seq![0x61u8, 0x2e, 0x2e, 0x63, 0x6f]) is None,
        host_name_for(seq![0x61u8, 0x5f, 0x62, 0x2e, 0x63, 0x6f]) == Some(seq![0x61u8, 0x5f, 0x62, 0x2e, 0x63, 0x6f]),
        host_name_for(seq![0xC3u8, 0xA9, 0x2e, 0x63, 0x6f]) is None,
        host_name_for(seq![]) is None,
        host_name_for(seq![0x2Eu8]) is None,
        // RFC 1123 §2.1: a label may start with a digit; a top-level label need not
        // be letters only; one label is enough.
        host_name_for(seq![0x31u8, 0x61, 0x2e, 0x78, 0x6e, 0x2d, 0x2d, 0x70, 0x31, 0x61, 0x69])
            == Some(seq![0x31u8, 0x61, 0x2e, 0x78, 0x6e, 0x2d, 0x2d, 0x70, 0x31, 0x61, 0x69]),
        host_name_for(server_bytes()) == Some(server_bytes()),
        // Case is kept.
        host_name_for(seq![0x45u8, 0x78, 0x2e, 0x43, 0x6f]) == Some(seq![0x45u8, 0x78, 0x2e, 0x43, 0x6f]),
        // 63 octets a label; 253 octets a name.
        host_name_for(repeat_byte(0x61, 63)) == Some(repeat_byte(0x61, 63)),
        host_name_for(repeat_byte(0x61, 64)) is None,
        host_name_for(too_long_name().subrange(2, 255)) is Some,
        host_name_for(too_long_name().subrange(1, 255)) is None,
{
    assert(host_name_for(example_com()) == Some(example_com())) by (compute);
    assert(host_name_for(example_com() + seq![0x2Eu8]) == Some(example_com())) by (compute);
    assert(host_name_for(example_com() + seq![0x2Eu8, 0x2E]) is None) by (compute);
    assert(host_name_for(ipv4_literal()) is None) by (compute);
    assert(host_name_for(seq![0x31u8, 0x32, 0x37, 0x2e, 0x31]) is None) by (compute);
    assert(host_name_for(seq![0x3au8, 0x3a, 0x31]) is None) by (compute);
    assert(host_name_for(seq![0x5bu8, 0x3a, 0x3a, 0x31, 0x5d]) is None) by (compute);
    assert(host_name_for(seq![0x2du8, 0x61, 0x2e, 0x63, 0x6f]) == Some(seq![0x2du8, 0x61, 0x2e, 0x63, 0x6f])) by (compute);
    assert(host_name_for(seq![0x61u8, 0x2d, 0x2e, 0x63, 0x6f]) == Some(seq![0x61u8, 0x2d, 0x2e, 0x63, 0x6f])) by (compute);
    assert(host_name_for(seq![0x61u8, 0x2e, 0x2e, 0x63, 0x6f]) is None) by (compute);
    assert(host_name_for(seq![0x61u8, 0x5f, 0x62, 0x2e, 0x63, 0x6f]) == Some(seq![0x61u8, 0x5f, 0x62, 0x2e, 0x63, 0x6f])) by (compute);
    assert(host_name_for(seq![0xC3u8, 0xA9, 0x2e, 0x63, 0x6f]) is None) by (compute);
    assert(host_name_for(seq![]) is None) by (compute);
    assert(host_name_for(seq![0x2Eu8]) is None) by (compute);
    assert(host_name_for(seq![0x31u8, 0x61, 0x2e, 0x78, 0x6e, 0x2d, 0x2d, 0x70, 0x31, 0x61, 0x69])
        == Some(seq![0x31u8, 0x61, 0x2e, 0x78, 0x6e, 0x2d, 0x2d, 0x70, 0x31, 0x61, 0x69])) by (compute);
    assert(host_name_for(server_bytes()) == Some(server_bytes())) by (compute);
    assert(host_name_for(seq![0x45u8, 0x78, 0x2e, 0x43, 0x6f]) == Some(seq![0x45u8, 0x78, 0x2e, 0x43, 0x6f])) by (compute);
    assert(host_name_for(repeat_byte(0x61, 63)) == Some(repeat_byte(0x61, 63))) by (compute);
    assert(host_name_for(repeat_byte(0x61, 64)) is None) by (compute);
    assert(host_name_for(too_long_name().subrange(2, 255)) is Some) by (compute);
    assert(host_name_for(too_long_name().subrange(1, 255)) is None) by (compute);
}

/// RFC 6066 §3: the encoding, against RFC 8448 §3's ClientHello, which names
/// "server"; and the decoder.
proof fn server_name_encoding()
    ensures
        write_server_name_list(example_com()) == seq![0x00u8, 0x0e, 0x00, 0x00, 0x0b] + example_com(),
        find_extension(s3_hello().extensions, ext_server_name()) == Some(write_server_name_list(server_bytes())),
        read_server_name_list(write_server_name_list(example_com()))
            == Some(seq![ServerName { name_type: name_type_host_name(), name: example_com() }]),
        // ServerNameList<1..2^16-1> and HostName<1..2^16-1>.
        read_server_name_list(seq![0x00u8, 0x00]) is None,
        read_server_name_list(seq![0x00u8, 0x03, 0x00, 0x00, 0x00]) is None,
        // A future NameType "MUST begin with a 16-bit length field".
        read_server_name_list(seq![0x00u8, 0x04, 0x07, 0x00, 0x01, 0x61]) == Some(seq![ServerName { name_type: 7, name: seq![0x61u8] }]),
{
    assert(write_server_name_list(example_com()) == seq![0x00u8, 0x0e, 0x00, 0x00, 0x0b] + example_com()) by (compute);
    assert(find_extension(s3_hello().extensions, ext_server_name()) == Some(write_server_name_list(server_bytes()))) by (compute);
    assert(read_server_name_list(write_server_name_list(example_com()))
        == Some(seq![ServerName { name_type: name_type_host_name(), name: example_com() }])) by (compute);
    assert(read_server_name_list(seq![0x00u8, 0x00]) is None) by (compute);
    assert(read_server_name_list(seq![0x00u8, 0x03, 0x00, 0x00, 0x00]) is None) by (compute);
    assert(read_server_name_list(seq![0x00u8, 0x04, 0x07, 0x00, 0x01, 0x61]) == Some(seq![ServerName { name_type: 7, name: seq![0x61u8] }])) by (compute);
}

// ==========================================================================
// The client's configuration and ClientHello.
// ==========================================================================

/// A client for "example.com." in compatibility mode.
pub open spec fn compat_config() -> ClientConfig {
    ClientConfig { host: example_com() + seq![0x2Eu8], compatibility_mode: true }
}

/// A client for an IPv4 literal, not in compatibility mode.
pub open spec fn plain_config() -> ClientConfig {
    ClientConfig { host: ipv4_literal(), compatibility_mode: false }
}

/// "h2".
pub open spec fn h2() -> Seq<u8> {
    seq![0x68u8, 0x32]
}

/// "http/1.1".
pub open spec fn http11() -> Seq<u8> {
    seq![0x68u8, 0x74, 0x74, 0x70, 0x2f, 0x31, 0x2e, 0x31]
}

/// The encoded elements of `protocol_name_list`.
pub open spec fn protocol_names_bytes(names: Seq<Seq<u8>>) -> Seq<u8>
    decreases names.len(),
{
    if names.len() == 0 {
        seq![]
    } else {
        write_vector(names[0], 0xff) + protocol_names_bytes(names.subrange(1, names.len() as int))
    }
}

/// A ProtocolNameList of the names.
pub open spec fn protocol_list(names: Seq<Seq<u8>>) -> Seq<u8> {
    write_vector(protocol_names_bytes(names), 0xffff)
}

/// A UseSRTPData of the profiles and MKI.
pub open spec fn srtp_data(profiles: Seq<nat>, srtp_mki: Seq<u8>) -> Seq<u8> {
    write_vector(write_uint16_list(profiles), 0xffff) + write_vector(srtp_mki, 255)
}

/// The other extensions the toy client offers: a request for each EE response and
/// certificate extension a server may send in reply.
pub open spec fn offered_others() -> Seq<Extension> {
    seq![
        // RFC 6066 §4: 2^10.
        ext(ext_max_fragment_length(), seq![2u8]),
        // RFC 6520 §2.
        ext(ext_heartbeat(), seq![1u8]),
        // RFC 7301 §3.1.
        ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![h2(), http11()])),
        // RFC 5764 §4.1.1: two profiles, MKI 09.
        ext(ext_use_srtp(), srtp_data(seq![1nat, 2nat], seq![9u8])),
        // RFC 6066 §8: OCSP, no responder ids, no extensions.
        ext(ext_status_request(), seq![1u8, 0, 0, 0, 0]),
        // RFC 6962 §3.3.1: "empty".
        ext(ext_signed_certificate_timestamp(), seq![]),
    ]
}

/// The toy ClientHello for `config`; `share` as `witnesses::toy_hello`.
pub open spec fn cfg_hello(config: ClientConfig, share: bool) -> ClientHello {
    build_client_hello_for(config, toy_bytes(0x11), toy_bytes(0x33), toy_schemes(),
        if share { Some(toy_digest(toy_bytes(0x22) + x25519_basepoint())) } else { None },
        offered_others())
}

/// RFC 6066 §3, §4.1.2, D.4: the builder meets the predicate for both
/// configurations, and the predicate is not vacuous.
proof fn client_hello_for_configuration()
    ensures
        client_hello_conforms_for(compat_config(), cfg_hello(compat_config(), true), toy_schemes()),
        client_hello_conforms_for(plain_config(), cfg_hello(plain_config(), true), toy_schemes()),
        // The name is sent without its trailing dot; an IP literal gets none.
        find_extension(cfg_hello(compat_config(), true).extensions, ext_server_name()) == Some(write_server_name_list(example_com())),
        find_extension(cfg_hello(plain_config(), true).extensions, ext_server_name()) is None,
        // §4.1.2: 32 bytes in the mode, none outside it.
        cfg_hello(compat_config(), true).legacy_session_id == toy_bytes(0x33),
        cfg_hello(plain_config(), true).legacy_session_id == no_bytes(),
        !client_hello_conforms_for(plain_config(), cfg_hello(compat_config(), true), toy_schemes()),
        !client_hello_conforms_for(compat_config(), ClientHello { legacy_session_id: seq![], ..cfg_hello(compat_config(), true) }, toy_schemes()),
        // `witnesses::toy_hello`'s empty server_name is not a ServerNameList.
        !client_hello_conforms_for(ClientConfig { host: example_com(), compatibility_mode: true }, toy_conforming_hello(), toy_schemes()),
{
    assert(client_hello_conforms_for(compat_config(), cfg_hello(compat_config(), true), toy_schemes())) by (compute);
    assert(client_hello_conforms_for(plain_config(), cfg_hello(plain_config(), true), toy_schemes())) by (compute);
    assert(find_extension(cfg_hello(compat_config(), true).extensions, ext_server_name()) == Some(write_server_name_list(example_com()))) by (compute);
    assert(find_extension(cfg_hello(plain_config(), true).extensions, ext_server_name()) is None) by (compute);
    assert(cfg_hello(compat_config(), true).legacy_session_id == toy_bytes(0x33)) by (compute);
    assert(cfg_hello(plain_config(), true).legacy_session_id == no_bytes()) by (compute);
    assert(!client_hello_conforms_for(plain_config(), cfg_hello(compat_config(), true), toy_schemes())) by (compute);
    assert(!client_hello_conforms_for(compat_config(), ClientHello { legacy_session_id: seq![], ..cfg_hello(compat_config(), true) }, toy_schemes())) by (compute);
    assert(!client_hello_conforms_for(ClientConfig { host: example_com(), compatibility_mode: true }, toy_conforming_hello(), toy_schemes())) by (compute);
}

// ==========================================================================
// §4.2 bodies, by message, through the state machine.
// ==========================================================================

/// The toy ServerHello for the compatibility-mode hello, with more extensions.
pub open spec fn cfg_server_hello(more: Seq<Extension>) -> ServerHello {
    ServerHello { legacy_session_id_echo: toy_bytes(0x33), extensions: toy_server_hello().extensions + more, ..toy_server_hello() }
}

/// WAIT_SH after the compatibility-mode hello.
pub open spec fn cfg_hs_wait_sh() -> ClientHandshake {
    start_handshake(cfg_hello(compat_config(), true), toy_bytes(0x22), toy_bytes(0x23))
}

/// WAIT_EE after it.
pub open spec fn cfg_hs_wait_ee() -> ClientHandshake {
    after(receive_handshake_message(toy_primitives(), cfg_hs_wait_sh(), write_server_hello(cfg_server_hello(seq![]))))
}

/// An EncryptedExtensions of `extensions` in WAIT_EE.
pub open spec fn ee_step(extensions: Seq<Extension>) -> HandshakeStep {
    receive_handshake_message(toy_primitives(), cfg_hs_wait_ee(), write_encrypted_extensions(EncryptedExtensions { extensions }))
}

/// Every EE response to `offered_others`, and server_name and supported_groups,
/// well formed.
pub open spec fn good_ee() -> Seq<Extension> {
    seq![
        ext(ext_server_name(), seq![]),
        ext(ext_max_fragment_length(), seq![2u8]),
        ext(ext_heartbeat(), seq![2u8]),
        ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![h2()])),
        ext(ext_use_srtp(), srtp_data(seq![2nat], seq![])),
        ext(ext_supported_groups(), write_named_group_list(seq![group_x25519(), 0x0017nat])),
    ]
}

/// §4.2.11, §4.2.1, §4.2.8: a ServerHello's bodies; §4.1.4's HelloRetryRequest
/// bodies as `body_well_formed` states them.
proof fn server_hello_bodies()
    ensures
        after(receive_handshake_message(toy_primitives(), cfg_hs_wait_sh(), write_server_hello(cfg_server_hello(seq![])))).state == ClientState::WaitEe,
        // PSK was not offered: that comes first, and the malformed body is listed too.
        server_hello_failures(cfg_hello(compat_config(), true), cfg_server_hello(seq![ext(ext_pre_shared_key(), seq![0u8])]), None)[0]
            == ClientError::ExtensionNotOffered,
        list_has(server_hello_failures(cfg_hello(compat_config(), true), cfg_server_hello(seq![ext(ext_pre_shared_key(), seq![0u8])]), None),
            ClientError::Malformed),
        !list_has(server_hello_failures(cfg_hello(compat_config(), true), cfg_server_hello(seq![ext(ext_pre_shared_key(), seq![0u8, 0])]), None),
            ClientError::Malformed),
        body_well_formed(ext_pre_shared_key(), TableMessage::Sh, seq![0u8, 0]),
        !body_well_formed(ext_supported_versions(), TableMessage::Sh, seq![3u8, 4, 0]),
        body_well_formed(ext_cookie(), TableMessage::Hrr, write_vector(seq![1u8], 0xffff)),
        !body_well_formed(ext_cookie(), TableMessage::Hrr, uint16(0)),
        !body_well_formed(ext_key_share(), TableMessage::Hrr, seq![0u8, 0x1d, 0]),
        // A body with no syntax for the message is not this file's to judge.
        body_well_formed(ext_cookie(), TableMessage::Sh, seq![]),
{
    assert(after(receive_handshake_message(toy_primitives(), cfg_hs_wait_sh(), write_server_hello(cfg_server_hello(seq![])))).state == ClientState::WaitEe) by (compute);
    assert(server_hello_failures(cfg_hello(compat_config(), true), cfg_server_hello(seq![ext(ext_pre_shared_key(), seq![0u8])]), None)[0]
        == ClientError::ExtensionNotOffered) by (compute);
    assert(list_has(server_hello_failures(cfg_hello(compat_config(), true), cfg_server_hello(seq![ext(ext_pre_shared_key(), seq![0u8])]), None),
        ClientError::Malformed)) by (compute);
    assert(!list_has(server_hello_failures(cfg_hello(compat_config(), true), cfg_server_hello(seq![ext(ext_pre_shared_key(), seq![0u8, 0])]), None),
        ClientError::Malformed)) by (compute);
    assert(body_well_formed(ext_pre_shared_key(), TableMessage::Sh, seq![0u8, 0])) by (compute);
    assert(!body_well_formed(ext_supported_versions(), TableMessage::Sh, seq![3u8, 4, 0])) by (compute);
    assert(body_well_formed(ext_cookie(), TableMessage::Hrr, write_vector(seq![1u8], 0xffff))) by (compute);
    assert(!body_well_formed(ext_cookie(), TableMessage::Hrr, uint16(0))) by (compute);
    assert(!body_well_formed(ext_key_share(), TableMessage::Hrr, seq![0u8, 0x1d, 0])) by (compute);
    assert(body_well_formed(ext_cookie(), TableMessage::Sh, seq![])) by (compute);
}

/// RFC 6066 §3 and §4, RFC 6520 §2, RFC 7301 §3.1, RFC 5764 §4.1.1 and §4.1.3,
/// §4.2.7, §4.2.10, RFC 7250 §3: EncryptedExtensions' bodies.
proof fn encrypted_extensions_bodies()
    ensures
        after(ee_step(good_ee())).state == ClientState::WaitCertCr,
        after(ee_step(seq![])).state == ClientState::WaitCertCr,
        // RFC 6066 §3: "SHALL be empty".
        aborted_with(ee_step(seq![ext(ext_server_name(), seq![0u8])]), ClientError::Malformed),
        aborted_with(ee_step(seq![ext(ext_server_name(), write_server_name_list(example_com()))]), ClientError::Malformed),
        // RFC 6066 §4: one byte, the one requested.
        aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![])]), ClientError::Malformed),
        aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![2u8, 2])]), ClientError::Malformed),
        aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![3u8])]), ClientError::ExtensionBodyInvalid(ext_max_fragment_length())),
        aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![9u8])]), ClientError::ExtensionBodyInvalid(ext_max_fragment_length())),
        // RFC 6520 §2: "an unknown mode".
        aborted_with(ee_step(seq![ext(ext_heartbeat(), seq![3u8])]), ClientError::ExtensionBodyInvalid(ext_heartbeat())),
        aborted_with(ee_step(seq![ext(ext_heartbeat(), seq![])]), ClientError::Malformed),
        // RFC 7301 §3.1: exactly one name, advertised; the list's syntax.
        aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![h2(), http11()]))]),
            ClientError::ExtensionBodyInvalid(ext_application_layer_protocol_negotiation())),
        aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![seq![0x68u8, 0x33]]))]),
            ClientError::ExtensionBodyInvalid(ext_application_layer_protocol_negotiation())),
        aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), uint16(0))]), ClientError::Malformed),
        aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![seq![]]))]), ClientError::Malformed),
        // RFC 5764 §4.1.1, §4.1.3: one offered profile; the MKI, if any, the one offered.
        after(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![1nat], seq![9u8]))])).state == ClientState::WaitCertCr,
        aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![1nat], seq![8u8]))]), ClientError::ExtensionBodyInvalid(ext_use_srtp())),
        aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![5nat], seq![]))]), ClientError::ExtensionBodyInvalid(ext_use_srtp())),
        aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![1nat, 2nat], seq![]))]), ClientError::ExtensionBodyInvalid(ext_use_srtp())),
        aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![], seq![]))]), ClientError::Malformed),
        // §4.2.7: syntax only.
        aborted_with(ee_step(seq![ext(ext_supported_groups(), write_vector(seq![0u8, 0x1d, 0], 0xffff))]), ClientError::Malformed),
        // Not offered, first; the malformed early_data body is listed after it.
        aborted_with(ee_step(seq![ext(ext_early_data(), seq![])]), ClientError::ExtensionNotOffered),
        list_has(encrypted_extensions_failures(cfg_hello(compat_config(), true),
            EncryptedExtensions { extensions: seq![ext(ext_early_data(), seq![1u8])] }), ClientError::Malformed),
        aborted_with(ee_step(seq![ext(ext_server_certificate_type(), seq![0u8])]), ClientError::ExtensionNotOffered),
        !body_well_formed(ext_client_certificate_type(), TableMessage::Ee, seq![1u8, 0, 2]),
        // §4.2's table rule still comes first.
        aborted_with(ee_step(seq![ext(ext_status_request(), seq![])]), ClientError::ExtensionNotSpecifiedForMessage),
{
    assert(after(ee_step(good_ee())).state == ClientState::WaitCertCr) by (compute);
    assert(after(ee_step(seq![])).state == ClientState::WaitCertCr) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_server_name(), seq![0u8])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_server_name(), write_server_name_list(example_com()))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![2u8, 2])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![3u8])]), ClientError::ExtensionBodyInvalid(ext_max_fragment_length()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_max_fragment_length(), seq![9u8])]), ClientError::ExtensionBodyInvalid(ext_max_fragment_length()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_heartbeat(), seq![3u8])]), ClientError::ExtensionBodyInvalid(ext_heartbeat()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_heartbeat(), seq![])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![h2(), http11()]))]),
        ClientError::ExtensionBodyInvalid(ext_application_layer_protocol_negotiation()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![seq![0x68u8, 0x33]]))]),
        ClientError::ExtensionBodyInvalid(ext_application_layer_protocol_negotiation()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), uint16(0))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_application_layer_protocol_negotiation(), protocol_list(seq![seq![]]))]), ClientError::Malformed)) by (compute);
    assert(after(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![1nat], seq![9u8]))])).state == ClientState::WaitCertCr) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![1nat], seq![8u8]))]), ClientError::ExtensionBodyInvalid(ext_use_srtp()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![5nat], seq![]))]), ClientError::ExtensionBodyInvalid(ext_use_srtp()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![1nat, 2nat], seq![]))]), ClientError::ExtensionBodyInvalid(ext_use_srtp()))) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_use_srtp(), srtp_data(seq![], seq![]))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_supported_groups(), write_vector(seq![0u8, 0x1d, 0], 0xffff))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_early_data(), seq![])]), ClientError::ExtensionNotOffered)) by (compute);
    assert(list_has(encrypted_extensions_failures(cfg_hello(compat_config(), true),
        EncryptedExtensions { extensions: seq![ext(ext_early_data(), seq![1u8])] }), ClientError::Malformed)) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_server_certificate_type(), seq![0u8])]), ClientError::ExtensionNotOffered)) by (compute);
    assert(!body_well_formed(ext_client_certificate_type(), TableMessage::Ee, seq![1u8, 0, 2])) by (compute);
    assert(aborted_with(ee_step(seq![ext(ext_status_request(), seq![])]), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
}

/// WAIT_CERT_CR after an empty EncryptedExtensions.
pub open spec fn cfg_hs_wait_cert_cr() -> ClientHandshake {
    after(ee_step(seq![]))
}

/// A CertificateRequest of signature_algorithms and `more`, in WAIT_CERT_CR.
pub open spec fn cr_step(more: Seq<Extension>) -> HandshakeStep {
    receive_handshake_message(toy_primitives(), cfg_hs_wait_cert_cr(), write_certificate_request(CertificateRequest {
        certificate_request_context: seq![],
        extensions: seq![ext(ext_signature_algorithms(), write_signature_scheme_list(seq![ed25519()]))] + more,
    }))
}

/// The encoded elements of `filters`, each OID with no values.
pub open spec fn oid_filter_bytes(oids: Seq<Seq<u8>>) -> Seq<u8>
    decreases oids.len(),
{
    if oids.len() == 0 {
        seq![]
    } else {
        write_vector(oids[0], 0xff) + write_vector(seq![], 0xffff) + oid_filter_bytes(oids.subrange(1, oids.len() as int))
    }
}

/// An OIDFilterExtension of filters with no values.
pub open spec fn oid_filters_of(oids: Seq<Seq<u8>>) -> Seq<u8> {
    write_vector(oid_filter_bytes(oids), 0xffff)
}

/// id-ce-extKeyUsage, 2.5.29.37, as DER content octets.
pub open spec fn eku_oid() -> Seq<u8> {
    seq![0x55u8, 0x1d, 0x25]
}

/// §4.2.3, §4.2.4, §4.2.5, §4.4.2.1, RFC 6962 §3.3.1: CertificateRequest's
/// bodies.
proof fn certificate_request_bodies()
    ensures
        after(cr_step(seq![
            ext(ext_status_request(), seq![]),
            ext(ext_signed_certificate_timestamp(), seq![]),
            ext(ext_certificate_authorities(), write_vector(write_vector(seq![0x30u8, 0], 0xffff), 0xffff)),
            ext(ext_oid_filters(), oid_filters_of(seq![eku_oid()])),
            ext(ext_signature_algorithms_cert(), write_signature_scheme_list(seq![rsa_pkcs1_sha256()])),
        ])).state == ClientState::WaitCert,
        after(cr_step(seq![ext(ext_oid_filters(), oid_filters_of(seq![]))])).state == ClientState::WaitCert,
        // §4.4.2.1: "an empty 'status_request' extension".
        aborted_with(cr_step(seq![ext(ext_status_request(), seq![1u8, 0, 0, 0, 0])]), ClientError::Malformed),
        aborted_with(cr_step(seq![ext(ext_signed_certificate_timestamp(), seq![0u8])]), ClientError::Malformed),
        // §4.2.4: authorities<3..2^16-1>, DistinguishedName<1..2^16-1>.
        aborted_with(cr_step(seq![ext(ext_certificate_authorities(), write_vector(seq![0u8, 0], 0xffff))]), ClientError::Malformed),
        aborted_with(cr_step(seq![ext(ext_certificate_authorities(), write_vector(seq![0u8, 0, 0], 0xffff))]), ClientError::Malformed),
        // §4.2.5: an OID of at least one byte, and none twice.
        aborted_with(cr_step(seq![ext(ext_oid_filters(), oid_filters_of(seq![seq![]]))]), ClientError::Malformed),
        aborted_with(cr_step(seq![ext(ext_oid_filters(), oid_filters_of(seq![eku_oid(), eku_oid()]))]), ClientError::ExtensionBodyInvalid(ext_oid_filters())),
        // §4.2.3.
        aborted_with(cr_step(seq![ext(ext_signature_algorithms_cert(), write_vector(seq![8u8, 7, 8], 0xfffe))]), ClientError::Malformed),
{
    assert(after(cr_step(seq![
        ext(ext_status_request(), seq![]),
        ext(ext_signed_certificate_timestamp(), seq![]),
        ext(ext_certificate_authorities(), write_vector(write_vector(seq![0x30u8, 0], 0xffff), 0xffff)),
        ext(ext_oid_filters(), oid_filters_of(seq![eku_oid()])),
        ext(ext_signature_algorithms_cert(), write_signature_scheme_list(seq![rsa_pkcs1_sha256()])),
    ])).state == ClientState::WaitCert) by (compute);
    assert(after(cr_step(seq![ext(ext_oid_filters(), oid_filters_of(seq![]))])).state == ClientState::WaitCert) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_status_request(), seq![1u8, 0, 0, 0, 0])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_signed_certificate_timestamp(), seq![0u8])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_certificate_authorities(), write_vector(seq![0u8, 0], 0xffff))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_certificate_authorities(), write_vector(seq![0u8, 0, 0], 0xffff))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_oid_filters(), oid_filters_of(seq![seq![]]))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_oid_filters(), oid_filters_of(seq![eku_oid(), eku_oid()]))]), ClientError::ExtensionBodyInvalid(ext_oid_filters()))) by (compute);
    assert(aborted_with(cr_step(seq![ext(ext_signature_algorithms_cert(), write_vector(seq![8u8, 7, 8], 0xfffe))]), ClientError::Malformed)) by (compute);
}

/// A Certificate of one accepted entry with `extensions`, in WAIT_CERT_CR.
pub open spec fn ct_step(extensions: Seq<Extension>) -> HandshakeStep {
    receive_handshake_message(toy_primitives(), cfg_hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], extensions))
}

/// §4.4.2.1, RFC 6066 §8, RFC 6962 §3.3: a CertificateEntry's bodies; §4.2.10: a
/// NewSessionTicket's.
proof fn certificate_and_ticket_bodies()
    ensures
        after(ct_step(seq![
            ext(ext_status_request(), seq![1u8, 0, 0, 2, 0x30, 0x00]),
            ext(ext_signed_certificate_timestamp(), write_vector(write_vector(seq![7u8], 0xffff), 0xffff)),
        ])).state == ClientState::WaitCv,
        // CertificateStatus: only ocsp(1) has an arm; OCSPResponse<1..2^24-1>.
        aborted_with(ct_step(seq![ext(ext_status_request(), seq![2u8, 0, 0, 1, 0x30])]), ClientError::Malformed),
        aborted_with(ct_step(seq![ext(ext_status_request(), seq![1u8, 0, 0, 0])]), ClientError::Malformed),
        aborted_with(ct_step(seq![ext(ext_status_request(), seq![])]), ClientError::Malformed),
        // SignedCertificateTimestampList: sct_list<1..2^16-1>, SerializedSCT<1..2^16-1>.
        aborted_with(ct_step(seq![ext(ext_signed_certificate_timestamp(), uint16(0))]), ClientError::Malformed),
        aborted_with(ct_step(seq![ext(ext_signed_certificate_timestamp(), write_vector(uint16(0), 0xffff))]), ClientError::Malformed),
        // The second entry's bodies are checked as well.
        aborted_with(receive_handshake_message(toy_primitives(), cfg_hs_wait_cert_cr(), write_certificate(Certificate {
            certificate_request_context: seq![],
            certificate_list: seq![
                CertificateEntry { cert_data: seq![0xEEu8], extensions: seq![] },
                CertificateEntry { cert_data: seq![0xCAu8], extensions: seq![ext(ext_status_request(), seq![1u8])] },
            ],
        })), ClientError::Malformed),
        // §4.2.10: `uint32 max_early_data_size`.
        after(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(1, seq![ext(ext_early_data(), seq![0u8, 0, 4, 0])]))) == hs_connected(),
        aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(1, seq![ext(ext_early_data(), seq![0u8, 4, 0])])), ClientError::Malformed),
{
    assert(after(ct_step(seq![
        ext(ext_status_request(), seq![1u8, 0, 0, 2, 0x30, 0x00]),
        ext(ext_signed_certificate_timestamp(), write_vector(write_vector(seq![7u8], 0xffff), 0xffff)),
    ])).state == ClientState::WaitCv) by (compute);
    assert(aborted_with(ct_step(seq![ext(ext_status_request(), seq![2u8, 0, 0, 1, 0x30])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ct_step(seq![ext(ext_status_request(), seq![1u8, 0, 0, 0])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ct_step(seq![ext(ext_status_request(), seq![])]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ct_step(seq![ext(ext_signed_certificate_timestamp(), uint16(0))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(ct_step(seq![ext(ext_signed_certificate_timestamp(), write_vector(uint16(0), 0xffff))]), ClientError::Malformed)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), cfg_hs_wait_cert_cr(), write_certificate(Certificate {
        certificate_request_context: seq![],
        certificate_list: seq![
            CertificateEntry { cert_data: seq![0xEEu8], extensions: seq![] },
            CertificateEntry { cert_data: seq![0xCAu8], extensions: seq![ext(ext_status_request(), seq![1u8])] },
        ],
    })), ClientError::Malformed)) by (compute);
    assert(after(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(1, seq![ext(ext_early_data(), seq![0u8, 0, 4, 0])]))) == hs_connected()) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(1, seq![ext(ext_early_data(), seq![0u8, 4, 0])])), ClientError::Malformed)) by (compute);
}

// ==========================================================================
// Appendix D.4, by records.
// ==========================================================================

/// The client of `config` after its first ClientHello, `share` as in `cfg_hello`.
pub open spec fn client_wait_sh(config: ClientConfig, share: bool) -> ClientConnection {
    start_client(toy_primitives(), config, cfg_hello(config, share), toy_bytes(0x22), toy_bytes(0x23)).0
}

/// The toy ServerHello as a record, echoing the session id of `config`.
pub open spec fn cfg_sh_record(config: ClientConfig) -> Seq<u8> {
    plain(ct_handshake(), write_server_hello(ServerHello {
        legacy_session_id_echo: if config.compatibility_mode { toy_bytes(0x33) } else { seq![] },
        ..toy_server_hello()
    }))
}

/// A HelloRetryRequest selecting X25519 as a record, echoing the session id of
/// `config`.
pub open spec fn cfg_hrr_record(config: ClientConfig) -> Seq<u8> {
    plain(ct_handshake(), write_server_hello(ServerHello {
        random: hello_retry_request_random(),
        legacy_session_id_echo: if config.compatibility_mode { toy_bytes(0x33) } else { seq![] },
        extensions: seq![retry_versions(), retry_key_share()],
        ..toy_server_hello()
    }))
}

/// The records to send of a result.
pub open spec fn sent_by(result: (ClientReceive, Seq<u8>)) -> Seq<Seq<u8>> {
    result.0->records_to_send
}

/// The client after a result.
pub open spec fn client_after(result: (ClientReceive, Seq<u8>)) -> ClientConnection {
    result.0->client
}

/// The server's encrypted flight from WAIT_EE `hs`: EncryptedExtensions,
/// Certificate, CertificateVerify, Finished, each correct for `hs`'s transcript.
pub open spec fn flight_from(hs: ClientHandshake) -> Seq<u8> {
    let p = toy_primitives();
    let ee = write_encrypted_extensions(EncryptedExtensions { extensions: seq![] });
    let at_cert = after(receive_handshake_message(p, hs, ee));
    let certificate = toy_certificate(seq![0xEEu8], seq![]);
    let at_cv = after(receive_handshake_message(p, at_cert, certificate));
    let cv = toy_cv(at_cv, ed25519());
    let at_finished = after(receive_handshake_message(p, at_cv, cv));
    ee + certificate + cv + toy_finished(at_finished)
}

/// The server's flight as one record under its handshake key, with the server's
/// own dummy change_cipher_spec before it.
pub open spec fn flight_records(client: ClientConnection) -> Seq<u8> {
    plain(ct_change_cipher_spec(), seq![1u8])
        + protect_record(toy_primitives(), traffic_state(toy_primitives(), client.connection.handshake.server_handshake_traffic_secret),
            ct_handshake(), flight_from(client.connection.handshake))
}

/// The compatibility-mode client after the ServerHello, without a retry.
pub open spec fn compat_wait_ee() -> ClientConnection {
    client_after(client_receive_stream(toy_primitives(), client_wait_sh(compat_config(), true), cfg_sh_record(compat_config())))
}

/// The plain client after the ServerHello.
pub open spec fn plain_wait_ee() -> ClientConnection {
    client_after(client_receive_stream(toy_primitives(), client_wait_sh(plain_config(), true), cfg_sh_record(plain_config())))
}

/// The compatibility-mode client, with no share, after a HelloRetryRequest.
pub open spec fn compat_retried() -> (ClientReceive, Seq<u8>) {
    client_receive_stream(toy_primitives(), client_wait_sh(compat_config(), false), cfg_hrr_record(compat_config()))
}

/// That client after the ServerHello that follows.
pub open spec fn compat_retried_wait_ee() -> ClientConnection {
    client_after(client_receive_stream(toy_primitives(), client_after(compat_retried()), cfg_sh_record(compat_config())))
}

/// D.4, §5: the record; nothing is written in response to a ServerHello; and RFC
/// 6066 §3's fatal unrecognized_name(112) from the server ends the run.
proof fn compatibility_mode_record_and_server_hello()
{
    assert(dummy_change_cipher_spec_record() == seq![0x14u8, 0x03, 0x03, 0x00, 0x01, 0x01]) by (compute);
    assert(sent_by(client_receive_stream(toy_primitives(), client_wait_sh(compat_config(), true), cfg_sh_record(compat_config()))) == Seq::<Seq<u8>>::empty()) by (compute);
    assert(!compat_wait_ee().change_cipher_spec_sent) by (compute);
    assert(compat_wait_ee().connection.handshake.state == ClientState::WaitEe) by (compute);
    assert(client_receive_stream(toy_primitives(), client_wait_sh(compat_config(), true), plain(ct_alert(), seq![2u8, 112])).0
        == ClientReceive::PeerError(ad_unrecognized_name())) by (compute);
}

/// D.4: without a retry, the dummy record, then the encrypted flight's Finished.
proof fn compatibility_mode_without_retry()
{
    assert(sent_by(client_receive_stream(toy_primitives(), compat_wait_ee(), flight_records(compat_wait_ee()))).len() == 2) by (compute);
    assert(sent_by(client_receive_stream(toy_primitives(), compat_wait_ee(), flight_records(compat_wait_ee())))[0]
        == dummy_change_cipher_spec_record()) by (compute);
    assert(client_after(client_receive_stream(toy_primitives(), compat_wait_ee(), flight_records(compat_wait_ee()))).connection.handshake.state
        == ClientState::Connected) by (compute);
    assert(client_after(client_receive_stream(toy_primitives(), compat_wait_ee(), flight_records(compat_wait_ee()))).change_cipher_spec_sent) by (compute);
}

/// D.4: outside the mode, the Finished alone.
proof fn no_compatibility_mode()
{
    assert(sent_by(client_receive_stream(toy_primitives(), plain_wait_ee(), flight_records(plain_wait_ee()))).len() == 1) by (compute);
    assert(sent_by(client_receive_stream(toy_primitives(), plain_wait_ee(), flight_records(plain_wait_ee())))[0]
        != dummy_change_cipher_spec_record()) by (compute);
}

/// D.4: with a retry, the dummy record before the second ClientHello.
proof fn compatibility_mode_retry_second_client_hello()
{
    assert(sent_by(compat_retried()).len() == 2) by (compute);
    assert(sent_by(compat_retried())[0] == dummy_change_cipher_spec_record()) by (compute);
    assert(sent_by(compat_retried())[1] == write_tls_plaintext(ct_handshake(), 0x0303,
        client_after(compat_retried()).connection.handshake.transcript[2])) by (compute);
}

/// D.4: with a retry, no second dummy record before the encrypted flight.
proof fn compatibility_mode_retry_encrypted_flight()
{
    assert(compat_retried_wait_ee().connection.handshake.state == ClientState::WaitEe) by (compute);
    assert(sent_by(client_receive_stream(toy_primitives(), compat_retried_wait_ee(), flight_records(compat_retried_wait_ee()))).len() == 1) by (compute);
    assert(client_after(client_receive_stream(toy_primitives(), compat_retried_wait_ee(), flight_records(compat_retried_wait_ee()))).connection.handshake.state
        == ClientState::Connected) by (compute);
}

} // verus!
