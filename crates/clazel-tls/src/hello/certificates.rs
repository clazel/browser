//! Specification theorems used by injected Hello-selection mutation certificates.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A complete base ServerHello with the optional legacy extension field absent.
pub open spec fn legacy_server_hello_without_extension_field() -> Seq<u8> {
    seq![3u8, 3] + crate::examples_hs::z32() + seq![0u8] + seq![0u8, 0x2f] + seq![0u8]
}

/// RFC 5246 §7.4.1.3 / RFC 8446 §4.1.3: a complete legacy message without
/// `supported_versions` is rejected at negotiation with `protocol_version`.
pub proof fn lemma_absent_legacy_extension_field_uses_protocol_version()
    ensures super::spec::validate(
        Seq::empty(), false, legacy_server_hello_without_extension_field(),
    ) == Err(crate::spec::PROTOCOL_VERSION)
{
    assert(super::spec::validate(
        Seq::empty(), false, legacy_server_hello_without_extension_field(),
    ) == Err(crate::spec::PROTOCOL_VERSION)) by (compute_only);
}

/// A syntactically decoded ServerHello with no extensions identifies no TLS 1.3 version.
pub proof fn lemma_legacy_server_hello_uses_protocol_version()
    ensures parameters(
        crate::spec::ServerHello {
            legacy_version: 0x0303,
            random: Seq::empty(),
            session_id_echo: Seq::empty(),
            cipher_suite: 0x002f,
            compression: 0,
            extensions: Seq::empty(),
        },
        Seq::empty(),
    ) == Some(crate::spec::PROTOCOL_VERSION)
{
    assert(parameters(
        crate::spec::ServerHello {
            legacy_version: 0x0303,
            random: Seq::empty(),
            session_id_echo: Seq::empty(),
            cipher_suite: 0x002f,
            compression: 0,
            extensions: Seq::empty(),
        },
        Seq::empty(),
    ) == Some(crate::spec::PROTOCOL_VERSION)) by (compute_only);
}

/// A complete base ServerHello whose extension vector is `exts` (the bytes
/// after the two-byte vector length, which this prefixes).
pub open spec fn legacy_server_hello_with_extensions(exts: Seq<u8>) -> Seq<u8> {
    legacy_server_hello_without_extension_field() + seq![0u8, exts.len() as u8] + exts
}

/// A nonempty extension list without `supported_versions` identifies no
/// TLS 1.3 version: `protocol_version`, even though the generic parser would
/// reject the (server_name) extension as not allowed in a ServerHello.
pub proof fn lemma_legacy_server_hello_extensions_without_supported_versions()
    ensures
        super::spec::validate(
            Seq::empty(), false, legacy_server_hello_with_extensions(seq![0u8, 0, 0, 0]),
        ) == Err(crate::spec::PROTOCOL_VERSION),
{
    assert(super::spec::validate(
        Seq::empty(), false, legacy_server_hello_with_extensions(seq![0u8, 0, 0, 0]),
    ) == Err(crate::spec::PROTOCOL_VERSION)) by (compute_only);
}

/// `supported_versions` in a non-first position is found: the message is not
/// a legacy ServerHello without it.
pub proof fn lemma_supported_versions_found_after_other_extension()
    ensures
        !crate::spec::legacy_server_hello_without_supported_versions(
            legacy_server_hello_with_extensions(seq![0x12u8, 0x34, 0, 1, 9, 0, 0x2b, 0, 2, 3, 4]),
        ),
{
    assert(!crate::spec::legacy_server_hello_without_supported_versions(
        legacy_server_hello_with_extensions(seq![0x12u8, 0x34, 0, 1, 9, 0, 0x2b, 0, 2, 3, 4]),
    )) by (compute_only);
}

/// A hash that is irrelevant to a CCS event.
pub open spec fn empty_hash(_messages: Seq<u8>) -> Seq<u8> { seq![] }

/// A bootstrap state awaiting ServerHello with `buf` already reassembled.
pub open spec fn awaiting_with_buffer(buf: Seq<u8>) -> super::bootstrap_spec::State {
    super::bootstrap_spec::State { mode: super::bootstrap_spec::Mode::AwaitServerHello,
        hello: None, pending_flight: seq![], compatibility: true,
        reassembly: crate::spec::Reasm { buf } }
}

/// RFC 8446 §5.1 (docs/ERRATA.md): a CCS inside a fragmented ServerHello is
/// fatal, while the same record at a message boundary is still dropped.
pub proof fn lemma_ccs_fatal_mid_message()
    ensures
        super::bootstrap_spec::receive(|m: Seq<u8>| empty_hash(m), awaiting_with_buffer(seq![1u8]),
            super::bootstrap_spec::PeerEvent::Ccs).1
            == super::bootstrap_spec::Action::Fail(crate::spec::UNEXPECTED_MESSAGE),
        super::bootstrap_spec::receive(|m: Seq<u8>| empty_hash(m), awaiting_with_buffer(seq![]),
            super::bootstrap_spec::PeerEvent::Ccs)
            == (awaiting_with_buffer(seq![]), super::bootstrap_spec::Action::None),
{
}
}
