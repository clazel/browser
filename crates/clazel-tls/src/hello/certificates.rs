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
