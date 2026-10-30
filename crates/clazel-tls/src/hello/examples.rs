//! Concrete RFC 8446 server-selection witnesses, independent of cryptography.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// A server selection for the fixed profile, echoing session ID 7.
pub open spec fn server() -> crate::spec::ServerHello {
    crate::spec::ServerHello {
        legacy_version: 0x0303, random: Seq::new(32, |i: int| 0u8), session_id_echo: seq![7u8],
        cipher_suite: 0x1303, compression: 0,
        extensions: seq![crate::spec::Ext { etype: 43, data: seq![3u8, 4u8] },
            crate::spec::Ext { etype: 51, data: seq![0u8, 29u8, 0u8, 32u8] + Seq::new(32, |i: int| 8u8) }],
    }
}
/// A cookie-only retry; the cookie's length prefix must be preserved.
pub open spec fn request() -> crate::spec::ServerHello {
    crate::spec::ServerHello { random: crate::spec::hrr_random(),
        extensions: seq![crate::spec::Ext { etype: 43, data: seq![3u8, 4u8] },
            crate::spec::Ext { etype: 44, data: seq![0u8, 1u8, 9u8] }], ..server() }
}
/// §4.1.3: accepted server share comes from the exact returned bytes.
pub proof fn lemma_valid_share()
    ensures parsed(server(), seq![7u8], false) == Ok(Selection::Share(Seq::new(32, |i: int| 8u8))),
{
    assert(parsed(server(), seq![7u8], false) == Ok(Selection::Share(Seq::new(32, |i: int| 8u8)))) by (compute_only);
}
/// §4.1.3: the selected cipher must have been offered.
pub proof fn lemma_cipher()
    ensures parameters(crate::spec::ServerHello { cipher_suite: 0x1301, ..server() }, seq![7u8]) == Some(47u8),
{
    assert(parameters(crate::spec::ServerHello { cipher_suite: 0x1301, ..server() }, seq![7u8]) == Some(47u8)) by (compute_only);
}
/// §4.1.3: session ID echo is byte-exact.
pub proof fn lemma_session()
    ensures parameters(server(), seq![8u8]) == Some(47u8),
{
    assert(parameters(server(), seq![8u8]) == Some(47u8)) by (compute_only);
}
/// §4.2.1: legacy_version must not override supported_versions.
pub proof fn lemma_legacy()
    ensures parameters(crate::spec::ServerHello { legacy_version: 0x0304, ..server() }, seq![7u8]) is None,
{
    assert(parameters(crate::spec::ServerHello { legacy_version: 0x0304, ..server() }, seq![7u8]) is None) by (compute_only);
}
/// §4.2.1: selected_version must be TLS 1.3.
pub proof fn lemma_version()
    ensures parameters(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 43, data: seq![3u8, 3u8] }], ..server() }, seq![7u8]) == Some(47u8),
{
    assert(parameters(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 43, data: seq![3u8, 3u8] }], ..server() }, seq![7u8]) == Some(47u8)) by (compute_only);
}
/// §4.1.4: only one retry, and a no-op retry is rejected.
pub proof fn lemma_retry_checks()
    ensures retry(request(), true) == Err(10u8),
        retry(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 43, data: seq![3u8, 4u8] }], ..request() }, false) == Err(47u8),
        retry(request(), false) == Ok(Selection::Retry(seq![0u8, 1u8, 9u8])),
{
    assert(retry(request(), true) == Err(10u8)) by (compute_only);
    assert(retry(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 43, data: seq![3u8, 4u8] }], ..request() }, false) == Err(47u8)) by (compute_only);
    assert(retry(request(), false) == Ok(Selection::Retry(seq![0u8, 1u8, 9u8]))) by (compute_only);
}
/// §4.2.8: no supported group remains for a replacement share in this profile.
pub proof fn lemma_redundant_retry_share()
    ensures retry(crate::spec::ServerHello { extensions: request().extensions.push(crate::spec::Ext { etype: 51, data: seq![0u8, 29u8] }), ..request() }, false) == Err(47u8),
{
    assert(retry(crate::spec::ServerHello { extensions: request().extensions.push(crate::spec::Ext { etype: 51, data: seq![0u8, 29u8] }), ..request() }, false) == Err(47u8)) by (compute_only);
}
/// §4.2: unknown unsolicited responses are rejected, HRR cookie is excepted.
pub proof fn lemma_unsolicited()
    ensures !offered(seq![crate::spec::Ext { etype: 65000, data: seq![] }], false),
        !offered(seq![crate::spec::Ext { etype: 44, data: seq![0u8, 1u8, 9u8] }], false),
        offered(seq![crate::spec::Ext { etype: 44, data: seq![0u8, 1u8, 9u8] }], true),
{
    assert(!offered(seq![crate::spec::Ext { etype: 65000, data: seq![] }], false)) by (compute_only);
    assert(!offered(seq![crate::spec::Ext { etype: 44, data: seq![0u8, 1u8, 9u8] }], false)) by (compute_only);
    assert(offered(seq![crate::spec::Ext { etype: 44, data: seq![0u8, 1u8, 9u8] }], true)) by (compute_only);
}
/// §4.2.8: another group is never silently accepted as X25519.
pub proof fn lemma_group()
    ensures share(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 51, data: seq![0u8, 23u8, 0u8, 32u8] + Seq::new(32, |i: int| 8u8) }], ..server() }) == Err(47u8),
{
    assert(share(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 51, data: seq![0u8, 23u8, 0u8, 32u8] + Seq::new(32, |i: int| 8u8) }], ..server() }) == Err(47u8)) by (compute_only);
}
/// §4.2.8.2: a short X25519 public input is rejected.
pub proof fn lemma_key_length()
    ensures share(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 51, data: seq![0u8, 29u8, 0u8, 1u8, 8u8] }], ..server() }) == Err(47u8),
{
    assert(share(crate::spec::ServerHello { extensions: seq![crate::spec::Ext { etype: 51, data: seq![0u8, 29u8, 0u8, 1u8, 8u8] }], ..server() }) == Err(47u8)) by (compute_only);
}
} // verus!
