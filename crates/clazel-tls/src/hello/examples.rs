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
/// Appendix D.5: a legacy_version of 0x0300 aborts with protocol_version;
/// §4.1.4: a HelloRetryRequest's must be 0x0303 (illegal_parameter), while a
/// ServerHello's other values are ignored (§4.2.1).
pub proof fn lemma_legacy_version_checks()
    ensures
        parsed(crate::spec::ServerHello { legacy_version: 0x0300, ..server() }, seq![7u8], false) == Err::<Selection, u8>(70u8),
        parsed(crate::spec::ServerHello { legacy_version: 0x0302, ..request() }, seq![7u8], false) == Err::<Selection, u8>(47u8),
        parsed(crate::spec::ServerHello { legacy_version: 0x0302, ..server() }, seq![7u8], false) is Ok,
{
    assert(parsed(crate::spec::ServerHello { legacy_version: 0x0300, ..server() }, seq![7u8], false) == Err::<Selection, u8>(70u8)) by (compute_only);
    assert(parsed(crate::spec::ServerHello { legacy_version: 0x0302, ..request() }, seq![7u8], false) == Err::<Selection, u8>(47u8)) by (compute_only);
    assert(parsed(crate::spec::ServerHello { legacy_version: 0x0302, ..server() }, seq![7u8], false) is Ok) by (compute_only);
}
/// §4.1.3: a server Random ending in the TLS 1.2 downgrade sentinel.
pub open spec fn sentinel_random() -> Seq<u8> {
    Seq::new(24, |i: int| 0u8) + downgrade_tls12()
}
/// §4.1.3: without supported_versions the sentinel gives illegal_parameter;
/// a ServerHello selecting TLS 1.3 does not indicate TLS 1.2 or below, so
/// its Random is not checked.
pub proof fn lemma_sentinel_only_below_tls13()
    ensures
        parameters(crate::spec::ServerHello { random: sentinel_random(), extensions: Seq::empty(), ..server() }, seq![7u8]) == Some(47u8),
        parameters(crate::spec::ServerHello { random: sentinel_random(), ..server() }, seq![7u8]) is None,
{
    assert(parameters(crate::spec::ServerHello { random: sentinel_random(), extensions: Seq::empty(), ..server() }, seq![7u8]) == Some(47u8)) by (compute_only);
    assert(parameters(crate::spec::ServerHello { random: sentinel_random(), ..server() }, seq![7u8]) is None) by (compute_only);
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
/// A HelloRetryRequest body echoing session ID 7, with `exts` after the
/// compression method (nothing, or an encoded extension block).
pub open spec fn retry_body(exts: Seq<u8>) -> Seq<u8> {
    seq![3u8, 3u8] + crate::spec::hrr_random() + seq![1u8, 7u8, 0x13u8, 3u8, 0u8] + exts
}
/// §4.1.3: the Random is examined first, so a HelloRetryRequest without
/// supported_versions is not a legacy ServerHello (protocol_version): with
/// no extension field it is malformed, and with only a cookie its missing
/// supported_versions is missing_extension (§4.1.4, §6.2).
pub proof fn lemma_retry_without_versions()
    ensures
        validate(seq![7u8], false, retry_body(Seq::empty())) == Err::<Selection, u8>(50u8),
        validate(seq![7u8], false, retry_body(seq![0u8, 7u8, 0u8, 44u8, 0u8, 3u8, 0u8, 1u8, 9u8])) == Err::<Selection, u8>(109u8),
{
    assert(validate(seq![7u8], false, retry_body(Seq::empty())) == Err::<Selection, u8>(50u8)) by (compute_only);
    assert(validate(seq![7u8], false, retry_body(seq![0u8, 7u8, 0u8, 44u8, 0u8, 3u8, 0u8, 1u8, 9u8])) == Err::<Selection, u8>(109u8)) by (compute_only);
}} // verus!
