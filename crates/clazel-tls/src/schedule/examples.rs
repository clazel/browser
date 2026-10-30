//! Concrete argument-routing witnesses for the RFC 8446 equations.
//! The tagged operations are not cryptography. RFC 8448 conformance
//! exercises real SHA-256/HMAC/HKDF outputs separately.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// An argument-tagging fixture, without any crypto assumption.
pub open spec fn fixture_crypto() -> Crypto {
    Crypto {
        hash: |m: Seq<u8>| seq![72u8] + m,
        extract: |salt: Seq<u8>, ikm: Seq<u8>| seq![69u8] + salt + ikm,
        expand: |secret: Seq<u8>, info: Seq<u8>, n: nat|
            seq![88u8] + secret + info + crate::spec::write_u16(n as u16),
        hmac: |key: Seq<u8>, m: Seq<u8>| seq![77u8] + key + m,
    }
}

/// RFC 8446 equation: label, with concrete tagged inputs.
pub proof fn lemma_label()
    ensures hkdf_label(seq![1u8], seq![2u8], 258) == seq![1u8, 2u8, 7u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 1u8, 1u8, 2u8],
{
    assert(hkdf_label(seq![1u8], seq![2u8], 258) == seq![1u8, 2u8, 7u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 1u8, 1u8, 2u8]) by (compute_only);
}

/// RFC 8446 equation: early, with concrete tagged inputs.
pub proof fn lemma_early()
    ensures early_secret(fixture_crypto()) == seq![69u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
{
    assert(early_secret(fixture_crypto()) == seq![69u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]) by (compute_only);
}

/// RFC 8446 equation: handshake, with concrete tagged inputs.
pub proof fn lemma_handshake()
    ensures handshake_secret(fixture_crypto(), seq![1u8], seq![2u8]) == seq![69u8, 88u8, 1u8, 0u8, 32u8, 13u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8, 1u8, 72u8, 0u8, 32u8, 2u8],
{
    assert(handshake_secret(fixture_crypto(), seq![1u8], seq![2u8]) == seq![69u8, 88u8, 1u8, 0u8, 32u8, 13u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8, 1u8, 72u8, 0u8, 32u8, 2u8]) by (compute_only);
}

/// RFC 8446 equation: master, with concrete tagged inputs.
pub proof fn lemma_master()
    ensures master_secret(fixture_crypto(), seq![1u8]) == seq![69u8, 88u8, 1u8, 0u8, 32u8, 13u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8, 1u8, 72u8, 0u8, 32u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
{
    assert(master_secret(fixture_crypto(), seq![1u8]) == seq![69u8, 88u8, 1u8, 0u8, 32u8, 13u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8, 1u8, 72u8, 0u8, 32u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]) by (compute_only);
}

/// RFC 8446 equation: derive, with concrete tagged inputs.
pub proof fn lemma_derive()
    ensures derive_secret(fixture_crypto(), seq![1u8], Label::ClientHandshake, seq![2u8]) == seq![88u8, 1u8, 0u8, 32u8, 18u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 99u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8, 2u8, 72u8, 2u8, 0u8, 32u8],
{
    assert(derive_secret(fixture_crypto(), seq![1u8], Label::ClientHandshake, seq![2u8]) == seq![88u8, 1u8, 0u8, 32u8, 18u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 99u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8, 2u8, 72u8, 2u8, 0u8, 32u8]) by (compute_only);
}

/// RFC 8446 equation: finished, with concrete tagged inputs.
pub proof fn lemma_finished()
    ensures finished(fixture_crypto(), seq![1u8], seq![2u8]) == seq![77u8, 88u8, 1u8, 0u8, 32u8, 14u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 102u8, 105u8, 110u8, 105u8, 115u8, 104u8, 101u8, 100u8, 0u8, 0u8, 32u8, 72u8, 2u8],
{
    assert(finished(fixture_crypto(), seq![1u8], seq![2u8]) == seq![77u8, 88u8, 1u8, 0u8, 32u8, 14u8, 116u8, 108u8, 115u8, 49u8, 51u8, 32u8, 102u8, 105u8, 110u8, 105u8, 115u8, 104u8, 101u8, 100u8, 0u8, 0u8, 32u8, 72u8, 2u8]) by (compute_only);
}

/// RFC 8446 ASCII label `derived`.
pub proof fn lemma_label_derived()
    ensures label_bytes(Label::Derived) == seq![100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8],
{
    assert(label_bytes(Label::Derived) == seq![100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8]) by (compute_only);
}

/// RFC 8446 ASCII label `c hs traffic`.
pub proof fn lemma_label_clienthandshake()
    ensures label_bytes(Label::ClientHandshake) == seq![99u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
{
    assert(label_bytes(Label::ClientHandshake) == seq![99u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8]) by (compute_only);
}

/// RFC 8446 ASCII label `s hs traffic`.
pub proof fn lemma_label_serverhandshake()
    ensures label_bytes(Label::ServerHandshake) == seq![115u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
{
    assert(label_bytes(Label::ServerHandshake) == seq![115u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8]) by (compute_only);
}

/// RFC 8446 ASCII label `c ap traffic`.
pub proof fn lemma_label_clientapplication()
    ensures label_bytes(Label::ClientApplication) == seq![99u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
{
    assert(label_bytes(Label::ClientApplication) == seq![99u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8]) by (compute_only);
}

/// RFC 8446 ASCII label `s ap traffic`.
pub proof fn lemma_label_serverapplication()
    ensures label_bytes(Label::ServerApplication) == seq![115u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
{
    assert(label_bytes(Label::ServerApplication) == seq![115u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8]) by (compute_only);
}

/// RFC 8446 ASCII label `finished`.
pub proof fn lemma_label_finished()
    ensures label_bytes(Label::Finished) == seq![102u8, 105u8, 110u8, 105u8, 115u8, 104u8, 101u8, 100u8],
{
    assert(label_bytes(Label::Finished) == seq![102u8, 105u8, 110u8, 105u8, 115u8, 104u8, 101u8, 100u8]) by (compute_only);
}

/// RFC 8446 ASCII label `traffic upd`.
pub proof fn lemma_label_update()
    ensures label_bytes(Label::Update) == seq![116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8, 32u8, 117u8, 112u8, 100u8],
{
    assert(label_bytes(Label::Update) == seq![116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8, 32u8, 117u8, 112u8, 100u8]) by (compute_only);
}

/// RFC 8446 ASCII label `key`.
pub proof fn lemma_label_key()
    ensures label_bytes(Label::Key) == seq![107u8, 101u8, 121u8],
{
    assert(label_bytes(Label::Key) == seq![107u8, 101u8, 121u8]) by (compute_only);
}

/// RFC 8446 ASCII label `iv`.
pub proof fn lemma_label_iv()
    ensures label_bytes(Label::Iv) == seq![105u8, 118u8],
{
    assert(label_bytes(Label::Iv) == seq![105u8, 118u8]) by (compute_only);
}

} // verus!
