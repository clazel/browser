//! Proofs of RFC 9525 security properties of the identity specification.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Security property: an IP-ID reference is never authenticated by a DNS-ID
/// SAN, regardless of the byte strings.
pub proof fn lemma_ip_dns_type_separation(reference: Seq<u8>, presented: Seq<u8>)
    ensures !service_identity_match(
        ReferenceIdentity::Ip(reference), PresentedIdentity::Dns(presented))
{
    assert(!service_identity_match(
        ReferenceIdentity::Ip(reference), PresentedIdentity::Dns(presented))) by (compute_only);
}

/// Security property: a DNS-ID reference is never authenticated by an
/// iPAddress SAN, regardless of the byte strings.
pub proof fn lemma_dns_ip_type_separation(reference: Seq<u8>, presented: Seq<u8>)
    ensures !service_identity_match(
        ReferenceIdentity::Dns(reference), PresentedIdentity::Ip(presented))
{
    assert(!service_identity_match(
        ReferenceIdentity::Dns(reference), PresentedIdentity::Ip(presented))) by (compute_only);
}

/// Security property: equal valid-width binary IP identifiers match exactly.
pub proof fn lemma_ip_identity_matches(address: Seq<u8>)
    requires address.len() == 4 || address.len() == 16
    ensures service_identity_match(
        ReferenceIdentity::Ip(address), PresentedIdentity::Ip(address))
{
    assert(service_identity_match(
        ReferenceIdentity::Ip(address), PresentedIdentity::Ip(address)));
}

/// Security property: equal-width but unequal IP values never match.
pub proof fn lemma_ip_unequal_does_not_match(reference: Seq<u8>, presented: Seq<u8>)
    requires (reference.len() == 4 || reference.len() == 16), reference != presented
    ensures !service_identity_match(
        ReferenceIdentity::Ip(reference), PresentedIdentity::Ip(presented))
{
    assert(!service_identity_match(
        ReferenceIdentity::Ip(reference), PresentedIdentity::Ip(presented)));
}

/// RFC 9525 §6.3 security property: a wildcard matches only one reference
/// label, so `*.example.test` does not match `a.b.example.test`.
pub proof fn lemma_dns_wildcard_matches_one_label_only()
    ensures !wildcard_matches_reference(
        seq![b'a', b'.', b'b', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
        seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
    )
{
    assert(!wildcard_matches_reference(
        seq![b'a', b'.', b'b', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
        seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
    )) by (compute_only);
}

/// RFC 9525 §6.3 identity matcher consequence of the one-label wildcard rule.
pub proof fn lemma_dns_match_wildcard_matches_one_label_only()
    ensures !dns_match(
        seq![b'a', b'.', b'b', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
        seq![b'*', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
    )
{
    hide(wildcard_suffix_is_public_suffix);
    lemma_dns_wildcard_matches_one_label_only();
    reveal(dns_match);
    assert(seq![b'*', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't']
        .subrange(2, 14) =~= seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't']) by (compute_only);
    assert(!wildcard_matches_reference(
        seq![b'a', b'.', b'b', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
        seq![b'*', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't']
            .subrange(2, 14)));
    assert(!dns_match(
        seq![b'a', b'.', b'b', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
        seq![b'*', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
    ));
}

} // verus!
