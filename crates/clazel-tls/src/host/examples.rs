//! Known answers for [`super::spec`], evaluated (`by (compute_only)`): the
//! bounds of `host_ok` and RFC 6066 §3's rule for server_name. They are the
//! theorems the mutation certificates in `mutations.json` contradict.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A DNS name of `n` octets `h`.
pub open spec fn name_of(n: nat) -> Seq<u8> { Seq::new(n, |i: int| 104u8) }

/// An address of `n` octets.
pub open spec fn address_of(n: nat) -> Seq<u8> { Seq::new(n, |i: int| 1u8) }

/// A DNS name of `n` octets, `h` in labels of 63 separated by dots.
pub open spec fn labels_of(n: nat) -> Seq<u8> { Seq::new(n, |i: int| if i % 64 == 63 { 0x2eu8 } else { 104u8 }) }

/// `host_ok`: a name of 1 to 253 octets with no trailing dot; an address of
/// 4 or 16 octets.
pub proof fn lemma_host_bounds()
    ensures
        host_ok(Host::Dns(name_of(1))),
        host_ok(Host::Dns(labels_of(253))),
        !host_ok(Host::Dns(labels_of(254))),
        !host_ok(Host::Dns(seq![104u8, 0x2eu8])),
        host_ok(Host::Ip(address_of(4))),
        host_ok(Host::Ip(address_of(16))),
        !host_ok(Host::Ip(address_of(5))),
        !host_ok(Host::Ip(address_of(0))),
{
    assert(host_ok(Host::Dns(name_of(1)))) by (compute_only);
    assert(host_ok(Host::Dns(labels_of(253)))) by (compute_only);
    assert(!host_ok(Host::Dns(labels_of(254)))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![104u8, 0x2eu8]))) by (compute_only);
    assert(host_ok(Host::Ip(address_of(4)))) by (compute_only);
    assert(host_ok(Host::Ip(address_of(16)))) by (compute_only);
    assert(!host_ok(Host::Ip(address_of(5)))) by (compute_only);
    assert(!host_ok(Host::Ip(address_of(0)))) by (compute_only);
}

/// `dns_labels_ok`: RFC 2181 §11's labels of 1 to 63 octets, of any ASCII
/// octets (an underscore included), and RFC 6066 §3's "Literal IPv4 and IPv6
/// addresses are not permitted".
pub proof fn lemma_dns_names()
    ensures
        host_ok(Host::Dns(seq![0x61u8, 0x5fu8, 0x62u8, 0x2eu8, 0x65u8])),
        host_ok(Host::Dns(name_of(63))),
        !host_ok(Host::Dns(name_of(64))),
        !host_ok(Host::Dns(seq![104u8, 0x2eu8, 0x2eu8, 104u8])),
        !host_ok(Host::Dns(seq![0x2eu8, 104u8])),
        !host_ok(Host::Dns(seq![0xe9u8])),
        !host_ok(Host::Dns(seq![0x3au8, 0x3au8, 0x31u8])),
        !host_ok(Host::Dns(seq![0x31u8, 0x2eu8, 0x32u8])),
        !host_ok(Host::Dns(seq![104u8, 0x2eu8, 0x32u8])),
        host_ok(Host::Dns(seq![0x31u8, 0x2eu8, 0x32u8, 104u8])),
{
    assert(host_ok(Host::Dns(seq![0x61u8, 0x5fu8, 0x62u8, 0x2eu8, 0x65u8]))) by (compute_only);
    assert(host_ok(Host::Dns(name_of(63)))) by (compute_only);
    assert(!host_ok(Host::Dns(name_of(64)))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![104u8, 0x2eu8, 0x2eu8, 104u8]))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![0x2eu8, 104u8]))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![0xe9u8]))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![0x3au8, 0x3au8, 0x31u8]))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![0x31u8, 0x2eu8, 0x32u8]))) by (compute_only);
    assert(!host_ok(Host::Dns(seq![104u8, 0x2eu8, 0x32u8]))) by (compute_only);
    assert(host_ok(Host::Dns(seq![0x31u8, 0x2eu8, 0x32u8, 104u8]))) by (compute_only);
}

/// RFC 6066 §3: a DNS host's HostName is its name; an address has none.
pub proof fn lemma_sni_host_name()
    ensures
        sni_host_name(Host::Dns(seq![104u8])) == Some(seq![104u8]),
        sni_host_name(Host::Ip(seq![192u8, 0, 2, 10])) is None,
{
    assert(sni_host_name(Host::Dns(seq![104u8])) == Some(seq![104u8])) by (compute_only);
    assert(sni_host_name(Host::Ip(seq![192u8, 0, 2, 10])) is None) by (compute_only);
}

} // verus!
