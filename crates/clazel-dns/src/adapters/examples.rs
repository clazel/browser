//! The spec's examples, evaluated on small buffers laid out as
//! `GetAdaptersAddresses` lays them out: what the DNS servers of the
//! adapters are, and what makes a server or a list end.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies (see `examples.rs`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `n` zero octets.
pub open spec fn zeros(n: nat) -> Seq<u8>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        zeros((n - 1) as nat).push(0u8)
    }
}

/// `v` as `n` octets, little-endian.
pub open spec fn le_bytes(v: nat, n: nat) -> Seq<u8>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![(v % 256) as u8] + le_bytes(v / 256, (n - 1) as nat)
    }
}

/// The address the examples' buffers start at.
pub open spec fn base() -> nat {
    0x1000
}

/// An `IP_ADAPTER_ADDRESSES_LH` up to `OperStatus` (108 octets).
pub open spec fn adapter(next: nat, dns: nat, status: nat) -> Seq<u8> {
    zeros(8) + le_bytes(next, 8) + zeros(32) + le_bytes(dns, 8) + zeros(48) + le_bytes(status, 4)
}

/// An `IP_ADAPTER_DNS_SERVER_ADDRESS_XP` up to `iSockaddrLength` (28 octets).
pub open spec fn server(next: nat, sockaddr: nat, len: nat) -> Seq<u8> {
    zeros(8) + le_bytes(next, 8) + le_bytes(sockaddr, 8) + le_bytes(len, 4)
}

/// A `SOCKADDR_IN` (16 octets) for the four octets `a`.
pub open spec fn sockaddr_in(a: Seq<u8>) -> Seq<u8> {
    le_bytes(2, 2) + zeros(2) + a + zeros(8)
}

/// A `SOCKADDR_IN6` (28 octets) for the sixteen octets `a`.
pub open spec fn sockaddr_in6(a: Seq<u8>) -> Seq<u8> {
    le_bytes(23, 2) + zeros(6) + a + zeros(4)
}

/// `fec0:0:0:ffff::1`, the site-local default Windows lists.
pub open spec fn fec0_default() -> Seq<u8> {
    seq![0xFEu8, 0xC0, 0, 0, 0, 0, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0, 0, 1]
}

/// `fe80::1`, a link-local address.
pub open spec fn fe80_one() -> Seq<u8> {
    seq![0xFEu8, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
}

/// `2606:4700:4700::1111`.
pub open spec fn cloudflare_v6() -> Seq<u8> {
    seq![0x26u8, 0x06, 0x47, 0x00, 0x47, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0x11, 0x11]
}

/// One adapter with `status` and one server, `1.1.1.1`, whose
/// `iSockaddrLength` is `len`.
pub open spec fn one_server(status: nat, len: nat) -> Seq<u8> {
    adapter(0, base() + 108, status) + server(0, base() + 136, len) + sockaddr_in(seq![1u8, 1, 1, 1])
}

/// One adapter that is up, whose servers are the site-local default and
/// then `8.8.8.8`.
pub open spec fn fec0_then_v4() -> Seq<u8> {
    adapter(0, base() + 108, 1) + server(base() + 136, base() + 164, 28) + server(0, base() + 192, 16)
        + sockaddr_in6(fec0_default()) + sockaddr_in(seq![8u8, 8, 8, 8])
}

/// One adapter that is up, with one IPv6 server `a`.
pub open spec fn one_v6(a: Seq<u8>) -> Seq<u8> {
    adapter(0, base() + 108, 1) + server(0, base() + 136, 28) + sockaddr_in6(a)
}

/// Two adapters that are up: the first's server is `1.1.1.1`, the
/// second's `9.9.9.9`.
pub open spec fn two_adapters() -> Seq<u8> {
    adapter(base() + 108, base() + 216, 1) + adapter(0, base() + 244, 1) + server(0, base() + 272, 16)
        + server(0, base() + 288, 16) + sockaddr_in(seq![1u8, 1, 1, 1]) + sockaddr_in(seq![9u8, 9, 9, 9])
}

/// An adapter and a server whose `Next` pointers point back at themselves.
pub open spec fn self_links() -> Seq<u8> {
    adapter(base(), base() + 108, 1) + server(base() + 108, base() + 136, 16) + sockaddr_in(seq![1u8, 1, 1, 1])
}

/// One adapter that is up and one IPv4 server: `1.1.1.1`.
pub proof fn lemma_adapters_example_0()
    ensures
        dns_servers(one_server(1, 16), base()) == seq![crate::spec::Addr::V4(16843009)],
{
    assert(dns_servers(one_server(1, 16), base()) == seq![crate::spec::Addr::V4(16843009)]) by (compute_only);
}

/// The same adapter down (`IfOperStatusDown`, 2): no servers.
pub proof fn lemma_adapters_example_1()
    ensures
        dns_servers(one_server(2, 16), base()) == Seq::<crate::spec::Addr>::empty(),
{
    assert(dns_servers(one_server(2, 16), base()) == Seq::<crate::spec::Addr>::empty()) by (compute_only);
}

/// The site-local default is dropped and the IPv4 server after it kept.
pub proof fn lemma_adapters_example_2()
    ensures
        dns_servers(fec0_then_v4(), base()) == seq![crate::spec::Addr::V4(134744072)],
{
    assert(dns_servers(fec0_then_v4(), base()) == seq![crate::spec::Addr::V4(134744072)]) by (compute_only);
}

/// A global IPv6 server is kept: `2606:4700:4700::1111`.
pub proof fn lemma_adapters_example_3()
    ensures
        dns_servers(one_v6(cloudflare_v6()), base()) == seq![crate::spec::Addr::V6(0x2606_4700_4700_0000_0000_0000_0000_1111)],
{
    assert(dns_servers(one_v6(cloudflare_v6()), base()) == seq![crate::spec::Addr::V6(0x2606_4700_4700_0000_0000_0000_0000_1111)]) by (compute_only);
}

/// A link-local server is dropped: `fe80::1`.
pub proof fn lemma_adapters_example_4()
    ensures
        dns_servers(one_v6(fe80_one()), base()) == Seq::<crate::spec::Addr>::empty(),
{
    assert(dns_servers(one_v6(fe80_one()), base()) == Seq::<crate::spec::Addr>::empty()) by (compute_only);
}

/// Two adapters: their servers in list order.
pub proof fn lemma_adapters_example_5()
    ensures
        dns_servers(two_adapters(), base()) == seq![crate::spec::Addr::V4(16843009), crate::spec::Addr::V4(151587081)],
{
    assert(dns_servers(two_adapters(), base()) == seq![crate::spec::Addr::V4(16843009), crate::spec::Addr::V4(151587081)]) by (compute_only);
}

/// `Next` pointers back to their own record end both lists: the server is
/// read once.
pub proof fn lemma_adapters_example_6()
    ensures
        dns_servers(self_links(), base()) == seq![crate::spec::Addr::V4(16843009)],
{
    assert(dns_servers(self_links(), base()) == seq![crate::spec::Addr::V4(16843009)]) by (compute_only);
}

/// A socket address that runs past the end of the buffer is not read.
pub proof fn lemma_adapters_example_7()
    ensures
        dns_servers(one_server(1, 16).subrange(0, 140), base()) == Seq::<crate::spec::Addr>::empty(),
{
    assert(dns_servers(one_server(1, 16).subrange(0, 140), base()) == Seq::<crate::spec::Addr>::empty()) by (compute_only);
}

/// An `iSockaddrLength` shorter than a `SOCKADDR_IN`: not a server.
pub proof fn lemma_adapters_example_8()
    ensures
        dns_servers(one_server(1, 8), base()) == Seq::<crate::spec::Addr>::empty(),
{
    assert(dns_servers(one_server(1, 8), base()) == Seq::<crate::spec::Addr>::empty()) by (compute_only);
}

/// The same buffer read at another base address: every pointer is outside
/// it, so the adapter's list of servers is empty.
pub proof fn lemma_adapters_example_9()
    ensures
        dns_servers(one_server(1, 16), base() + 0x100) == Seq::<crate::spec::Addr>::empty(),
{
    assert(dns_servers(one_server(1, 16), base() + 0x100) == Seq::<crate::spec::Addr>::empty()) by (compute_only);
}

/// No adapters (`ERROR_NO_DATA`): an empty buffer has no servers.
pub proof fn lemma_adapters_example_10()
    ensures
        dns_servers(Seq::<u8>::empty(), base()) == Seq::<crate::spec::Addr>::empty(),
{
    assert(dns_servers(Seq::<u8>::empty(), base()) == Seq::<crate::spec::Addr>::empty()) by (compute_only);
}

} // verus!
