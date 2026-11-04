//! Contract the executable adapter-buffer reader must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `dns_servers(&[u8], u64) -> Vec<Addr>`: the DNS servers of
/// the adapters that are up, in list order.
pub open spec fn dns_servers_ensures(buffer: Seq<u8>, base: nat, output: Seq<crate::spec::Addr>) -> bool {
    output == dns_servers(buffer, base)
}

} // verus!
