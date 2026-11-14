//! Contracts the executable functions must be proven to meet. Each exec
//! function's `ensures` clause is exactly one of these predicates, so
//! reviewing these and [`super::spec`] is enough to know what the
//! implementation guarantees. All are about the list the generated tables
//! hold ([`super::table::psl_rules`]), or its ICANN section
//! ([`super::table::psl_icann_rules`]); the executable code reads those
//! tables, so the proofs are relative to them.
//!
//! Strings are code points as `u32`, as in `clazel-url`. A function that
//! returns a suffix of its input returns a copy.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `public_suffix_of_domain_exec(&[u32]) -> Option<Vec<u32>>`:
/// URL §3.2 "obtain the public suffix of a host" for a domain.
pub open spec fn public_suffix_of_domain_ensures(domain: Seq<u32>, output: Option<Seq<u32>>) -> bool {
    output == public_suffix_of_domain(super::table::psl_rules(), domain)
}

/// Contract for `registrable_domain_of_domain_exec(&[u32]) ->
/// Option<Vec<u32>>`: URL §3.2 "obtain the registrable domain of a host"
/// for a domain.
pub open spec fn registrable_domain_of_domain_ensures(domain: Seq<u32>, output: Option<Seq<u32>>) -> bool {
    output == registrable_domain_of_domain(super::table::psl_rules(), domain)
}

/// Contract for `is_public_suffix_exec(&[u32]) -> bool`.
pub open spec fn is_public_suffix_ensures(domain: Seq<u32>, output: bool) -> bool {
    output == is_public_suffix(super::table::psl_rules(), domain)
}

/// Contract for `is_icann_public_suffix_exec(&[u32]) -> bool`:
/// `is_public_suffix` over the ICANN section alone.
pub open spec fn is_icann_public_suffix_ensures(domain: Seq<u32>, output: bool) -> bool {
    output == is_public_suffix(super::table::psl_icann_rules(), domain)
}

/// Contract for `cookie_root_of_domain_exec(&[u32]) -> Vec<u32>`: the cookie
/// root of a domain.
pub open spec fn cookie_root_of_domain_ensures(domain: Seq<u32>, output: Seq<u32>) -> bool {
    output == cookie_root_of_domain(super::table::psl_rules(), domain)
}

/// Contract for `public_suffix_exec(&ParsedHost) -> Option<Vec<u32>>`: URL
/// §3.2 "obtain the public suffix of a host".
pub open spec fn public_suffix_ensures(host: clazel_url::host::spec::Host, output: Option<Seq<u32>>) -> bool {
    output == public_suffix(super::table::psl_rules(), host)
}

/// Contract for `registrable_domain_exec(&ParsedHost) -> Option<Vec<u32>>`:
/// URL §3.2 "obtain the registrable domain of a host".
pub open spec fn registrable_domain_ensures(host: clazel_url::host::spec::Host, output: Option<Seq<u32>>) -> bool {
    output == registrable_domain(super::table::psl_rules(), host)
}

/// Contract for `cookie_root_exec(&ParsedHost) -> ParsedHost`: the cookie
/// root of a host.
pub open spec fn cookie_root_ensures(host: clazel_url::host::spec::Host, output: clazel_url::host::spec::Host) -> bool {
    output == cookie_root(super::table::psl_rules(), host)
}

} // verus!
