//! Contracts for the executable `PathCert` and `Anchor` constructors.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The executable `parse_path_cert` returns exactly the composed model.
pub open spec fn parse_path_cert_ensures(der: Seq<u8>, output: Option<PathCert>) -> bool {
    output == parse_path_cert(der)
}

/// The executable `anchor_from_root` returns exactly the anchor model.
pub open spec fn anchor_from_root_ensures(
    der: Seq<u8>, server_distrust_after: Option<Seq<u8>>, output: Option<Anchor>,
) -> bool {
    output == anchor_from_root(der, server_distrust_after)
}

} // verus!
