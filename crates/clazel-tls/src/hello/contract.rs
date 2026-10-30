//! Contracts for the fixed TLS 1.3 ClientHello profile's server selection.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Every result agrees with the complete byte-level acceptance algorithm.
pub open spec fn validate_ensures(session_id: Seq<u8>, retried: bool, body: Seq<u8>,
    out: Result<super::spec::Selection, u8>) -> bool
{
    out == super::spec::validate(session_id, retried, body)
}
/// Accepted fields are bound to this offered session, TLS version and cipher.
pub open spec fn parameters_bound(sh: crate::spec::ServerHello, session_id: Seq<u8>) -> bool {
    sh.session_id_echo == session_id
        && sh.cipher_suite == 0x1303 && sh.compression == 0
        && super::spec::extension(sh.extensions, 43) == Some(seq![3u8, 4u8])
}
} // verus!
