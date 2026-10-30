//! Security properties of server parameter acceptance.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Successful parameter checks bind all the offered fields, including version bytes.
pub proof fn lemma_parameters_bound(sh: crate::spec::ServerHello, session_id: Seq<u8>)
    requires super::spec::parameters(sh, session_id) is None,
    ensures super::contract::parameters_bound(sh, session_id),
{
    let data = super::spec::extension(sh.extensions, 43).unwrap();
    assert(data.len() == 2);
    assert(data.take(2) =~= data);
    crate::lemmas_pl::lemma_be_value_bound(data);
    assert(crate::spec::pow256(2) == 65536) by (compute_only);
    assert(crate::spec::be_value(data) == 0x0304);
    crate::lemmas_pl::lemma_be_bytes_of_be_value(data);
    assert(crate::spec::be_bytes(0x0304, 2) == seq![3u8, 4u8]) by (compute_only);
    assert(data =~= seq![3u8, 4u8]);
}
/// A second HRR never selects parameters or triggers another retry.
pub proof fn lemma_second_retry(sh: crate::spec::ServerHello)
    ensures super::spec::retry(sh, true) == Err(10u8),
{}
/// Every accepted share has the sole offered group and its required length.
pub proof fn lemma_share_length(sh: crate::spec::ServerHello, bytes: Seq<u8>)
    requires super::spec::share(sh) == Ok(super::spec::Selection::Share(bytes)),
    ensures bytes.len() == 32,
{}
/// This profile never changes key-share groups in a retry.
pub proof fn lemma_retry_never_replaces_share(sh: crate::spec::ServerHello, retried: bool)
    requires super::spec::extension(sh.extensions, 51) is Some,
    ensures super::spec::retry(sh, retried) is Err,
{}
} // verus!
