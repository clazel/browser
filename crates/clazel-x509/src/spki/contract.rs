//! Contracts for RFC 5280 SubjectPublicKeyInfo decoding.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn view_result(
    result: Option<super::exec::SubjectPublicKeyInfo<'_>>,
) -> Option<SubjectPublicKeyInfo> {
    match result { Some(value) => Some(value@), None => None }
}

pub open spec fn parse_subject_public_key_info_ensures(
    input: Seq<u8>, output: Option<SubjectPublicKeyInfo>,
) -> bool {
    output == parse_subject_public_key_info(input)
}

} // verus!
