//! Contracts for RFC 5280 §4.1.2 TBSCertificate parsing.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub open spec fn view_result(
    result: Option<super::exec::TbsCertificate<'_>>,
) -> Option<TbsCertificate> {
    match result {
        Some(value) => Some(value@),
        None => None,
    }
}

pub open spec fn parse_tbs_certificate_ensures(
    input: Seq<u8>, output: Option<TbsCertificate>,
) -> bool {
    output == parse_tbs_certificate(input)
}

} // verus!
