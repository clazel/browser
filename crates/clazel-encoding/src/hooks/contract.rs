//! Contracts the executable "BOM sniff" and "decode" hooks must be proven
//! to meet, in terms of [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `bom_sniff(&[u8]) -> Option<Encoding>`: equals "BOM sniff"
/// (§6); `None` is null.
pub open spec fn bom_sniff_ensures(input: Seq<u8>, output: Option<crate::labels::spec::Encoding>) -> bool {
    output == bom_sniff(input)
}

/// Contract for `decode(&[u8], Encoding) -> Option<Vec<u32>>`: equals
/// "decode" (§6) with that fallback encoding, `None` when the encoding it
/// would use has no decoder in this crate.
pub open spec fn decode_ensures(input: Seq<u8>, encoding: crate::labels::spec::Encoding, output: Option<Seq<u32>>) -> bool {
    output == decode(input, encoding)
}

} // verus!
