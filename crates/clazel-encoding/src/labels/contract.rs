//! Contracts the executable "get an encoding" and name lookup must be
//! proven to meet, in terms of [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `get_an_encoding(&[u32]) -> Option<Encoding>`: equals "get
/// an encoding" (§4.2); `None` is failure.
pub open spec fn get_an_encoding_ensures(label: Seq<u32>, output: Option<Encoding>) -> bool {
    output == get_an_encoding(label)
}

/// Contract for `name(Encoding) -> Vec<u8>`: the encoding's name, as bytes
/// (it is ASCII).
pub open spec fn name_ensures(e: Encoding, output: Seq<u8>) -> bool {
    output.map_values(|b: u8| b as u32) == name(e)
}

} // verus!
