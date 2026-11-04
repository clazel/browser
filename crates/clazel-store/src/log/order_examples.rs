//! Examples of the key order, evaluated on [`super::spec`] by Verus. A module
//! of its own: [`super::examples`] evaluates CRCs and takes far longer.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The order is by unsigned octets, a prefix first, and never reflexive.
pub proof fn example_key_less()
    ensures
        key_less(seq![], seq![0x00u8]),
        !key_less(seq![], seq![]),
        !key_less(seq![0x00u8], seq![]),
        key_less(seq![0x61u8], seq![0x62u8]),
        !key_less(seq![0x62u8], seq![0x61u8]),
        key_less(seq![0x61u8], seq![0x61u8, 0x00]),
        key_less(seq![0x61u8, 0xff], seq![0x62u8]),
        key_less(seq![0x7fu8], seq![0x80u8]),
        !key_less(seq![0x61u8, 0x62], seq![0x61u8, 0x62]),
{
    assert(key_less(seq![], seq![0x00u8])) by (compute_only);
    assert(!key_less(seq![], seq![])) by (compute_only);
    assert(!key_less(seq![0x00u8], seq![])) by (compute_only);
    assert(key_less(seq![0x61u8], seq![0x62u8])) by (compute_only);
    assert(!key_less(seq![0x62u8], seq![0x61u8])) by (compute_only);
    assert(key_less(seq![0x61u8], seq![0x61u8, 0x00])) by (compute_only);
    assert(key_less(seq![0x61u8, 0xff], seq![0x62u8])) by (compute_only);
    assert(key_less(seq![0x7fu8], seq![0x80u8])) by (compute_only);
    assert(!key_less(seq![0x61u8, 0x62], seq![0x61u8, 0x62])) by (compute_only);
}

} // verus!
