//! The examples of RFC 7143 §A.4 "CRC Examples", evaluated on the spec by
//! Verus. They check the transcription, above all its reading of §11's bit
//! numbering (see [`super::spec`]): read the other way, none of these holds.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §A.4, "32 bytes of zeroes": `aa 36 91 8a`.
pub proof fn lemma_crc32c_example_zeros()
    ensures
        crc32c(Seq::new(32, |i: int| 0u8)) == seq![0xaau8, 0x36, 0x91, 0x8a],
{
    reveal(vstd::arithmetic::power::pow);
    assert(crc32c(Seq::new(32, |i: int| 0u8)) == seq![0xaau8, 0x36, 0x91, 0x8a]) by (compute_only);
}

/// §A.4, "32 bytes of ones": `43 ab a8 62`.
pub proof fn lemma_crc32c_example_ones()
    ensures
        crc32c(Seq::new(32, |i: int| 0xffu8)) == seq![0x43u8, 0xab, 0xa8, 0x62],
{
    reveal(vstd::arithmetic::power::pow);
    assert(crc32c(Seq::new(32, |i: int| 0xffu8)) == seq![0x43u8, 0xab, 0xa8, 0x62]) by (compute_only);
}

/// §A.4, "32 bytes of incrementing 00..1f": `4e 79 dd 46`.
pub proof fn lemma_crc32c_example_incrementing()
    ensures
        crc32c(Seq::new(32, |i: int| i as u8)) == seq![0x4eu8, 0x79, 0xdd, 0x46],
{
    reveal(vstd::arithmetic::power::pow);
    assert(crc32c(Seq::new(32, |i: int| i as u8)) == seq![0x4eu8, 0x79, 0xdd, 0x46]) by (compute_only);
}

/// §A.4, "32 bytes of decrementing 1f..00": `5c db 3f 11`.
pub proof fn lemma_crc32c_example_decrementing()
    ensures
        crc32c(Seq::new(32, |i: int| (31 - i) as u8)) == seq![0x5cu8, 0xdb, 0x3f, 0x11],
{
    reveal(vstd::arithmetic::power::pow);
    assert(crc32c(Seq::new(32, |i: int| (31 - i) as u8)) == seq![0x5cu8, 0xdb, 0x3f, 0x11]) by (compute_only);
}

} // verus!
