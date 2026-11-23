//! The RFCs' own worked examples, evaluated on the spec. Kept apart from
//! [`super::lemmas`] so that a mutant that breaks one of them does not stop
//! Verus before it checks a kill certificate there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 1951 §3.2.2's first example: the alphabet ABCD with bit lengths
/// (2, 1, 3, 3) gets the codes A = 10, B = 0, C = 110, D = 111 ("the code is
/// completely defined by the sequence of bit lengths (2, 1, 3, 3)").
pub proof fn lemma_example_abcd() {
    let lens = seq![2nat, 1, 3, 3];
    reveal_with_fuel(count_eq, 10);
    reveal_with_fuel(next_code, 6);
    assert(code_of(lens, 0) == 2);
    assert(code_of(lens, 1) == 0);
    assert(code_of(lens, 2) == 6);
    assert(code_of(lens, 3) == 7);
}

/// RFC 1951 §3.2.2's worked example: "the alphabet ABCDEFGH, with bit lengths
/// (3, 3, 3, 3, 3, 2, 4, 4). After step 1, we have: N 2 3 4, bl_count[N] 1 5
/// 2. Step 2 computes the following next_code values: N 1 2 3 4, next_code[N]
/// 0 0 2 14. Step 3 produces the following code values: A 010, B 011, C 100,
/// D 101, E 110, F 00, G 1110, H 1111."
pub proof fn lemma_example_abcdefgh() {
    let lens = seq![3nat, 3, 3, 3, 3, 2, 4, 4];
    reveal_with_fuel(count_eq, 10);
    reveal_with_fuel(next_code, 6);
    assert(bl_count(lens, 2) == 1);
    assert(bl_count(lens, 3) == 5);
    assert(bl_count(lens, 4) == 2);
    assert(next_code(lens, 1) == 0);
    assert(next_code(lens, 2) == 0);
    assert(next_code(lens, 3) == 2);
    assert(next_code(lens, 4) == 14);
    assert(code_of(lens, 0) == 2);
    assert(code_of(lens, 1) == 3);
    assert(code_of(lens, 2) == 4);
    assert(code_of(lens, 3) == 5);
    assert(code_of(lens, 4) == 6);
    assert(code_of(lens, 5) == 0);
    assert(code_of(lens, 6) == 14);
    assert(code_of(lens, 7) == 15);
}


/// RFC 1950 §2.2 and §2.3: each way a header is wrong (streams of two bytes,
/// so that nothing is decoded), and a right header with no data after it.
pub proof fn lemma_example_zlib()
    ensures
        zlib_decompress(seq![0x78u8], 10) == Err::<(Seq<u8>, nat), Error>(Error::Truncated),
        zlib_decompress(seq![0x78u8, 0x00], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibCheck),
        zlib_decompress(seq![0x78u8, 0x9D], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibCheck),
        zlib_decompress(seq![0x79u8, 0x18], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibMethod),
        zlib_decompress(seq![0x88u8, 0x1C], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibWindow),
        zlib_decompress(seq![0x78u8, 0x20], 10) == Err::<(Seq<u8>, nat), Error>(Error::PresetDictionary),
        zlib_decompress(seq![0x78u8, 0x9C], 10) == Err::<(Seq<u8>, nat), Error>(Error::Truncated),
{
    assert(zlib_decompress(seq![0x78u8], 10) == Err::<(Seq<u8>, nat), Error>(Error::Truncated)) by (compute_only);
    assert(zlib_decompress(seq![0x78u8, 0x00], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibCheck)) by (compute_only);
    assert(zlib_decompress(seq![0x78u8, 0x9D], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibCheck)) by (compute_only);
    assert(zlib_decompress(seq![0x79u8, 0x18], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibMethod)) by (compute_only);
    assert(zlib_decompress(seq![0x88u8, 0x1C], 10) == Err::<(Seq<u8>, nat), Error>(Error::BadZlibWindow)) by (compute_only);
    assert(zlib_decompress(seq![0x78u8, 0x20], 10) == Err::<(Seq<u8>, nat), Error>(Error::PresetDictionary)) by (compute_only);
    assert(zlib_decompress(seq![0x78u8, 0x9C], 10) == Err::<(Seq<u8>, nat), Error>(Error::Truncated)) by (compute_only);
}

} // verus!
