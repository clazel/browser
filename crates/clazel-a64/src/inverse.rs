//! The encoder and the decoder are inverse on the subset (jit.md J.4, J.6),
//! and the proofs of the facts [`crate::contract`] leaves to this half.
//!
//! - [`lemma_encode_fits`] and [`lemma_canonical_injective`] prove the two
//!   statements about the spec that `contract.rs` names
//!   ([`encode_fits`], [`canonical_injective`]). Injectivity is the part that
//!   needs the work: two instructions of different variants have different
//!   words because their fixed bits differ ([`lemma_class_exact`]), and two of
//!   the same variant have different words because the fields can be read back
//!   ([`lemma_cand_class`]).
//! - [`decode_encode`] and [`encode_decode`] are the two directions on words:
//!   decoding what the encoder wrote gives the instruction back, and encoding
//!   what the decoder accepted gives the word back.
//! - [`encode_bytes`] and [`decode_bytes`] are the same on the four bytes of a
//!   word in memory (little-endian, [`word_bytes`]), and
//!   [`decode_encode_bytes`] is the round trip through them.
//! - [`A64`] implements the contract-only trait [`A64Codec`].

use super::api::A64Codec;
#[cfg(verus_only)]
use super::classes::*;
#[cfg(verus_only)]
use super::contract::*;
use super::decoder::*;
use super::encoder::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The canonical encoding of every instruction of the subset is a 32-bit word.
pub proof fn lemma_encode_fits()
    ensures
        encode_fits(),
{
    lemma_signed_fits();
    assert forall|i: Instr| valid_instr(i) implies 0 <= #[trigger] encode(i) < 0x1_0000_0000 by {
        match i {
            Instr::B { imm26 } => {
                assert(0 <= (imm26 as int) % 0x400_0000 < 0x400_0000);
            },
            Instr::BCond { cond, imm19 } => {
                assert(0 <= (imm19 as int) % 0x8_0000 < 0x8_0000);
            },
            Instr::CompareBranch { sf, iszero, t, imm19 } => {
                assert(0 <= (imm19 as int) % 0x8_0000 < 0x8_0000);
            },
            _ => {},
        }
    }
}

/// No two instructions of the subset share a canonical encoding.
pub proof fn lemma_canonical_injective()
    ensures
        canonical_injective(),
{
    assert forall|i: Instr, j: Instr, w: u32|
        is_canonical_encoding(w, i) && is_canonical_encoding(w, j) implies i == j by {
        lemma_class_exact(w, i);
        lemma_class_exact(w, j);
        lemma_cand_class(w, i);
        lemma_cand_class(w, j);
    }
}

/// The two inverse statements of the contract hold for every instruction and word.
pub proof fn lemma_inverse_contract(i: Instr, w: u32)
    ensures
        encode_decode_inverse(i, w),
        decode_encode_inverse(w, i),
{
}

/// For an instruction of the subset, decoding its encoding gives the
/// instruction back.
pub fn decode_encode(i: &Instr) -> (r: Option<Instr>)
    requires
        valid_instr(*i),
    ensures
        r == Some(*i),
{
    let w = encode_instr(i);
    let r = decode_instr(w);
    proof {
        lemma_canonical_injective();
        assert(is_canonical_encoding(w, *i));
        if r is Some {
            assert(is_canonical_encoding(w, r->0));
        }
    }
    r
}

/// If the decoder accepts a word, encoding the instruction gives the word
/// back; and it accepts exactly the words that are some instruction's
/// canonical encoding.
pub fn encode_decode(w: u32) -> (r: Option<u32>)
    ensures
        r is Some ==> r == Some(w),
        r is None ==> forall|i: Instr| !is_canonical_encoding(w, i),
        r is Some ==> exists|i: Instr| is_canonical_encoding(w, i),
{
    match decode_instr(w) {
        Some(i) => {
            let e = encode_instr(&i);
            Some(e)
        },
        None => None,
    }
}

/// The four bytes of the word in memory, least significant first.
pub fn encode_bytes(i: &Instr) -> (b: [u8; 4])
    requires
        valid_instr(*i),
    ensures
        b@ =~= word_bytes(encode(*i)),
{
    let w = encode_instr(i);
    proof {
        assert(w as int / 0x100_0000 < 0x100);
    }
    [(w % 256) as u8, ((w / 0x100) % 256) as u8, ((w / 0x1_0000) % 256) as u8, (w / 0x100_0000) as u8]
}

/// The word of four bytes in memory, least significant first (`u32::from_le_bytes`).
pub open spec fn le_word(b0: u8, b1: u8, b2: u8, b3: u8) -> int {
    b0 as int + 0x100 * (b1 as int) + 0x1_0000 * (b2 as int) + 0x100_0000 * (b3 as int)
}

/// `u32::from_le_bytes`.
pub fn le_word_exec(b0: u8, b1: u8, b2: u8, b3: u8) -> (w: u32)
    ensures
        w as int == le_word(b0, b1, b2, b3),
{
    (b0 as u32).wrapping_add((b1 as u32).wrapping_mul(0x100)).wrapping_add(
        (b2 as u32).wrapping_mul(0x1_0000),
    ).wrapping_add((b3 as u32).wrapping_mul(0x100_0000))
}

/// Decodes the four bytes of one word in memory.
pub fn decode_bytes(b0: u8, b1: u8, b2: u8, b3: u8) -> (r: Option<Instr>)
    ensures
        decode_ensures(le_word(b0, b1, b2, b3) as u32, r),
{
    let w = le_word_exec(b0, b1, b2, b3);
    decode_instr(w)
}

/// Bit-vector fact: the four bytes of a word, read back little-endian, give the word.
proof fn bv_le_word_roundtrip(w: u32)
    by (bit_vector)
    ensures
        w % 0x100 + 0x100 * ((w / 0x100) % 0x100) + 0x1_0000 * ((w / 0x1_0000) % 0x100)
            + 0x100_0000 * ((w / 0x100_0000) % 0x100) == w,
{
}

/// Reading back the bytes of a word gives the word.
pub proof fn lemma_le_word_roundtrip(w: u32, b: [u8; 4])
    requires
        b@ =~= word_bytes(w as int),
    ensures
        le_word(b[0], b[1], b[2], b[3]) == w as int,
{
    bv_le_word_roundtrip(w);
    assert(w as int / 0x100_0000 < 0x100);
}

/// For an instruction of the subset, decoding the bytes of its encoding gives
/// the instruction back.
pub fn decode_encode_bytes(i: &Instr) -> (r: Option<Instr>)
    requires
        valid_instr(*i),
    ensures
        r == Some(*i),
{
    let b = encode_bytes(i);
    let r = decode_bytes(b[0], b[1], b[2], b[3]);
    proof {
        lemma_canonical_injective();
        lemma_encode_fits();
        let w = encode(*i) as u32;
        lemma_le_word_roundtrip(w, b);
        assert(is_canonical_encoding(w, *i));
        if r is Some {
            assert(is_canonical_encoding(w, r->0));
        }
    }
    r
}

/// The encoder and the decoder, as the contract-only trait of
/// [`crate::api`].
pub struct A64;

impl A64Codec for A64 {
    fn encode_instr(i: &Instr) -> (out: u32) {
        crate::encoder::encode_instr(i)
    }

    fn decode_instr(w: u32) -> (r: Option<Instr>) {
        crate::decoder::decode_instr(w)
    }
}

} // verus!
