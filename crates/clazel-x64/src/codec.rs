//! The implementation of [`crate::api::X64Codec`] and the proofs that the
//! encoder and the decoder are inverse on the subset (jit.md J.3, J.6).
//!
//! - [`X64::encode_instr`] is [`encode_exec`], proven equal to the spec's
//!   `encode`.
//! - [`X64::decode_instr`] is [`decode_exec`], proven to meet `decode_ensures`.
//! - [`lemma_encode_decode_inverse`] and [`lemma_decode_encode_inverse`] are
//!   the two inverse statements of `contract.rs`, for every instruction and
//!   every input, from the contracts and the prefix-freeness lemma.

use super::api::X64Codec;
use super::decoder_exec::decode_exec;
use super::encoder::encode_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The codec of the subset.
pub struct X64;

impl X64Codec for X64 {
    fn encode_instr(i: &Instr) -> (out: Vec<u8>) {
        encode_exec(i)
    }

    fn decode_instr(bytes: &[u8]) -> (r: Option<(Instr, usize)>) {
        decode_exec(bytes)
    }
}

/// The encoder's output is read back by the decoder, whatever follows it:
/// a valid instruction's canonical encoding followed by anything begins with
/// that encoding (the statement of `encode_decode_inverse`).
pub proof fn lemma_encode_decode_inverse(i: Instr, rest: Seq<u8>)
    ensures
        crate::contract::encode_decode_inverse(i, rest),
{
    if valid_instr(i) {
        let e = encode(i);
        assert((e + rest).subrange(0, e.len() as int) =~= e);
    }
}

/// Whatever the decoder accepts, the encoder writes back: a `Some((i, n))`
/// satisfying `decode_ensures` has `encode(i)` equal to the `n` bytes read.
pub proof fn lemma_decode_encode_inverse(bytes: Seq<u8>, i: Instr, n: usize)
    ensures
        crate::contract::decode_encode_inverse(bytes, i, n),
{
}

/// The decoder, run on the encoder's output followed by any bytes, returns
/// that instruction and its encoded length. Uses the prefix-freeness of the
/// canonical encodings (`decoder_proofs::lemma_canonical_prefix_free`).
pub proof fn lemma_roundtrip(i: Instr, rest: Seq<u8>, r: Option<(Instr, usize)>)
    requires
        valid_instr(i),
        crate::contract::decode_ensures(encode(i) + rest, r),
    ensures
        r == Some((i, encode(i).len() as usize)),
{
    lemma_encode_decode_inverse(i, rest);
    super::decoder_proofs::lemma_canonical_prefix_free();
    let b = encode(i) + rest;
    assert(starts_with_encoding(b, i));
    match r {
        Some((j, n)) => {
            assert(starts_with_encoding(b, j));
        },
        None => {},
    }
}

} // verus!
