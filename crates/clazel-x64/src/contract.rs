//! Contracts the encoder and the decoder must be proven to meet (CLAUDE.md
//! rule 3, docs/SPEC-STYLE.md). Each method of [`super::api::X64Codec`] has one
//! `requires` and one `ensures` predicate here, written in terms of
//! [`super::spec`]. Reviewing these and the spec is enough to know what the
//! implementation guarantees.
//!
//! What they say (jit.md J.3):
//!
//! - **The encoder emits only the canonical encoding** of a valid
//!   instruction.
//! - **The decoder accepts only canonical encodings.** A `Some` result is a
//!   valid instruction whose canonical encoding is exactly the bytes it
//!   consumed. A `None` result means that no valid instruction's canonical
//!   encoding begins the input: nothing the subset names is refused, and
//!   everything else (redundant prefixes, alternative ModRM forms, other
//!   opcodes, a truncated instruction) is.
//! - **They are inverse on the subset:** [`encode_decode_inverse`] and
//!   [`decode_encode_inverse`] follow from the two ensures above together
//!   with [`canonical_prefix_free`]; the last is a statement about the spec,
//!   to be proven in the implementation half (it is what makes the decoder's
//!   `Some` result unique).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of the encoder: the instruction is in the subset.
pub open spec fn encode_requires(i: Instr) -> bool {
    valid_instr(i)
}

/// Postcondition of the encoder: the bytes are the canonical encoding.
pub open spec fn encode_ensures(i: Instr, out: Seq<u8>) -> bool {
    is_canonical_encoding(out, i)
}

/// Precondition of the decoder: none. Every byte string is a legal input.
pub open spec fn decode_requires(bytes: Seq<u8>) -> bool {
    true
}

/// Postcondition of the decoder.
pub open spec fn decode_ensures(bytes: Seq<u8>, r: Option<(Instr, usize)>) -> bool {
    match r {
        Some((i, n)) => n <= bytes.len() && is_canonical_encoding(bytes.subrange(0, n as int), i),
        None => forall|i: Instr| !starts_with_encoding(bytes, i),
    }
}

/// No canonical encoding is a proper prefix of another instruction's, nor
/// two different instructions' encodings of one input: the set of canonical
/// encodings is a prefix code, so a decoder's `Some` is unique. To be proven
/// about [`encode`] in the implementation half; the contracts above are
/// meaningful (a decoder may pick any match) without it.
pub open spec fn canonical_prefix_free() -> bool {
    forall|i: Instr, j: Instr, bytes: Seq<u8>|
        starts_with_encoding(bytes, i) && starts_with_encoding(bytes, j) ==> i == j
}

/// The encoder's output is read back by the decoder, whatever follows it.
pub open spec fn encode_decode_inverse(i: Instr, rest: Seq<u8>) -> bool {
    valid_instr(i) ==> starts_with_encoding(encode(i) + rest, i)
}

/// A decoded instruction encodes to the bytes decoded.
pub open spec fn decode_encode_inverse(bytes: Seq<u8>, i: Instr, n: usize) -> bool {
    decode_ensures(bytes, Some((i, n))) ==> encode(i) == bytes.subrange(0, n as int)
}

} // verus!
