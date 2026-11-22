//! Contracts the encoder and the decoder must be proven to meet (CLAUDE.md
//! rule 3, docs/SPEC-STYLE.md). Each method of [`super::api::A64Codec`] has
//! one `requires` and one `ensures` predicate here, written in terms of
//! [`super::spec`]. Reviewing these and the spec is enough to know what the
//! implementation guarantees.
//!
//! What they say (jit.md J.4):
//!
//! - **The encoder emits only the canonical encoding** of a valid
//!   instruction: the 32-bit word [`encode`] gives.
//! - **The decoder accepts only canonical encodings.** A `Some` result is a
//!   valid instruction whose canonical encoding is the word. A `None` result
//!   means that the word is no valid instruction's canonical encoding:
//!   nothing the subset names is refused, and everything else (other
//!   instructions, the field values [`valid_instr`] excludes, such as a shift
//!   by 0 written `LSR`, a condition of `AL` or `NV`, a load with base `SP`,
//!   unallocated encodings) is.
//! - **They are inverse on the subset:** [`encode_decode_inverse`] and
//!   [`decode_encode_inverse`] follow from the two ensures above together
//!   with [`canonical_injective`]; the last is a statement about the spec,
//!   to be proven in the implementation half (it is what makes the decoder's
//!   `Some` result unique). A64 words have a fixed size, so there is no
//!   prefix question as on x86-64: the decoder takes one word.
//!
//! The words are in memory little-endian ([`word_bytes`]); turning four
//! bytes into a word is the caller's (`u32::from_le_bytes`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of the encoder: the instruction is in the subset.
pub open spec fn encode_requires(i: Instr) -> bool {
    valid_instr(i)
}

/// Postcondition of the encoder: the word is the canonical encoding.
pub open spec fn encode_ensures(i: Instr, out: u32) -> bool {
    is_canonical_encoding(out, i)
}

/// Precondition of the decoder: none. Every word is a legal input.
pub open spec fn decode_requires(w: u32) -> bool {
    true
}

/// Postcondition of the decoder.
pub open spec fn decode_ensures(w: u32, r: Option<Instr>) -> bool {
    match r {
        Some(i) => is_canonical_encoding(w, i),
        None => forall|i: Instr| !is_canonical_encoding(w, i),
    }
}

/// No two instructions of the subset share a canonical encoding, so a
/// decoder's `Some` is unique. To be proven about [`encode`] in the
/// implementation half; the contracts above are meaningful (a decoder may
/// pick any match) without it.
pub open spec fn canonical_injective() -> bool {
    forall|i: Instr, j: Instr, w: u32|
        is_canonical_encoding(w, i) && is_canonical_encoding(w, j) ==> i == j
}

/// The canonical encoding of every instruction of the subset is a 32-bit
/// word (so the encoder's `u32` result can hold it). To be proven about
/// [`encode`] in the implementation half.
pub open spec fn encode_fits() -> bool {
    forall|i: Instr| valid_instr(i) ==> 0 <= #[trigger] encode(i) < 0x1_0000_0000
}

/// The encoder's output is read back by the decoder.
pub open spec fn encode_decode_inverse(i: Instr, w: u32) -> bool {
    encode_ensures(i, w) ==> decode_ensures(w, Some(i))
}

/// A decoded instruction encodes to the word decoded.
pub open spec fn decode_encode_inverse(w: u32, i: Instr) -> bool {
    decode_ensures(w, Some(i)) ==> encode(i) == w as int
}

} // verus!
