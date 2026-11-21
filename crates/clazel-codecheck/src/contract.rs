//! Contract of the validator (CLAUDE.md rule 3, docs/SPEC-STYLE.md): one
//! `requires` and one `ensures` predicate for [`super::api::Validator`], in
//! terms of [`super::spec`]. Reviewing these and the spec is enough to know
//! what an implementation guarantees.
//!
//! What they say (jit.md J.6):
//!
//! - **Soundness.** If the validator says yes, the blob is [`accepted`]:
//!   exactly the canonical encodings of subset instructions that pass the
//!   policy. This is the direction safety rests on: a `true` the spec does
//!   not license would let unchecked code run.
//! - **Completeness, given a prefix code.** If the blob is accepted, the
//!   validator says yes, provided `clazel-x64`'s `canonical_prefix_free`
//!   holds (a statement about its encoder that is to be proven there). It
//!   makes the instruction sequence of a blob unique, so a decoder that reads
//!   the first match finds the one the spec quantifies over. Without it only
//!   soundness is promised, so a validator proven against this contract is
//!   safe whether or not that lemma is ever proven; what it would lack is the
//!   guarantee that it refuses nothing the spec accepts.
//! - **Entries** are byte offsets inside the blob; each must be the start of
//!   a unit, or the answer is no ([`accepted`] requires it).
//! - **A blob is at most 2^31 - 1 bytes** (`requires`).
//!
//! Not stated here: that an accepted blob is *safe to run*. That is jit.md's
//! theorem (exit criterion 2), over `clazel_x64::spec::step`, stated in
//! [`super::safety`] and proven in [`super::safety::proof`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The largest blob the validator takes, in bytes.
pub open spec fn max_blob_len() -> int {
    0x7FFF_FFFF
}

/// The entries as the spec's integer offsets.
pub open spec fn entry_offsets(entries: Seq<usize>) -> Seq<int> {
    entries.map_values(|e: usize| e as int)
}

/// Precondition of the validator: the blob is within the size limit. Every
/// other input, including random bytes and any entries, is legal.
pub open spec fn validate_requires(blob: Seq<u8>, entries: Seq<usize>) -> bool {
    blob.len() <= max_blob_len()
}

/// Postcondition of the validator.
pub open spec fn validate_ensures(blob: Seq<u8>, entries: Seq<usize>, ok: bool) -> bool {
    &&& ok ==> accepted(blob, entry_offsets(entries))
    &&& clazel_x64::contract::canonical_prefix_free() ==> (accepted(blob, entry_offsets(entries))
        ==> ok)
}

} // verus!
