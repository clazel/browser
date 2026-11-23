//! Contract of the A64 validator (CLAUDE.md rule 3, docs/SPEC-STYLE.md): one
//! `requires` and one `ensures` predicate for [`super::api::A64Validator`],
//! in terms of [`super::spec`]. Reviewing these and the spec is enough to
//! know what an implementation guarantees. It is the A64 counterpart of
//! [`crate::contract`].
//!
//! What they say (jit.md J.6):
//!
//! - **Soundness.** If the validator says yes, the blob is [`accepted`]:
//!   exactly the canonical encodings of subset instructions that pass the
//!   policy. This is the direction safety rests on: a `true` the spec does
//!   not license would let unchecked code run.
//! - **Completeness, with no assumption.** If the blob is accepted, the
//!   validator says yes. Unlike x86-64 there is no prefix lemma to assume: A64
//!   words have a fixed size, and `clazel-a64` has proven its canonical
//!   encoding injective, so the instruction sequence of a blob is unique.
//! - **Entries** are byte offsets; each must be the start of a unit (so a
//!   multiple of 4 inside the blob), or the answer is no ([`accepted`]
//!   requires it).
//! - **A blob is at most 2^31 - 1 bytes** (`requires`).
//!
//! Not stated here: that an accepted blob is *safe to run*. That is jit.md's
//! theorem (exit criterion 2), over `clazel_a64::spec::step`, and it is not
//! yet written; see [`super::spec`]'s header.

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

/// Postcondition of the validator: it says yes if and only if the blob is
/// accepted.
pub open spec fn validate_ensures(blob: Seq<u8>, entries: Seq<usize>, ok: bool) -> bool {
    ok <==> accepted(blob, entry_offsets(entries))
}

} // verus!
