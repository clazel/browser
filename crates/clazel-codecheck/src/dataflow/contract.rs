//! Contract of the second x86-64 validator (CLAUDE.md rule 3,
//! docs/SPEC-STYLE.md), jit.md J.6: "a second validator per instruction set,
//! written as a dataflow analysis, proven to accept only what the first
//! accepts".
//!
//! # What it says
//!
//! - **Soundness only.** If the second validator says yes, the blob is
//!   [`accepted`] (`crate::spec`), which is what the first validator decides
//!   exactly. So the second accepts only blobs the first accepts, see
//!   [`lemma_accepts_only_what_first_accepts`], which derives the sentence
//!   from this `ensures` and the first validator's own contract.
//! - **No completeness is promised.** The second validator may refuse a blob
//!   the spec accepts: it computes its facts by a bounded fixpoint iteration
//!   and gives up (refuses) if the iteration has not settled within its pass
//!   budget, and it makes no claim about *why* it refused. That is the safe
//!   direction: a `true` is what code runs on. Completeness would need a proof
//!   that every refusal is justified by the spec, which is not what J.6 asks
//!   of an independent check, and the first validator already has it.
//! - **The requirement** is the first validator's: a blob of at most
//!   2^31 - 1 bytes. Every other input is legal and never panics.
//!
//! The two validators share the specification [`accepted`] and the decoder of
//! bytes into instructions (`clazel-x64`'s, proven); they do not share the
//! algorithm that checks the policy.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of the second validator: the first validator's.
pub open spec fn df_requires(blob: Seq<u8>, entries: Seq<usize>) -> bool {
    crate::contract::validate_requires(blob, entries)
}

/// Postcondition of the second validator: a `true` answer means the blob,
/// entered at `entries`, is [`accepted`].
pub open spec fn df_ensures(blob: Seq<u8>, entries: Seq<usize>, ok: bool) -> bool {
    ok ==> accepted(blob, crate::contract::entry_offsets(entries))
}

/// The second validator accepts only what the first accepts: if both meet
/// their contracts, then whenever the second says yes the first says yes.
/// (The first validator's contract promises completeness given
/// `canonical_prefix_free`, which `clazel-x64` proves.)
pub proof fn lemma_accepts_only_what_first_accepts(
    blob: Seq<u8>,
    entries: Seq<usize>,
    ok_second: bool,
    ok_first: bool,
)
    requires
        df_ensures(blob, entries, ok_second),
        crate::contract::validate_ensures(blob, entries, ok_first),
    ensures
        ok_second ==> ok_first,
{
    clazel_x64::decoder_proofs::lemma_canonical_prefix_free();
}

} // verus!
