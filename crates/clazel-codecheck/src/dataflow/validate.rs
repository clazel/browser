//! The second x86-64 validator, proven **sound**: [`validate`] returns `true`
//! only if the blob is [`crate::spec::accepted`], so it meets
//! [`super::contract::df_ensures`] and accepts only what the first validator
//! ([`crate::validate::validate`]) accepts. It is not claimed complete
//! (see [`super::contract`]).
//!
//! The pipeline is different from the first validator's single scan:
//!
//! 1. decode ([`crate::decode_all::decode_all`], the proven decoder both
//!    share);
//! 2. flag the entries and jump targets, the graph's non-fall-through edges
//!    ([`super::targets::mark_targets`], verified);
//! 3. **solve**: a control-flow graph of basic blocks and a forward dataflow
//!    fixpoint over the abstract register facts ([`super::solve::solve`],
//!    unverified: an untrusted solver);
//! 4. **check** the solution and every unit against it
//!    ([`super::check::check_units`], verified: the certificate must be a
//!    post-fixpoint, and every access, branch and reserved-register write is
//!    checked against it);
//! 5. every flagged offset must be a unit start.
//!
//! A `false` is never proven to be a refusal of the spec; a `true` is.

use super::check::check_units;
use super::solve::solve;
#[allow(unused_imports)]
use super::spec::*;
use super::targets::mark_targets;
use crate::decode_all::decode_all;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Whether `blob`, entered at `entries`, is accepted, by the dataflow
/// analysis: a `true` is [`accepted`]. See the module comment.
#[verifier::spinoff_prover]
#[verifier::rlimit(4000)]
pub fn validate(blob: &[u8], entries: &[usize]) -> (ok: bool)
    requires
        super::contract::df_requires(blob@, entries@),
    ensures
        super::contract::df_ensures(blob@, entries@, ok),
{
    let total = blob.len();
    let ghost ent = crate::contract::entry_offsets(entries@);
    let (ins, st) = match decode_all(blob) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let n = ins.len();
    proof {
        crate::validate::lemma_enc_all_len(ins@);
        assert(total as int == start_of(ins@, n as int));
        crate::validate::lemma_start_of_ge(ins@, n as int);
    }
    if n == 0 {
        return false;
    }
    let last_ok = matches!(ins.get(n.saturating_sub(1)), Some(Instr::Ret | Instr::Jmp { .. }));
    if !last_ok {
        return false;
    }
    let ghost tg = all_targets(ins@, ent);
    let mark = match mark_targets(ins.as_slice(), st.as_slice(), entries, total, Ghost(ent)) {
        Some(m) => m,
        None => {
            return false;
        },
    };
    let inn = solve(ins.as_slice(), st.as_slice(), mark.as_slice());
    let us = match check_units(
        ins.as_slice(),
        st.as_slice(),
        mark.as_slice(),
        inn.as_slice(),
        Ghost(tg),
        total,
    ) {
        Some(us) => us,
        None => {
            return false;
        },
    };
    // Every flagged offset is a unit start.
    let mut p: usize = 0;
    while p < total
        invariant
            p <= total,
            mark@.len() == total,
            us@.len() == total,
            forall|q: int| 0 <= q < p ==> (mark@[q] ==> us@[q]),
        decreases total - p,
    {
        let t = match mark.get(p) {
            Some(t) => *t,
            None => {
                return false;
            },
        };
        let u = match us.get(p) {
            Some(u) => *u,
            None => {
                return false;
            },
        };
        if t && !u {
            return false;
        }
        p = p.saturating_add(1);
    }
    proof {
        let starts = scan(ins@, tg, 0, no_facts())->Some_0;
        assert forall|i: int| 0 <= i < tg.len() implies seq_has(starts, #[trigger] tg[i]) by {
            crate::validate::lemma_seq_has_at(tg, i);
            assert(super::targets::covered(mark@, tg[i]));
            assert(us@[tg[i]]);
        }
        crate::validate::lemma_subset_intro(tg, starts);
        assert(policy(ins@, ent));
        assert(decodes_to(blob@, ins@));
    }
    true
}

} // verus!
