//! The arena's contract (phase-7.md item 7.5, "Tier 1"), stated before the
//! implementation (CLAUDE.md rule 3).
//!
//! The arena is a vector of slots. A slot holds a `u16` generation and is in
//! exactly one of three states ([`Kind`]). References to it are an index
//! and the generation the slot had when the reference was made.
//!
//! # Invariants
//!
//! These hold of every arena, after every operation ([`well_formed`]):
//!
//! 1. **No slot is both free and live.** A slot has one [`Kind`], and the
//!    free list (a chain of indices from `head`, each free slot naming the
//!    next) visits only slots of kind [`Kind::Free`], each at most once (it
//!    has no cycle), and visits every slot of kind [`Kind::Free`].
//! 2. **The live count is the number of live slots.**
//!
//! And across every operation ([`step_ok`]):
//!
//! 3. **Generations only grow.** The arena never loses a slot, and no
//!    slot's generation ever decreases. Freeing a live slot raises its
//!    generation by exactly one, which is what makes every outstanding
//!    reference to it stale.
//! 4. **A generation is never reused.** A slot whose generation has reached
//!    `u16::MAX` when it is freed is [`Kind::Retired`], and is never
//!    allocated again, so the generation does not wrap and a stale reference
//!    can never match a later occupant.
//!
//! And of every lookup (checked by unit tests and the harnesses):
//!
//! 5. A reference resolves only to a live slot of the same generation. Any
//!    other reference (index out of range, slot free or retired, generation
//!    different) is an error, never another object.

/// What a slot holds, with the payload removed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Holds a value.
    Live,
    /// On the free list; the payload is the next free index, if any.
    Free(Option<u32>),
    /// Never to be allocated again (its generation is exhausted).
    Retired,
}

/// A slot as the contract sees it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlotView {
    /// The slot's current generation.
    pub generation: u16,
    /// What the slot holds.
    pub kind: Kind,
}

/// Invariants 1 and 2, for the slots, the free list's head and the live
/// count an arena reports.
///
/// The free list is walked at most `slots.len()` steps: a longer walk
/// would repeat a slot, which is a cycle.
#[must_use]
pub fn well_formed(slots: &[SlotView], head: Option<u32>, live: usize) -> bool {
    // 2. The live count.
    let live_slots = slots.iter().filter(|s| s.kind == Kind::Live).count();
    if live_slots != live {
        return false;
    }
    // 1. The free list visits only free slots, none twice.
    let mut seen = 0usize;
    let mut at = head;
    while let Some(i) = at {
        let Some(s) = usize::try_from(i).ok().and_then(|i| slots.get(i)) else {
            return false; // names a slot that does not exist
        };
        let Kind::Free(next) = s.kind else {
            return false; // names a slot that is live or retired
        };
        seen = match seen.checked_add(1) {
            Some(n) if n <= slots.len() => n,
            _ => return false, // longer than the arena: a cycle
        };
        at = next;
    }
    // ... and every free slot was visited (the walk saw no repeat, so
    // `seen` counts distinct free slots).
    let free_slots = slots
        .iter()
        .filter(|s| matches!(s.kind, Kind::Free(_)))
        .count();
    seen == free_slots
}

/// Invariants 3 and 4 for one operation: `before` and `after` are the
/// slots either side of it.
#[must_use]
pub fn step_ok(before: &[SlotView], after: &[SlotView]) -> bool {
    if after.len() < before.len() {
        return false; // slots are never removed
    }
    before.iter().zip(after.iter()).all(|(b, a)| {
        let grew = a.generation >= b.generation;
        // A retired slot stays retired, with its generation.
        let retired_stays = b.kind != Kind::Retired || a == b;
        // A slot goes from live to free with generation + 1, or to retired
        // at the top generation, unchanged.
        let freed_right = match (b.kind, a.kind) {
            (Kind::Live, Kind::Free(_)) => b.generation.checked_add(1) == Some(a.generation),
            (Kind::Live, Kind::Retired) => b.generation == u16::MAX && a.generation == b.generation,
            _ => true,
        };
        // Allocating a free slot does not change its generation.
        let alloc_right = match (b.kind, a.kind) {
            (Kind::Free(_), Kind::Live) => a.generation == b.generation,
            _ => true,
        };
        grew && retired_stays && freed_right && alloc_right
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const fn v(generation: u16, kind: Kind) -> SlotView {
        SlotView { generation, kind }
    }

    #[test]
    fn a_free_list_over_free_slots_is_well_formed() {
        let s = [
            v(0, Kind::Free(Some(1))),
            v(3, Kind::Free(None)),
            v(0, Kind::Live),
        ];
        assert!(well_formed(&s, Some(0), 1));
        assert!(well_formed(&[], None, 0));
    }

    #[test]
    fn a_live_slot_on_the_free_list_is_rejected() {
        let s = [v(0, Kind::Free(Some(1))), v(0, Kind::Live)];
        assert!(!well_formed(&s, Some(0), 1));
    }

    #[test]
    fn a_free_slot_off_the_free_list_is_rejected() {
        let s = [v(0, Kind::Free(None)), v(0, Kind::Free(None))];
        assert!(!well_formed(&s, Some(0), 0));
    }

    #[test]
    fn a_cycle_is_rejected() {
        let s = [v(0, Kind::Free(Some(1))), v(0, Kind::Free(Some(0)))];
        assert!(!well_formed(&s, Some(0), 0));
    }

    #[test]
    fn a_dangling_link_and_a_wrong_count_are_rejected() {
        let s = [v(0, Kind::Free(Some(9)))];
        assert!(!well_formed(&s, Some(0), 0));
        let s = [v(0, Kind::Live)];
        assert!(!well_formed(&s, None, 0));
    }

    #[test]
    fn a_step_may_not_lower_a_generation_or_lose_a_slot() {
        let live = [v(2, Kind::Live)];
        assert!(step_ok(&live, &[v(3, Kind::Free(None))]));
        assert!(!step_ok(&live, &[v(1, Kind::Free(None))]));
        assert!(!step_ok(&live, &[v(2, Kind::Free(None))]));
        assert!(!step_ok(&live, &[]));
    }

    #[test]
    fn a_retired_slot_stays_retired() {
        let top = [v(u16::MAX, Kind::Live)];
        assert!(step_ok(&top, &[v(u16::MAX, Kind::Retired)]));
        assert!(!step_ok(&top, &[v(0, Kind::Free(None))]));
        let r = [v(u16::MAX, Kind::Retired)];
        assert!(!step_ok(&r, &[v(u16::MAX, Kind::Free(None))]));
    }
}
