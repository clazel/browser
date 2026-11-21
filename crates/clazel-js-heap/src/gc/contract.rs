//! The collector's contract (phase-7.md items 7.0(f) and 7.6), stated before
//! the implementation (CLAUDE.md rule 3). This is the part a person reads.
//!
//! # Model
//!
//! 7.0(f) chooses G1: a stop-the-world, non-moving mark and sweep over the
//! arena. A collection starts from the **roots** and keeps what they reach.
//! The heap is abstracted here as a [`Node`] graph over arena slot indices:
//! node `i` is slot `i`.
//!
//! - A **strong edge** `i -> j` is a reference stored in object `i` that
//!   keeps `j` alive: a property or element value, the prototype, a
//!   `FinalizationRegistry`'s callback and held values.
//! - An **ephemeron** `(k, v)` of node `i` is one `WeakMap` entry: the
//!   value `v` is kept alive only while both the map `i` and the key `k`
//!   are alive (ECMA-262, "WeakMap Objects" and "Processing Model of
//!   WeakRef and FinalizationRegistry Targets", whose liveness definition
//!   makes a WeakMap value live only through its key).
//! - Everything else is **weak** and is not an edge at all: a `WeakSet`
//!   member, a `WeakRef` target, a `FinalizationRegistry` cell's target
//!   and unregister token, and the key of a `WeakMap` entry itself.
//!
//! # Reachability
//!
//! [`reachable`] is the specification: the least set of nodes that contains
//! every in-range root, contains the target of a strong edge of a member,
//! and contains the value `v` of an ephemeron `(k, v)` of a member when `k`
//! is a member. It is written as the plainest fixpoint, with no worklist
//! and no cleverness, so that reading it is checking it.
//!
//! # Invariants
//!
//! For one collection, with `roots` the references the embedder reports
//! (the value-stack region, the open handles, the objects kept alive for
//! the current job, the DOM wrappers, and the job and task queues):
//!
//! - **GC1 Safety.** A slot reachable from the roots is never freed. It
//!   keeps its index and generation, so every reference the program holds
//!   to it still resolves, to the same object. This is the invariant the
//!   Kani harnesses prove for every heap up to their bound, and the
//!   property test checks on random heaps of any size ([`safe`]).
//! - **GC2 Precision.** A slot not reachable from the roots is freed in
//!   that collection, so a collection leaves exactly the reachable slots
//!   ([`exact`]). Garbage is not a safety matter; this keeps the collector
//!   from being "correct" by keeping everything.
//! - **GC3 No dangling references.** After a collection no live object
//!   holds a reference, strong or weak, to a slot that is not live. Weak
//!   references to a freed slot are removed (GC4), so none is left to
//!   alias a later occupant even before the generation check ([`closed`]
//!   for the strong ones).
//! - **GC4 Weak clearing.** A `WeakRef` whose target was freed reads as
//!   empty. A `WeakMap` entry or `WeakSet` member whose key was freed is
//!   removed. A registry cell whose target was freed is removed, and so is
//!   an unregister token that was freed. Weak references to survivors are
//!   unchanged.
//! - **GC5 Ephemerons.** A `WeakMap` value is kept alive only through its
//!   own key: a value that refers to its key does not keep the key alive,
//!   and a chain of entries (the value of one is the key of the next) is
//!   followed to its end, whatever the order of the entries.
//! - **GC6 Finalization.** Each cell of a *surviving* registry whose target
//!   was freed produces exactly one cleanup, for the registry's callback and
//!   that cell's held value, which the collection returns for the embedder
//!   to run as a task, in that registry's cell order. A freed registry
//!   produces none. Both the callback and the held values are kept alive
//!   by the collection, and the embedder roots them until the task runs.
//!   Nothing runs during a collection.
//! - **GC7 Safe points.** A collection runs only between operations: the
//!   heap refuses (`Error::InOperation`) while an operation is in
//!   progress, because a handler may hold a reference that no root names.
//!   With exit-based JIT code (jit.md, "Exit") that means only from Rust,
//!   at the interpreter's dispatch point.
//! - **GC8 Handles.** A handle scope is closed in the order it was opened,
//!   and a mismatch is an error, not a silent unrooting.
//! - **GC9 `WeakRef` liveness.** A `WeakRef`'s target read during a job is
//!   kept alive until the job ends (ECMA-262 abstract operations
//!   `AddToKeptObjects` and `ClearKeptObjects`; section numbers differ
//!   between editions, so they are cited by name), so a program never sees
//!   a target vanish within one job.
//!
//! The arena's own invariants (`crate::arena::contract`) hold throughout:
//! freeing goes through `Arena::free`, so a stale reference to a freed slot
//! is a defined error, whatever the collector does (7.0(f)).

/// One slot of the abstract heap graph (see the module header).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Node {
    /// Slots this slot keeps alive.
    pub strong: Vec<usize>,
    /// `WeakMap` entries as `(key, value)` slot pairs.
    pub ephemerons: Vec<(usize, usize)>,
}

/// The nodes reachable from `roots` (module header, "Reachability"), as one
/// flag per node. A root or edge naming no node (a stale or out-of-range
/// reference) reaches nothing.
#[must_use]
pub fn reachable(graph: &[Node], roots: &[usize]) -> Vec<bool> {
    let mut marked = vec![false; graph.len()];
    for &r in roots {
        mark(&mut marked, r);
    }
    loop {
        let mut changed = false;
        for (i, node) in graph.iter().enumerate() {
            if !marked.get(i).copied().unwrap_or(false) {
                continue;
            }
            for &e in &node.strong {
                changed |= mark(&mut marked, e);
            }
            for &(k, v) in &node.ephemerons {
                if marked.get(k).copied().unwrap_or(false) {
                    changed |= mark(&mut marked, v);
                }
            }
        }
        if !changed {
            return marked;
        }
    }
}

/// Mark node `i`; whether that changed anything.
fn mark(marked: &mut [bool], i: usize) -> bool {
    match marked.get_mut(i) {
        Some(m) if !*m => {
            *m = true;
            true
        }
        _ => false,
    }
}

/// GC1: every reachable node survives.
#[must_use]
pub fn safe(graph: &[Node], roots: &[usize], survives: &[bool]) -> bool {
    survives.len() == graph.len()
        && reachable(graph, roots)
            .iter()
            .zip(survives)
            .all(|(&r, &s)| !r || s)
}

/// GC1 and GC2: exactly the reachable nodes survive.
#[must_use]
pub fn exact(graph: &[Node], roots: &[usize], survives: &[bool]) -> bool {
    reachable(graph, roots) == survives
}

/// GC3 for the survivors: every strong edge of a surviving node, and every
/// ephemeron value whose key survives, names a surviving node. An ephemeron
/// key of a surviving map may name a freed node only before GC4 clears the
/// entry, so keys are not checked here.
#[must_use]
pub fn closed(graph: &[Node], survives: &[bool]) -> bool {
    let alive = |i: usize| survives.get(i).copied().unwrap_or(false);
    graph
        .iter()
        .enumerate()
        .filter(|&(i, _)| alive(i))
        .all(|(_, n)| {
            n.strong.iter().all(|&e| alive(e))
                && n.ephemerons.iter().all(|&(k, v)| !alive(k) || alive(v))
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(strong: &[usize], eph: &[(usize, usize)]) -> Node {
        Node {
            strong: strong.to_vec(),
            ephemerons: eph.to_vec(),
        }
    }

    #[test]
    fn roots_and_strong_edges_are_followed() {
        // 0 -> 1 -> 2; 3 is unreachable; 4 -> 0 does not make 4 reachable.
        let g = [
            node(&[1], &[]),
            node(&[2], &[]),
            node(&[], &[]),
            node(&[], &[]),
            node(&[0], &[]),
        ];
        assert_eq!(reachable(&g, &[0]), [true, true, true, false, false]);
        assert_eq!(reachable(&g, &[]), [false; 5]);
    }

    #[test]
    fn cycles_terminate_and_are_not_kept_without_a_root() {
        let g = [node(&[1], &[]), node(&[0], &[])];
        assert_eq!(reachable(&g, &[0]), [true, true]);
        assert_eq!(reachable(&g, &[]), [false, false]);
    }

    #[test]
    fn an_ephemeron_value_needs_its_map_and_its_key() {
        // Node 0 is a map with entry (1 -> 2).
        let g = [node(&[], &[(1, 2)]), node(&[], &[]), node(&[], &[])];
        assert_eq!(reachable(&g, &[0]), [true, false, false]);
        assert_eq!(reachable(&g, &[0, 1]), [true, true, true]);
        // The key alone, without the map, keeps nothing.
        assert_eq!(reachable(&g, &[1]), [false, true, false]);
    }

    #[test]
    fn a_value_that_refers_to_its_key_does_not_keep_it_alive() {
        // Map 0 has entry (1 -> 2), and 2 -> 1.
        let g = [node(&[], &[(1, 2)]), node(&[], &[]), node(&[1], &[])];
        assert_eq!(reachable(&g, &[0]), [true, false, false]);
    }

    #[test]
    fn ephemeron_chains_are_followed_in_any_order() {
        // Map 0: (3 -> 2), (2 -> 1), (1 -> 4): listed against the chain.
        let g = [
            node(&[], &[(3, 2), (2, 1), (1, 4)]),
            node(&[], &[]),
            node(&[], &[]),
            node(&[], &[]),
            node(&[], &[]),
        ];
        assert_eq!(reachable(&g, &[0, 3]), [true, true, true, true, true]);
        assert_eq!(reachable(&g, &[0]), [true, false, false, false, false]);
    }

    #[test]
    fn names_of_no_node_reach_nothing() {
        let g = [node(&[9], &[(9, 8)])];
        assert_eq!(reachable(&g, &[7, 0]), [true]);
    }

    #[test]
    fn safe_exact_and_closed_tell_the_cases_apart() {
        let g = [node(&[1], &[]), node(&[], &[]), node(&[], &[])];
        assert!(safe(&g, &[0], &[true, true, false]));
        assert!(exact(&g, &[0], &[true, true, false]));
        // Keeping garbage is safe, not exact.
        assert!(safe(&g, &[0], &[true, true, true]));
        assert!(!exact(&g, &[0], &[true, true, true]));
        // Freeing something reachable is neither.
        assert!(!safe(&g, &[0], &[true, false, false]));
        assert!(!exact(&g, &[0], &[true, false, false]));
        assert!(closed(&g, &[true, true, false]));
        assert!(!closed(&g, &[true, false, false]));
        assert!(!safe(&g, &[0], &[true]));
    }
}
