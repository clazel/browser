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
//!   to it still resolves, to the same object. The Kani
//!   harness proves the marker keeps every reachable node of every graph
//!   up to its bound (see `src/proofs.rs` for the bound and for what is
//!   not proven), and the property test checks the whole collector on
//!   random heaps of any size ([`safe`]).
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
//! - **GC5 (work).** Marking is linear: for a graph of `n` nodes, `s`
//!   strong edges and `e` ephemerons, it does at most `n + s + 2e` units
//!   of work ([`work_bound`]), whatever the order of the entries. A unit is
//!   one node taken off the work list, one strong edge examined, one
//!   ephemeron examined when its map is processed, or one pending ephemeron
//!   fired when its key is marked. (A pass over every ephemeron until
//!   nothing changes is quadratic on a chain listed backwards; the
//!   collector indexes the pending ephemerons by key instead.) This bounds
//!   the work; it is not a pause-time claim.
//! - **GC10 Shapes.** After a collection, every shape of a live object, and
//!   the parent of every live shape, is live, and so is the root shape
//!   (`crate::shape::ROOT`): a lookup that walks a live shape's parent
//!   chain never meets a freed shape. A shape the embedder names as a root
//!   (an inline cache's, a class's initial shape) is live. A *transition*
//!   (a shape's table of children) is weak: it does not keep the child
//!   alive, and a transition to a freed shape is removed.
//! - **GC11 Keys.** After a collection, every interned string that a live
//!   shape names (the key it added, or, for a dictionary shape, every key it
//!   holds) is live, and so is every key the embedder names as a root (a
//!   constant of live bytecode). Resolving a live key gives the string it
//!   was interned as.
//! - **GC12 Precision for shapes and keys.** A shape that none of GC10's
//!   rules keeps is freed, and so is a key that none of GC11's rules keeps
//!   ([`live_shapes`] is the exact set; [`shapes_safe`] and
//!   [`shapes_exact`] check against it). Shapes of dead objects keep
//!   nothing, so a dictionary shape dies with its object.
//! - **GC13 Ids are never reused.** A freed shape id resolves to nothing
//!   from then on, and a freed key too: a table never hands out an id twice,
//!   so an inline cache that cached a freed shape id cannot hit another
//!   shape, and a stale key is a defined error, not another property.
//!   (The cost is a tombstone per freed entry; compacting the tables is a
//!   later optimization that must flush the inline caches.)
//!
//! Symbols are not collected in this slice, and nothing outside the heap's
//! own tables (an embedder's own copies of a `Key`) is traced: the
//! embedder reports the keys and shapes it holds.
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

/// A heap graph: what [`reachable`] and the collector's `mark` read. The
/// provided implementations are for the slices of [`Node`]; the Kani
/// harnesses give it fixed-size arrays, which CBMC handles far faster than
/// vectors of vectors.
pub trait Graph {
    /// The number of nodes.
    fn len(&self) -> usize;
    /// The strong edges of node `i` (none if there is no node `i`).
    fn strong(&self, i: usize) -> &[usize];
    /// The ephemerons of node `i` (none if there is no node `i`).
    fn ephemerons(&self, i: usize) -> &[(usize, usize)];
    /// Whether there are no nodes.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Graph for [Node] {
    fn len(&self) -> usize {
        <[Node]>::len(self)
    }
    fn strong(&self, i: usize) -> &[usize] {
        self.get(i).map_or(&[], |n| &n.strong)
    }
    fn ephemerons(&self, i: usize) -> &[(usize, usize)] {
        self.get(i).map_or(&[], |n| &n.ephemerons)
    }
}

impl Graph for Vec<Node> {
    fn len(&self) -> usize {
        Vec::len(self)
    }
    fn strong(&self, i: usize) -> &[usize] {
        self.as_slice().strong(i)
    }
    fn ephemerons(&self, i: usize) -> &[(usize, usize)] {
        self.as_slice().ephemerons(i)
    }
}

impl<const N: usize> Graph for [Node; N] {
    fn len(&self) -> usize {
        N
    }
    fn strong(&self, i: usize) -> &[usize] {
        self.as_slice().strong(i)
    }
    fn ephemerons(&self, i: usize) -> &[(usize, usize)] {
        self.as_slice().ephemerons(i)
    }
}

/// The nodes reachable from `roots` (module header, "Reachability"), as one
/// flag per node. A root or edge naming no node (a stale or out-of-range
/// reference) reaches nothing.
#[must_use]
pub fn reachable<G: Graph + ?Sized>(graph: &G, roots: &[usize]) -> Vec<bool> {
    let mut marked = vec![false; graph.len()];
    for &r in roots {
        mark(&mut marked, r);
    }
    loop {
        let mut changed = false;
        for i in 0..graph.len() {
            if !marked.get(i).copied().unwrap_or(false) {
                continue;
            }
            for &e in graph.strong(i) {
                changed |= mark(&mut marked, e);
            }
            for &(k, v) in graph.ephemerons(i) {
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
pub fn safe<G: Graph + ?Sized>(graph: &G, roots: &[usize], survives: &[bool]) -> bool {
    survives.len() == graph.len()
        && reachable(graph, roots)
            .iter()
            .zip(survives)
            .all(|(&r, &s)| !r || s)
}

/// GC1 and GC2: exactly the reachable nodes survive.
#[must_use]
pub fn exact<G: Graph + ?Sized>(graph: &G, roots: &[usize], survives: &[bool]) -> bool {
    reachable(graph, roots) == survives
}

/// GC3 for the survivors: every strong edge of a surviving node, and every
/// ephemeron value whose key survives, names a surviving node. An ephemeron
/// key of a surviving map may name a freed node only before GC4 clears the
/// entry, so keys are not checked here.
#[must_use]
pub fn closed<G: Graph + ?Sized>(graph: &G, survives: &[bool]) -> bool {
    let alive = |i: usize| survives.get(i).copied().unwrap_or(false);
    (0..graph.len()).filter(|&i| alive(i)).all(|i| {
        graph.strong(i).iter().all(|&e| alive(e))
            && graph
                .ephemerons(i)
                .iter()
                .all(|&(k, v)| !alive(k) || alive(v))
    })
}

/// GC5's bound on the work of marking a graph of `nodes` nodes, `strong`
/// strong edges and `ephemerons` ephemerons: `nodes + strong + 2 *
/// ephemerons` (saturating).
#[must_use]
pub const fn work_bound(nodes: usize, strong: usize, ephemerons: usize) -> usize {
    nodes
        .saturating_add(strong)
        .saturating_add(ephemerons.saturating_mul(2))
}

/// The totals of a graph, for [`work_bound`]: its nodes, strong edges and
/// ephemerons.
#[must_use]
pub fn totals<G: Graph + ?Sized>(graph: &G) -> (usize, usize, usize) {
    let (mut strong, mut eph) = (0usize, 0usize);
    for i in 0..graph.len() {
        strong = strong.saturating_add(graph.strong(i).len());
        eph = eph.saturating_add(graph.ephemerons(i).len());
    }
    (graph.len(), strong, eph)
}

/// The shape table, as GC10 to GC12 see it: entry `i` is the table's own
/// index (the shape with id `n` is entry `n - 1`), and an interned key is a
/// number below the key table's size.
pub trait ShapeGraph {
    /// The number of table entries, freed ones included.
    fn len(&self) -> usize;
    /// Whether entry `i` is a live shape (a freed or missing one is not).
    fn exists(&self, i: usize) -> bool;
    /// The parent of shape `i`, if it has one.
    fn parent(&self, i: usize) -> Option<usize>;
    /// Calls `f` with each key shape `i` names: the one key a shared shape
    /// added, or all the keys of a dictionary shape.
    fn each_key(&self, i: usize, f: &mut dyn FnMut(usize));
    /// Whether there are no entries.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// The live shapes and keys (GC10 to GC12), as two flag vectors (shapes by
/// entry, keys by number below `key_count`): the least sets such that a
/// root that is a live shape is in the first, the parent of a member is in
/// the first, and a root key and every key a member names is in the second.
/// Written as the plainest fixpoint. A root or key naming nothing is
/// ignored.
#[must_use]
pub fn live_shapes<G: ShapeGraph + ?Sized>(
    graph: &G,
    roots: &[usize],
    root_keys: &[usize],
    key_count: usize,
) -> (Vec<bool>, Vec<bool>) {
    let mut shapes = vec![false; graph.len()];
    let mut keys = vec![false; key_count];
    for &r in roots {
        if graph.exists(r) {
            mark(&mut shapes, r);
        }
    }
    for &k in root_keys {
        mark(&mut keys, k);
    }
    loop {
        let mut changed = false;
        for i in 0..graph.len() {
            if !shapes.get(i).copied().unwrap_or(false) {
                continue;
            }
            if let Some(p) = graph.parent(i).filter(|&p| graph.exists(p)) {
                changed |= mark(&mut shapes, p);
            }
            graph.each_key(i, &mut |k| changed |= mark(&mut keys, k));
        }
        if !changed {
            return (shapes, keys);
        }
    }
}

/// GC10 and GC11: every live shape and key survives.
#[must_use]
pub fn shapes_safe<G: ShapeGraph + ?Sized>(
    graph: &G,
    roots: &[usize],
    root_keys: &[usize],
    shapes: &[bool],
    keys: &[bool],
) -> bool {
    let (want_s, want_k) = live_shapes(graph, roots, root_keys, keys.len());
    shapes.len() == want_s.len()
        && want_s.iter().zip(shapes).all(|(&w, &s)| !w || s)
        && want_k.iter().zip(keys).all(|(&w, &s)| !w || s)
}

/// GC10 to GC12: exactly the live shapes and keys survive.
#[must_use]
pub fn shapes_exact<G: ShapeGraph + ?Sized>(
    graph: &G,
    roots: &[usize],
    root_keys: &[usize],
    shapes: &[bool],
    keys: &[bool],
) -> bool {
    live_shapes(graph, roots, root_keys, keys.len()) == (shapes.to_vec(), keys.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Shape tables for the spec's tests: `(exists, parent, keys)`.
    struct Table(Vec<(bool, Option<usize>, Vec<usize>)>);

    impl ShapeGraph for Table {
        fn len(&self) -> usize {
            self.0.len()
        }
        fn exists(&self, i: usize) -> bool {
            self.0.get(i).is_some_and(|e| e.0)
        }
        fn parent(&self, i: usize) -> Option<usize> {
            self.0.get(i).and_then(|e| e.1)
        }
        fn each_key(&self, i: usize, f: &mut dyn FnMut(usize)) {
            for &k in self.0.get(i).map_or(&[][..], |e| &e.2) {
                f(k);
            }
        }
    }

    #[test]
    fn a_live_shape_keeps_its_parents_and_its_keys() {
        // 0 <- 1 <- 2 (keys 0, 1, 2), and 3 is a separate shape of key 3.
        let t = Table(vec![
            (true, None, vec![]),
            (true, Some(0), vec![0]),
            (true, Some(1), vec![1]),
            (true, None, vec![3]),
        ]);
        let (s, k) = live_shapes(&t, &[2], &[], 5);
        assert_eq!(s, [true, true, true, false]);
        assert_eq!(k, [true, true, false, false, false]);
        // A root key alone keeps its string, and nothing else.
        let (s, k) = live_shapes(&t, &[], &[4], 5);
        assert_eq!(s, [false; 4]);
        assert_eq!(k, [false, false, false, false, true]);
    }

    #[test]
    fn freed_and_missing_shapes_and_keys_reach_nothing() {
        let t = Table(vec![(false, None, vec![]), (true, Some(0), vec![9])]);
        // The parent was freed (it cannot be, in a heap; the spec does not
        // follow it), a root names a missing shape and a missing key.
        let (s, k) = live_shapes(&t, &[1, 7], &[8], 2);
        assert_eq!(s, [false, true]);
        assert_eq!(k, [false, false]);
    }

    #[test]
    fn safe_and_exact_tell_the_cases_apart() {
        let t = Table(vec![(true, None, vec![]), (true, Some(0), vec![0])]);
        assert!(shapes_exact(&t, &[1], &[], &[true, true], &[true]));
        assert!(shapes_safe(&t, &[1], &[], &[true, true], &[true]));
        // Keeping the key of nothing is safe, not exact.
        assert!(shapes_safe(&t, &[0], &[], &[true, true], &[true]));
        assert!(!shapes_exact(&t, &[0], &[], &[true, true], &[true]));
        // Freeing a parent or a key is neither.
        assert!(!shapes_safe(&t, &[1], &[], &[false, true], &[true]));
        assert!(!shapes_safe(&t, &[1], &[], &[true, true], &[false]));
    }

    #[test]
    fn the_work_bound_counts_each_ephemeron_twice() {
        assert_eq!(work_bound(10, 3, 4), 21);
        assert_eq!(work_bound(usize::MAX, 1, 1), usize::MAX);
        let g = [
            Node {
                strong: vec![1],
                ephemerons: vec![(1, 2)],
            },
            Node::default(),
        ];
        assert_eq!(totals(&g), (2, 1, 1));
    }

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
