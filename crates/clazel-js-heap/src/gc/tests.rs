//! Unit tests for each weak kind and for the roots, and the property test of
//! GC1 to GC6 over random heaps of any size, from a fixed-seed generator.

use super::contract::{self, Node};
use super::*;
use crate::arena::Error as ArenaError;
use std::collections::HashSet;

type R<T> = Result<T, Error>;

fn obj(h: &mut Heap) -> R<Ref> {
    h.alloc(Object::ordinary())
}

fn val(r: Ref) -> Value {
    Value::heap_ref(r)
}

fn int(i: i32) -> Value {
    Value::int32(i)
}

fn kind_of(h: &mut Heap, kind: Kind) -> R<Ref> {
    h.alloc(Object::of(kind))
}

fn stale(h: &Heap, r: Ref) -> bool {
    h.get(r).err() == Some(Error::Arena(ArenaError::Stale))
}

fn add_slot(h: &mut Heap, to: Ref, v: Value) -> R<()> {
    h.get_mut(to)?.slots.push(v);
    Ok(())
}

// ---- Roots and tracing ------------------------------------------------

#[test]
fn what_the_roots_reach_survives_and_the_rest_is_freed() -> R<()> {
    let mut h = Heap::new();
    let a = obj(&mut h)?;
    let b = obj(&mut h)?;
    let c = obj(&mut h)?;
    let garbage = obj(&mut h)?;
    add_slot(&mut h, a, val(b))?;
    add_slot(&mut h, b, val(c))?;
    add_slot(&mut h, garbage, val(a))?;
    // Prototype and element edges count too.
    let d = obj(&mut h)?;
    h.get_mut(c)?.proto = Some(d);
    let e = obj(&mut h)?;
    assert_eq!(h.get_mut(d)?.elements.set(3, val(e)), Ok(()));
    let out = h.collect(&[val(a)])?;
    assert_eq!((out.freed, out.survivors), (1, 5));
    for r in [a, b, c, d, e] {
        assert!(h.is_live(r));
    }
    assert!(stale(&h, garbage));
    assert!(h.arena().is_well_formed());
    Ok(())
}

#[test]
fn cycles_without_a_root_are_freed() -> R<()> {
    let mut h = Heap::new();
    let a = obj(&mut h)?;
    let b = obj(&mut h)?;
    add_slot(&mut h, a, val(b))?;
    add_slot(&mut h, b, val(a))?;
    let out = h.collect(&[int(7), Value::UNDEFINED])?;
    assert_eq!((out.freed, h.live()), (2, 0));
    Ok(())
}

#[test]
fn a_freed_slot_is_reused_with_a_new_generation_so_old_references_stay_stale() -> R<()> {
    let mut h = Heap::new();
    let old = obj(&mut h)?;
    h.collect(&[])?;
    let new = obj(&mut h)?;
    assert_eq!(new.index, old.index);
    assert_ne!(new.generation, old.generation);
    assert!(stale(&h, old));
    // A stale root reaches nothing, and does not keep the new occupant.
    h.collect(&[val(old)])?;
    assert!(stale(&h, new) || !h.is_live(new));
    Ok(())
}

#[test]
fn a_long_chain_does_not_recurse() -> R<()> {
    let mut h = Heap::new();
    let head = obj(&mut h)?;
    let mut tail = head;
    for _ in 0..100_000 {
        let n = obj(&mut h)?;
        add_slot(&mut h, tail, val(n))?;
        tail = n;
    }
    let out = h.collect(&[val(head)])?;
    assert_eq!((out.freed, out.survivors), (0, 100_001));
    let out = h.collect(&[])?;
    assert_eq!(out.freed, 100_001);
    Ok(())
}

#[test]
fn the_value_stack_handles_and_kept_objects_are_roots() -> R<()> {
    let mut h = Heap::new();
    let on_stack = obj(&mut h)?;
    let handled = obj(&mut h)?;
    let nested = obj(&mut h)?;
    let garbage = obj(&mut h)?;
    let scope = h.open_scope();
    h.root(val(handled))?;
    let inner = h.open_scope();
    h.root(val(nested))?;
    h.collect(&[val(on_stack)])?;
    assert!(h.is_live(on_stack) && h.is_live(handled) && h.is_live(nested));
    assert!(stale(&h, garbage));
    h.close_scope(inner)?;
    h.collect(&[])?;
    assert!(h.is_live(handled) && !h.is_live(nested) && !h.is_live(on_stack));
    h.close_scope(scope)?;
    h.collect(&[])?;
    assert_eq!(h.live(), 0);
    Ok(())
}

#[test]
fn scopes_close_in_order_and_handles_need_a_scope() -> R<()> {
    let mut h = Heap::new();
    let a = obj(&mut h)?;
    assert_eq!(h.root(val(a)), Err(Error::NoScope));
    let outer = h.open_scope();
    let inner = h.open_scope();
    assert_eq!(h.close_scope(outer), Err(Error::ScopeMismatch));
    h.close_scope(inner)?;
    h.close_scope(Scope { depth: 1 })?;
    // The mismatch above did not unroot anything.
    let s = h.open_scope();
    h.root(val(a))?;
    let t = h.open_scope();
    assert_eq!(h.close_scope(s), Err(Error::ScopeMismatch));
    h.collect(&[])?;
    assert!(h.is_live(a));
    h.close_scope(t)?;
    Ok(())
}

#[test]
fn a_collection_is_refused_during_an_operation() -> R<()> {
    let mut h = Heap::new();
    let a = obj(&mut h)?;
    assert_eq!(h.exit_op(), Err(Error::NotInOperation));
    h.enter_op();
    h.enter_op();
    assert_eq!(h.collect(&[]).err(), Some(Error::InOperation));
    h.exit_op()?;
    assert_eq!(h.collect(&[]).err(), Some(Error::InOperation));
    h.exit_op()?;
    assert!(h.is_live(a), "the refused collection freed nothing");
    assert_eq!(h.collect(&[])?.freed, 1);
    Ok(())
}

// ---- WeakMap and WeakSet ----------------------------------------------

fn weak_map(h: &mut Heap, entries: &[(Ref, Value)]) -> R<Ref> {
    kind_of(h, Kind::WeakMap(entries.to_vec()))
}

fn map_entries(h: &Heap, m: Ref) -> R<Vec<(Ref, Value)>> {
    match &h.get(m)?.kind {
        Kind::WeakMap(e) => Ok(e.clone()),
        _ => Err(Error::NotAWeakRef),
    }
}

#[test]
fn a_weakmap_entry_lives_while_its_key_does() -> R<()> {
    let mut h = Heap::new();
    let key = obj(&mut h)?;
    let dead_key = obj(&mut h)?;
    let value = obj(&mut h)?;
    let dead_value = obj(&mut h)?;
    let m = weak_map(
        &mut h,
        &[
            (key, val(value)),
            (dead_key, val(dead_value)),
            (key, int(1)),
        ],
    )?;
    let out = h.collect(&[val(m), val(key)])?;
    assert_eq!(out.freed, 2);
    assert!(h.is_live(value) && stale(&h, dead_value) && stale(&h, dead_key));
    assert_eq!(map_entries(&h, m)?, [(key, val(value)), (key, int(1))]);
    // Drop the key: the entries go, and so does the value.
    h.collect(&[val(m)])?;
    assert_eq!(map_entries(&h, m)?, []);
    assert!(stale(&h, value) && stale(&h, key));
    Ok(())
}

#[test]
fn a_weakmap_does_not_keep_its_keys_and_an_unreachable_map_is_freed() -> R<()> {
    let mut h = Heap::new();
    let key = obj(&mut h)?;
    let value = obj(&mut h)?;
    // The value refers to its key: still not enough to keep the key.
    add_slot(&mut h, value, val(key))?;
    let m = weak_map(&mut h, &[(key, val(value))])?;
    h.collect(&[val(m)])?;
    assert_eq!(h.live(), 1);
    // Without the map, a rooted key keeps nothing of the map's.
    let k2 = obj(&mut h)?;
    let v2 = obj(&mut h)?;
    let m2 = weak_map(&mut h, &[(k2, val(v2))])?;
    h.collect(&[val(k2)])?;
    assert!(h.is_live(k2) && stale(&h, v2) && stale(&h, m2) && stale(&h, m));
    Ok(())
}

#[test]
fn ephemeron_chains_resolve_in_any_entry_order() -> R<()> {
    // Entries (k[i] -> k[i+1]) listed from the end of the chain to the start.
    let mut h = Heap::new();
    let ks: Vec<Ref> = (0..2000).map(|_| obj(&mut h)).collect::<R<_>>()?;
    let entries: Vec<(Ref, Value)> = ks
        .windows(2)
        .rev()
        .filter_map(|w| Some((*w.first()?, val(*w.get(1)?))))
        .collect();
    let m = weak_map(&mut h, &entries)?;
    let first = *ks.first().ok_or(Error::NoScope)?;
    h.collect(&[val(m), val(first)])?;
    assert_eq!(h.live(), 2001, "the whole chain, and the map");
    h.collect(&[val(m)])?;
    assert_eq!(h.live(), 1, "the map alone");
    Ok(())
}

#[test]
fn a_weakset_drops_dead_members_and_keeps_none_alive() -> R<()> {
    let mut h = Heap::new();
    let live = obj(&mut h)?;
    let dead = obj(&mut h)?;
    let s = kind_of(&mut h, Kind::WeakSet(vec![live, dead, live]))?;
    h.collect(&[val(s), val(live)])?;
    assert!(matches!(&h.get(s)?.kind, Kind::WeakSet(m) if *m == [live, live]));
    assert!(stale(&h, dead));
    h.collect(&[val(s)])?;
    assert!(matches!(&h.get(s)?.kind, Kind::WeakSet(m) if m.is_empty()));
    Ok(())
}

// ---- WeakRef ----------------------------------------------------------

#[test]
fn a_weakref_is_cleared_when_its_target_is_freed() -> R<()> {
    let mut h = Heap::new();
    let target = obj(&mut h)?;
    let w = kind_of(&mut h, Kind::WeakRef(Some(target)))?;
    let w2 = kind_of(&mut h, Kind::WeakRef(Some(target)))?;
    // Rooted target: both stay set.
    h.collect(&[val(w), val(w2), val(target)])?;
    assert_eq!(h.deref_weak(w)?, Some(target));
    h.end_job();
    // Unrooted: cleared, the target freed, and a clear WeakRef stays clear.
    h.collect(&[val(w)])?;
    assert_eq!(h.deref_weak(w)?, None);
    assert!(stale(&h, target) && stale(&h, w2));
    h.collect(&[val(w)])?;
    assert_eq!(h.deref_weak(w)?, None);
    Ok(())
}

#[test]
fn a_target_read_in_a_job_is_kept_until_the_job_ends() -> R<()> {
    let mut h = Heap::new();
    let target = obj(&mut h)?;
    let w = kind_of(&mut h, Kind::WeakRef(Some(target)))?;
    assert_eq!(h.deref_weak(w)?, Some(target));
    h.collect(&[val(w)])?;
    assert!(h.is_live(target), "GC9: kept for the job");
    assert_eq!(h.deref_weak(w)?, Some(target));
    h.end_job();
    h.collect(&[val(w)])?;
    assert!(stale(&h, target));
    assert_eq!(h.deref_weak(w)?, None);
    Ok(())
}

#[test]
fn deref_of_something_that_is_not_a_weakref_is_an_error() -> R<()> {
    let mut h = Heap::new();
    let o = obj(&mut h)?;
    assert_eq!(h.deref_weak(o), Err(Error::NotAWeakRef));
    h.collect(&[])?;
    assert_eq!(h.deref_weak(o), Err(Error::Arena(ArenaError::Stale)));
    Ok(())
}

// ---- FinalizationRegistry ---------------------------------------------

fn registry(h: &mut Heap, callback: Value, cells: Vec<Cell>) -> R<Ref> {
    kind_of(h, Kind::Registry(Registry { callback, cells }))
}

fn cell(target: Ref, held: Value, token: Option<Ref>) -> Cell {
    Cell {
        target,
        held,
        token,
    }
}

fn cells_of(h: &Heap, r: Ref) -> R<Vec<Cell>> {
    match &h.get(r)?.kind {
        Kind::Registry(reg) => Ok(reg.cells.clone()),
        _ => Err(Error::NotAWeakRef),
    }
}

#[test]
fn a_dead_target_queues_one_cleanup_and_its_cell_goes() -> R<()> {
    let mut h = Heap::new();
    let callback = obj(&mut h)?;
    let held = obj(&mut h)?;
    let alive = obj(&mut h)?;
    let dies = obj(&mut h)?;
    let dies_too = obj(&mut h)?;
    let reg = registry(
        &mut h,
        val(callback),
        vec![
            cell(dies, val(held), None),
            cell(alive, int(5), None),
            cell(dies_too, int(6), None),
        ],
    )?;
    let out = h.collect(&[val(reg), val(alive)])?;
    assert_eq!(
        out.cleanups,
        [
            Cleanup {
                callback: val(callback),
                held: val(held)
            },
            Cleanup {
                callback: val(callback),
                held: int(6)
            },
        ]
    );
    // The callback and the held value outlive the collection (GC6).
    assert!(h.is_live(callback) && h.is_live(held));
    assert!(stale(&h, dies) && stale(&h, dies_too));
    let left = cells_of(&h, reg)?;
    assert_eq!(left.len(), 1);
    assert_eq!(left.first().map(|c| c.target), Some(alive));
    // No cleanup is repeated.
    assert_eq!(h.collect(&[val(reg), val(alive)])?.cleanups, []);
    // When the target goes later, it is queued then.
    let out = h.collect(&[val(reg)])?;
    assert_eq!(out.cleanups.len(), 1);
    Ok(())
}

#[test]
fn an_unreachable_registry_queues_nothing() -> R<()> {
    let mut h = Heap::new();
    let target = obj(&mut h)?;
    let reg = registry(&mut h, int(0), vec![cell(target, int(1), None)])?;
    let out = h.collect(&[])?;
    assert_eq!((out.freed, out.cleanups.len()), (2, 0));
    assert!(stale(&h, reg));
    Ok(())
}

#[test]
fn a_dead_unregister_token_is_cleared_and_a_live_one_kept() -> R<()> {
    let mut h = Heap::new();
    let target = obj(&mut h)?;
    let tok_live = obj(&mut h)?;
    let tok_dead = obj(&mut h)?;
    let reg = registry(
        &mut h,
        int(0),
        vec![
            cell(target, int(1), Some(tok_live)),
            cell(target, int(2), Some(tok_dead)),
        ],
    )?;
    let out = h.collect(&[val(reg), val(target), val(tok_live)])?;
    assert!(out.cleanups.is_empty());
    let cells = cells_of(&h, reg)?;
    assert_eq!(
        cells.iter().map(|c| c.token).collect::<Vec<_>>(),
        [Some(tok_live), None]
    );
    assert!(stale(&h, tok_dead));
    Ok(())
}

#[test]
fn held_values_are_strong_so_a_held_value_naming_its_target_keeps_it() -> R<()> {
    // The standard says so: the registry holds `held` strongly.
    let mut h = Heap::new();
    let target = obj(&mut h)?;
    let reg = registry(&mut h, int(0), vec![cell(target, val(target), None)])?;
    let out = h.collect(&[val(reg)])?;
    assert!(out.cleanups.is_empty() && h.is_live(target));
    Ok(())
}

// ---- The property test ------------------------------------------------

/// A small deterministic generator, so the test needs no dependency.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    /// A number below `n` (which is not zero).
    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n.max(1)).unwrap_or(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    fn pick(&mut self, live: &[Ref]) -> Option<Ref> {
        live.get(self.below(live.len())).copied()
    }

    /// A reference to a live object about nine times in ten, else an int.
    fn value(&mut self, live: &[Ref]) -> Value {
        match self.pick(live) {
            Some(r) if !self.chance(10) => val(r),
            _ => int(i32::try_from(self.next() % 1000).unwrap_or(0)),
        }
    }
}

/// Everything a collection may change about an object, as plain data.
#[derive(Clone, Debug, PartialEq)]
struct Snap {
    proto: Option<Ref>,
    slots: Vec<Value>,
    elements: Vec<Value>,
    entries: Vec<(Ref, Value)>,
    members: Vec<Ref>,
    target: Option<Ref>,
    callback: Option<Value>,
    cells: Vec<(Ref, Value, Option<Ref>)>,
}

fn snap(o: &Object) -> Snap {
    let mut s = Snap {
        proto: o.proto,
        slots: o.slots.clone(),
        elements: o.elements.values().collect(),
        entries: vec![],
        members: vec![],
        target: None,
        callback: None,
        cells: vec![],
    };
    match &o.kind {
        Kind::Ordinary => {}
        Kind::WeakMap(e) => s.entries.clone_from(e),
        Kind::WeakSet(m) => s.members.clone_from(m),
        Kind::WeakRef(t) => s.target = *t,
        Kind::Registry(r) => {
            s.callback = Some(r.callback);
            s.cells = r
                .cells
                .iter()
                .map(|c| (c.target, c.held, c.token))
                .collect();
        }
    }
    s
}

fn snapshot(h: &Heap) -> Vec<(Ref, Snap)> {
    h.arena().iter().map(|(r, o)| (r, snap(o))).collect()
}

fn random_object(rng: &mut Lcg) -> Object {
    Object::of(match rng.below(10) {
        0 | 1 => Kind::WeakMap(vec![]),
        2 => Kind::WeakSet(vec![]),
        3 => Kind::WeakRef(None),
        4 => Kind::Registry(Registry {
            callback: int(0),
            cells: vec![],
        }),
        _ => Kind::Ordinary,
    })
}

/// Add random edges, all to live objects, from the live objects.
fn wire(h: &mut Heap, rng: &mut Lcg, live: &[Ref], density: usize) -> R<()> {
    for &r in live {
        if !rng.chance(density) {
            continue;
        }
        let proto = if rng.chance(30) { rng.pick(live) } else { None };
        let slots: Vec<Value> = (0..rng.below(4)).map(|_| rng.value(live)).collect();
        let elems: Vec<Value> = (0..rng.below(3)).map(|_| rng.value(live)).collect();
        let (t, k, v) = (rng.pick(live), rng.pick(live), rng.value(live));
        let (t2, k2) = (rng.pick(live), rng.pick(live));
        let o = h.get_mut(r)?;
        if proto.is_some() {
            o.proto = proto;
        }
        o.slots.extend(slots);
        for (i, e) in elems.into_iter().enumerate() {
            let _ = o.elements.set(u32::try_from(i).unwrap_or(0), e);
        }
        match &mut o.kind {
            Kind::Ordinary => {}
            Kind::WeakMap(es) => es.extend(k.map(|k| (k, v))),
            Kind::WeakSet(ms) => ms.extend(t),
            Kind::WeakRef(target) => *target = t,
            Kind::Registry(reg) => {
                reg.callback = v;
                reg.cells.extend(t.map(|t| cell(t, Value::int32(1), k)));
                reg.cells.extend(t2.map(|t| cell(t, v, k2)));
            }
        }
    }
    Ok(())
}

fn survived(before: &Ref, h: &Heap) -> bool {
    h.get(*before).is_ok()
}

/// The objects reachable from `roots`, by a second, independent walk over
/// the snapshot of the heap's public data: it shares nothing with
/// `Heap::graph` (whose omissions it would otherwise share), so the test
/// does not trust the extraction it checks.
fn oracle(before: &[(Ref, Snap)], roots: &[Ref]) -> HashSet<Ref> {
    let all: HashSet<Ref> = before.iter().map(|(r, _)| *r).collect();
    let mut seen: HashSet<Ref> = roots.iter().copied().filter(|r| all.contains(r)).collect();
    loop {
        let mut add: Vec<Ref> = vec![];
        for (r, s) in before {
            if !seen.contains(r) {
                continue;
            }
            add.extend(s.proto);
            add.extend(s.slots.iter().chain(&s.elements).filter_map(|v| v.as_ref()));
            add.extend(s.callback.and_then(|v| v.as_ref()));
            add.extend(s.cells.iter().filter_map(|c| c.1.as_ref()));
            add.extend(
                s.entries
                    .iter()
                    .filter(|(k, _)| seen.contains(k))
                    .filter_map(|(_, v)| v.as_ref()),
            );
        }
        let n = seen.len();
        seen.extend(add.into_iter().filter(|r| all.contains(r)));
        if seen.len() == n {
            return seen;
        }
    }
}

/// GC1 to GC6, checked for one collection of `h` against the world before.
/// `held` are the references the caller made roots other than through
/// `roots`: its open handles and the targets it kept for the job.
fn collect_and_check(h: &mut Heap, roots: &[Value], held: &[Ref]) -> R<()> {
    let graph = h.graph();
    let root_idx = h.root_indices(roots);
    let before = snapshot(h);
    let all_roots: Vec<Ref> = roots
        .iter()
        .filter_map(|v| v.as_ref())
        .chain(held.iter().copied())
        .collect();
    let want = oracle(&before, &all_roots);
    let out = h.collect(roots)?;
    for (r, _) in &before {
        assert_eq!(
            want.contains(r),
            h.get(*r).is_ok(),
            "the oracle's reachability"
        );
    }

    // Which slots survived, by (index, generation) as before.
    let mut survives = vec![false; graph.len()];
    for (r, _) in &before {
        let slot = usize::try_from(r.index)
            .ok()
            .and_then(|i| survives.get_mut(i));
        if let (true, Some(s)) = (survived(r, h), slot) {
            *s = true;
        }
    }
    // GC1 and GC2, against the specification's reachability.
    assert!(contract::safe(&graph, &root_idx, &survives), "GC1");
    assert!(contract::exact(&graph, &root_idx, &survives), "GC2");
    assert_eq!(out.survivors, survives.iter().filter(|&&s| s).count());
    assert_eq!(out.freed.checked_add(out.survivors), Some(before.len()));
    assert_eq!(h.live(), out.survivors);
    // Every freed slot's old reference is a defined error (arena).
    for (r, _) in &before {
        if !survived(r, h) {
            assert!(stale(h, *r));
        }
    }
    // GC3: the survivors' graph is closed, and no weak reference dangles.
    let after = h.graph();
    assert!(contract::closed(&after, &survives), "GC3");
    let alive = |r: &Ref| h.is_live(*r);
    for (r, s) in snapshot(h) {
        assert!(s.entries.iter().all(|(k, _)| alive(k)), "GC3 map key");
        assert!(s.members.iter().all(alive), "GC3 set member");
        assert!(s.target.iter().all(alive), "GC3 weakref");
        assert!(
            s.cells
                .iter()
                .all(|(t, _, k)| alive(t) && k.iter().all(alive))
        );
        // GC4: weak references to survivors are unchanged, the rest removed,
        // and nothing else about a survivor changed.
        let was = before
            .iter()
            .find(|(b, _)| *b == r)
            .map(|(_, s)| s.clone())
            .ok_or(Error::NoScope)?;
        let keep = |x: &Ref| survived(x, h);
        let want = Snap {
            entries: was
                .entries
                .iter()
                .copied()
                .filter(|(k, _)| keep(k))
                .collect(),
            members: was.members.iter().copied().filter(keep).collect(),
            target: was.target.filter(keep),
            cells: was
                .cells
                .iter()
                .filter(|(t, _, _)| keep(t))
                .map(|&(t, hv, k)| (t, hv, k.filter(keep)))
                .collect(),
            ..was
        };
        assert_eq!(s, want, "GC4");
    }
    // GC6: one cleanup per dead cell of a surviving registry, in order.
    let mut cleanups = vec![];
    for (r, s) in &before {
        if let (true, Some(callback)) = (survived(r, h), s.callback) {
            for (t, held, _) in &s.cells {
                if !survived(t, h) {
                    cleanups.push(Cleanup {
                        callback,
                        held: *held,
                    });
                }
            }
        }
    }
    assert_eq!(out.cleanups, cleanups, "GC6");
    // Their callbacks and held values are alive.
    for c in &out.cleanups {
        for v in [c.callback, c.held] {
            assert!(v.as_ref().is_none_or(|r| h.is_live(r)));
        }
    }
    assert!(h.arena().is_well_formed());
    Ok(())
}

fn live_refs(h: &Heap) -> Vec<Ref> {
    h.arena().iter().map(|(r, _)| r).collect()
}

#[test]
fn random_heaps_of_any_size_keep_what_the_roots_reach() -> R<()> {
    let mut rng = Lcg(0x005E_ED6C);
    let mut cases = 0;
    for case in 0..240usize {
        // Mostly small heaps, a few large ones.
        let n = match case % 20 {
            0 => 1500 + rng.below(1500),
            1..=4 => 50 + rng.below(250),
            _ => rng.below(30),
        };
        let mut h = Heap::new();
        let mut live = Vec::new();
        for _ in 0..n {
            live.push(h.alloc(random_object(&mut rng))?);
        }
        let density = 20 + rng.below(80);
        wire(&mut h, &mut rng, &live, density)?;
        // Several rounds: collect with random roots, then mutate the
        // survivors, reuse freed slots, and collect again.
        for _ in 0..4 {
            let live = live_refs(&h);
            let mut roots: Vec<Value> = (0..rng.below(1 + live.len() / 4))
                .map(|_| rng.value(&live))
                .collect();
            // Some roots are handles; some targets are kept for the job.
            if rng.chance(50) {
                let scope = h.open_scope();
                let mut held: Vec<Ref> = vec![];
                for v in roots.drain(..roots.len() / 2) {
                    h.root(v)?;
                    held.extend(v.as_ref());
                }
                for &r in &live {
                    if rng.chance(3) {
                        held.extend(h.deref_weak(r).ok().flatten());
                    }
                }
                collect_and_check(&mut h, &roots, &held)?;
                h.close_scope(scope)?;
            } else {
                collect_and_check(&mut h, &roots, &[])?;
            }
            h.end_job();
            cases += 1;
            let survivors = live_refs(&h);
            for _ in 0..rng.below(20) {
                h.alloc(random_object(&mut rng))?;
            }
            let all = live_refs(&h);
            let some: Vec<Ref> = survivors
                .iter()
                .copied()
                .filter(|_| rng.chance(50))
                .collect();
            let fresh: Vec<Ref> = all
                .iter()
                .copied()
                .filter(|r| !survivors.contains(r))
                .collect();
            wire(&mut h, &mut rng, &some, 60)?;
            wire(&mut h, &mut rng, &fresh, 100)?;
        }
    }
    assert_eq!(cases, 960);
    Ok(())
}

/// The marker agrees with the specification on random graphs, including
/// ones with wild edges (no such node) that a heap's graph never has.
#[test]
fn mark_equals_the_specification_on_random_graphs() {
    let mut rng = Lcg(0xA11CE);
    for _ in 0..2000 {
        let n = rng.below(12);
        let name = |rng: &mut Lcg| rng.below(n + 2);
        let graph: Vec<Node> = (0..n)
            .map(|_| Node {
                strong: (0..rng.below(3)).map(|_| name(&mut rng)).collect(),
                ephemerons: (0..rng.below(3))
                    .map(|_| (name(&mut rng), name(&mut rng)))
                    .collect(),
            })
            .collect();
        let roots: Vec<usize> = (0..rng.below(4)).map(|_| name(&mut rng)).collect();
        assert_eq!(mark(&graph, &roots), contract::reachable(&graph, &roots));
    }
}
