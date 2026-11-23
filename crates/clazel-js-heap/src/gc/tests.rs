//! Unit tests for each weak kind and for the roots, and the property test of
//! GC1 to GC6 over random heaps of any size, from a fixed-seed generator.

use super::contract::{self, Node};
use super::*;
use crate::arena::Error as ArenaError;
use crate::shape::MAX_FAST_PROPERTIES;
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
    // Miri interprets every step, so it builds a shorter chain; the normal
    // test job builds the full one.
    let length = if cfg!(miri) { 2_000 } else { 100_000 };
    for _ in 0..length {
        let n = obj(&mut h)?;
        add_slot(&mut h, tail, val(n))?;
        tail = n;
    }
    let out = h.collect(&[val(head)])?;
    assert_eq!((out.freed, out.survivors), (0, length + 1));
    let out = h.collect(&[])?;
    assert_eq!(out.freed, length + 1);
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
    // Marking is linear (GC5): a chain listed backwards used to resolve one
    // link per pass, and 2000 keys took 2999 s under Miri.
    let length: usize = if cfg!(miri) { 400 } else { 2000 };
    let ks: Vec<Ref> = (0..length).map(|_| obj(&mut h)).collect::<R<_>>()?;
    let entries: Vec<(Ref, Value)> = ks
        .windows(2)
        .rev()
        .filter_map(|w| Some((*w.first()?, val(*w.get(1)?))))
        .collect();
    let m = weak_map(&mut h, &entries)?;
    let first = *ks.first().ok_or(Error::NoScope)?;
    h.collect(&[val(m), val(first)])?;
    assert_eq!(h.live(), length + 1, "the whole chain, and the map");
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
    shape: ShapeId,
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
        shape: o.shape,
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
fn wire(h: &mut Heap, rng: &mut Lcg, live: &[Ref], keys: &[Key], density: usize) -> R<()> {
    for &r in live {
        if !rng.chance(density) {
            continue;
        }
        // Properties through the shape table: few distinct keys, so shapes
        // are shared and have parents.
        for _ in 0..rng.below(4) {
            let (key, v) = (keys.get(rng.below(keys.len())).copied(), rng.value(live));
            if let Some(key) = key {
                match h.add_property(r, key, Attrs::ALL, v) {
                    Ok(_) | Err(Error::Shape(shape::Error::Exists)) => {}
                    Err(e) => return Err(e),
                }
            }
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

/// A shape's properties: key, slot, attributes.
type Props = Vec<(Key, u32, Attrs)>;

/// The live shapes and keys, as plain data from the public accessors.
struct Tables {
    shapes: Vec<(ShapeId, Props)>,
    keys: Vec<(Key, JsString)>,
    issued_shapes: usize,
    issued_keys: usize,
}

fn tables(h: &Heap) -> Tables {
    let issued_shapes = h.shapes().issued();
    let issued_keys = h.keys().issued();
    let shapes = (1..=issued_shapes)
        .filter_map(|i| u32::try_from(i).ok().map(ShapeId))
        .filter(|&id| h.shapes().is_live(id))
        .map(|id| (id, h.shapes().properties(id)))
        .collect();
    let keys = (0..issued_keys)
        .filter_map(|i| u32::try_from(i).ok().map(Key))
        .filter_map(|k| h.key_string(k).map(|s| (k, s.clone())))
        .collect();
    Tables {
        shapes,
        keys,
        issued_shapes,
        issued_keys,
    }
}

/// GC10 to GC12's oracle: the shapes and keys that must survive, by an
/// independent walk over the public accessors (`Shapes::parent`,
/// `Shapes::properties`) and the snapshot, not `mark_shapes` or the table's
/// `ShapeGraph`. `objects` are the shapes of the objects that survive.
fn table_oracle(
    h: &Heap,
    objects: &[ShapeId],
    ekeys: &[Key],
    eshapes: &[ShapeId],
) -> (HashSet<ShapeId>, HashSet<Key>) {
    let mut shapes: HashSet<ShapeId> = HashSet::from([ROOT]);
    let mut stack: Vec<ShapeId> = objects.iter().chain(eshapes).copied().collect();
    while let Some(id) = stack.pop() {
        if h.shapes().is_live(id) && shapes.insert(id) {
            stack.extend(h.shapes().parent(id));
        }
    }
    let mut keys: HashSet<Key> = ekeys
        .iter()
        .copied()
        .filter(|&k| h.key_string(k).is_some())
        .collect();
    for &id in &shapes {
        keys.extend(h.shapes().properties(id).into_iter().map(|(k, _, _)| k));
    }
    (shapes, keys)
}

/// What a collection must do to the shape and key tables.
struct TableWant {
    before: Tables,
    shapes: HashSet<ShapeId>,
    keys: HashSet<Key>,
    spec_shapes: Vec<bool>,
    spec_keys: Vec<bool>,
}

fn entry(id: &ShapeId) -> Option<usize> {
    usize::try_from(id.0).ok().and_then(|i| i.checked_sub(1))
}

/// The oracle's and the specification's sets, computed before a collection.
fn table_want(
    h: &Heap,
    survivors_shapes: &[ShapeId],
    ekeys: &[Key],
    eshapes: &[ShapeId],
) -> TableWant {
    let before = tables(h);
    let (shapes, keys) = table_oracle(h, survivors_shapes, ekeys, eshapes);
    // The specification's sets, over the same table (GC10 to GC12).
    let spec_roots: Vec<usize> = std::iter::once(0)
        .chain(survivors_shapes.iter().filter_map(entry))
        .chain(eshapes.iter().filter_map(entry))
        .collect();
    let spec_root_keys: Vec<usize> = ekeys
        .iter()
        .filter(|&&k| h.key_string(k).is_some())
        .filter_map(|k| usize::try_from(k.0).ok())
        .collect();
    let (spec_shapes, spec_keys) =
        contract::live_shapes(h.shapes(), &spec_roots, &spec_root_keys, before.issued_keys);
    TableWant {
        before,
        shapes,
        keys,
        spec_shapes,
        spec_keys,
    }
}

/// GC10 to GC13 after a collection; returns the freed shape ids and keys.
fn check_tables(h: &Heap, want: &TableWant, out: &Collection) -> R<(Vec<ShapeId>, Vec<Key>)> {
    let mut freed_shapes = vec![];
    for (id, props) in &want.before.shapes {
        let live = h.shapes().is_live(*id);
        assert_eq!(live, want.shapes.contains(id), "GC10/GC12 shape {id:?}");
        let i = entry(id).ok_or(Error::NoScope)?;
        assert_eq!(live, want.spec_shapes.get(i).copied().unwrap_or(false));
        if live {
            assert_eq!(
                &h.shapes().properties(*id),
                props,
                "a live shape is as it was"
            );
        } else {
            freed_shapes.push(*id);
            assert_eq!(h.shapes().slot_count(*id), None, "GC13");
        }
    }
    let mut freed_keys = vec![];
    for (k, string) in &want.before.keys {
        let live = h.key_string(*k).is_some();
        assert_eq!(live, want.keys.contains(k), "GC11/GC12 key {k:?}");
        let i = usize::try_from(k.0).map_err(|_| Error::NoScope)?;
        assert_eq!(live, want.spec_keys.get(i).copied().unwrap_or(false));
        if live {
            assert_eq!(h.key_string(*k), Some(string), "GC11: the same string");
            assert_eq!(h.keys().find(string), Some(*k));
        } else {
            freed_keys.push(*k);
            assert_eq!(h.keys().find(string), None);
        }
    }
    assert_eq!(out.freed_shapes, freed_shapes.len());
    assert_eq!(out.freed_keys, freed_keys.len());
    let after = tables(h);
    assert_eq!(h.shapes().len(), after.shapes.len());
    assert_eq!(h.keys().len(), after.keys.len());
    // GC13: nothing was issued or renumbered.
    assert_eq!(after.issued_shapes, want.before.issued_shapes);
    assert_eq!(after.issued_keys, want.before.issued_keys);
    assert!(h.shapes().is_live(ROOT), "ROOT is never freed");
    // GC10: every live object's shape, and every parent, is live.
    for (_, o) in h.arena().iter() {
        let mut at = Some(o.shape);
        while let Some(id) = at {
            assert!(h.shapes().is_live(id), "GC10");
            at = h.shapes().parent(id);
        }
    }
    Ok((freed_shapes, freed_keys))
}

/// GC1 to GC6 and GC10 to GC13, checked for one collection of `h` against
/// the world before. `held` are the references the caller made roots other
/// than through `roots`: its open handles and the targets it kept for the
/// job. `ekeys` and `eshapes` are the keys and shapes it reports. Returns
/// the shape ids and keys that were freed.
fn collect_and_check(
    h: &mut Heap,
    roots: &[Value],
    held: &[Ref],
    ekeys: &[Key],
    eshapes: &[ShapeId],
) -> R<(Vec<ShapeId>, Vec<Key>)> {
    let graph = h.graph();
    let root_idx = h.root_indices(roots);
    let before = snapshot(h);
    let all_roots: Vec<Ref> = roots
        .iter()
        .filter_map(|v| v.as_ref())
        .chain(held.iter().copied())
        .collect();
    let want = oracle(&before, &all_roots);
    let survivors_shapes: Vec<ShapeId> = before
        .iter()
        .filter(|(r, _)| want.contains(r))
        .map(|(_, s)| s.shape)
        .collect();
    let table_want = table_want(h, &survivors_shapes, ekeys, eshapes);
    let out = h.collect_with(&RootSet {
        values: roots,
        keys: ekeys,
        shapes: eshapes,
    })?;
    let freed = check_tables(h, &table_want, &out)?;
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
    Ok(freed)
}

fn live_refs(h: &Heap) -> Vec<Ref> {
    h.arena().iter().map(|(r, _)| r).collect()
}

/// The names of the property keys of the property test: enough that one
/// object can pass the dictionary cutoff. Under Miri, 16: a chain of 128
/// shapes made the specification's fixpoint and the oracle's walks too slow
/// (the first version of this test took 837 s), and the dictionary is
/// covered by its own unit test there.
fn pool_strings() -> R<Vec<JsString>> {
    let n = if cfg!(miri) {
        16
    } else {
        MAX_FAST_PROPERTIES + 12
    };
    (0..n)
        .map(|i| JsString::from_rust_str(&format!("key{i}")).map_err(|_| Error::Intern))
        .collect()
}

/// The pool's keys, interned again (a freed one gets a new key, GC13).
fn intern_pool(h: &mut Heap, pool: &[JsString]) -> R<Vec<Key>> {
    pool.iter().map(|s| h.intern(s)).collect()
}

#[test]
fn random_heaps_of_any_size_keep_what_the_roots_reach() -> R<()> {
    let mut rng = Lcg(0x005E_ED6C);
    let mut cases = 0;
    // Under Miri, the first 2 cases of the same sequence (at a fraction of
    // their size); the normal test job runs all 240.
    let count: usize = if cfg!(miri) { 2 } else { 240 };
    for case in 0..count {
        // Mostly small heaps, a few large ones.
        let n = match case % 20 {
            // Under Miri, a thirtieth of the size, from the same draw.
            0 if cfg!(miri) => 50 + rng.below(50),
            0 => 1500 + rng.below(1500),
            // Under Miri, a heap of 20 to 80: the checks are quadratic, and
            // 300 objects took 570 s.
            1..=4 if cfg!(miri) => 20 + rng.below(60),
            1..=4 => 50 + rng.below(250),
            _ => rng.below(30),
        };
        let mut h = Heap::new();
        let mut live = Vec::new();
        for _ in 0..n {
            live.push(h.alloc(random_object(&mut rng))?);
        }
        let density = 20 + rng.below(80);
        let pool = pool_strings()?;
        let mut keys = intern_pool(&mut h, &pool)?;
        // Ids freed so far: they must stay freed, whatever is added later.
        let mut dead_shapes: Vec<ShapeId> = vec![];
        let mut dead_keys: Vec<Key> = vec![];
        wire(
            &mut h,
            &mut rng,
            &live,
            keys.get(..12).unwrap_or(&[]),
            density,
        )?;
        // In two cases of the twenty, one object has so many properties that
        // its shape is a dictionary of its own.
        if let (true, Some(&big)) = (case % 20 < 2 && !cfg!(miri), live.first()) {
            for &k in &keys {
                match h.add_property(big, k, Attrs::ALL, Value::int32(1)) {
                    Ok(_) | Err(Error::Shape(shape::Error::Exists)) => {}
                    Err(e) => return Err(e),
                }
            }
            assert!(h.shapes().is_dictionary(h.get(big)?.shape));
        }
        // Several rounds: collect with random roots, then mutate the
        // survivors, reuse freed slots, and collect again.
        for _ in 0..4 {
            let live = live_refs(&h);
            let mut roots: Vec<Value> = (0..rng.below(1 + live.len() / 4))
                .map(|_| rng.value(&live))
                .collect();
            // The embedder reports some keys and shapes it holds.
            let ekeys: Vec<Key> = keys.iter().copied().filter(|_| rng.chance(3)).collect();
            let eshapes: Vec<ShapeId> = (1..=h.shapes().issued())
                .filter_map(|i| u32::try_from(i).ok().map(ShapeId))
                .filter(|&id| h.shapes().is_live(id) && rng.chance(2))
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
                let freed = collect_and_check(&mut h, &roots, &held, &ekeys, &eshapes)?;
                dead_shapes.extend(freed.0);
                dead_keys.extend(freed.1);
                h.close_scope(scope)?;
            } else {
                let freed = collect_and_check(&mut h, &roots, &[], &ekeys, &eshapes)?;
                dead_shapes.extend(freed.0);
                dead_keys.extend(freed.1);
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
            // The interned strings come back with new keys when freed, and a
            // stale key is refused.
            let old = keys;
            keys = intern_pool(&mut h, &pool)?;
            for (a, b) in old.iter().zip(&keys) {
                assert_eq!(a == b, h.key_string(*a).is_some());
            }
            if let (Some(&k), Some(&r)) = (dead_keys.first(), some.first()) {
                let stale = h.add_property(r, k, Attrs::ALL, Value::int32(0));
                assert_eq!(stale, Err(Error::StaleKey));
            }
            wire(&mut h, &mut rng, &some, keys.get(..12).unwrap_or(&[]), 60)?;
            wire(&mut h, &mut rng, &fresh, keys.get(..12).unwrap_or(&[]), 100)?;
            // GC13: nothing freed has come back, under its old id.
            assert!(dead_shapes.iter().all(|&id| !h.shapes().is_live(id)));
            assert!(dead_keys.iter().all(|&k| h.key_string(k).is_none()));
        }
    }
    assert_eq!(cases, count * 4);
    Ok(())
}

/// The marker agrees with the specification on random graphs, including
/// ones with wild edges (no such node) that a heap's graph never has.
#[test]
fn mark_equals_the_specification_on_random_graphs() {
    let mut rng = Lcg(0xA11CE);
    // Under Miri, the first 100 graphs of the same sequence.
    let graphs = if cfg!(miri) { 100 } else { 2000 };
    for _ in 0..graphs {
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
        let (marked, units) = mark_counted(&graph, &roots);
        assert_eq!(marked, contract::reachable(&graph, &roots));
        let (nodes, strong, eph) = contract::totals(&graph);
        assert!(units <= contract::work_bound(nodes, strong, eph), "GC5");
    }
}

/// A map (node 0) of the chain `1 -> 2 -> ... -> n` (entry `(i, i + 1)`),
/// listed forwards or backwards, and the work of marking from the map and
/// the first key.
fn chain_work(n: usize, backwards: bool) -> (usize, usize) {
    let mut entries: Vec<(usize, usize)> = (1..n).map(|i| (i, i.saturating_add(1))).collect();
    if backwards {
        entries.reverse();
    }
    let mut graph = vec![Node::default(); n.saturating_add(1)];
    if let Some(map) = graph.first_mut() {
        map.ephemerons = entries;
    }
    let (marked, units) = mark_counted(&graph, &[0, 1]);
    assert!(marked.iter().all(|&m| m), "the whole chain is marked");
    let (nodes, strong, eph) = contract::totals(&graph);
    assert!(units <= contract::work_bound(nodes, strong, eph), "GC5");
    (units, nodes.saturating_add(strong).saturating_add(eph))
}

/// GC5, counted rather than timed: the work on a chain listed in either
/// order is a bounded number of units per element, and doubling the length
/// doubles it (a quadratic marker would quadruple it).
#[test]
fn ephemeron_marking_work_is_linear_in_either_order() {
    let sizes: &[usize] = if cfg!(miri) {
        &[50, 100, 200]
    } else {
        &[500, 1000, 2000, 4000]
    };
    let mut last: Option<usize> = None;
    for &n in sizes {
        let (fwd, _) = chain_work(n, false);
        let (back, size) = chain_work(n, true);
        // Listed forwards, each key is marked before its entry is examined;
        // backwards, each entry waits on its key and is fired: at most two
        // units more per entry, in either order.
        assert!(fwd <= back, "waiting costs, at most, a firing per entry");
        assert!(back <= 4 * size, "a bounded number of units per element");
        if let Some(prev) = last {
            assert!(back <= 2 * prev + 8, "doubling the chain doubles the work");
        }
        last = Some(back);
    }
}

/// Many entries waiting on one key, and one value kept by many keys: each
/// entry is still handled once.
#[test]
fn many_entries_on_one_key_and_many_keys_for_one_value_are_linear() {
    let n = if cfg!(miri) { 100 } else { 3000 };
    // Node 0: the map. 1: the shared key. 2: the shared value. Nodes 3..:
    // keys that are marked last, each with an entry to node 2, and an entry
    // (1, i) from the shared key to each of them.
    let mut graph = vec![Node::default(); n + 3];
    let mut entries: Vec<(usize, usize)> = (3..n + 3).map(|i| (1, i)).collect();
    entries.extend((3..n + 3).map(|i| (i, 2)));
    if let Some(map) = graph.first_mut() {
        map.ephemerons = entries;
    }
    let (marked, units) = mark_counted(&graph, &[0, 1]);
    assert!(marked.iter().all(|&m| m));
    let (nodes, strong, eph) = contract::totals(&graph);
    assert!(units <= contract::work_bound(nodes, strong, eph));
    // And without the shared key, nothing else is marked.
    let (marked, _) = mark_counted(&graph, &[0]);
    assert_eq!(marked.iter().filter(|&&m| m).count(), 1);
}

// ---- Strings and shapes ----------------------------------------------------

fn key(h: &mut Heap, s: &str) -> R<Key> {
    h.intern(&JsString::from_rust_str(s).map_err(|_| Error::Intern)?)
}

fn shape_of(h: &Heap, r: Ref) -> R<ShapeId> {
    Ok(h.get(r)?.shape)
}

#[test]
fn a_live_objects_shape_and_keys_survive_and_the_rest_are_freed() -> R<()> {
    let mut h = Heap::new();
    let (a, b, c) = (key(&mut h, "a")?, key(&mut h, "b")?, key(&mut h, "c")?);
    let keep = obj(&mut h)?;
    let drop = obj(&mut h)?;
    h.add_property(keep, a, Attrs::ALL, int(1))?;
    h.add_property(drop, b, Attrs::ALL, int(2))?;
    let kept_shape = shape_of(&h, keep)?;
    let dropped_shape = shape_of(&h, drop)?;
    // `c` is interned and used by nothing.
    let out = h.collect(&[val(keep)])?;
    assert_eq!((out.freed_shapes, out.freed_keys), (1, 2));
    assert!(h.shapes().is_live(kept_shape) && h.shapes().is_live(ROOT));
    assert!(!h.shapes().is_live(dropped_shape));
    assert_eq!(h.shapes().lookup(kept_shape, a), Some((0, Attrs::ALL)));
    assert!(h.key_string(a).is_some());
    assert!(h.key_string(b).is_none() && h.key_string(c).is_none());
    assert_eq!(h.keys().len(), 1);
    Ok(())
}

#[test]
fn a_shape_keeps_its_parents_but_a_parent_does_not_keep_its_children() -> R<()> {
    let mut h = Heap::new();
    let (a, b) = (key(&mut h, "a")?, key(&mut h, "b")?);
    let o = obj(&mut h)?;
    h.add_property(o, a, Attrs::ALL, int(1))?;
    let s1 = shape_of(&h, o)?;
    h.add_property(o, b, Attrs::ALL, int(2))?;
    let s2 = shape_of(&h, o)?;
    // A second object stays at {a}, and the first dies: the child {a, b}
    // goes, its parent {a} stays, and so does the key `a`, not `b`.
    let other = obj(&mut h)?;
    h.add_property(other, a, Attrs::ALL, int(1))?;
    assert_eq!(shape_of(&h, other)?, s1, "shared");
    h.collect(&[val(other)])?;
    assert!(h.shapes().is_live(s1) && !h.shapes().is_live(s2));
    assert!(h.key_string(a).is_some() && h.key_string(b).is_none());
    // The transition to the freed child is gone: the same property added
    // again is a new shape, never the old id, and a stale key is refused.
    assert_eq!(
        h.add_property(other, b, Attrs::ALL, int(3)),
        Err(Error::StaleKey)
    );
    let b2 = key(&mut h, "b")?;
    assert_ne!(b2, b, "a freed key id is not reused");
    h.add_property(other, b2, Attrs::ALL, int(3))?;
    let s3 = shape_of(&h, other)?;
    assert!(s3.0 > s2.0, "a freed shape id is not reused");
    assert_eq!(h.shapes().lookup(s3, a), Some((0, Attrs::ALL)));
    // With the object gone, so is everything but the root.
    h.collect(&[])?;
    assert!(!h.shapes().is_live(s1) && !h.shapes().is_live(s3));
    assert_eq!(h.shapes().len(), 1);
    assert_eq!(h.keys().len(), 0);
    Ok(())
}

#[test]
fn a_dictionary_shape_dies_with_its_object_and_its_keys_with_it() -> R<()> {
    let mut h = Heap::new();
    let o = obj(&mut h)?;
    let mut keys = vec![];
    for i in 0..=MAX_FAST_PROPERTIES {
        let k = key(&mut h, &format!("p{i}"))?;
        keys.push(k);
        h.add_property(o, k, Attrs::ALL, int(1))?;
    }
    let dict = shape_of(&h, o)?;
    assert!(h.shapes().is_dictionary(dict));
    let out = h.collect(&[val(o)])?;
    // A dictionary has no parent: the shared chain below it is garbage, but
    // the dictionary holds every key.
    assert_eq!(out.freed_shapes, MAX_FAST_PROPERTIES);
    assert_eq!(out.freed_keys, 0);
    assert!(keys.iter().all(|&k| h.key_string(k).is_some()));
    let out = h.collect(&[])?;
    assert!(!h.shapes().is_live(dict));
    assert_eq!(out.freed_keys, MAX_FAST_PROPERTIES + 1);
    assert_eq!((h.shapes().len(), h.keys().len()), (1, 0));
    Ok(())
}

#[test]
fn the_embedder_keeps_keys_and_shapes_it_reports() -> R<()> {
    let mut h = Heap::new();
    let (a, b) = (key(&mut h, "a")?, key(&mut h, "b")?);
    let o = obj(&mut h)?;
    h.add_property(o, a, Attrs::ALL, int(1))?;
    let s1 = shape_of(&h, o)?;
    // `o` dies, but its shape is an inline cache's, and `b` a constant's.
    let out = h.collect_with(&RootSet {
        values: &[],
        keys: &[b],
        shapes: &[s1],
    })?;
    assert_eq!(out.freed_shapes, 0);
    assert!(h.shapes().is_live(s1));
    assert!(h.key_string(a).is_some(), "the reported shape names `a`");
    assert!(h.key_string(b).is_some());
    // A stale or made-up root is ignored.
    let out = h.collect_with(&RootSet {
        values: &[],
        keys: &[Key(77)],
        shapes: &[ShapeId(0), ShapeId(500)],
    })?;
    assert_eq!((out.freed_shapes, out.freed_keys), (1, 2));
    assert_eq!(h.shapes().len(), 1);
    Ok(())
}

#[test]
fn an_object_needs_a_live_shape_and_a_refused_collection_frees_nothing() -> R<()> {
    let mut h = Heap::new();
    let mut o = Object::ordinary();
    o.shape = ShapeId(40);
    assert_eq!(
        h.alloc(o).map(|_| ()),
        Err(Error::Shape(shape::Error::Unknown))
    );
    let k = key(&mut h, "k")?;
    h.enter_op();
    assert_eq!(h.collect(&[]).map(|_| ()), Err(Error::InOperation));
    assert!(h.key_string(k).is_some(), "nothing changed");
    h.exit_op()?;
    Ok(())
}

/// A shape table for the marker's agreement with the specification:
/// `(exists, parent, keys)` per entry.
struct Table(Vec<(bool, Option<usize>, Vec<usize>)>);

impl contract::ShapeGraph for Table {
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

/// `mark_shapes` equals the specification on random tables, including wild
/// ones a real table never has (cycles, parents that do not exist, keys out
/// of range, roots naming nothing).
#[test]
fn mark_shapes_equals_the_specification_on_random_tables() {
    let mut rng = Lcg(0x5AA5E);
    let tables = if cfg!(miri) { 100 } else { 3000 };
    for _ in 0..tables {
        let n = rng.below(14);
        let key_count = rng.below(8);
        let table: Vec<(bool, Option<usize>, Vec<usize>)> = (0..n)
            .map(|_| {
                let parent = rng.chance(70).then(|| rng.below(n + 2));
                let keys = (0..rng.below(3))
                    .map(|_| rng.below(key_count + 2))
                    .collect();
                (rng.chance(85), parent, keys)
            })
            .collect();
        let g = Table(table);
        let roots: Vec<usize> = (0..rng.below(4)).map(|_| rng.below(n + 2)).collect();
        let root_keys: Vec<usize> = (0..rng.below(3))
            .map(|_| rng.below(key_count + 2))
            .collect();
        let mut shapes = vec![false; n];
        let mut keys = vec![false; key_count];
        mark_shapes(&g, &roots, &root_keys, &mut shapes, &mut keys);
        assert!(contract::shapes_exact(
            &g, &roots, &root_keys, &shapes, &keys
        ));
    }
}
