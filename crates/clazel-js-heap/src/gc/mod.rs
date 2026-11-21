//! The collector (phase-7.md item 7.6). [`contract`] states what it must
//! satisfy (GC1 to GC9); this is the implementation, and `src/proofs.rs`
//! holds the Kani harnesses for it.
//!
//! 7.0(f) G1: stop-the-world mark and sweep, non-moving. A collection:
//!
//! 1. refuses to run during an operation (GC7);
//! 2. builds the abstract graph of the live objects ([`Heap::graph`]) and
//!    the root slots, from the caller's roots, the open handle scopes and
//!    the objects kept alive for the job (GC9);
//! 3. marks ([`mark`], which is proven equal to [`contract::reachable`]);
//! 4. clears weak references to unmarked slots and takes the finalization
//!    cleanups (GC4, GC6);
//! 5. frees every unmarked slot through [`Arena::free`], which bumps its
//!    generation (GC2; the arena's invariant 3);
//! 6. marks and sweeps the shapes and interned keys from the survivors
//!    (below).
//!
//! # What an embedder reports
//!
//! 7.0(f) names the roots: the value-stack region, the handles that
//! bindings and built-ins hold, every DOM node's wrapper, and the job and
//! task queues. The heap knows its own handle stack and kept-alive list;
//! the rest the embedder passes to [`Heap::collect`] as `roots` (the
//! engine's `Host` tracing method makes the DOM wrappers and task queues
//! part of that list). The cleanups a collection returns are tasks; their
//! callback and held values are alive after the collection, and the
//! embedder must report them as roots until it has run them.
//!
//! # Strings and shapes (GC10 to GC13)
//!
//! The heap owns the property-key [`Interner`] and the [`Shapes`] table,
//! and a collection also frees what no live thing reaches (step 6):
//!
//! - the shapes of the *surviving* objects, their parents, and the shapes the
//!   embedder reports ([`RootSet::shapes`]) are kept, and so is
//!   [`ROOT`];
//! - the keys those shapes name, and the keys the embedder reports
//!   ([`RootSet::keys`]), are kept;
//! - everything else is freed ([`Shapes::sweep`], [`Interner::sweep`]), and
//!   its id is never issued again.
//!
//! Shapes and keys hold no reference into the arena, so they are marked
//! after the objects, from the survivors. [`mark_shapes`] is the marker,
//! proven closed over its roots by Kani (`src/proofs.rs`).
//!
//! # What is not here
//!
//! Symbols are not collected. A key or shape id the embedder keeps outside
//! the heap (a bytecode constant, an inline cache's shape) is the
//! embedder's to report; one it forgot to report is a defined miss after
//! the collection (GC13), not another property. Compacting the tombstones
//! of the two tables is later, and must flush the inline caches.

pub mod contract;

use crate::arena::{self, Arena, Ref};
use crate::elements::Elements;
use crate::shape::{self, Attrs, ROOT, ShapeId, Shapes};
use crate::string::{Interner, JsString, Key};
use crate::value::Value;
use contract::{Graph, Node, ShapeGraph};

/// What a heap object is, beyond its ordinary properties.
#[derive(Clone, Debug)]
pub enum Kind {
    /// An object with only strong properties.
    Ordinary,
    /// `WeakMap`: `(key, value)` entries; the key is weak, and the value is
    /// kept alive by the key (an ephemeron).
    WeakMap(Vec<(Ref, Value)>),
    /// `WeakSet`: weakly held members.
    WeakSet(Vec<Ref>),
    /// `WeakRef`: a weakly held target, `None` once cleared.
    WeakRef(Option<Ref>),
    /// `FinalizationRegistry`.
    Registry(Registry),
}

/// A `FinalizationRegistry`'s state.
#[derive(Clone, Debug)]
pub struct Registry {
    /// The cleanup callback, held strongly.
    pub callback: Value,
    /// Registered targets.
    pub cells: Vec<Cell>,
}

/// One `FinalizationRegistry.prototype.register` call.
#[derive(Clone, Copy, Debug)]
pub struct Cell {
    /// The weakly held target.
    pub target: Ref,
    /// The value passed to the callback, held strongly.
    pub held: Value,
    /// The weakly held unregister token, if any.
    pub token: Option<Ref>,
}

/// A heap object: a prototype, property slots, indexed elements and a kind.
#[derive(Clone, Debug)]
pub struct Object {
    /// The prototype, a strong reference.
    pub proto: Option<Ref>,
    /// The shape: which keys the property slots below belong to. A live
    /// object's shape is live (GC10).
    pub shape: ShapeId,
    /// Property values (a shape maps keys to these indices), all strong.
    pub slots: Vec<Value>,
    /// Indexed properties, all strong.
    pub elements: Elements,
    /// What kind of object this is.
    pub kind: Kind,
}

impl Object {
    /// An ordinary object with no properties and no prototype.
    #[must_use]
    pub const fn ordinary() -> Self {
        Self::of(Kind::Ordinary)
    }

    /// An object of the given kind with no properties and no prototype.
    #[must_use]
    pub const fn of(kind: Kind) -> Self {
        Self {
            proto: None,
            shape: ROOT,
            slots: Vec::new(),
            elements: Elements::new(),
            kind,
        }
    }
}

/// One finalization callback to run: the embedder queues it as a task
/// (GC6). Nothing runs during a collection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cleanup {
    /// The registry's callback.
    pub callback: Value,
    /// The held value of the cell whose target was freed.
    pub held: Value,
}

/// What one collection did.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Collection {
    /// Slots freed.
    pub freed: usize,
    /// Slots that survived.
    pub survivors: usize,
    /// Cleanups for the embedder to run as tasks.
    pub cleanups: Vec<Cleanup>,
    /// Shapes freed (GC12).
    pub freed_shapes: usize,
    /// Interned keys freed (GC12).
    pub freed_keys: usize,
}

/// Why a heap operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The arena refused ([`arena::Error`]).
    Arena(arena::Error),
    /// A collection was requested during an operation (GC7).
    InOperation,
    /// `exit_op` without a matching `enter_op`.
    NotInOperation,
    /// A handle was made with no scope open.
    NoScope,
    /// A scope was closed out of order (GC8).
    ScopeMismatch,
    /// The reference does not name a live `WeakRef`.
    NotAWeakRef,
    /// A shape operation failed ([`shape::Error`]); `Unknown` also when an
    /// object is allocated with a shape that is not live.
    Shape(shape::Error),
    /// The key is not live: never issued, or freed by a collection (GC13).
    StaleKey,
    /// The interner is full, or the string is too long.
    Intern,
}

impl From<arena::Error> for Error {
    fn from(e: arena::Error) -> Self {
        Self::Arena(e)
    }
}

impl From<shape::Error> for Error {
    fn from(e: shape::Error) -> Self {
        Self::Shape(e)
    }
}

/// What the embedder reports to a collection besides the heap's own roots
/// (the handle stack and the job's kept targets).
#[derive(Clone, Copy, Debug, Default)]
pub struct RootSet<'a> {
    /// The value stack, DOM wrappers, task queues and pending cleanups.
    pub values: &'a [Value],
    /// Keys held outside the heap, such as bytecode constants.
    pub keys: &'a [Key],
    /// Shapes held outside the heap, such as an inline cache's.
    pub shapes: &'a [ShapeId],
}

/// An open handle scope; closing it unroots the handles made in it.
#[derive(Debug)]
pub struct Scope {
    depth: usize,
}

/// The heap: the arena of objects, the handle stack, the objects kept
/// alive for the current job and the operation guard.
#[derive(Debug)]
pub struct Heap {
    arena: Arena<Object>,
    handles: Vec<Value>,
    scope_marks: Vec<usize>,
    kept: Vec<Ref>,
    op_depth: u32,
    shapes: Shapes,
    keys: Interner,
}

impl Default for Heap {
    fn default() -> Self {
        Self::new()
    }
}

/// Which slots are alive after marking: the generation of each live slot
/// (before the sweep) and its mark. Owned, so the sweep can mutate the
/// arena while asking it.
struct Liveness {
    generation: Vec<Option<u16>>,
    marked: Vec<bool>,
}

impl Liveness {
    /// Whether `r` names an object that survives this collection.
    fn survives(&self, r: Ref) -> bool {
        let Some(i) = usize::try_from(r.index).ok() else {
            return false;
        };
        self.generation.get(i).copied().flatten() == Some(r.generation)
            && self.marked.get(i).copied().unwrap_or(false)
    }
}

impl Heap {
    /// An empty heap that may grow to [`arena::MAX_SLOTS`] objects.
    #[must_use]
    pub fn new() -> Self {
        Self::with_limit(arena::MAX_SLOTS)
    }

    /// An empty heap of at most `limit` objects: the memory limit, and the
    /// harnesses' bound.
    #[must_use]
    pub fn with_limit(limit: usize) -> Self {
        Self {
            arena: Arena::with_limit(limit),
            handles: Vec::new(),
            scope_marks: Vec::new(),
            kept: Vec::new(),
            op_depth: 0,
            shapes: Shapes::new(),
            keys: Interner::new(),
        }
    }

    /// Store an object. Never collects: a full heap is reported, and the
    /// embedder collects at its next safe point.
    ///
    /// # Errors
    /// [`arena::Error::Full`] as [`Error::Arena`]; [`shape::Error::Unknown`]
    /// as [`Error::Shape`] if the object's shape is not live.
    pub fn alloc(&mut self, object: Object) -> Result<Ref, Error> {
        if !self.shapes.is_live(object.shape) {
            return Err(Error::Shape(shape::Error::Unknown));
        }
        Ok(self.arena.alloc(object)?)
    }

    /// The key for `s`, interning it if no live key has its string.
    ///
    /// # Errors
    /// [`Error::Intern`] if the table is full.
    pub fn intern(&mut self, s: &JsString) -> Result<Key, Error> {
        self.keys.intern(s).map_err(|_| Error::Intern)
    }

    /// The string a live key stands for.
    #[must_use]
    pub fn key_string(&self, k: Key) -> Option<&JsString> {
        self.keys.resolve(k)
    }

    /// The interner, for its invariants' checks.
    #[must_use]
    pub const fn keys(&self) -> &Interner {
        &self.keys
    }

    /// The shape table, for lookups and its invariants' checks.
    #[must_use]
    pub const fn shapes(&self) -> &Shapes {
        &self.shapes
    }

    /// Give object `r` the property `key` with `attrs` and the value `v`:
    /// its shape becomes the transition on `(key, attrs)` (shared with every
    /// object that gains the same properties in the same order), and the
    /// slot the shape assigns holds `v` (earlier slots missing from the
    /// object read as `undefined`). Returns the slot.
    ///
    /// # Errors
    /// [`Error::StaleKey`] if `key` is not live; [`Error::Arena`] for a bad
    /// `r`; [`Error::Shape`] as [`Shapes::add_property`] (`Exists` if the
    /// object's shape has the key already).
    pub fn add_property(&mut self, r: Ref, key: Key, attrs: Attrs, v: Value) -> Result<u32, Error> {
        if self.keys.resolve(key).is_none() {
            return Err(Error::StaleKey);
        }
        let from = self.arena.get(r)?.shape;
        let (to, slot) = self.shapes.add_property(from, key, attrs)?;
        let o = self.arena.get_mut(r)?;
        let at = usize::try_from(slot).map_err(|_| Error::Shape(shape::Error::TooMany))?;
        if o.slots.len() <= at {
            o.slots.resize(at.saturating_add(1), Value::UNDEFINED);
        }
        if let Some(cell) = o.slots.get_mut(at) {
            *cell = v;
        }
        o.shape = to;
        Ok(slot)
    }

    /// The object `r` names.
    ///
    /// # Errors
    /// [`Error::Arena`]: out of range, or stale.
    pub fn get(&self, r: Ref) -> Result<&Object, Error> {
        Ok(self.arena.get(r)?)
    }

    /// The object `r` names, mutably.
    ///
    /// # Errors
    /// As [`Heap::get`].
    pub fn get_mut(&mut self, r: Ref) -> Result<&mut Object, Error> {
        Ok(self.arena.get_mut(r)?)
    }

    /// Whether `r` names a live object.
    #[must_use]
    pub fn is_live(&self, r: Ref) -> bool {
        self.arena.is_live(r)
    }

    /// The number of live objects.
    #[must_use]
    pub const fn live(&self) -> usize {
        self.arena.live()
    }

    /// The arena, for its invariants' checks.
    #[must_use]
    pub const fn arena(&self) -> &Arena<Object> {
        &self.arena
    }

    /// An operation begins: no collection may run until it ends (GC7).
    pub fn enter_op(&mut self) {
        self.op_depth = self.op_depth.saturating_add(1);
    }

    /// The operation ends.
    ///
    /// # Errors
    /// [`Error::NotInOperation`] if none was begun.
    pub fn exit_op(&mut self) -> Result<(), Error> {
        self.op_depth = self.op_depth.checked_sub(1).ok_or(Error::NotInOperation)?;
        Ok(())
    }

    /// Open a handle scope (GC8).
    pub fn open_scope(&mut self) -> Scope {
        self.scope_marks.push(self.handles.len());
        Scope {
            depth: self.scope_marks.len(),
        }
    }

    /// Root `v` until the innermost scope closes; returns it.
    ///
    /// # Errors
    /// [`Error::NoScope`] if no scope is open.
    pub fn root(&mut self, v: Value) -> Result<Value, Error> {
        if self.scope_marks.is_empty() {
            return Err(Error::NoScope);
        }
        self.handles.push(v);
        Ok(v)
    }

    /// Close `scope`, unrooting its handles.
    ///
    /// # Errors
    /// [`Error::ScopeMismatch`] if it is not the innermost open scope; the
    /// handles stay rooted then.
    pub fn close_scope(&mut self, scope: Scope) -> Result<(), Error> {
        if scope.depth != self.scope_marks.len() {
            return Err(Error::ScopeMismatch);
        }
        let to = self.scope_marks.pop().ok_or(Error::ScopeMismatch)?;
        self.handles.truncate(to);
        Ok(())
    }

    /// `WeakRef.prototype.deref` (ECMA-262 `AddToKeptObjects`): the target,
    /// or `None` if it was collected. A live target is kept alive until
    /// [`Heap::end_job`] (GC9).
    ///
    /// # Errors
    /// [`Error::NotAWeakRef`] if `weak` is not a live `WeakRef`.
    pub fn deref_weak(&mut self, weak: Ref) -> Result<Option<Ref>, Error> {
        let Kind::WeakRef(target) = self.arena.get(weak)?.kind else {
            return Err(Error::NotAWeakRef);
        };
        let Some(t) = target.filter(|&t| self.arena.is_live(t)) else {
            return Ok(None);
        };
        self.kept.push(t);
        Ok(Some(t))
    }

    /// The job ends (ECMA-262 `ClearKeptObjects`): the targets read by
    /// `deref_weak` are no longer kept alive.
    pub fn end_job(&mut self) {
        self.kept.clear();
    }

    /// The abstract graph of the heap: one node per arena slot, the empty
    /// node for a slot that is not live. A reference to a slot that is not
    /// live, or is a different generation, is no edge.
    #[must_use]
    pub fn graph(&self) -> Vec<Node> {
        let mut nodes = vec![Node::default(); self.arena.slots()];
        let idx = |r: Ref| -> Option<usize> {
            self.arena
                .is_live(r)
                .then(|| usize::try_from(r.index).ok())
                .flatten()
        };
        let val = |v: Value| v.as_ref().and_then(idx);
        for (r, o) in self.arena.iter() {
            let Some(node) = usize::try_from(r.index).ok().and_then(|i| nodes.get_mut(i)) else {
                continue;
            };
            node.strong.extend(o.proto.and_then(idx));
            node.strong.extend(o.slots.iter().copied().filter_map(val));
            node.strong.extend(o.elements.values().filter_map(val));
            match &o.kind {
                Kind::Ordinary | Kind::WeakSet(_) | Kind::WeakRef(_) => {}
                Kind::WeakMap(entries) => {
                    for &(k, v) in entries {
                        if let (Some(k), Some(v)) = (idx(k), val(v)) {
                            node.ephemerons.push((k, v));
                        }
                    }
                }
                Kind::Registry(reg) => {
                    node.strong.extend(val(reg.callback));
                    node.strong
                        .extend(reg.cells.iter().filter_map(|c| val(c.held)));
                }
            }
        }
        nodes
    }

    /// The slot indices of the live objects among `roots`, the open
    /// handles and the kept-alive targets.
    #[must_use]
    pub fn root_indices(&self, roots: &[Value]) -> Vec<usize> {
        let from_refs = self.kept.iter().copied();
        let from_values = roots
            .iter()
            .chain(self.handles.iter())
            .filter_map(|v| v.as_ref());
        from_refs
            .chain(from_values)
            .filter(|&r| self.arena.is_live(r))
            .filter_map(|r| usize::try_from(r.index).ok())
            .collect()
    }

    /// Collect garbage (module header). `roots` are the embedder's:
    /// the value stack, DOM wrappers, task queues and pending cleanups. No
    /// key or shape is reported (see [`Heap::collect_with`]).
    ///
    /// # Errors
    /// As [`Heap::collect_with`].
    pub fn collect(&mut self, roots: &[Value]) -> Result<Collection, Error> {
        self.collect_with(&RootSet {
            values: roots,
            ..RootSet::default()
        })
    }

    /// Collect garbage (module header), with the keys and shapes the
    /// embedder holds as well as its values.
    ///
    /// # Errors
    /// [`Error::InOperation`] during an operation (GC7); nothing changes.
    /// [`Error::Arena`] if the arena reports corruption while freeing
    /// (unreachable by construction).
    pub fn collect_with(&mut self, roots: &RootSet<'_>) -> Result<Collection, Error> {
        if self.op_depth != 0 {
            return Err(Error::InOperation);
        }
        let graph = self.graph();
        let marked = mark(&graph, &self.root_indices(roots.values));
        let mut generation = vec![None; self.arena.slots()];
        let live: Vec<Ref> = self.arena.iter().map(|(r, _)| r).collect();
        for r in &live {
            if let Some(g) = usize::try_from(r.index)
                .ok()
                .and_then(|i| generation.get_mut(i))
            {
                *g = Some(r.generation);
            }
        }
        let liveness = Liveness { generation, marked };
        let mut out = Collection::default();
        // The shapes of the survivors, and the embedder's, are the roots of
        // the shape table (entry 0 is `ROOT`).
        let mut shape_roots: Vec<usize> = vec![0];
        let entry = |id: ShapeId| usize::try_from(id.0).ok().and_then(|i| i.checked_sub(1));
        shape_roots.extend(roots.shapes.iter().copied().filter_map(entry));
        for &r in &live {
            if liveness.survives(r) {
                out.survivors = out.survivors.saturating_add(1);
                shape_roots.extend(self.arena.get(r).ok().and_then(|o| entry(o.shape)));
                if let Ok(o) = self.arena.get_mut(r) {
                    clear_weak(o, &liveness, &mut out.cleanups);
                }
            } else {
                self.arena.free(r)?;
                out.freed = out.freed.saturating_add(1);
            }
        }
        let key_roots: Vec<usize> = roots
            .keys
            .iter()
            .filter_map(|k| usize::try_from(k.0).ok())
            .collect();
        let mut shape_marks = vec![false; self.shapes.issued()];
        let mut key_marks = vec![false; self.keys.issued()];
        mark_shapes(
            &self.shapes,
            &shape_roots,
            &key_roots,
            &mut shape_marks,
            &mut key_marks,
        );
        out.freed_shapes = self.shapes.sweep(&shape_marks);
        out.freed_keys = self.keys.sweep(&key_marks);
        Ok(out)
    }
}

/// GC4 and GC6 for one surviving object: remove weak references to freed
/// slots, and take the cleanups of a registry's dead cells.
fn clear_weak(o: &mut Object, live: &Liveness, cleanups: &mut Vec<Cleanup>) {
    match &mut o.kind {
        Kind::Ordinary => {}
        Kind::WeakMap(entries) => entries.retain(|&(k, _)| live.survives(k)),
        Kind::WeakSet(members) => members.retain(|&m| live.survives(m)),
        Kind::WeakRef(target) => {
            if target.is_some_and(|t| !live.survives(t)) {
                *target = None;
            }
        }
        Kind::Registry(reg) => {
            let callback = reg.callback;
            reg.cells.retain_mut(|cell| {
                if live.survives(cell.target) {
                    if cell.token.is_some_and(|t| !live.survives(t)) {
                        cell.token = None;
                    }
                    true
                } else {
                    cleanups.push(Cleanup {
                        callback,
                        held: cell.held,
                    });
                    false
                }
            });
        }
    }
}

/// Mark the shapes and keys that `roots` (shape table entries) and
/// `root_keys` reach (GC10 to GC12): each root shape, its parents, and every
/// key any of them names. `shapes` (one flag per table entry) and `keys`
/// (one per key issued) are all false on entry. Each shape is marked once,
/// so the work is linear in the table. [`contract::live_shapes`] is its
/// specification. A root naming no live shape, or a key past `keys`, is
/// ignored; a parent that is not live ends a chain.
pub fn mark_shapes<G: ShapeGraph + ?Sized>(
    graph: &G,
    roots: &[usize],
    root_keys: &[usize],
    shapes: &mut [bool],
    keys: &mut [bool],
) {
    for &root in roots {
        let mut at = Some(root);
        while let Some(i) = at {
            if !graph.exists(i) {
                break;
            }
            match shapes.get_mut(i) {
                Some(m) if !*m => *m = true,
                _ => break,
            }
            graph.each_key(i, &mut |k| {
                if let Some(m) = keys.get_mut(k) {
                    *m = true;
                }
            });
            at = graph.parent(i);
        }
    }
    for &k in root_keys {
        if let Some(m) = keys.get_mut(k) {
            *m = true;
        }
    }
}

/// Marking's end of a list of pending ephemerons, and of an empty head.
const NONE: usize = usize::MAX;

/// Mark the nodes reachable from `roots`: a worklist for the strong edges,
/// and a pending list per key for the ephemerons, so that every edge and
/// every ephemeron is looked at a bounded number of times (GC5's work
/// bound). [`contract::reachable`] is its specification, and the Kani
/// harnesses prove it closed over the roots and edges (so GC1) on every
/// graph of their bound.
#[must_use]
pub fn mark<G: Graph + ?Sized>(graph: &G, roots: &[usize]) -> Vec<bool> {
    mark_counted(graph, roots).0
}

/// [`mark`], and the units of work it did (GC5, [`contract::work_bound`]).
#[must_use]
pub fn mark_counted<G: Graph + ?Sized>(graph: &G, roots: &[usize]) -> (Vec<bool>, usize) {
    let n = graph.len();
    let (_, _, ephemerons) = contract::totals(graph);
    let mut marked = vec![false; n];
    // Each node is queued at most once, so a stack of `n` never overflows.
    let mut work = vec![0usize; n];
    let mut head = vec![NONE; n];
    // Each ephemeron is listed at most once: when its map is processed.
    let mut link = vec![(0usize, NONE); ephemerons];
    let units = mark_into(graph, roots, &mut marked, &mut work, &mut head, &mut link);
    (marked, units)
}

/// [`mark`] over storage the caller provides, returning the units of work:
/// - `marked`: one flag per node, all false, filled in;
/// - `work`: a stack of at least one slot per node;
/// - `head`: one entry per node, all `usize::MAX`;
/// - `link`: at least one entry per ephemeron in the graph.
///
/// The Kani harnesses call this with arrays, because CBMC does not finish
/// with vectors in the model.
///
/// An ephemeron `(k, v)` of a marked node is examined once. If `k` is marked
/// then, `v` is marked; otherwise the entry goes on `k`'s pending list
/// (`head[k]`, then `link`, newest first), and marking `k` marks every `v`
/// on it. So a key marked later still reaches its values, and no pass over
/// the ephemerons repeats.
pub fn mark_into<G: Graph + ?Sized>(
    graph: &G,
    roots: &[usize],
    marked: &mut [bool],
    work: &mut [usize],
    head: &mut [usize],
    link: &mut [(usize, usize)],
) -> usize {
    let mut top = 0usize;
    let mut used = 0usize;
    let mut units = 0usize;
    for &r in roots {
        visit(marked, work, &mut top, r);
    }
    while top > 0 {
        top = top.saturating_sub(1);
        let Some(i) = work.get(top).copied() else {
            break;
        };
        units = units.saturating_add(1);
        // `i` is marked, as a key too: fire what waited for it.
        let mut at = head.get(i).copied().unwrap_or(NONE);
        while let Some(&(v, next)) = link.get(at) {
            units = units.saturating_add(1);
            visit(marked, work, &mut top, v);
            at = next;
        }
        for &e in graph.strong(i) {
            units = units.saturating_add(1);
            visit(marked, work, &mut top, e);
        }
        for &(k, v) in graph.ephemerons(i) {
            units = units.saturating_add(1);
            if marked.get(k).copied().unwrap_or(false) {
                visit(marked, work, &mut top, v);
            } else if let (Some(h), Some(slot)) = (head.get_mut(k), link.get_mut(used)) {
                *slot = (v, *h);
                *h = used;
                used = used.saturating_add(1);
            }
        }
    }
    units
}

/// Mark `i` and queue it, if it names a node not yet marked.
fn visit(marked: &mut [bool], work: &mut [usize], top: &mut usize, i: usize) -> bool {
    match marked.get_mut(i) {
        Some(m) if !*m => {
            *m = true;
            if let Some(slot) = work.get_mut(*top) {
                *slot = i;
                *top = top.saturating_add(1);
            }
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests;
