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
//!    generation (GC2; the arena's invariant 3).
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
//! # What is not here
//!
//! Strings in the property-key interner and shapes live outside the arena
//! and are not collected in this slice; neither holds a reference into it.

pub mod contract;

use crate::arena::{self, Arena, Ref};
use crate::elements::Elements;
use crate::value::Value;
use contract::{Graph, Node};

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
}

impl From<arena::Error> for Error {
    fn from(e: arena::Error) -> Self {
        Self::Arena(e)
    }
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
        }
    }

    /// Store an object. Never collects: a full heap is reported, and the
    /// embedder collects at its next safe point.
    ///
    /// # Errors
    /// [`arena::Error::Full`] as [`Error::Arena`].
    pub fn alloc(&mut self, object: Object) -> Result<Ref, Error> {
        Ok(self.arena.alloc(object)?)
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
    /// the value stack, DOM wrappers, task queues and pending cleanups.
    ///
    /// # Errors
    /// [`Error::InOperation`] during an operation (GC7); nothing changes.
    /// [`Error::Arena`] if the arena reports corruption while freeing
    /// (unreachable by construction).
    pub fn collect(&mut self, roots: &[Value]) -> Result<Collection, Error> {
        if self.op_depth != 0 {
            return Err(Error::InOperation);
        }
        let graph = self.graph();
        let marked = mark(&graph, &self.root_indices(roots));
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
        for &r in &live {
            if liveness.survives(r) {
                out.survivors = out.survivors.saturating_add(1);
                if let Ok(o) = self.arena.get_mut(r) {
                    clear_weak(o, &liveness, &mut out.cleanups);
                }
            } else {
                self.arena.free(r)?;
                out.freed = out.freed.saturating_add(1);
            }
        }
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

/// Mark the nodes reachable from `roots`: a worklist for the strong edges,
/// and passes over the ephemerons until none marks anything new.
/// [`contract::reachable`] is its specification, and the Kani harnesses
/// prove it closed over the roots and edges (so GC1) on every graph of
/// their bound.
#[must_use]
pub fn mark<G: Graph + ?Sized>(graph: &G, roots: &[usize]) -> Vec<bool> {
    let mut marked = vec![false; graph.len()];
    // Each node is queued at most once, so a stack of `len` never overflows.
    let mut work = vec![0usize; graph.len()];
    mark_into(graph, roots, &mut marked, &mut work);
    marked
}

/// [`mark`] over storage the caller provides: `marked` (one flag per node,
/// all false) is filled in, and `work` (a stack of at least one slot per
/// node) is scratch. The Kani harnesses call this with arrays, because
/// CBMC does not finish with vectors in the model.
pub fn mark_into<G: Graph + ?Sized>(
    graph: &G,
    roots: &[usize],
    marked: &mut [bool],
    work: &mut [usize],
) {
    let mut top = 0usize;
    for &r in roots {
        visit(marked, work, &mut top, r);
    }
    loop {
        while top > 0 {
            top = top.saturating_sub(1);
            let Some(i) = work.get(top).copied() else {
                break;
            };
            for &e in graph.strong(i) {
                visit(marked, work, &mut top, e);
            }
        }
        let mut progressed = false;
        for i in 0..graph.len() {
            if !marked.get(i).copied().unwrap_or(false) {
                continue;
            }
            for &(k, v) in graph.ephemerons(i) {
                if marked.get(k).copied().unwrap_or(false) {
                    progressed |= visit(marked, work, &mut top, v);
                }
            }
        }
        if !progressed {
            return;
        }
    }
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
