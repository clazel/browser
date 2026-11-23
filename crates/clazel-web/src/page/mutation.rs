//! The page's tree mutations, and what observes them: DOM §4.3† mutation
//! observers (`MutationObserver`, `MutationRecord`) and the live ranges'
//! boundary updates (§5.5†, in the "insert", "remove" and "replace data"
//! algorithms).
//!
//! This is the one place the page changes its arena (phase-7.md item 7.13:
//! "the insertion steps and removing steps hooks ... added here, once, for
//! mutation observers and live collections"): every script-visible change
//! goes through a method of [`Page`] below, which runs `clazel-dom`'s proven
//! operation and also does what the standard's algorithm adds around it:
//! queue the mutation records, add the transient registered observers, and
//! move the live ranges' boundaries. `clazel-dom` itself has no observers
//! (its `insertion_steps` and `removing_steps` change nothing), and the live
//! collections of `node.rs` are recomputed on each read, so they need no
//! hook.
//!
//! Modelling choices:
//! - **The records are computed from the state before the operation**, which
//!   the proven operation then performs as a whole. The one place this
//!   differs from the standard's step order is "replace" (§4.2.3†), whose
//!   standard text removes the child, then adopts the new node (which may
//!   remove it from elsewhere), then inserts it: the live ranges of those
//!   three steps are applied in that order, to the indexes the standard
//!   gives, except that a `node` that is a later sibling of `child` in the
//!   same parent has its index lowered by one for the second step.
//! - **No microtask:** "queue a mutation observer microtask" appends the
//!   observer to [`Observers::notify`]; the host calls
//!   [`notify_mutation_observers`] at its microtask checkpoint (the page's
//!   event loop is not joined to the engine yet, item 7.15).
//! - **One document:** "adopt" never changes the node document, so only its
//!   removal from the old parent remains.

use std::collections::HashMap;

use clazel_dom::exec::{Arena, ExecAttr};
use clazel_dom::spec::DomError;
use clazel_js::{Handle, Result, Runtime, Scope};
use clazel_webidl::convert::DomString;
use clazel_webidl::generated::bindings::{
    MutationObserverImpl, MutationObserverInit, MutationRecordImpl,
};
use clazel_webidl::platform::ObjectKey;

use super::node::node_of;
use super::{
    Collection, HookCall, LogLevel, Object, Page, page, points_to_units, type_error,
    units_to_points,
};

/// What an observer registered for: the options of `observe()` after its
/// normalizing steps (DOM §4.3.2†).
#[derive(Clone, Debug, Default)]
pub(crate) struct Options {
    pub(crate) child_list: bool,
    pub(crate) attributes: bool,
    pub(crate) character_data: bool,
    pub(crate) subtree: bool,
    pub(crate) attribute_old_value: bool,
    pub(crate) character_data_old_value: bool,
    pub(crate) attribute_filter: Option<Vec<Vec<u32>>>,
}

/// A "registered observer" of a node, or a "transient registered observer"
/// (`source` is the registration it came from).
#[derive(Clone, Debug)]
pub(crate) struct Registration {
    pub(crate) node: usize,
    pub(crate) observer: u64,
    pub(crate) options: Options,
    pub(crate) source: Option<(usize, u64)>,
}

/// A `MutationRecord`'s data.
#[derive(Clone, Debug)]
pub(crate) struct Record {
    pub(crate) kind: &'static str,
    pub(crate) target: usize,
    pub(crate) added: Vec<usize>,
    pub(crate) removed: Vec<usize>,
    pub(crate) previous: Option<usize>,
    pub(crate) next: Option<usize>,
    pub(crate) attribute_name: Option<Vec<u32>>,
    pub(crate) attribute_namespace: Option<Vec<u32>>,
    pub(crate) old_value: Option<Vec<u32>>,
}

impl Record {
    fn child_list(
        target: usize,
        added: Vec<usize>,
        removed: Vec<usize>,
        previous: Option<usize>,
        next: Option<usize>,
    ) -> Record {
        Record {
            kind: "childList",
            target,
            added,
            removed,
            previous,
            next,
            attribute_name: None,
            attribute_namespace: None,
            old_value: None,
        }
    }
}

/// One `MutationObserver`.
#[derive(Debug)]
pub(crate) struct Observer {
    pub(crate) callback: Handle,
    pub(crate) key: ObjectKey,
    /// "record queue".
    pub(crate) queue: Vec<Record>,
}

/// Every observer, registration and pending notification of the page.
#[derive(Debug, Default)]
pub(crate) struct Observers {
    pub(crate) map: HashMap<u64, Observer>,
    pub(crate) regs: Vec<Registration>,
    /// "pending mutation observers": the observers with records to deliver.
    pub(crate) notify: Vec<u64>,
    pub(crate) next: u64,
}

fn index_of(arena: &Arena, parent: usize, child: usize) -> usize {
    arena
        .children(parent)
        .iter()
        .position(|&c| c == child)
        .unwrap_or(0)
}

fn is_fragment(arena: &Arena, n: usize) -> bool {
    matches!(
        arena.kind(n),
        clazel_dom::exec::ExecKind::DocumentFragment { .. }
    )
}

impl Page {
    /// Whether some observer has records to deliver: the host's cue to run
    /// [`notify_mutation_observers`] at its next microtask checkpoint.
    #[must_use]
    pub fn has_pending_mutation_observers(&self) -> bool {
        !self.mo.notify.is_empty()
    }

    // ---- DOM §4.3.1† "queue a mutation record" ---------------------------

    /// DOM §4.3.1† "queue a mutation record": "3. For each node in nodes
    /// (the target's inclusive ancestors), and then for each registered of
    /// node's registered observer list: ... interestedObservers ... 4. For
    /// each observer → mappedOldValue of interestedObservers: Let record be
    /// a new MutationRecord ... Enqueue record to observer's record queue.
    /// 5. Queue a mutation observer microtask."
    pub(crate) fn queue_mutation_record(&mut self, rec: Record) {
        if self.mo.regs.is_empty() {
            return;
        }
        let mut interested: Vec<(u64, Option<Vec<u32>>)> = Vec::new();
        let mut node = Some(rec.target);
        while let Some(n) = node {
            for reg in self.mo.regs.iter().filter(|r| r.node == n) {
                let o = &reg.options;
                if n != rec.target && !o.subtree {
                    continue;
                }
                let old_wanted = match rec.kind {
                    "attributes" => {
                        if !o.attributes {
                            continue;
                        }
                        if let Some(filter) = &o.attribute_filter {
                            let name = rec.attribute_name.as_deref().unwrap_or(&[]);
                            if rec.attribute_namespace.is_some()
                                || !filter.iter().any(|f| f.as_slice() == name)
                            {
                                continue;
                            }
                        }
                        o.attribute_old_value
                    }
                    "characterData" => {
                        if !o.character_data {
                            continue;
                        }
                        o.character_data_old_value
                    }
                    _ => {
                        if !o.child_list {
                            continue;
                        }
                        false
                    }
                };
                let old = if old_wanted {
                    rec.old_value.clone()
                } else {
                    None
                };
                match interested.iter_mut().find(|(id, _)| *id == reg.observer) {
                    Some(slot) => {
                        if old_wanted {
                            slot.1 = old;
                        }
                    }
                    None => interested.push((reg.observer, old)),
                }
            }
            node = self.arena.parent(n);
        }
        for (id, old) in interested {
            let mut r = rec.clone();
            r.old_value = old;
            if let Some(o) = self.mo.map.get_mut(&id) {
                o.queue.push(r);
            }
            if !self.mo.notify.contains(&id) {
                self.mo.notify.push(id);
            }
        }
    }

    // ---- live ranges (DOM §5.5†) ------------------------------------------

    /// Applies `f` to every live range's two boundary points.
    fn each_range(&mut self, mut f: impl FnMut(&Arena, &mut (usize, usize))) {
        let arena = &self.arena;
        for o in self.objects.values_mut() {
            if let Object::Range(r) = o {
                f(arena, &mut r.start);
                f(arena, &mut r.end);
            }
        }
    }

    /// The live range steps of DOM §4.2.3† "remove", steps 4 to 8, before
    /// `node` (child `index` of `parent`) is removed.
    fn ranges_before_remove(&mut self, node: usize, parent: usize, index: usize) {
        self.each_range(|arena, b| {
            if arena.is_inclusive_ancestor(node, b.0) {
                *b = (parent, index);
            } else if b.0 == parent && b.1 > index {
                b.1 = b.1.saturating_sub(1);
            }
        });
    }

    /// The live range steps of "insert" step 6, for `count` nodes inserted
    /// into `parent` before its child at `index`: "For each live range whose
    /// start node is parent and start offset is greater than index, increase
    /// its start offset by count" (and the same for end).
    fn ranges_after_insert(&mut self, parent: usize, index: usize, count: usize) {
        self.each_range(|_, b| {
            if b.0 == parent && b.1 > index {
                b.1 = b.1.saturating_add(count);
            }
        });
    }

    /// Moves the boundary points of `node`'s data, for DOM §4.10† "replace
    /// data" steps 8 to 11 (`offset`, `count` and the new data's length in
    /// code units).
    pub(crate) fn ranges_replace_data(
        &mut self,
        node: usize,
        offset: usize,
        count: usize,
        length: usize,
    ) {
        self.each_range(|_, b| {
            if b.0 != node {
                return;
            }
            if b.1 > offset && b.1 <= offset.saturating_add(count) {
                b.1 = offset;
            } else if b.1 > offset.saturating_add(count) {
                b.1 = b.1.saturating_add(length).saturating_sub(count);
            }
        });
    }

    /// The boundary points that `splitText` moves (DOM §4.11† "split",
    /// steps 7.2 to 7.5): those at `node` beyond `offset` go to `new`, and
    /// those at `parent` just after `node` move one on.
    pub(crate) fn ranges_split_text(
        &mut self,
        node: usize,
        new: usize,
        offset: usize,
        parent: Option<usize>,
        index: usize,
    ) {
        self.each_range(|_, b| {
            if b.0 == node && b.1 > offset {
                *b = (new, b.1.saturating_sub(offset));
            } else if Some(b.0) == parent && b.1 == index.saturating_add(1) {
                b.1 = b.1.saturating_add(1);
            }
        });
    }

    /// Every live range's boundary points, as a list of mutable references
    /// to be updated by `f`: for the algorithms (`normalize`) that move them
    /// by their own rules.
    pub(crate) fn update_range_points(&mut self, f: impl FnMut(&Arena, &mut (usize, usize))) {
        self.each_range(f);
    }

    // ---- DOM §4.2.3† "remove" -----------------------------------------------

    /// DOM §4.2.3† "remove" `node` from its parent, with the suppress
    /// observers flag `suppress`: the live range steps, the transient
    /// registered observers ("For each inclusive ancestor inclusiveAncestor
    /// of parent, and then for each registered of inclusiveAncestor's
    /// registered observer list, if registered's options["subtree"] is true,
    /// then append a new transient registered observer ... to node's
    /// registered observer list"), the record ("If suppress observers flag
    /// is unset, queue a tree mutation record for parent with « », « node »,
    /// oldPreviousSibling, and oldNextSibling"), then the proven remove.
    pub(crate) fn remove_node_flagged(&mut self, node: usize, suppress: bool) {
        let Some(parent) = self.arena.parent(node) else {
            return;
        };
        let index = index_of(&self.arena, parent, node);
        let previous = self.arena.previous_sibling(node);
        let next = self.arena.next_sibling(node);
        self.ranges_before_remove(node, parent, index);
        self.add_transient_observers(node, parent);
        if !suppress {
            self.queue_mutation_record(Record::child_list(
                parent,
                Vec::new(),
                vec![node],
                previous,
                next,
            ));
        }
        self.arena.remove(node);
    }

    /// "remove" with the suppress observers flag unset.
    pub(crate) fn remove_node(&mut self, node: usize) {
        self.remove_node_flagged(node, false);
    }

    fn add_transient_observers(&mut self, node: usize, parent: usize) {
        if self.mo.regs.is_empty() {
            return;
        }
        let mut add = Vec::new();
        let mut cur = Some(parent);
        while let Some(a) = cur {
            for reg in self.mo.regs.iter().filter(|r| r.node == a) {
                if reg.options.subtree {
                    add.push(Registration {
                        node,
                        observer: reg.observer,
                        options: reg.options.clone(),
                        source: Some((a, reg.observer)),
                    });
                }
            }
            cur = self.arena.parent(a);
        }
        self.mo.regs.extend(add);
    }

    // ---- DOM §4.2.3† "pre-insert", "insert" -----------------------------

    /// DOM §4.2.3† "pre-insert" `node` into `parent` before `child`:
    /// "1. Ensure pre-insertion validity ... 2. Let referenceChild be child.
    /// 3. If referenceChild is node, then set referenceChild to node's next
    /// sibling. 4. Insert node into parent before referenceChild." and
    /// "insert" with the live range and record steps (step 6, "For each
    /// live range ... increase", and step 8, "queue a tree mutation record
    /// for parent with nodes, « », previousSibling, and child").
    pub(crate) fn insert_node(
        &mut self,
        node: usize,
        parent: usize,
        child: Option<usize>,
    ) -> Option<DomError> {
        if let Some(e) = self
            .arena
            .ensure_pre_insertion_validity(node, parent, child)
        {
            return Some(e);
        }
        let mut reference = child;
        if reference == Some(node) {
            reference = self.arena.next_sibling(node);
        }
        // "Adopt node into parent's node document": remove it from its
        // parent (a fragment has none).
        if self.arena.parent(node).is_some() {
            self.remove_node(node);
        }
        let added: Vec<usize> = if is_fragment(&self.arena, node) {
            let kids = self.arena.children(node).to_vec();
            for &k in &kids {
                self.remove_node_flagged(k, true);
            }
            kids
        } else {
            vec![node]
        };
        // The fragment's children are gone now, so the proven operation
        // inserts the (empty) fragment: put the nodes in one by one,
        // before the same reference child, in order.
        let previous = match reference {
            Some(r) => self.arena.previous_sibling(r),
            None => self.arena.last_child(parent),
        };
        if let Some(r) = reference {
            let idx = index_of(&self.arena, parent, r);
            self.ranges_after_insert(parent, idx, added.len());
        }
        let result = if is_fragment(&self.arena, node) {
            let mut err = None;
            for &a in &added {
                // Each was valid inside the fragment (step 5 and 6 of the
                // validity check looked at all of them together).
                if let Some(e) = self.arena.pre_insert(a, parent, reference) {
                    err = Some(e);
                    break;
                }
            }
            err
        } else {
            self.arena.pre_insert(node, parent, reference)
        };
        if result.is_none() {
            self.queue_mutation_record(Record::child_list(
                parent,
                added,
                Vec::new(),
                previous,
                reference,
            ));
        }
        result
    }

    /// DOM §4.2.3† "replace" `child` with `node` within `parent`: the proven
    /// operation, with the standard's removal and insertion with the
    /// suppress observers flag set and the one record of step 16, "Queue a
    /// tree mutation record for parent with nodes, removedNodes,
    /// previousSibling, and referenceChild".
    pub(crate) fn replace_node(
        &mut self,
        child: usize,
        node: usize,
        parent: usize,
    ) -> Option<DomError> {
        // The state the standard's steps 9 to 14 read.
        let mut reference = self.arena.next_sibling(child);
        if reference == Some(node) {
            reference = self.arena.next_sibling(node);
        }
        let mut previous = self.arena.previous_sibling(child);
        if previous == Some(node) {
            previous = self.arena.previous_sibling(node);
        }
        let child_in_parent = self.arena.parent(child) == Some(parent);
        let child_index = if child_in_parent {
            index_of(&self.arena, parent, child)
        } else {
            0
        };
        let node_old_parent = self.arena.parent(node);
        let node_index = node_old_parent.map(|p| index_of(&self.arena, p, node));
        let added: Vec<usize> = if is_fragment(&self.arena, node) {
            self.arena.children(node).to_vec()
        } else {
            vec![node]
        };
        let (node_previous, node_next) = (
            self.arena.previous_sibling(node),
            self.arena.next_sibling(node),
        );
        if let Some(e) = self.arena.replace(child, node, parent) {
            return Some(e);
        }
        if child_in_parent {
            // Steps 13.2: remove child (suppressed).
            self.ranges_before_remove_state(child, parent, child_index);
            self.add_transient_observers(child, parent);
        }
        // Step 15's adopt: node leaves its old parent (a record there).
        if let (Some(op), Some(ni)) = (node_old_parent, node_index) {
            let mut ni = ni;
            if op == parent && ni > child_index && child_in_parent {
                ni = ni.saturating_sub(1);
            }
            self.ranges_before_remove_state(node, op, ni);
            self.add_transient_observers(node, op);
            self.queue_mutation_record(Record::child_list(
                op,
                Vec::new(),
                vec![node],
                node_previous,
                node_next,
            ));
        }
        if let Some(r) = reference {
            let idx = index_of(&self.arena, parent, r).saturating_sub(added.len());
            self.ranges_after_insert(parent, idx, added.len());
        }
        self.queue_mutation_record(Record::child_list(
            parent,
            added,
            if child_in_parent {
                vec![child]
            } else {
                Vec::new()
            },
            previous,
            reference,
        ));
        None
    }

    /// The boundary points of `ranges_before_remove`, for a node that is
    /// already out of the tree: "inclusive descendant of node" is decided by
    /// the node's own subtree, which the removal keeps intact.
    fn ranges_before_remove_state(&mut self, node: usize, parent: usize, index: usize) {
        self.each_range(|arena, b| {
            if arena.is_inclusive_ancestor(node, b.0) {
                *b = (parent, index);
            } else if b.0 == parent && b.1 > index {
                b.1 = b.1.saturating_sub(1);
            }
        });
    }

    /// DOM §4.2.3† "replace all" with `node` (or nothing) within `parent`:
    /// "1. If node is non-null, then adopt node ... 2. Let removedNodes be
    /// parent's children. 3. Let addedNodes be the empty set. 4. If node is
    /// a DocumentFragment node, then set addedNodes to node's children.
    /// Otherwise, if node is non-null, set addedNodes to « node ». 5. Remove
    /// all parent's children, in tree order, with the suppress observers
    /// flag set. 6. If node is non-null, then insert node into parent
    /// before null with the suppress observers flag set. 7. If either
    /// addedNodes or removedNodes is not empty, then queue a tree mutation
    /// record for parent with addedNodes, removedNodes, null, and null."
    pub(crate) fn replace_all_with(&mut self, node: Option<usize>, parent: usize) {
        if let Some(n) = node
            && self.arena.parent(n).is_some()
        {
            self.remove_node(n);
        }
        let removed = self.arena.children(parent).to_vec();
        let added: Vec<usize> = match node {
            Some(n) if is_fragment(&self.arena, n) => self.arena.children(n).to_vec(),
            Some(n) => vec![n],
            None => Vec::new(),
        };
        for &c in &removed {
            let index = index_of(&self.arena, parent, c);
            self.ranges_before_remove(c, parent, index);
            self.add_transient_observers(c, parent);
        }
        if let Some(n) = node
            && is_fragment(&self.arena, n)
        {
            for &k in &added {
                self.ranges_before_remove(k, n, 0);
            }
        }
        self.arena.replace_all(node, parent);
        if !added.is_empty() || !removed.is_empty() {
            self.queue_mutation_record(Record::child_list(parent, added, removed, None, None));
        }
    }

    // ---- DOM §4.10† "replace data" ----------------------------------------

    /// DOM §4.10† "replace data" on a Text, Comment or PI `node` with
    /// `offset`, `count` and `data` (code units; `offset` and `count` are
    /// already checked): "4. Queue a mutation record of "characterData" for
    /// node with null, null, node's data, « », « », null, and null." Then
    /// the new data, and steps 8 to 11's live ranges.
    pub(crate) fn replace_data_units(
        &mut self,
        node: usize,
        offset: usize,
        count: usize,
        data: &[u16],
    ) {
        let Some(old) = super::node::data_of_node(&self.arena, node) else {
            return;
        };
        let old = old.to_vec();
        let mut units = points_to_units(&old);
        let end = offset.saturating_add(count).min(units.len());
        let offset = offset.min(units.len());
        units.splice(offset..end, data.iter().copied());
        self.queue_mutation_record(Record {
            kind: "characterData",
            target: node,
            added: Vec::new(),
            removed: Vec::new(),
            previous: None,
            next: None,
            attribute_name: None,
            attribute_namespace: None,
            old_value: Some(old),
        });
        self.arena.set_data(node, units_to_points(&units));
        self.ranges_replace_data(node, offset, end.saturating_sub(offset), data.len());
    }

    /// "replace data" of the whole of `node`'s data (the setters).
    pub(crate) fn set_node_data(&mut self, node: usize, data: &[u32]) {
        let units = points_to_units(data);
        let len =
            super::node::data_of_node(&self.arena, node).map_or(0, |d| points_to_units(d).len());
        self.replace_data_units(node, 0, len, &units);
    }

    // ---- DOM §4.9† attribute changes ---------------------------------------

    fn attribute_record(
        &mut self,
        e: usize,
        local: Vec<u32>,
        namespace: Option<Vec<u32>>,
        old: Option<Vec<u32>>,
    ) {
        self.queue_mutation_record(Record {
            kind: "attributes",
            target: e,
            added: Vec::new(),
            removed: Vec::new(),
            previous: None,
            next: None,
            attribute_name: Some(local),
            attribute_namespace: namespace,
            old_value: old,
        });
    }

    /// DOM §4.9† "change an attribute": "1. Handle attribute changes for
    /// attribute with attribute's element, attribute's value, and value
    /// (queue an "attributes" record with the old value). 2. Set attribute's
    /// value to value."
    pub(crate) fn attr_change(&mut self, e: usize, i: usize, value: Vec<u32>) {
        let (local, ns, old) = {
            let a = super::node::attributes_of_element(&self.arena, e);
            match a.get(i) {
                Some(a) => (
                    a.local_name.clone(),
                    a.namespace.as_ref().map(super::node::namespace_uri_points),
                    a.value.clone(),
                ),
                None => return,
            }
        };
        self.attribute_record(e, local, ns, Some(old));
        self.arena.change_attribute(e, i, value);
    }

    /// DOM §4.9† "append an attribute".
    pub(crate) fn attr_append(&mut self, e: usize, attr: ExecAttr) {
        let local = attr.local_name.clone();
        let ns = attr
            .namespace
            .as_ref()
            .map(super::node::namespace_uri_points);
        self.attribute_record(e, local, ns, None);
        self.arena.append_attribute(e, attr);
    }

    /// DOM §4.9† "remove an attribute": the Attr object, if script made one
    /// for it, keeps its value and has no owner element.
    pub(crate) fn attr_remove(&mut self, e: usize, i: usize) {
        let (local, ns, old) = {
            let a = super::node::attributes_of_element(&self.arena, e);
            match a.get(i) {
                Some(a) => (
                    a.local_name.clone(),
                    a.namespace.as_ref().map(super::node::namespace_uri_points),
                    a.value.clone(),
                ),
                None => return,
            }
        };
        self.detach_attr_object(e, i);
        self.attribute_record(e, local, ns, Some(old));
        self.arena.remove_attribute(e, i);
    }

    /// DOM §4.9† "replace an attribute".
    pub(crate) fn attr_replace(&mut self, e: usize, i: usize, new: ExecAttr) {
        let (local, ns, old) = {
            let a = super::node::attributes_of_element(&self.arena, e);
            match a.get(i) {
                Some(a) => (
                    a.local_name.clone(),
                    a.namespace.as_ref().map(super::node::namespace_uri_points),
                    a.value.clone(),
                ),
                None => return,
            }
        };
        self.detach_attr_object(e, i);
        self.attribute_record(e, local, ns, Some(old));
        self.arena.replace_attribute(e, i, new);
    }
}

// ---------------------------------------------------------------------------
// MutationObserver and MutationRecord (DOM §4.3†)

fn observer_id(scope: &mut Scope<'_>, this: ObjectKey) -> Result<u64> {
    match page(scope)?.object(this) {
        Some(Object::MutationObserver(id)) => Ok(*id),
        _ => Err(type_error(scope, "not a MutationObserver")),
    }
}

fn record_of<'a>(scope: &'a mut Scope<'_>, this: ObjectKey) -> Result<&'a Record> {
    if !matches!(page(scope)?.object(this), Some(Object::MutationRecord(_))) {
        return Err(type_error(scope, "not a MutationRecord"));
    }
    match page(scope)?.object(this) {
        Some(Object::MutationRecord(r)) => Ok(r),
        _ => Err(clazel_js::Error::WrongType("a MutationRecord")),
    }
}

impl MutationObserverImpl for Page {
    /// DOM §4.3.1† `new MutationObserver(callback)`: "set this's callback to
    /// callback and append this to the surrounding agent's mutation
    /// observers" (the observer table).
    fn constructor<'s>(scope: &mut Scope<'s>, callback: clazel_js::Local<'s>) -> Result<ObjectKey> {
        let handle = scope.persist(callback);
        let p = page(scope)?;
        let id = p.mo.next;
        p.mo.next = p.mo.next.saturating_add(1);
        let key = p.add_object(Object::MutationObserver(id));
        p.mo.map.insert(
            id,
            Observer {
                callback: handle,
                key,
                queue: Vec::new(),
            },
        );
        Ok(key)
    }

    /// DOM §4.3.2† `observe(target, options)`.
    fn observe<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        target: ObjectKey,
        options: MutationObserverInit,
    ) -> Result<()> {
        let id = observer_id(scope, this)?;
        let t = node_of(scope, target)?;
        // 1. "If either options["attributeOldValue"] or
        // options["attributeFilter"] exists, and options["attributes"] does
        // not exist, then set options["attributes"] to true."
        let mut attributes = options.attributes;
        if (options.attribute_old_value.is_some() || options.attribute_filter.is_some())
            && attributes.is_none()
        {
            attributes = Some(true);
        }
        // 2. "If options["characterDataOldValue"] exists and
        // options["characterData"] does not exist, set characterData true."
        let mut character_data = options.character_data;
        if options.character_data_old_value.is_some() && character_data.is_none() {
            character_data = Some(true);
        }
        // 3. "If none of options["childList"], options["attributes"], and
        // options["characterData"] is true, then throw a TypeError."
        if !options.child_list && attributes != Some(true) && character_data != Some(true) {
            return Err(type_error(
                scope,
                "the options must set childList, attributes or characterData",
            ));
        }
        // 4. to 6.
        if options.attribute_old_value == Some(true) && attributes == Some(false) {
            return Err(type_error(
                scope,
                "attributeOldValue needs attributes to be true",
            ));
        }
        if options.attribute_filter.is_some() && attributes == Some(false) {
            return Err(type_error(
                scope,
                "attributeFilter needs attributes to be true",
            ));
        }
        if options.character_data_old_value == Some(true) && character_data == Some(false) {
            return Err(type_error(
                scope,
                "characterDataOldValue needs characterData to be true",
            ));
        }
        let o = Options {
            child_list: options.child_list,
            attributes: attributes == Some(true),
            character_data: character_data == Some(true),
            subtree: options.subtree,
            attribute_old_value: options.attribute_old_value == Some(true),
            character_data_old_value: options.character_data_old_value == Some(true),
            attribute_filter: options
                .attribute_filter
                .map(|f| f.iter().map(|s| units_to_points(s)).collect()),
        };
        // 7. "For each registered of target's registered observer list, if
        // registered's observer is this: 1. For each node of this's node
        // list, remove all transient registered observers whose source is
        // registered. 2. Set registered's options to options." "Otherwise,
        // append a new registered observer to target's list."
        let regs = &mut page(scope)?.mo.regs;
        let existing = regs
            .iter()
            .position(|r| r.node == t && r.observer == id && r.source.is_none());
        match existing {
            Some(i) => {
                regs.retain(|r| r.source != Some((t, id)));
                if let Some(r) = regs
                    .iter_mut()
                    .find(|r| r.node == t && r.observer == id && r.source.is_none())
                {
                    r.options = o;
                }
                let _ = i;
            }
            None => regs.push(Registration {
                node: t,
                observer: id,
                options: o,
                source: None,
            }),
        }
        Ok(())
    }

    /// DOM §4.3.2† `disconnect()`: "1. For each node of this's node list,
    /// remove any registered observer from node's registered observer list
    /// for which this is the observer. 2. Empty this's record queue."
    fn disconnect<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        let id = observer_id(scope, this)?;
        let p = page(scope)?;
        p.mo.regs.retain(|r| r.observer != id);
        if let Some(o) = p.mo.map.get_mut(&id) {
            o.queue.clear();
        }
        p.mo.notify.retain(|&n| n != id);
        Ok(())
    }

    /// DOM §4.3.2† `takeRecords()`: "1. Let records be a clone of this's
    /// record queue. 2. Empty this's record queue. 3. Return records."
    fn take_records<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Vec<ObjectKey>> {
        let id = observer_id(scope, this)?;
        let p = page(scope)?;
        let records = match p.mo.map.get_mut(&id) {
            Some(o) => core::mem::take(&mut o.queue),
            None => Vec::new(),
        };
        p.mo.notify.retain(|&n| n != id);
        Ok(records
            .into_iter()
            .map(|r| p.add_object(Object::MutationRecord(Box::new(r))))
            .collect())
    }
}

impl MutationRecordImpl for Page {
    fn type_<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        Ok(record_of(scope, this)?.kind.encode_utf16().collect())
    }

    fn target<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let t = record_of(scope, this)?.target;
        Ok(Page::node_key(t))
    }

    fn added_nodes<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let added = record_of(scope, this)?.added.clone();
        Ok(page(scope)?.add_object(Object::NodeList(Collection::Static(added))))
    }

    fn removed_nodes<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let removed = record_of(scope, this)?.removed.clone();
        Ok(page(scope)?.add_object(Object::NodeList(Collection::Static(removed))))
    }

    fn previous_sibling<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(record_of(scope, this)?.previous.map(Page::node_key))
    }

    fn next_sibling<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(record_of(scope, this)?.next.map(Page::node_key))
    }

    fn attribute_name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        Ok(record_of(scope, this)?
            .attribute_name
            .as_deref()
            .map(points_to_units))
    }

    fn attribute_namespace<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
    ) -> Result<Option<DomString>> {
        Ok(record_of(scope, this)?
            .attribute_namespace
            .as_deref()
            .map(points_to_units))
    }

    fn old_value<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        Ok(record_of(scope, this)?
            .old_value
            .as_deref()
            .map(points_to_units))
    }
}

/// DOM §4.3.1† "notify mutation observers": "1. Set the surrounding agent's
/// mutation observer microtask queued to false. 2. Let notifySet be a clone
/// of the surrounding agent's mutation observers. 3. Let signalSet be a
/// clone of ... signal slots. 4. Empty ... 5. For each mo of notifySet: 1.
/// Let records be a clone of mo's record queue. 2. Empty mo's record queue.
/// 3. For each node of mo's node list, remove all transient registered
/// observers whose observer is mo from node's registered observer list. 4.
/// If records is not empty, then invoke mo's callback with « records, mo »,
/// and mo. If this throws an exception, then report the exception."
///
/// The host calls this at its microtask checkpoint, and again until it
/// returns false (an observer's callback may make more records).
///
/// # Errors
/// What the engine returns other than an exception thrown by a callback,
/// which is reported to the host's log.
pub fn notify_mutation_observers(rt: &mut Runtime) -> Result<bool> {
    rt.scope(|scope| {
        let mut any = false;
        loop {
            let ids = core::mem::take(&mut page(scope)?.mo.notify);
            if ids.is_empty() {
                return Ok(any);
            }
            for id in ids {
                let (callback, key, records) = {
                    let p = page(scope)?;
                    p.mo.regs
                        .retain(|r| !(r.observer == id && r.source.is_some()));
                    let Some(o) = p.mo.map.get_mut(&id) else {
                        continue;
                    };
                    (o.callback.clone(), o.key, core::mem::take(&mut o.queue))
                };
                if records.is_empty() {
                    continue;
                }
                any = true;
                let result = (|| -> Result<()> {
                    let mut locals = Vec::new();
                    for r in records {
                        let k = page(scope)?.add_object(Object::MutationRecord(Box::new(r)));
                        locals.push(clazel_webidl::platform::wrap::<Page>(scope, k)?);
                    }
                    let array = scope.new_array_from(&locals)?;
                    let this = clazel_webidl::platform::wrap::<Page>(scope, key)?;
                    let f = scope.local(&callback)?;
                    scope.call(f, this, &[array, this])?;
                    Ok(())
                })();
                if let Err(clazel_js::Error::Thrown(e)) = &result {
                    let report = scope.report(e)?;
                    let text = format!("Uncaught {}: {}", report.name, report.message);
                    page(scope)?.record(HookCall::Log(LogLevel::Error, text));
                } else {
                    result?;
                }
            }
        }
    })
}
