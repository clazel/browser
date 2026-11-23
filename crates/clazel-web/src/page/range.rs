//! `Range` and `AbstractRange` (DOM §5†): the live range, as a subset.
//!
//! <https://dom.spec.whatwg.org/#ranges>
//!
//! What is here: construction (`new Range()`, `document.createRange()`), the
//! boundary points and their setters (`setStart`, `setEnd`, `setStartBefore`
//! and the others, `collapse`, `selectNode`, `selectNodeContents`),
//! `compareBoundaryPoints`, `comparePoint`, `isPointInRange`,
//! `intersectsNode`, `cloneRange`, `detach` (which does nothing, as the
//! standard says), `toString`, `deleteContents`, `extractContents`,
//! `cloneContents`, `insertNode`, `surroundContents` and
//! `createContextualFragment`. A range is live: the algorithms of
//! `mutation.rs` move its boundary points when nodes are inserted, removed or
//! have their data replaced, as DOM §4.2.3† and §4.10† say.
//!
//! Not here: `StaticRange` (the bindings do not expose it), `Selection` and
//! everything that needs layout (`getClientRects`, `getBoundingClientRect`,
//! `Range.expand`).
//!
//! Modelling choices:
//! - A boundary point is `(node, offset)` with the node's arena id; the
//!   offset counts UTF-16 code units for character data, children
//!   otherwise (DOM §4.2† "length").
//! - "Extract" and "clone the contents" recurse on the tree's depth (the
//!   standard's steps do); the recursion stops at 256 levels with a
//!   `NotSupportedError`.

use std::cmp::Ordering;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_js::{Result, Scope};
use clazel_webidl::convert::DomString;
use clazel_webidl::exception::DomErrorName;
use clazel_webidl::generated::bindings::{AbstractRangeImpl, NodeRangeImpl, RangeImpl};
use clazel_webidl::platform::ObjectKey;

use super::fragment::parse_fragment;
use super::node::{data_of_node, dom_error_of, node_of};
use super::{Object, Page, dom_error, page, points_to_units, type_error, units_to_points};

/// A live range's boundary points.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RangeState {
    pub(crate) start: (usize, usize),
    pub(crate) end: (usize, usize),
}

/// DOM §4.2† "length" of a node: "DocumentType: 0. CharacterData: its data's
/// length (code units). Otherwise: its number of children."
pub(crate) fn node_length(arena: &Arena, n: usize) -> usize {
    match arena.kind(n) {
        ExecKind::DocumentType { .. } => 0,
        ExecKind::Text { data }
        | ExecKind::Comment { data }
        | ExecKind::ProcessingInstruction { data, .. } => points_to_units(data).len(),
        _ => arena.children(n).len(),
    }
}

fn is_character_data(arena: &Arena, n: usize) -> bool {
    data_of_node(arena, n).is_some()
}

fn is_text(arena: &Arena, n: usize) -> bool {
    matches!(arena.kind(n), ExecKind::Text { .. })
}

fn is_doctype(arena: &Arena, n: usize) -> bool {
    matches!(arena.kind(n), ExecKind::DocumentType { .. })
}

fn root_of(arena: &Arena, mut n: usize) -> usize {
    while let Some(p) = arena.parent(n) {
        n = p;
    }
    n
}

fn index_of(arena: &Arena, n: usize) -> usize {
    match arena.parent(n) {
        Some(p) => arena.children(p).iter().position(|&c| c == n).unwrap_or(0),
        None => 0,
    }
}

/// The path of child indexes from the root to `n`.
fn path(arena: &Arena, n: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut cur = n;
    while let Some(p) = arena.parent(cur) {
        out.push(index_of(arena, cur));
        cur = p;
    }
    out.reverse();
    out
}

/// Tree order of two nodes of one tree: `Less` if `a` precedes `b`.
pub(crate) fn tree_cmp(arena: &Arena, a: usize, b: usize) -> Ordering {
    path(arena, a).cmp(&path(arena, b))
}

/// DOM §5.2† "position of a boundary point relative to another": "1. If
/// nodeA is nodeB, then return equal if offsetA is offsetB, before if
/// offsetA is less than offsetB, and after if offsetA is greater than
/// offsetB. 2. If nodeA is following nodeB, then: if the position of (nodeB,
/// offsetB) relative to (nodeA, offsetA) is before, return after; if it is
/// after, return before. 3. If nodeA is an ancestor of nodeB: let child be
/// nodeB; while child is not a child of nodeA, set child to its parent; if
/// child's index is less than offsetA, then return after. 4. Return
/// before." Both nodes are in one tree.
pub(crate) fn compare_points(arena: &Arena, a: (usize, usize), b: (usize, usize)) -> Ordering {
    if a.0 == b.0 {
        return a.1.cmp(&b.1);
    }
    if tree_cmp(arena, a.0, b.0) == Ordering::Greater {
        return compare_points(arena, b, a).reverse();
    }
    if arena.is_inclusive_ancestor(a.0, b.0) {
        let mut child = b.0;
        while arena.parent(child) != Some(a.0) {
            match arena.parent(child) {
                Some(p) => child = p,
                None => break,
            }
        }
        if index_of(arena, child) < a.1 {
            return Ordering::Greater;
        }
    }
    Ordering::Less
}

fn range_of(scope: &mut Scope<'_>, this: ObjectKey) -> Result<RangeState> {
    match page(scope)?.object(this) {
        Some(Object::Range(r)) => Ok(*r),
        _ => Err(type_error(scope, "not a Range")),
    }
}

fn set_range(scope: &mut Scope<'_>, this: ObjectKey, state: RangeState) -> Result<()> {
    if let Some(Object::Range(r)) = page(scope)?.object_mut(this) {
        *r = state;
    }
    Ok(())
}

fn range_root(arena: &Arena, r: &RangeState) -> usize {
    root_of(arena, r.start.0)
}

/// DOM §5.5† "contained": "A node node is contained in a live range range if
/// node's root is range's root, and (node, 0) is after range's start, and
/// (node, node's length) is before range's end."
fn contained(arena: &Arena, r: &RangeState, n: usize) -> bool {
    root_of(arena, n) == range_root(arena, r)
        && compare_points(arena, (n, 0), r.start) == Ordering::Greater
        && compare_points(arena, (n, node_length(arena, n)), r.end) == Ordering::Less
}

/// "partially contained": "A node is partially contained in a live range if
/// it's an inclusive ancestor of the live range's start node but not its end
/// node, or vice versa."
fn partially_contained(arena: &Arena, r: &RangeState, n: usize) -> bool {
    arena.is_inclusive_ancestor(n, r.start.0) != arena.is_inclusive_ancestor(n, r.end.0)
}

fn collapsed(r: &RangeState) -> bool {
    r.start == r.end
}

fn units_of(arena: &Arena, n: usize) -> Vec<u16> {
    data_of_node(arena, n)
        .map(points_to_units)
        .unwrap_or_default()
}

// ---------------------------------------------------------------------------
// The algorithms

fn too_deep(scope: &mut Scope<'_>) -> clazel_js::Error {
    dom_error(
        scope,
        DomErrorName::NotSupportedError,
        "the range's contents are nested too deeply",
    )
}

fn new_node(scope: &mut Scope<'_>, kind: ExecKind) -> Result<usize> {
    match page(scope)?.arena.create(kind) {
        Some(n) => Ok(n),
        None => Err(dom_error(
            scope,
            DomErrorName::NotSupportedError,
            "the document has too many nodes",
        )),
    }
}

/// The character data node `n` copied, with data `data` (DOM "clone a node"
/// on a character data node, then "set its data").
fn clone_char_data(scope: &mut Scope<'_>, n: usize, data: &[u16]) -> Result<usize> {
    let points = units_to_points(data);
    let kind = match page(scope)?.arena.kind(n) {
        ExecKind::Text { .. } => ExecKind::Text { data: points },
        ExecKind::Comment { .. } => ExecKind::Comment { data: points },
        ExecKind::ProcessingInstruction { target, .. } => ExecKind::ProcessingInstruction {
            target: target.clone(),
            data: points,
        },
        _ => return Err(type_error(scope, "not character data")),
    };
    new_node(scope, kind)
}

fn append_to(scope: &mut Scope<'_>, node: usize, parent: usize) -> Result<()> {
    match page(scope)?.insert_node(node, parent, None) {
        Some(e) => Err(dom_error_of(scope, e)),
        None => Ok(()),
    }
}

fn clone_node_shallow(scope: &mut Scope<'_>, n: usize) -> Result<usize> {
    match page(scope)?.arena.clone_node(n) {
        Some(c) => Ok(c),
        None => Err(dom_error(
            scope,
            DomErrorName::NotSupportedError,
            "the document has too many nodes",
        )),
    }
}

fn clone_node_deep(scope: &mut Scope<'_>, n: usize) -> Result<usize> {
    match page(scope)?.arena.clone_deep(n) {
        Some(c) => Ok(c),
        None => Err(dom_error(
            scope,
            DomErrorName::NotSupportedError,
            "the document has too many nodes",
        )),
    }
}

/// The new node and offset a range collapses to after its contents are
/// deleted or extracted (DOM §5.5† "delete the contents" step 5, "extract"
/// steps 11 and 12): "If originalStartNode is an inclusive ancestor of
/// originalEndNode, set newNode to originalStartNode and newOffset to
/// originalStartOffset. Otherwise: ... let referenceNode be
/// originalStartNode; while referenceNode's parent is non-null and is not an
/// inclusive ancestor of originalEndNode, set referenceNode to its parent.
/// Set newNode to the parent of referenceNode, and newOffset to one plus
/// the index of referenceNode."
fn collapse_target(arena: &Arena, start: (usize, usize), end: (usize, usize)) -> (usize, usize) {
    if arena.is_inclusive_ancestor(start.0, end.0) {
        return start;
    }
    let mut reference = start.0;
    while let Some(p) = arena.parent(reference) {
        if arena.is_inclusive_ancestor(p, end.0) {
            break;
        }
        reference = p;
    }
    match arena.parent(reference) {
        Some(p) => (p, index_of(arena, reference).saturating_add(1)),
        None => start,
    }
}

/// The nodes DOM §5.5† "delete the contents" step 4 removes: "the nodes that
/// are contained in range, in tree order, omitting any node whose parent is
/// also contained in range".
fn nodes_to_remove(arena: &Arena, r: &RangeState) -> Vec<usize> {
    let ca = common_ancestor(arena, r);
    let mut out = Vec::new();
    let mut stack: Vec<usize> = arena.children(ca).iter().rev().copied().collect();
    while let Some(n) = stack.pop() {
        if contained(arena, r, n) {
            out.push(n);
        } else {
            stack.extend(arena.children(n).iter().rev().copied());
        }
    }
    out
}

fn common_ancestor(arena: &Arena, r: &RangeState) -> usize {
    let mut c = r.start.0;
    while !arena.is_inclusive_ancestor(c, r.end.0) {
        match arena.parent(c) {
            Some(p) => c = p,
            None => break,
        }
    }
    c
}

fn replace_data(
    scope: &mut Scope<'_>,
    n: usize,
    offset: usize,
    count: usize,
    data: &[u16],
) -> Result<()> {
    page(scope)?.replace_data_units(n, offset, count, data);
    Ok(())
}

/// DOM §5.5† "delete the contents".
fn delete_contents(scope: &mut Scope<'_>, r: RangeState) -> Result<(usize, usize)> {
    let arena = &page(scope)?.arena;
    let (s, e) = (r.start, r.end);
    // 3. "If original start node is original end node and it is a
    // CharacterData node, then replace data with node original start node,
    // offset original start offset, count original end offset minus
    // original start offset, and data the empty string, and then return."
    if s.0 == e.0 && is_character_data(arena, s.0) {
        replace_data(scope, s.0, s.1, e.1.saturating_sub(s.1), &[])?;
        return Ok(s);
    }
    let remove = nodes_to_remove(arena, &r);
    let target = collapse_target(arena, s, e);
    let start_is_cd = is_character_data(arena, s.0);
    let end_is_cd = is_character_data(arena, e.0);
    let start_len = node_length(arena, s.0);
    if start_is_cd {
        replace_data(scope, s.0, s.1, start_len.saturating_sub(s.1), &[])?;
    }
    for n in remove {
        page(scope)?.remove_node(n);
    }
    if end_is_cd {
        replace_data(scope, e.0, 0, e.1, &[])?;
    }
    Ok(target)
}

/// DOM §5.5† "extract" (`mutate`) and "clone the contents" (`!mutate`) of
/// the range from `start` to `end`: the fragment of the copied or moved
/// contents, and the point the range collapses to.
fn contents(
    scope: &mut Scope<'_>,
    start: (usize, usize),
    end: (usize, usize),
    mutate: bool,
    depth: usize,
) -> Result<(usize, (usize, usize))> {
    if depth > 256 {
        return Err(too_deep(scope));
    }
    let r = RangeState { start, end };
    // 1. "Let fragment be a new DocumentFragment node whose node document
    // is range's start node's node document."
    let fragment = new_node(scope, ExecKind::DocumentFragment { host: None })?;
    // 2. "If range is collapsed, then return fragment."
    if collapsed(&r) {
        return Ok((fragment, start));
    }
    let arena = &page(scope)?.arena;
    // 5. "If original start node is original end node and it is a
    // CharacterData node, then: clone it, set its data to the substring
    // from original start offset to original end offset, append it to
    // fragment, [extract: replace data (...)], return fragment."
    if start.0 == end.0 && is_character_data(arena, start.0) {
        let units = units_of(arena, start.0);
        let piece = units
            .get(start.1..end.1.min(units.len()))
            .unwrap_or(&[])
            .to_vec();
        let clone = clone_char_data(scope, start.0, &piece)?;
        append_to(scope, clone, fragment)?;
        if mutate {
            replace_data(scope, start.0, start.1, end.1.saturating_sub(start.1), &[])?;
        }
        return Ok((fragment, start));
    }
    // 6. "Let common ancestor be original start node. While common ancestor
    // is not an inclusive ancestor of original end node, set common
    // ancestor to its own parent."
    let ca = common_ancestor(arena, &r);
    // 7. and 8.
    let first_partial = if arena.is_inclusive_ancestor(start.0, end.0) {
        None
    } else {
        arena
            .children(ca)
            .iter()
            .copied()
            .find(|&c| partially_contained(arena, &r, c))
    };
    let last_partial = if arena.is_inclusive_ancestor(end.0, start.0) {
        None
    } else {
        arena
            .children(ca)
            .iter()
            .rev()
            .copied()
            .find(|&c| partially_contained(arena, &r, c))
    };
    // 9. "Let contained children be a list of all children of common
    // ancestor that are contained in range, in tree order."
    let contained_children: Vec<usize> = arena
        .children(ca)
        .iter()
        .copied()
        .filter(|&c| contained(arena, &r, c))
        .collect();
    // 10. "If any member of contained children is a DocumentType node, then
    // throw a HierarchyRequestError."
    if contained_children.iter().any(|&c| is_doctype(arena, c)) {
        return Err(dom_error(
            scope,
            DomErrorName::HierarchyRequestError,
            "the range contains a doctype",
        ));
    }
    // 11. and 12.
    let target = collapse_target(arena, start, end);
    // 13. and 14.
    if let Some(f) = first_partial {
        let arena = &page(scope)?.arena;
        if is_character_data(arena, f) {
            let units = units_of(arena, start.0);
            let len = units.len();
            let piece = units.get(start.1..).unwrap_or(&[]).to_vec();
            let clone = clone_char_data(scope, start.0, &piece)?;
            append_to(scope, clone, fragment)?;
            if mutate {
                replace_data(scope, start.0, start.1, len.saturating_sub(start.1), &[])?;
            }
        } else {
            let clone = clone_node_shallow(scope, f)?;
            append_to(scope, clone, fragment)?;
            let flen = node_length(&page(scope)?.arena, f);
            let (sub, _) = contents(scope, start, (f, flen), mutate, depth.saturating_add(1))?;
            append_to(scope, sub, clone)?;
        }
    }
    // 15. "For each contained child in contained children, append
    // contained child to fragment." (Clone: a deep clone.)
    for c in contained_children {
        if mutate {
            append_to(scope, c, fragment)?;
        } else {
            let copy = clone_node_deep(scope, c)?;
            append_to(scope, copy, fragment)?;
        }
    }
    // 16. and 17.
    if let Some(l) = last_partial {
        let arena = &page(scope)?.arena;
        if is_character_data(arena, l) {
            let units = units_of(arena, end.0);
            let piece = units.get(..end.1.min(units.len())).unwrap_or(&[]).to_vec();
            let clone = clone_char_data(scope, end.0, &piece)?;
            append_to(scope, clone, fragment)?;
            if mutate {
                replace_data(scope, end.0, 0, end.1, &[])?;
            }
        } else {
            let clone = clone_node_shallow(scope, l)?;
            append_to(scope, clone, fragment)?;
            let (sub, _) = contents(scope, (l, 0), end, mutate, depth.saturating_add(1))?;
            append_to(scope, sub, clone)?;
        }
    }
    Ok((fragment, target))
}

fn check_boundary(scope: &mut Scope<'_>, node: usize, offset: u32) -> Result<(usize, usize)> {
    let arena = &page(scope)?.arena;
    if is_doctype(arena, node) {
        return Err(dom_error(
            scope,
            DomErrorName::InvalidNodeTypeError,
            "a doctype has no boundary points",
        ));
    }
    let offset = usize::try_from(offset).unwrap_or(usize::MAX);
    if offset > node_length(arena, node) {
        return Err(dom_error(
            scope,
            DomErrorName::IndexSizeError,
            "the offset is past the end of the node",
        ));
    }
    Ok((node, offset))
}

/// DOM §5.5† "set the start or end of a range to a boundary point": "1. If
/// range's root is not equal to node's root, or if bp is after the range's
/// end (start: ) ... set range's end (start) to bp. 3. Set range's start
/// (end) to bp."
fn set_start_or_end(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    bp: (usize, usize),
    is_start: bool,
) -> Result<()> {
    let mut r = range_of(scope, this)?;
    let arena = &page(scope)?.arena;
    if is_start {
        if root_of(arena, bp.0) != range_root(arena, &r)
            || compare_points(arena, bp, r.end) == Ordering::Greater
        {
            r.end = bp;
        }
        r.start = bp;
    } else {
        if root_of(arena, bp.0) != range_root(arena, &r)
            || compare_points(arena, bp, r.start) == Ordering::Less
        {
            r.start = bp;
        }
        r.end = bp;
    }
    set_range(scope, this, r)
}

fn parent_and_index(scope: &mut Scope<'_>, node: usize) -> Result<(usize, usize)> {
    let arena = &page(scope)?.arena;
    match arena.parent(node) {
        Some(p) => Ok((p, index_of(arena, node))),
        None => Err(dom_error(
            scope,
            DomErrorName::InvalidNodeTypeError,
            "the node has no parent",
        )),
    }
}

impl Page {
    /// A new live range at (the document, 0).
    pub(crate) fn new_range(&mut self) -> ObjectKey {
        self.add_object(Object::Range(RangeState {
            start: (0, 0),
            end: (0, 0),
        }))
    }
}

impl AbstractRangeImpl for Page {
    fn start_offset<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(u32::try_from(range_of(scope, this)?.start.1).unwrap_or(u32::MAX))
    }

    fn end_offset<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(u32::try_from(range_of(scope, this)?.end.1).unwrap_or(u32::MAX))
    }

    fn collapsed<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(collapsed(&range_of(scope, this)?))
    }
}

impl NodeRangeImpl for Page {
    fn start_container<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        Ok(Page::node_key(range_of(scope, this)?.start.0))
    }

    fn end_container<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        Ok(Page::node_key(range_of(scope, this)?.end.0))
    }
}

impl RangeImpl for Page {
    /// DOM §5.5† `new Range()`: "Set this's start and end to (current
    /// global object's associated Document, 0)."
    fn constructor<'s>(scope: &mut Scope<'s>) -> Result<ObjectKey> {
        Ok(page(scope)?.new_range())
    }

    /// DOM §5.5† `commonAncestorContainer`: "Let container be start node.
    /// While container is not an inclusive ancestor of end node, let
    /// container be container's parent. Return container."
    fn common_ancestor_container<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let r = range_of(scope, this)?;
        Ok(Page::node_key(common_ancestor(&page(scope)?.arena, &r)))
    }

    fn set_start<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
        offset: u32,
    ) -> Result<()> {
        let n = node_of(scope, node)?;
        let bp = check_boundary(scope, n, offset)?;
        set_start_or_end(scope, this, bp, true)
    }

    fn set_end<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
        offset: u32,
    ) -> Result<()> {
        let n = node_of(scope, node)?;
        let bp = check_boundary(scope, n, offset)?;
        set_start_or_end(scope, this, bp, false)
    }

    fn set_start_before<'s>(scope: &mut Scope<'s>, this: ObjectKey, node: ObjectKey) -> Result<()> {
        let n = node_of(scope, node)?;
        let (p, i) = parent_and_index(scope, n)?;
        set_start_or_end(scope, this, (p, i), true)
    }

    fn set_start_after<'s>(scope: &mut Scope<'s>, this: ObjectKey, node: ObjectKey) -> Result<()> {
        let n = node_of(scope, node)?;
        let (p, i) = parent_and_index(scope, n)?;
        set_start_or_end(scope, this, (p, i.saturating_add(1)), true)
    }

    fn set_end_before<'s>(scope: &mut Scope<'s>, this: ObjectKey, node: ObjectKey) -> Result<()> {
        let n = node_of(scope, node)?;
        let (p, i) = parent_and_index(scope, n)?;
        set_start_or_end(scope, this, (p, i), false)
    }

    fn set_end_after<'s>(scope: &mut Scope<'s>, this: ObjectKey, node: ObjectKey) -> Result<()> {
        let n = node_of(scope, node)?;
        let (p, i) = parent_and_index(scope, n)?;
        set_start_or_end(scope, this, (p, i.saturating_add(1)), false)
    }

    /// DOM §5.5† `collapse(toStart)`.
    fn collapse<'s>(scope: &mut Scope<'s>, this: ObjectKey, to_start: bool) -> Result<()> {
        let mut r = range_of(scope, this)?;
        if to_start {
            r.end = r.start;
        } else {
            r.start = r.end;
        }
        set_range(scope, this, r)
    }

    /// DOM §5.5† `selectNode(node)`: "1. Let parent be node's parent. 2. If
    /// parent is null, then throw an InvalidNodeTypeError. 3. Let index be
    /// node's index. 4. Set range's start to boundary point (parent, index).
    /// 5. Set range's end to boundary point (parent, index plus 1)."
    fn select_node<'s>(scope: &mut Scope<'s>, this: ObjectKey, node: ObjectKey) -> Result<()> {
        let n = node_of(scope, node)?;
        let (p, i) = parent_and_index(scope, n)?;
        set_range(
            scope,
            this,
            RangeState {
                start: (p, i),
                end: (p, i.saturating_add(1)),
            },
        )
    }

    /// DOM §5.5† `selectNodeContents(node)`.
    fn select_node_contents<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
    ) -> Result<()> {
        let n = node_of(scope, node)?;
        let arena = &page(scope)?.arena;
        if is_doctype(arena, n) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidNodeTypeError,
                "a doctype has no contents",
            ));
        }
        let len = node_length(arena, n);
        set_range(
            scope,
            this,
            RangeState {
                start: (n, 0),
                end: (n, len),
            },
        )
    }

    /// DOM §5.5† `compareBoundaryPoints(how, sourceRange)`: "1. If how is
    /// not one of START_TO_START, START_TO_END, END_TO_END, END_TO_START,
    /// then throw a NotSupportedError. 2. If this's root is not the same as
    /// sourceRange's root, then throw a WrongDocumentError. 3. ... 4.
    /// If this point is before other point, return −1; equal, 0; after, 1."
    fn compare_boundary_points<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        how: u16,
        source_range: ObjectKey,
    ) -> Result<i16> {
        if how > 3 {
            return Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "not a comparison",
            ));
        }
        let a = range_of(scope, this)?;
        let b = range_of(scope, source_range)?;
        let arena = &page(scope)?.arena;
        if range_root(arena, &a) != range_root(arena, &b) {
            return Err(dom_error(
                scope,
                DomErrorName::WrongDocumentError,
                "the ranges are in different trees",
            ));
        }
        let (this_point, other_point) = match how {
            0 => (a.start, b.start),
            1 => (a.end, b.start),
            2 => (a.end, b.end),
            _ => (a.start, b.end),
        };
        Ok(match compare_points(arena, this_point, other_point) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        })
    }

    /// DOM §5.5† `deleteContents()`: "Delete the contents ... Set range's
    /// start and end to (new node, new offset)."
    fn delete_contents<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        let r = range_of(scope, this)?;
        if collapsed(&r) {
            return Ok(());
        }
        let target = delete_contents(scope, r)?;
        set_range(
            scope,
            this,
            RangeState {
                start: target,
                end: target,
            },
        )
    }

    fn extract_contents<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let r = range_of(scope, this)?;
        let (fragment, target) = contents(scope, r.start, r.end, true, 0)?;
        set_range(
            scope,
            this,
            RangeState {
                start: target,
                end: target,
            },
        )?;
        Ok(Page::node_key(fragment))
    }

    fn clone_contents<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let r = range_of(scope, this)?;
        let (fragment, _) = contents(scope, r.start, r.end, false, 0)?;
        Ok(Page::node_key(fragment))
    }

    /// DOM §5.5† `insertNode(node)`.
    fn insert_node<'s>(scope: &mut Scope<'s>, this: ObjectKey, node: ObjectKey) -> Result<()> {
        let n = node_of(scope, node)?;
        let r = range_of(scope, this)?;
        let arena = &page(scope)?.arena;
        let start_node = r.start.0;
        let hierarchy = |scope: &mut Scope<'_>| {
            dom_error(
                scope,
                DomErrorName::HierarchyRequestError,
                "the node cannot be inserted here",
            )
        };
        // 1. "If range's start node is a ProcessingInstruction or Comment
        // node, is a Text node whose parent is null, or is node, then throw
        // a HierarchyRequestError."
        let kind_bad = matches!(
            arena.kind(start_node),
            ExecKind::ProcessingInstruction { .. } | ExecKind::Comment { .. }
        ) || (is_text(arena, start_node) && arena.parent(start_node).is_none())
            || start_node == n;
        if kind_bad {
            return Err(hierarchy(scope));
        }
        // 2. to 4.
        let mut reference: Option<usize> = if is_text(arena, start_node) {
            Some(start_node)
        } else {
            arena.children(start_node).get(r.start.1).copied()
        };
        // 5. "Let parent be range's start node if referenceNode is null, and
        // referenceNode's parent otherwise."
        let parent = match reference {
            None => start_node,
            Some(rn) => arena.parent(rn).unwrap_or(start_node),
        };
        // 6. "Ensure pre-insertion validity of node into parent before
        // referenceNode."
        if let Some(e) = arena.ensure_pre_insertion_validity(n, parent, reference) {
            return Err(dom_error_of(scope, e));
        }
        // 7. "If range's start node is a Text node, set referenceNode to the
        // result of splitting it with offset range's start offset."
        if is_text(&page(scope)?.arena, start_node) {
            reference = Some(super::node::split_text(scope, start_node, r.start.1)?);
        }
        // 8. "If node is referenceNode, then set referenceNode to its next
        // sibling."
        if reference == Some(n) {
            reference = page(scope)?.arena.next_sibling(n);
        }
        // 9. "If node's parent is non-null, then remove node."
        if page(scope)?.arena.parent(n).is_some() {
            page(scope)?.remove_node(n);
        }
        // 10. and 11.
        let arena = &page(scope)?.arena;
        let mut new_offset = match reference {
            Some(rn) => index_of(arena, rn),
            None => node_length(arena, parent),
        };
        new_offset = new_offset.saturating_add(
            if matches!(arena.kind(n), ExecKind::DocumentFragment { .. }) {
                node_length(arena, n)
            } else {
                1
            },
        );
        // 12. "Pre-insert node into parent before referenceNode."
        if let Some(e) = page(scope)?.insert_node(n, parent, reference) {
            return Err(dom_error_of(scope, e));
        }
        // 13. "If range is collapsed, then set range's end to (parent,
        // newOffset)."
        let mut now = range_of(scope, this)?;
        if collapsed(&r) {
            now.end = (parent, new_offset);
            set_range(scope, this, now)?;
        }
        Ok(())
    }

    /// DOM §5.5† `surroundContents(newParent)`.
    fn surround_contents<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        new_parent: ObjectKey,
    ) -> Result<()> {
        let np = node_of(scope, new_parent)?;
        let r = range_of(scope, this)?;
        let arena = &page(scope)?.arena;
        // 1. "If a non-Text node is partially contained in this, then throw
        // an InvalidStateError."
        // A node is partially contained if it is an inclusive ancestor of
        // one boundary node and not of the other.
        let partial = [r.start.0, r.end.0].iter().any(|&boundary| {
            let mut cur = Some(boundary);
            while let Some(n) = cur {
                if partially_contained(arena, &r, n) && !is_text(arena, n) {
                    return true;
                }
                cur = arena.parent(n);
            }
            false
        });
        if partial {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidStateError,
                "a node is partially selected",
            ));
        }
        // 2. "If newParent is a Document, DocumentType, or DocumentFragment
        // node, then throw an InvalidNodeTypeError."
        if matches!(
            arena.kind(np),
            ExecKind::Document { .. }
                | ExecKind::DocumentType { .. }
                | ExecKind::DocumentFragment { .. }
        ) {
            return Err(dom_error(
                scope,
                DomErrorName::InvalidNodeTypeError,
                "newParent cannot be a document, doctype or fragment",
            ));
        }
        // 3. "Let fragment be the result of extracting this."
        let (fragment, target) = contents(scope, r.start, r.end, true, 0)?;
        set_range(
            scope,
            this,
            RangeState {
                start: target,
                end: target,
            },
        )?;
        // 4. "If newParent has children, then replace all with null within
        // newParent."
        if !page(scope)?.arena.children(np).is_empty() {
            page(scope)?.replace_all_with(None, np);
        }
        // 5. "Insert newParent into this."
        <Page as RangeImpl>::insert_node(scope, this, new_parent)?;
        // 6. "Append fragment to newParent."
        append_to(scope, fragment, np)?;
        // 7. "Select newParent within this."
        <Page as RangeImpl>::select_node(scope, this, new_parent)
    }

    fn clone_range<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        let r = range_of(scope, this)?;
        Ok(page(scope)?.add_object(Object::Range(r)))
    }

    /// DOM §5.5† `detach()`: "The detach() method steps are to do nothing."
    fn detach<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        range_of(scope, this)?;
        Ok(())
    }

    fn is_point_in_range<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
        offset: u32,
    ) -> Result<bool> {
        let n = node_of(scope, node)?;
        let r = range_of(scope, this)?;
        let arena = &page(scope)?.arena;
        // 1. "If node's root is different from this's root, return false."
        if root_of(arena, n) != range_root(arena, &r) {
            return Ok(false);
        }
        let bp = check_boundary(scope, n, offset)?;
        let arena = &page(scope)?.arena;
        // 4. "If (node, offset) is before start or after end, return false."
        Ok(compare_points(arena, bp, r.start) != Ordering::Less
            && compare_points(arena, bp, r.end) != Ordering::Greater)
    }

    fn compare_point<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
        offset: u32,
    ) -> Result<i16> {
        let n = node_of(scope, node)?;
        let r = range_of(scope, this)?;
        let arena = &page(scope)?.arena;
        // 1. "If node's root is different from this's root, then throw a
        // WrongDocumentError."
        if root_of(arena, n) != range_root(arena, &r) {
            return Err(dom_error(
                scope,
                DomErrorName::WrongDocumentError,
                "the node is in another tree",
            ));
        }
        let bp = check_boundary(scope, n, offset)?;
        let arena = &page(scope)?.arena;
        Ok(if compare_points(arena, bp, r.start) == Ordering::Less {
            -1
        } else if compare_points(arena, bp, r.end) == Ordering::Greater {
            1
        } else {
            0
        })
    }

    /// DOM §5.5† `intersectsNode(node)`: "1. If node's root is different
    /// from this's root, return false. 2. Let parent be node's parent. 3. If
    /// parent is null, return true. 4. Let offset be node's index. 5. If
    /// (parent, offset) is before end and (parent, offset plus 1) is after
    /// start, return true. 6. Return false."
    fn intersects_node<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        node: ObjectKey,
    ) -> Result<bool> {
        let n = node_of(scope, node)?;
        let r = range_of(scope, this)?;
        let arena = &page(scope)?.arena;
        if root_of(arena, n) != range_root(arena, &r) {
            return Ok(false);
        }
        let Some(parent) = arena.parent(n) else {
            return Ok(true);
        };
        let offset = index_of(arena, n);
        Ok(
            compare_points(arena, (parent, offset), r.end) == Ordering::Less
                && compare_points(arena, (parent, offset.saturating_add(1)), r.start)
                    == Ordering::Greater,
        )
    }

    /// DOM Parsing §? `createContextualFragment(string)`: "1. Let node be
    /// this's start node. 2. Let element be null. 3. If node implements
    /// Element, set element to node. 4. Otherwise, if node implements Text
    /// or Comment, set element to node's parent element. 5. If element is
    /// null or all of: element's node document is an HTML document, element's
    /// local name is "html", and element's namespace is the HTML namespace,
    /// then set element to the result of creating an element given this's
    /// node document, "body", and the HTML namespace. 6. Let fragment node be
    /// the result of invoking the fragment parsing algorithm steps with
    /// element and compliantString."
    fn create_contextual_fragment<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        string: DomString,
    ) -> Result<ObjectKey> {
        let r = range_of(scope, this)?;
        let node = r.start.0;
        let arena = &page(scope)?.arena;
        let element = match arena.kind(node) {
            ExecKind::Element { .. } => Some(node),
            ExecKind::Text { .. } | ExecKind::Comment { .. } => arena
                .parent(node)
                .filter(|&p| matches!(arena.kind(p), ExecKind::Element { .. })),
            _ => None,
        };
        let context = match element {
            Some(e) if !super::node::is_html_named(arena, e, "html") => e,
            _ => super::node::new_body_element(scope)?,
        };
        let html = units_to_points(&string);
        match parse_fragment(&mut page(scope)?.arena, context, &html) {
            Some(f) => Ok(Page::node_key(f)),
            None => Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "the document has too many nodes",
            )),
        }
    }

    /// DOM §5.5† `toString()`: "1. Let s be the empty string. 2. If this's
    /// start node is this's end node and it is a Text node, then return the
    /// substring of that Text node's data beginning at this's start offset
    /// and ending at this's end offset. 3. If this's start node is a Text
    /// node, then append the substring of that node's data from this's start
    /// offset until the end to s. 4. Append the concatenation of the data of
    /// all Text nodes that are contained in this, in tree order, to s. 5. If
    /// this's end node is a Text node, then append the substring of that
    /// node's data from its start until this's end offset to s. 6. Return s."
    fn stringify<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        let r = range_of(scope, this)?;
        let arena = &page(scope)?.arena;
        let units = |n: usize| units_of(arena, n);
        if r.start.0 == r.end.0 && is_text(arena, r.start.0) {
            let u = units(r.start.0);
            return Ok(u
                .get(r.start.1..r.end.1.min(u.len()))
                .unwrap_or(&[])
                .to_vec());
        }
        let mut s: Vec<u16> = Vec::new();
        if is_text(arena, r.start.0) {
            let u = units(r.start.0);
            s.extend_from_slice(u.get(r.start.1..).unwrap_or(&[]));
        }
        let ca = common_ancestor(arena, &r);
        let mut stack: Vec<usize> = arena.children(ca).iter().rev().copied().collect();
        while let Some(n) = stack.pop() {
            if is_text(arena, n) && contained(arena, &r, n) {
                s.extend(units(n));
            }
            stack.extend(arena.children(n).iter().rev().copied());
        }
        if is_text(arena, r.end.0) {
            let u = units(r.end.0);
            s.extend_from_slice(u.get(..r.end.1.min(u.len())).unwrap_or(&[]));
        }
        Ok(s)
    }
}
