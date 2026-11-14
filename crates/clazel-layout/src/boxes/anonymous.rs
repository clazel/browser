//! Anonymous block boxes (CSS 2.1 §9.2.1.1), anonymous inline boxes and
//! text runs (§9.2.2.1, with CSS Text 3 §4.1.1 Phase I) (phase-5.md item
//! 5.13).
//!
//! Source: CSS 2.1 (W3C Recommendation, 7 June 2011), §9.2.1.1 "Anonymous
//! block boxes" and §9.2.2.1 "Anonymous inline boxes",
//! <https://www.w3.org/TR/2011/REC-CSS2-20110607/visuren.html#anonymous-block-level>;
//! CSS Text 3 (CRD of 14 August 2026) §4.1.1 and §4.1.2 through item
//! 5.12's [`crate::text`].
//!
//! §9.2.1.1 has two rules. "If a block container box … has a block-level
//! box inside it …, then we force it to have only block-level boxes inside
//! it": each maximal run of inline-level children goes into an anonymous
//! block box. "When an inline box contains an in-flow block-level box, the
//! inline box (and its inline ancestors within the same line box) are
//! broken around the block-level box (and any block-level siblings that are
//! consecutive or separated only by collapsible whitespace and/or
//! out-of-flow elements), splitting the inline box into two boxes (even if
//! either side is empty), one on each side of the block-level box(es). The
//! line boxes before the break and after the break are enclosed in
//! anonymous block boxes, and the block-level box becomes a sibling of
//! those anonymous boxes." [`split_blocks`] does both in one scan per block
//! container ([`split_step`], `state.rs`).
//!
//! Modelling choices:
//!
//! - **A split inline box becomes fragments**: new inline boxes with its
//!   node, each marked as its first, last or a middle fragment
//!   ([`Fragment`]), one per anonymous block it has content in; the box
//!   itself leaves the tree. "Even if either side is empty": the first
//!   fragment is made when the inline box's first content is a block-level
//!   box, and the last when its last content is one.
//! - **Consecutive block-level boxes** inside an inline box get no fragment
//!   between them. Block-level boxes "separated only by collapsible
//!   whitespace" get one, holding the white space, which Phase I then
//!   removes: an anonymous block with nothing left at all is removed, but
//!   one that still holds an empty fragment is kept (it has an empty line,
//!   which CSS 2.1 §9.4.2 makes zero-height), so a split inline's middle
//!   fragments are never lost. There are no out-of-flow elements.
//! - **A marker box** stays its list item's first child, outside every
//!   anonymous box and inline formatting context (it is placed as
//!   `list-style-position: outside` places it, by layout).
//! - **Phase I per inline formatting context**: for each block container
//!   whose children are inline-level, its content in order (the text runs
//!   under it, through inline boxes, and its atomic inlines, whose
//!   breaking is governed by the style of their parent element) goes
//!   through `text::collapse::collapse` once, so collapsing runs across
//!   inline boundaries as §4.1.1 says. Each run keeps its own units.
//! - **"White space content that would subsequently be collapsed away …
//!   does not generate any anonymous inline boxes"** (§9.2.2.1): a text run
//!   with no unit left after Phase I is removed; so are the runs of an
//!   inline formatting context whose units are all collapsible spaces,
//!   since Phase II (CSS Text 3 §4.1.2 step 1) removes "a sequence of
//!   collapsible spaces at the beginning of a line", and they are all on
//!   its first line. Other leading and trailing collapsible spaces stay for
//!   layout's Phase II, which depends on where lines break.

use clazel_dom::exec::Arena;

use super::StyleFns;
use super::generate::text_style;
use super::state::{SplitAction, SplitEvent, SplitState};
use super::tree::{BoxId, BoxKind, BoxTree, Class, Fragment};
use crate::text::collapse::{Item, Kind, collapse};
use crate::text::{TextStyle, Unit};

/// One step of §9.2.1.1's scan (see [`SplitState`]): what the driver does
/// for `event`, and the state after it. Contract: from a state satisfying
/// [`SplitState::invariant`], the next state satisfies it; inline content
/// is placed only with every fragment of the path open (so it lands inside
/// the innermost inline box, as in the document); a block-level box is
/// placed only with no anonymous block or fragment left open, after every
/// inline box on the path has had a fragment (its "before" side, possibly
/// empty); and an exit leaves the exited box's last fragment made.
pub fn split_step(s: SplitState, event: SplitEvent) -> (SplitAction, SplitState) {
    let none = SplitAction {
        open_anonymous: false,
        open_from: s.depth,
        place_inline: false,
        exit: false,
        place_block: false,
    };
    // Open the anonymous block if needed and a fragment of each inline box
    // on the path that has none open.
    let ensure = SplitAction {
        open_anonymous: !s.anonymous,
        open_from: s.open,
        ..none
    };
    match event {
        SplitEvent::Enter => (
            none,
            SplitState {
                depth: s.depth.saturating_add(1),
                ..s
            },
        ),
        SplitEvent::Inline => (
            SplitAction {
                place_inline: true,
                ..ensure
            },
            SplitState {
                depth: s.depth,
                open: s.depth,
                parted: s.depth,
                anonymous: true,
            },
        ),
        SplitEvent::Block => {
            // "Even if either side is empty": an inline box on the path with
            // no fragment yet gets an empty first one before the block.
            let action = if s.parted < s.depth { ensure } else { none };
            (
                SplitAction {
                    place_block: true,
                    ..action
                },
                SplitState {
                    depth: s.depth,
                    open: 0,
                    parted: s.depth,
                    anonymous: false,
                },
            )
        }
        // The driver sends `Exit` only with a non-empty path.
        SplitEvent::Exit if s.depth == 0 => (none, s),
        SplitEvent::Exit => {
            // The innermost box's last fragment, empty if its last content
            // was a block-level box.
            let action = if s.open < s.depth { ensure } else { none };
            let depth = s.depth.saturating_sub(1);
            (
                SplitAction {
                    exit: true,
                    ..action
                },
                SplitState {
                    depth,
                    open: depth,
                    parted: depth,
                    anonymous: true,
                },
            )
        }
    }
}

/// For each box, whether it is an inline box holding a block-level box
/// (through inline boxes only). Children come after their parent in
/// preorder, so the reverse order sees them first.
fn holds_blocks(tree: &BoxTree) -> Vec<bool> {
    let mut holds = vec![false; tree.boxes.len()];
    for b in tree.preorder().into_iter().rev() {
        if tree.class(b) != Class::Inline {
            continue;
        }
        let any = tree.children(b).iter().any(|&c| {
            let k = tree.class(c);
            k.is_block_level() || (k == Class::Inline && holds.get(c).copied().unwrap_or(false))
        });
        if let Some(h) = holds.get_mut(b) {
            *h = any;
        }
    }
    holds
}

/// A path entry of the scan: an inline box being split, and its open
/// fragment.
struct Entry {
    original: BoxId,
    fragment: Option<BoxId>,
}

/// What §9.2.1.1's scan over one container builds.
struct Scan {
    /// The container's new children.
    out: Vec<BoxId>,
    /// (parent, child) appends, applied after `out` replaces the children,
    /// in order: each parent's children are then in document order.
    moves: Vec<(BoxId, BoxId)>,
    /// The inline boxes being split, outermost first.
    path: Vec<Entry>,
    /// The open anonymous block.
    anonymous: Option<BoxId>,
}

impl Scan {
    /// Applies one [`SplitAction`], taken in state `s`, for box `child`.
    fn apply(
        &mut self,
        tree: &mut BoxTree,
        s: &SplitState,
        action: SplitAction,
        child: Option<BoxId>,
    ) {
        if action.open_anonymous {
            let a = tree.add(BoxKind::Block, None);
            self.out.push(a);
            self.anonymous = Some(a);
        }
        for i in action.open_from..s.depth {
            let parent = match i.checked_sub(1).and_then(|j| self.path.get(j)) {
                Some(e) => e.fragment,
                None => self.anonymous,
            };
            let Some(entry) = self.path.get_mut(i) else {
                break;
            };
            let node = tree.get(entry.original).and_then(|b| b.node);
            let f = tree.add(
                BoxKind::Inline(Fragment {
                    first: i >= s.parted,
                    last: false,
                }),
                node,
            );
            entry.fragment = Some(f);
            if let Some(p) = parent {
                self.moves.push((p, f));
            }
        }
        let innermost = self.path.last().and_then(|e| e.fragment).or(self.anonymous);
        if action.place_inline
            && let (Some(c), Some(target)) = (child, innermost)
        {
            self.moves.push((target, c));
        }
        if action.exit
            && let Some(f) = self.path.pop().and_then(|e| e.fragment)
            && let Some(BoxKind::Inline(fragment)) = tree.boxes.get_mut(f).map(|b| &mut b.kind)
        {
            fragment.last = true;
        }
        if action.place_block {
            self.anonymous = None;
            for e in &mut self.path {
                e.fragment = None;
            }
            if let Some(c) = child {
                self.out.push(c);
            }
        }
    }
}

/// §9.2.1.1 on block container `container`, whose inline boxes `holds`
/// says hold block-level boxes: its new children are its marker (if any),
/// anonymous blocks and block-level boxes.
fn split(tree: &mut BoxTree, container: BoxId, holds: &[bool]) {
    let mut scan = Scan {
        out: Vec::new(),
        moves: Vec::new(),
        path: Vec::new(),
        anonymous: None,
    };
    let mut state = SplitState::START;
    let mut cursors: Vec<(Vec<BoxId>, usize)> = vec![(tree.children(container).to_vec(), 0)];
    // Every box under the container is read once and every inline box on
    // the path exited once, so this bound is never reached.
    let bound = tree.boxes.len().saturating_mul(2).saturating_add(2);
    for _ in 0..bound {
        let Some((list, i)) = cursors.last_mut() else {
            break;
        };
        let next = list.get(*i).copied();
        *i = i.saturating_add(1);
        let (event, child) = match next {
            None => {
                cursors.pop();
                if cursors.is_empty() {
                    break;
                }
                (SplitEvent::Exit, None)
            }
            Some(c) => {
                let k = tree.class(c);
                if k == Class::Marker {
                    scan.out.push(c);
                    continue;
                } else if k.is_block_level() {
                    (SplitEvent::Block, Some(c))
                } else if k == Class::Inline && holds.get(c).copied().unwrap_or(false) {
                    cursors.push((tree.children(c).to_vec(), 0));
                    scan.path.push(Entry {
                        original: c,
                        fragment: None,
                    });
                    (SplitEvent::Enter, Some(c))
                } else {
                    (SplitEvent::Inline, Some(c))
                }
            }
        };
        let (action, after) = split_step(state, event);
        scan.apply(tree, &state, action, child);
        state = after;
    }
    tree.set_children(container, scan.out);
    for (p, c) in scan.moves {
        tree.append(p, c);
    }
}

/// §9.2.1.1 on every block container that has a block-level box among its
/// children or inside its inline boxes.
pub fn split_blocks(tree: &mut BoxTree) {
    let holds = holds_blocks(tree);
    for b in tree.preorder() {
        if !tree.class(b).is_block_container() {
            continue;
        }
        let mixed = tree.children(b).iter().any(|&c| {
            let k = tree.class(c);
            k.is_block_level() || (k == Class::Inline && holds.get(c).copied().unwrap_or(false))
        });
        if mixed {
            split(tree, b, &holds);
        }
    }
}

/// One item of an inline formatting context, as gathered.
enum Gathered {
    /// A text run (its box).
    Text(BoxId),
    /// An atomic inline, with the style that governs breaking around it.
    Atomic(TextStyle),
}

/// The content of the inline formatting context of block container `b`, in
/// order: its text runs and atomic inlines, through its inline boxes.
fn gather(tree: &BoxTree, arena: &Arena, styles: &impl StyleFns, b: BoxId) -> Vec<Gathered> {
    let mut out = Vec::new();
    let mut stack: Vec<BoxId> = tree.children(b).iter().rev().copied().collect();
    // Each box under `b` is pushed once.
    for _ in 0..tree.boxes.len().saturating_add(1) {
        let Some(c) = stack.pop() else { break };
        let k = tree.class(c);
        if matches!(k, Class::Text { .. }) {
            out.push(Gathered::Text(c));
        } else if k.is_atomic_inline() {
            let node = tree.get(c).and_then(|x| x.node);
            let parent = node.and_then(|n| arena.parent(n));
            out.push(Gathered::Atomic(text_style(
                parent.and_then(|p| styles.style(p)),
            )));
        } else if k == Class::Inline {
            stack.extend(tree.children(c).iter().rev());
        }
    }
    out
}

/// Removes the boxes `removed` marks from their parents' children, each
/// parent's list filtered once.
fn unlink_all(tree: &mut BoxTree, removed: &[bool]) {
    let mut parents: Vec<BoxId> = removed
        .iter()
        .enumerate()
        .filter(|&(_, &r)| r)
        .filter_map(|(c, _)| tree.get(c).and_then(|b| b.parent))
        .collect();
    parents.sort_unstable();
    parents.dedup();
    for p in parents {
        let rest: Vec<BoxId> = tree
            .children(p)
            .iter()
            .copied()
            .filter(|&c| !removed.get(c).copied().unwrap_or(false))
            .collect();
        tree.set_children(p, rest);
    }
}

/// Phase I (CSS Text 3 §4.1.1) over the inline formatting context of block
/// container `b`, and §9.2.2.1's removal of what it collapses away.
fn collapse_context(
    tree: &mut BoxTree,
    arena: &Arena,
    styles: &impl StyleFns,
    b: BoxId,
    removed: &mut [bool],
) {
    let gathered = gather(tree, arena, styles, b);
    let units: Vec<Unit> = {
        let items: Vec<Item<'_>> = gathered
            .iter()
            .map(|g| match g {
                Gathered::Text(id) => match tree.get(*id).map(|x| &x.kind) {
                    Some(BoxKind::Text(run)) => Item::Text {
                        text: &run.text,
                        style: run.style,
                    },
                    _ => Item::Text {
                        text: "",
                        style: TextStyle::INITIAL,
                    },
                },
                Gathered::Atomic(style) => Item::Atomic { style: *style },
            })
            .collect();
        collapse(&items)
    };
    let mut per_item: Vec<Vec<Unit>> = vec![Vec::new(); gathered.len()];
    for u in &units {
        if let Some(list) = per_item.get_mut(u.item) {
            list.push(*u);
        }
    }
    let all_collapsible = units.iter().all(|u| u.kind == Kind::CollapsibleSpace);
    for (g, list) in gathered.iter().zip(per_item) {
        let Gathered::Text(id) = g else { continue };
        let empty = list.is_empty() || all_collapsible;
        if let Some(BoxKind::Text(run)) = tree.boxes.get_mut(*id).map(|x| &mut x.kind) {
            run.units = list;
        }
        if empty && let Some(r) = removed.get_mut(*id) {
            *r = true;
        }
    }
}

/// Phase I on every inline formatting context (every block container whose
/// children are not block-level), then the removal of anonymous blocks left
/// with no children.
pub fn text_runs(tree: &mut BoxTree, arena: &Arena, styles: &impl StyleFns) {
    let order = tree.preorder();
    let mut removed = vec![false; tree.boxes.len()];
    for &b in &order {
        let k = tree.class(b);
        let inline_content = !tree
            .children(b)
            .iter()
            .any(|&c| tree.class(c).is_block_level());
        if k.is_block_container() && inline_content {
            collapse_context(tree, arena, styles, b, &mut removed);
        }
    }
    unlink_all(tree, &removed);
    let mut removed = vec![false; tree.boxes.len()];
    for b in order {
        let anonymous_block = tree
            .get(b)
            .is_some_and(|x| x.kind == BoxKind::Block && x.node.is_none());
        if anonymous_block
            && tree.children(b).is_empty()
            && let Some(r) = removed.get_mut(b)
        {
            *r = true;
        }
    }
    unlink_all(tree, &removed);
}
