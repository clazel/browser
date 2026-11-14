//! The states of `boxes/`'s passes, their invariants, and the contracts of
//! the steps over them.
//!
//! Every pass over the tree is a loop whose body is one step: a function of
//! a small state and the next thing the loop reads (a DOM node, or one child
//! of the box whose children are being regrouped), returning a decision and
//! the next state. The drivers (`generate::generate`, `table::stage_1` to
//! `table::stage_3`, `anonymous::split_blocks`) only read the tree, call
//! the step, and apply its decision to the arena. A Kani harness over **any
//! state satisfying the invariant** and any next input then covers trees of
//! every size and depth: the start state satisfies the invariant, and each
//! step preserves it, so no step on any tree can panic or break the
//! properties the harness asserts.
//!
//! The steps are, with their sources:
//!
//! - **Box generation** (`generate::decide` and `generate::walk_step`), CSS
//!   2.1 §9.2 and §9.7, CSS Display 3 §2.5† (`none` and `contents`), §12.5
//!   (list items), HTML §15.3.4 (`br`, `wbr`), §15.4 and §15.5 (replaced
//!   elements): `decide(node: NodeInfo) -> Decision` says what a node
//!   generates; `walk_step(frame: Frame, decision: Decision, next_box:
//!   BoxId) -> Walk` says, for the frame popped from the walk's stack, which
//!   boxes are added and under which box the node's children are walked.
//!   The stack's frames each satisfy [`Frame::invariant`].
//! - **§17.2.1 stage 1, "Remove irrelevant boxes"** (`table::irrelevant`):
//!   `irrelevant(parent: Class, child: Class, before: Option<Class>, after:
//!   Option<Class>) -> bool`: whether `child` is "treated as if it had
//!   'display: none'". It needs no state.
//! - **§17.2.1 stages 2 and 3** (`table::wrapper_2`, `table::wrapper_3_1`,
//!   `table::wrapper_3_2` with [`group_step`]): a scan over one box's
//!   children that puts each maximal run of consecutive children that a
//!   rule wraps into one anonymous box. The state is whether a wrapper is
//!   open ([`Group`]).
//! - **§9.2.1.1, anonymous block boxes and split inlines**
//!   (`anonymous::split_step`): a scan over a block container's content
//!   that descends into the inline boxes holding block-level boxes. The
//!   state ([`SplitState`]) summarises the path of inline boxes being
//!   split: its depth, how many of them have a fragment open in the
//!   current anonymous block, how many have had a fragment at all, and
//!   whether an anonymous block is open.
//!
//! CSS Text 3 Phase I is item 5.12's `text::collapse::step`, proved there.

use super::tree::BoxId;

/// A frame of the generation walk's stack: DOM node `node` is still to be
/// walked, and its boxes go under box `parent`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Frame {
    /// The DOM node.
    pub node: usize,
    /// The box its boxes are appended to.
    pub parent: BoxId,
}

impl Frame {
    /// The invariant of every frame on the stack, given the arena's node
    /// count and the number of boxes made so far: the node is in the arena
    /// and the parent box exists.
    pub fn invariant(&self, nodes: usize, boxes: usize) -> bool {
        self.node < nodes && self.parent < boxes
    }
}

/// What a box-generating element's principal box is (§9.2, §17.2), before
/// the anonymous boxes of §9.2.1.1 and §17.2.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Principal {
    /// A block box (`block`, or `list-item` with `marker`).
    Block {
        /// `list-item`: a marker box is added as its first child.
        marker: bool,
    },
    /// `inline-block`.
    InlineBlock,
    /// `inline`.
    Inline,
    /// `table` or `inline-table`.
    Table {
        /// `inline-table`.
        inline: bool,
    },
    /// A row group.
    RowGroup(super::tree::RowGroup),
    /// `table-row`.
    Row,
    /// `table-cell`.
    Cell,
    /// `table-column-group`.
    ColumnGroup,
    /// `table-column`.
    Column,
    /// `table-caption`.
    Caption,
    /// A replaced element (`replaced.rs`): its children are not walked.
    Replaced {
        /// Inline-level.
        inline: bool,
    },
    /// A `br` or `wbr` element: one text run, no children walked (HTML
    /// §15.3.4).
    Break,
}

/// What a DOM node generates (`generate::decide`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Decision {
    /// No box, and its children are not walked: `display: none`, a node that
    /// is neither an element nor text, or an element with no computed style.
    Nothing,
    /// No box, and its children are walked under the same parent (`display:
    /// contents`, and the document).
    Contents,
    /// A text run.
    Text,
    /// A principal box (and, for some, additional boxes).
    Element(Principal),
}

/// What `generate::walk_step` does with a popped frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Walk {
    /// The number of boxes added (ids `next_box ..`): the principal box,
    /// then a list item's marker or a `br`'s text run.
    pub added: usize,
    /// The box the node's children are walked under, if they are.
    pub children_under: Option<BoxId>,
}

/// The state of the scan that groups a box's children for one of §17.2.1's
/// rules: whether an anonymous wrapper is open, so that the next child the
/// rule wraps goes into it ("around C and all consecutive siblings of C
/// that …").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Group {
    /// A wrapper is open: the previous child went into it.
    pub open: bool,
}

/// What the grouping scan does with one child.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Place {
    /// The child stays where it is (any open wrapper is closed).
    Keep,
    /// A new anonymous wrapper is made in the child's place, and the child
    /// goes into it.
    Open,
    /// The child goes into the open wrapper.
    Join,
}

impl Group {
    /// No wrapper open: before the first child.
    pub const START: Group = Group { open: false };
}

/// One step of the grouping scan: where a child goes, given whether the
/// rule wraps it (`wrapped`), and the state after it. Contract: a child the
/// rule wraps is never kept, one it does not wrap always is, and a wrapper
/// is opened only when none is open.
pub fn group_step(state: Group, wrapped: bool) -> (Place, Group) {
    match (wrapped, state.open) {
        (false, _) => (Place::Keep, Group { open: false }),
        (true, false) => (Place::Open, Group { open: true }),
        (true, true) => (Place::Join, Group { open: true }),
    }
}

/// The state of §9.2.1.1's scan over one block container's content.
///
/// The scan walks the container's children and descends into each inline
/// box that holds a block-level box, keeping the *path* of those inline
/// boxes (outermost first). Inline-level content goes into the current
/// anonymous block, inside a fragment of each inline box on the path; a
/// block-level box closes the anonymous block and the fragments, and
/// becomes a child of the container; the next inline content opens a new
/// anonymous block and new fragments.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct SplitState {
    /// The number of inline boxes on the path.
    pub depth: usize,
    /// How many of them, from the outermost, have a fragment open in the
    /// current anonymous block.
    pub open: usize,
    /// How many of them, from the outermost, have had a fragment at all.
    pub parted: usize,
    /// An anonymous block is open.
    pub anonymous: bool,
}

/// What the §9.2.1.1 scan reads next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum SplitEvent {
    /// An inline box that holds a block-level box: it joins the path and the
    /// scan goes through its children.
    Enter,
    /// Any other inline-level box: it goes, whole, into the innermost open
    /// fragment (or the anonymous block).
    Inline,
    /// A block-level box.
    Block,
    /// The end of the innermost inline box on the path.
    Exit,
}

/// What `anonymous::split_step` asks the driver to do, in this order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct SplitAction {
    /// Open a new anonymous block (a child of the container).
    pub open_anonymous: bool,
    /// Open new fragments of the path's inline boxes from this index to the
    /// depth (each inside the previous one, the first inside the anonymous
    /// block).
    pub open_from: usize,
    /// Put the event's box into the innermost open fragment (or the
    /// anonymous block): for [`SplitEvent::Inline`].
    pub place_inline: bool,
    /// Mark the innermost fragment as its inline box's last, and drop the
    /// innermost inline box from the path: for [`SplitEvent::Exit`].
    pub exit: bool,
    /// Close the anonymous block and every fragment, and make the event's
    /// box a child of the container: for [`SplitEvent::Block`].
    pub place_block: bool,
}

impl SplitState {
    /// Before the container's first child.
    pub const START: SplitState = SplitState {
        depth: 0,
        open: 0,
        parted: 0,
        anonymous: false,
    };

    /// The invariant: open fragments are a prefix of those that have been
    /// opened, which are a prefix of the path; a fragment is open only
    /// inside an open anonymous block.
    pub fn invariant(&self) -> bool {
        self.open <= self.parted && self.parted <= self.depth && (self.anonymous || self.open == 0)
    }
}
