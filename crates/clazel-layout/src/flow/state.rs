//! The states of `flow/`'s passes, their invariants, and the contracts of
//! the steps over them (phase-5.md item 5.14).
//!
//! Layout is one walk over the box tree with an explicit stack (`block.rs`):
//! a box is *entered* with its containing block's width, which gives its
//! used width (top down), and *exited* once its children are done, which
//! gives its height (bottom up). Everything a box's layout needs from its
//! siblings and ancestors is carried by small states, each with an
//! invariant written as a function, and changed only by step functions
//! whose contracts are stated here. A Kani harness over **any state
//! satisfying the invariant** and any input (`proofs.rs`) then covers trees
//! of every size and depth: each state starts satisfying its invariant and
//! every step keeps it, so no step on any tree can panic, overflow or break
//! the properties the harness asserts.
//!
//! The states and steps, with their sources:
//!
//! - **A set of adjoining margins** ([`Collapsed`]), CSS 2.1 §8.3.1: "When
//!   two or more margins collapse, the resulting margin width is the
//!   maximum of the collapsing margins' widths. In the case of negative
//!   margins, the maximum of the absolute values of the negative adjoining
//!   margins is deducted from the maximum of the positive adjoining margins.
//!   If there are no positive margins, the maximum of the absolute values of
//!   the adjoining margins is deducted from zero." The result needs only the
//!   largest positive margin and the most negative one, so a set of any
//!   number of margins is two numbers. Steps (`margins.rs`):
//!   - `Collapsed::of(m)`: the set of one margin `m`;
//!   - `Collapsed::adjoin(self, m)`: the set with `m` added; contract: the
//!     invariant is kept, and adding margins in any order gives the same set;
//!   - `Collapsed::join(self, other)`: the union of two sets; contract: the
//!     invariant is kept, and it is symmetric;
//!   - `Collapsed::resolve(self)`: the collapsed margin's width, the
//!     section's rule above; contract: for one margin it is that margin, for
//!     margins of one sign it is the one of largest absolute value, and it
//!     never overflows (it saturates).
//! - **The block flow of one block container** ([`Flow`]), CSS 2.1 §9.4.1
//!   and §8.3.1: where the next in-flow block-level child goes, which
//!   margins are pending (adjoining, not yet resolved), and whether the
//!   container's own top margin still adjoins its content ("open"). An open
//!   container has handed its top margin to the content that comes first;
//!   when that content is placed, the open containers around it are closed
//!   from the outermost in (`block.rs`'s resolution walk), each at the top
//!   of its parent's content. Steps (`margins.rs`):
//!   - `enter(parent, child: BlockFacts, margin_top) -> (Entry, Flow)`: a
//!     block-level child starts. Contract: if the child's top margin adjoins
//!     its first child's ([`BlockFacts`]: `top_adjoins`), the parent's
//!     pending margins and the child's top margin are handed to the child
//!     ([`Entry::Open`]); otherwise they are the margins above its border box
//!     ([`Entry::Content`]). Either way the parent keeps none pending, its
//!     `y` does not move, and its invariant is kept.
//!   - `place(frame, margins) -> (y, Flow)`: content is placed in a closed
//!     frame after `margins`. Contract: the content's top is the frame's `y`
//!     plus the margins resolved; the frame keeps nothing pending and its
//!     `y` does not move (the content's exit moves it). Requires a closed
//!     frame.
//!   - `close(frame) -> Flow`: an open frame's top margin has been resolved
//!     (content was placed inside it). Contract: the frame is closed, with
//!     `y` zero and content placed; nothing else changes.
//!   - `exit(parent, child: Exited) -> Flow`: a block-level child ended.
//!     Contract: a child that collapsed through ([`Exited::Through`]) only
//!     hands its margins on (the parent's `y` and openness do not change); a
//!     placed child ([`Exited::Placed`]) moves `y` to its bottom border edge
//!     and leaves pending what adjoins its bottom; the invariant is kept.
//!   - `finish(flow, facts) -> Finish`: the container's content ended.
//!     Contract (§8.3.1's adjoining rules and §10.6.3's "first applicable"
//!     list): a container still open whose facts allow it collapses through
//!     (content height zero, its pending margins go on); one still open that
//!     cannot must be resolved by the driver; a closed one whose bottom
//!     adjoins its last child's ends at `y` with its pending margins going
//!     on; any other ends at `y` plus its pending margins resolved, with
//!     nothing going on.
//! - **The used widths of a block-level box** ([`WidthInput`] to
//!   [`UsedWidths`]), CSS 2.1 §10.3.3 and §10.4 (`widths.rs`):
//!   - `solve_block(input) -> UsedWidths`: §10.3.3's five rules (numbered
//!     here 1 to 5 in their order in the text). Contract: unless a sum
//!     saturates, `margin-left + edges + width + margin-right` equals the
//!     containing block's width; a width given is kept unless the box is
//!     over-constrained, when `margin-right` follows from the equality (rule
//!     2, `direction` is `ltr` in this phase); `auto` margins are equal when
//!     both are `auto` and nothing is too wide (rule 5); the width is never
//!     negative.
//!   - `align(used, to) -> UsedWidths`: HTML §15.2's "align descendants".
//!     Contract: only a box whose margin-right rule 2 forced to a greater
//!     value moves, the sum is kept, and the width does not change.
//!   - `min_max(tentative, min, max) -> Option<i32>`: §10.4's steps 2 and 3:
//!     the width to apply the rules again with, if any. Contract: the result
//!     is `max` when the tentative width is above it, then `min` when what
//!     results is below it.
//!   - `shrink_to_fit(min, max, available)`: §10.3.5's "min(max(preferred
//!     minimum width, available width), preferred width)". Contract: that
//!     formula, never negative for non-negative preferred widths.
//! - **A line box's vertical extent** ([`LineExtent`]), CSS 2.1 §10.8: "The
//!   line box height is the distance between the uppermost box top and the
//!   lowermost box bottom." Steps (`inline.rs`):
//!   - `half_leading(a, d, line_height) -> (above, below)`: §10.8.1's
//!     `A' = A + L/2`, `D' = D + L/2` with `L = line-height - AD`. Contract:
//!     `above + below = line-height` unless a sum saturates.
//!   - `LineExtent::add(self, top, bottom)`: one more box. Contract: the
//!     invariant is kept and the extent covers the box and every box before.
//!   - `align_offset(align, available, width)`: CSS 2.1 §16.2 with CSS Text
//!     3 §7.1's overflow rule. Contract: in `0..=available - width` when the
//!     content fits, zero when it does not (start-aligned).
//! - **What each box is to the walk** ([`Role`]), from its class and its
//!   parent's (`block.rs`): `role(class, parent) -> Role`. Contract: a
//!   block-level box in a block container is in its parent's flow, an
//!   atomic inline is laid out on its own, inline boxes and text runs only
//!   inside their inline formatting context, a marker beside its list item,
//!   columns as empty boxes, and table-internal boxes (the placeholder of
//!   `mod.rs`) in their parent's flow.
//!
//! White space, line break opportunities and choosing lines are item 5.12's
//! (`text::lines::fit_step`, proved there); the steps here are the ones
//! formatting adds.

use clazel_style::cascade::computed::TextAlign;

/// A set of adjoining margins (CSS 2.1 §8.3.1), as the two numbers its
/// collapsed width needs: the largest positive margin and the most negative
/// one (1/64 px).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Collapsed {
    /// The largest margin that is not negative, or zero if none is.
    pub positive: i32,
    /// The most negative margin, or zero if none is negative.
    pub negative: i32,
}

impl Collapsed {
    /// The empty set (it resolves to zero).
    pub const NONE: Collapsed = Collapsed {
        positive: 0,
        negative: 0,
    };

    /// The invariant: `positive` is not negative and `negative` is not
    /// positive.
    pub fn invariant(&self) -> bool {
        self.positive >= 0 && self.negative <= 0
    }
}

/// What §8.3.1's conditions read about a block-level box.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct BlockFacts {
    /// A block container that is not replaced: its content is laid out in a
    /// flow of its own (block-level children, or line boxes).
    pub container: bool,
    /// It establishes a new block formatting context (§9.4.1), or it is the
    /// root element ("Margins of the root element's box do not collapse").
    pub bfc_root: bool,
    /// Its top border or top padding is not zero.
    pub top_edge: bool,
    /// Its bottom border or bottom padding is not zero.
    pub bottom_edge: bool,
    /// Its computed `height` is `auto` (or a percentage that computes to
    /// `auto`, §10.5).
    pub height_auto: bool,
    /// Its computed `height` is zero.
    pub height_zero: bool,
    /// Its computed `min-height` is zero (or `auto`).
    pub min_height_zero: bool,
}

/// The block flow of one block container (CSS 2.1 §9.4.1, §8.3.1), in its
/// content box's coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Flow {
    /// The bottom border edge of the last content placed (zero before any):
    /// where the next content goes, before the pending margins.
    pub y: i32,
    /// The margins adjoining the next content's top, not yet resolved.
    pub pending: Collapsed,
    /// The container's top margin still adjoins its content: nothing has
    /// been placed, and its top margin was handed to its first child.
    pub open: bool,
    /// Some content (a block-level box that did not collapse through, or a
    /// line box that is not empty) has been placed.
    pub placed: bool,
}

impl Flow {
    /// The flow of a container whose top margin does not adjoin its
    /// content (a block formatting context root, or a box with a top border
    /// or padding), before its first child.
    pub const CLOSED: Flow = Flow {
        y: 0,
        pending: Collapsed::NONE,
        open: false,
        placed: false,
    };

    /// The flow of a container whose top margin adjoins its first child's,
    /// with the margins `pending` handed to it.
    pub fn open(pending: Collapsed) -> Flow {
        Flow {
            y: 0,
            pending,
            open: true,
            placed: false,
        }
    }

    /// The invariant: the pending set is well formed, and an open flow has
    /// placed nothing and is still at its top.
    pub fn invariant(&self) -> bool {
        self.pending.invariant() && (!self.open || (self.y == 0 && !self.placed))
    }
}

/// What `margins::enter` says about a block-level child's top.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Entry {
    /// Its top margin adjoins its first child's: it opens a flow with these
    /// margins pending.
    Open(Collapsed),
    /// Its border box is content: it goes after these margins.
    Content(Collapsed),
}

/// What a block-level child left when it ended, for `margins::exit`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Exited {
    /// Its margins collapsed through it (§8.3.1, the last pair): these go
    /// on, its bottom margin included.
    Through(Collapsed),
    /// It was placed: its bottom border edge in the parent's content box,
    /// and the margins adjoining what comes next (its bottom margin, with
    /// its last child's when they adjoin).
    Placed {
        /// The bottom border edge.
        bottom: i32,
        /// The margins that go on.
        pending: Collapsed,
    },
}

/// What `margins::finish` says about a container whose content ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Finish {
    /// Its top and bottom margins adjoin: it collapses through.
    pub through: bool,
    /// It is still open but cannot collapse through: the driver resolves
    /// its pending margins as its top margin before placing it.
    pub resolve: bool,
    /// Its content height for `height: auto` (§10.6.3, §10.6.7).
    pub content: i32,
    /// The margins that go on past its bottom (before its own bottom
    /// margin is added).
    pub out: Collapsed,
}

/// What the width rules read (CSS 2.1 §10.3.3), in 1/64 px; `None` is
/// `auto`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct WidthInput {
    /// The containing block's width.
    pub containing: i32,
    /// `margin-left`.
    pub margin_left: Option<i32>,
    /// `margin-right`.
    pub margin_right: Option<i32>,
    /// `border-left-width + padding-left + padding-right +
    /// border-right-width`.
    pub edges: i32,
    /// `width`.
    pub width: Option<i32>,
}

/// The used values §10.3.3 gives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct UsedWidths {
    /// `margin-left`.
    pub margin_left: i32,
    /// `width`.
    pub width: i32,
    /// `margin-right`.
    pub margin_right: i32,
    /// Rule 2 applied and gave `margin-right` a value greater than its
    /// computed one (what HTML's "align descendants" moves).
    pub forced_right: bool,
}

/// HTML §15.2's "align descendants" directions, as [`UsedWidths`] reads
/// them (`clazel-style`'s `AlignDescendants`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Align {
    /// To the left (nothing moves in a left-to-right block).
    Left,
    /// To the center.
    Center,
    /// To the right.
    Right,
}

/// A line box's vertical extent so far (CSS 2.1 §10.8), relative to its
/// root inline box's baseline (y down).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct LineExtent {
    /// The uppermost box top.
    pub top: i32,
    /// The lowermost box bottom.
    pub bottom: i32,
    /// Some box has been added.
    pub any: bool,
}

impl LineExtent {
    /// No box yet.
    pub const EMPTY: LineExtent = LineExtent {
        top: 0,
        bottom: 0,
        any: false,
    };

    /// The invariant: an extent with a box is not inverted, and one without
    /// is empty.
    pub fn invariant(&self) -> bool {
        if self.any {
            self.top <= self.bottom
        } else {
            self.top == 0 && self.bottom == 0
        }
    }
}

/// The horizontal alignment of a line's content (CSS 2.1 §16.2, with CSS
/// Text 3 §7.1's `start` and `end`), as `align_offset` reads it.
pub fn line_align(t: TextAlign) -> Align {
    match t {
        // `justify` is drawn as `left` (phase-5.md item 5.14; §16.2 allows
        // it: "Conforming user agents may interpret the value 'justify' as
        // 'left'"), and `start` is `left` in a left-to-right block.
        TextAlign::Start | TextAlign::Left | TextAlign::Justify | TextAlign::JustifyAll => {
            Align::Left
        }
        TextAlign::End | TextAlign::Right => Align::Right,
        TextAlign::Center => Align::Center,
    }
}

/// What a box is to the layout walk (`block.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Role {
    /// The root box: the initial containing block.
    Root,
    /// A block-level box (or a table-internal box, in the placeholder) in
    /// its parent's block flow.
    Flow,
    /// An atomic inline: laid out as a box of its own before its inline
    /// formatting context's lines are made.
    Atomic,
    /// An inline box or a text run: laid out only as part of its inline
    /// formatting context's lines.
    Inline,
    /// A list item's marker: placed beside its list item's first line.
    Marker,
    /// A table column or column group: an empty box (the placeholder).
    Column,
}
