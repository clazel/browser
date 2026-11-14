//! Collapsing margins (CSS 2.1 §8.3.1) and the block flow of a block
//! container (§9.4.1, §10.6.3, §10.6.7): the steps over [`Collapsed`] and
//! [`Flow`] whose contracts `state.rs` states.
//!
//! Source: CSS 2.1 (W3C Recommendation, 7 June 2011), §8.3.1 "Collapsing
//! margins", <https://www.w3.org/TR/2011/REC-CSS2-20110607/box.html#collapsing-margins>.
//! The section defines adjoining margins by four pairs and then restates
//! the rules as eight bullets; both are cited where they are used. The
//! bullets on floats, absolutely positioned boxes and clearance never apply
//! (no floats or positioning in the subset).
//!
//! Modelling choices:
//!
//! - **A set of adjoining margins is two numbers** ([`Collapsed`]): the
//!   section's result reads only the largest positive margin and the most
//!   negative one. Collapsing is transitive ("margins … adjoining …
//!   collapse", and a box's margins can adjoin through it), so the flow
//!   keeps one set of *pending* margins, which every margin that adjoins the
//!   next content joins.
//! - **The definition and the bullets disagree** on two conditions, and the
//!   bullets are followed (`docs/ERRATA.md`, "CSS 2.1 §8.3.1"): a box's own
//!   top and bottom margins adjoin when "all of its in-flow children's
//!   margins (if any) collapse" (the definition says "no in-flow
//!   children"), and a box's bottom margin adjoins its last child's only if
//!   its `min-height` is zero too (the definition reads only `height`).
//! - **"Line boxes … must be treated as not existing for any other purpose"**
//!   (§9.4.2): a block container whose line boxes are all empty has no
//!   content for margin collapsing, so its margins can collapse through it.
//! - **Where a box whose margins collapse through it goes**: §8.3.1, "the
//!   position of the element's top border edge is the same as it would have
//!   been if the element had a non-zero bottom border", and, when its top
//!   margin collapses with its parent's, "the top border edge of the box is
//!   defined to be the same as the parent's" (`block.rs`).

use super::state::{BlockFacts, Collapsed, Entry, Exited, Finish, Flow};

impl Collapsed {
    /// The set of the one margin `m`.
    pub fn of(m: i32) -> Collapsed {
        Collapsed::NONE.adjoin(m)
    }

    /// The set with margin `m` added: it becomes the largest positive margin
    /// if it is larger, and the most negative if it is more negative.
    pub fn adjoin(self, m: i32) -> Collapsed {
        Collapsed {
            positive: self.positive.max(m),
            negative: self.negative.min(m),
        }
    }

    /// The union of two sets.
    pub fn join(self, other: Collapsed) -> Collapsed {
        Collapsed {
            positive: self.positive.max(other.positive),
            negative: self.negative.min(other.negative),
        }
    }

    /// The collapsed margin's width: "the maximum of the absolute values of
    /// the negative adjoining margins is deducted from the maximum of the
    /// positive adjoining margins. If there are no positive margins, the
    /// maximum of the absolute values of the adjoining margins is deducted
    /// from zero." Both cases are `positive + negative` (with `positive`
    /// zero when no margin is positive, and `negative` zero when none is
    /// negative), saturating.
    pub fn resolve(self) -> i32 {
        self.positive.saturating_add(self.negative)
    }
}

impl BlockFacts {
    /// §8.3.1, "top margin of a box and top margin of its first in-flow
    /// child", with the bullets "Margins of elements that establish new
    /// block formatting contexts … do not collapse with their in-flow
    /// children" and "The top margin of an in-flow block element collapses
    /// with its first in-flow block-level child's top margin if the element
    /// has no top border, no top padding, and the child has no clearance"
    /// (and, for a block container with inline content, its first line
    /// box, which §8.3.1's "no line boxes … separate them" reads the same
    /// way): whether this box's top margin adjoins its content's.
    pub fn top_adjoins(&self) -> bool {
        self.container && !self.bfc_root && !self.top_edge
    }

    /// §8.3.1, "bottom margin of a last in-flow child and bottom margin of
    /// its parent if the parent has 'auto' computed height", with the
    /// bullet "The bottom margin of an in-flow block box with a 'height' of
    /// 'auto' and a 'min-height' of zero collapses with its last in-flow
    /// block-level child's bottom margin if the box has no bottom padding and
    /// no bottom border": whether this box's bottom margin adjoins its last
    /// child's.
    pub fn bottom_adjoins(&self) -> bool {
        self.container
            && !self.bfc_root
            && !self.bottom_edge
            && self.height_auto
            && self.min_height_zero
    }

    /// §8.3.1's bullet "A box's own margins collapse if the 'min-height'
    /// property is zero, and it has neither top or bottom borders nor top or
    /// bottom padding, and it has a 'height' of either 0 or 'auto', and it
    /// does not contain a line box, and all of its in-flow children's
    /// margins (if any) collapse", with the definition's "a box that does not
    /// establish a new block formatting context": the conditions on the box
    /// itself (the flow says whether it holds a line box or a child that
    /// does not collapse through).
    pub fn may_collapse_through(&self) -> bool {
        self.container
            && !self.bfc_root
            && !self.top_edge
            && !self.bottom_edge
            && (self.height_auto || self.height_zero)
            && self.min_height_zero
    }
}

/// A block-level child starts in `parent`'s flow, with used top margin
/// `margin_top` (`state.rs`, `enter`).
pub fn enter(parent: Flow, child: BlockFacts, margin_top: i32) -> (Entry, Flow) {
    // "bottom margin of box and top margin of its next in-flow following
    // sibling", and through an open parent "top margin of a box and top
    // margin of its first in-flow child": the child's top margin joins what
    // is pending.
    let margins = parent.pending.adjoin(margin_top);
    let next = Flow {
        pending: Collapsed::NONE,
        ..parent
    };
    if child.top_adjoins() {
        (Entry::Open(margins), next)
    } else {
        (Entry::Content(margins), next)
    }
}

/// Content is placed in the closed `frame` after `margins` (`state.rs`,
/// `place`): its top edge, and the frame with nothing pending.
pub fn place(frame: Flow, margins: Collapsed) -> (i32, Flow) {
    let top = frame.y.saturating_add(margins.resolve());
    (
        top,
        Flow {
            pending: Collapsed::NONE,
            placed: true,
            ..frame
        },
    )
}

/// An open frame whose top margin has been resolved (`state.rs`, `close`):
/// its content starts at its top.
pub fn close(frame: Flow) -> Flow {
    Flow {
        y: 0,
        pending: frame.pending,
        open: false,
        placed: true,
    }
}

/// A block-level child of `parent` ended (`state.rs`, `exit`).
pub fn exit(parent: Flow, child: Exited) -> Flow {
    match child {
        Exited::Through(pending) => Flow { pending, ..parent },
        Exited::Placed { bottom, pending } => Flow {
            y: bottom,
            pending,
            open: false,
            placed: true,
        },
    }
}

/// The content of a container with flow `flow` and facts `facts` ended
/// (`state.rs`, `finish`): CSS 2.1 §10.6.3's "first applicable of the
/// following" for `height: auto`, and §10.6.7 for a block formatting
/// context root.
pub fn finish(flow: Flow, facts: BlockFacts) -> Finish {
    if flow.open {
        // Nothing was placed: no line box, and every child collapsed
        // through. §8.3.1's last bullet decides whether this box does too.
        if facts.may_collapse_through() {
            Finish {
                through: true,
                resolve: false,
                content: 0,
                out: flow.pending,
            }
        } else {
            // The pending margins are this box's top margin and its
            // children's, all adjoining its top: the driver resolves them
            // there, and the content (§10.6.3 rule 4, "zero, otherwise") is
            // empty.
            Finish {
                through: false,
                resolve: true,
                content: 0,
                out: Collapsed::NONE,
            }
        }
    } else if facts.bottom_adjoins() {
        // §10.6.3 rule 3: "the bottom border edge of the last in-flow child
        // whose top margin doesn't collapse with the element's bottom
        // margin" (or rule 1, the last line box's bottom): the pending
        // margins adjoin this box's bottom margin and go on.
        Finish {
            through: false,
            resolve: false,
            content: flow.y,
            out: flow.pending,
        }
    } else {
        // §10.6.3 rule 2, "the bottom edge of the bottom (possibly
        // collapsed) margin of its last in-flow child, if the child's bottom
        // margin does not collapse with the element's bottom margin", and
        // §10.6.7, "the bottom margin-edge of the bottommost block-level
        // child box".
        Finish {
            through: false,
            resolve: false,
            content: flow.y.saturating_add(flow.pending.resolve()),
            out: Collapsed::NONE,
        }
    }
}
