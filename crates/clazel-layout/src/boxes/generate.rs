//! Box generation: each node's principal box and additional boxes, before
//! any anonymous box (phase-5.md item 5.13).
//!
//! Sources: CSS 2.1 §9.2 "Controlling box generation" (§9.2.1, §9.2.2,
//! §9.2.4 the `display` values), §9.7 "Relationships between 'display',
//! 'position', and 'float'", §12.5 "Lists" and §17.2 "The CSS table
//! model"; CSS Display 3 §2.5† (`display: none` and `contents`); HTML
//! §15.3.4 "Phrasing content" (`br`, `wbr`) at commit `4c54fae1`.
//!
//! Modelling choices:
//!
//! - **§9.7 is the identity here.** Its steps 2 to 4 apply only to a box
//!   that is absolutely positioned, fixed or floated, and `position` and
//!   `float` are not in the subset (phase-5.md 5.0(b) A): `clazel-style`
//!   neither parses nor computes them, so every box is in flow with
//!   `position: static` and `float: none`, and step 5 ("Otherwise, the
//!   remaining 'display' property values apply as specified") applies.
//!   Step 4's blockification of the root element is done by the cascade
//!   (its `display` is "blockified for the root element", CSS Display 3
//!   §2.7†); a hand-written table that does not do it gets §17.2.1's or
//!   §9.2.1.1's anonymous boxes around the root instead.
//! - **`display: contents`** is not a value `clazel-style` computes (the
//!   subset's `display` is phase-5.md item 5.6's list); [`StyleFns`] has a
//!   hook for it, which [`ComputedTable`] answers `false`, so hand-written
//!   tables can test it. Such an element generates no box and its children
//!   are walked as if they were its parent's (CSS Display 3 §2.5†). On a
//!   replaced element, `contents` acts as `none` (§2.5†, "Unusual elements").
//! - **The walk is iterative**, with an explicit stack of [`Frame`]s and
//!   one step per node; it visits each node at most once, and at most
//!   `arena.len() + 1` frames are popped, whatever the arena holds.
//! - **`br` and `wbr`.** HTML §15.3.4's sheet gives them `display-outside:
//!   newline` and `break-opportunity`, which are not in the subset, so they
//!   compute to `inline`. An HTML `br` with any `display` but `none`
//!   generates a text run of one line feed with `white-space: pre` (a
//!   forced line break, CSS Text 3 §5.5); a `wbr` generates a text run of
//!   one zero width space (U+200B), a soft wrap opportunity (UAX #14's ZW)
//!   with no width. Neither walks its children.
//! - **Text runs take their style from the text node's parent** (CSS
//!   Cascade 4 §7.2†: text inherits from its parent element); a parent with
//!   no computed style gives the initial values.
//! - **A list item** (`display: list-item`) generates a block box with a
//!   marker box as its first child (§9.2.1: "'list-item' elements … generate
//!   additional boxes"), unless its `list-style-type` is `none`, which
//!   "specifies no marker" (§12.6.2). A replaced element whose `display` is
//!   `list-item` is a block-level replaced element with no marker.
//! - **A replaced element** (`replaced.rs`) is block-level when its
//!   `display` is `block`, `list-item` or `table`, and atomic inline-level
//!   otherwise (the table-internal values included: a replaced element has
//!   no table-internal box, CSS Display 3 §2.4†). Its children are not
//!   walked.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::{ComputedStyle, Display, ListStyleType, WhiteSpace};
use clazel_style::cascade::hints::is_html;

use super::StyleFns;
use super::marker;
use super::replaced::{replaced, string};
use super::state::{Decision, Frame, Principal, Walk};
use super::tree::{BoxId, BoxKind, BoxTree, Fragment, Marker, RowGroup, TextRun};
use crate::text::TextStyle;

/// What kind of node a DOM node is, as box generation reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum NodeClass {
    /// The document.
    Document,
    /// An element.
    Element,
    /// A text node.
    Text,
    /// A doctype, comment, processing instruction or fragment.
    Other,
}

/// What `decide` reads of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct NodeInfo {
    /// Its kind.
    pub class: NodeClass,
    /// Its computed `display`, if it is an element with a computed style.
    pub display: Option<Display>,
    /// `display: contents` ([`StyleFns::display_contents`]).
    pub contents: bool,
    /// It is a replaced element (`replaced.rs`).
    pub replaced: bool,
    /// It is an HTML `br` or `wbr`.
    pub line_break: bool,
    /// Its `list-style-type` is not `none`.
    pub marker: bool,
}

/// What a node generates (§9.2, §9.2.4, §17.2; the module's modelling
/// choices). Contract: only an element generates a principal box, only a
/// text node a text run, and only the document or a `contents` element has
/// its children walked without a box.
pub fn decide(n: NodeInfo) -> Decision {
    match n.class {
        // The document generates no box; its element child is the root
        // element (the root box stands for the initial containing block).
        NodeClass::Document => Decision::Contents,
        // §9.2.2.1: text becomes (part of) an anonymous inline box, or the
        // inline box of its element: a text run either way.
        NodeClass::Text => Decision::Text,
        NodeClass::Other => Decision::Nothing,
        NodeClass::Element => {
            // An element outside the document tree, or in a hand-written
            // table without a style: no box.
            let Some(display) = n.display else {
                return Decision::Nothing;
            };
            // Display 3 §2.5†: `contents` on a replaced element is `none`.
            if n.contents {
                return if n.replaced {
                    Decision::Nothing
                } else {
                    Decision::Contents
                };
            }
            // §9.2.4: "none: This value causes an element to not appear in
            // the formatting structure (i.e., in visual media the element
            // generates no boxes and has no effect on layout). Descendant
            // elements do not generate any boxes either".
            if display == Display::None {
                return Decision::Nothing;
            }
            if n.line_break {
                return Decision::Element(Principal::Break);
            }
            if n.replaced {
                let block = matches!(display, Display::Block | Display::ListItem | Display::Table);
                return Decision::Element(Principal::Replaced { inline: !block });
            }
            Decision::Element(match display {
                // Handled above.
                Display::None => Principal::Inline,
                Display::Block => Principal::Block { marker: false },
                Display::ListItem => Principal::Block { marker: n.marker },
                Display::Inline => Principal::Inline,
                Display::InlineBlock => Principal::InlineBlock,
                Display::Table => Principal::Table { inline: false },
                Display::InlineTable => Principal::Table { inline: true },
                Display::TableRowGroup => Principal::RowGroup(RowGroup::Body),
                Display::TableHeaderGroup => Principal::RowGroup(RowGroup::Header),
                Display::TableFooterGroup => Principal::RowGroup(RowGroup::Footer),
                Display::TableRow => Principal::Row,
                Display::TableCell => Principal::Cell,
                Display::TableColumnGroup => Principal::ColumnGroup,
                Display::TableColumn => Principal::Column,
                Display::TableCaption => Principal::Caption,
            })
        }
    }
}

/// One step of the generation walk: for the frame popped, given what its
/// node generates and the id the next new box gets (`next_box`, the number
/// of boxes so far), how many boxes are added and under which box the
/// node's children are walked. Contract: given a frame satisfying
/// [`Frame::invariant`] with `next_box` boxes, every frame pushed for a
/// child satisfies it with `next_box + added` boxes.
pub fn walk_step(frame: Frame, decision: Decision, next_box: BoxId) -> Walk {
    match decision {
        Decision::Nothing => Walk {
            added: 0,
            children_under: None,
        },
        Decision::Contents => Walk {
            added: 0,
            children_under: Some(frame.parent),
        },
        Decision::Text
        | Decision::Element(Principal::Break)
        | Decision::Element(Principal::Replaced { .. }) => Walk {
            added: 1,
            children_under: None,
        },
        Decision::Element(Principal::Block { marker: true }) => Walk {
            added: 2,
            children_under: Some(next_box),
        },
        Decision::Element(_) => Walk {
            added: 1,
            children_under: Some(next_box),
        },
    }
}

/// The text style an element's computed style gives its text (CSS Text 3
/// §3, §5.1, §5.4); the initial values without one.
pub fn text_style(style: Option<&ComputedStyle>) -> TextStyle {
    style.map_or(TextStyle::INITIAL, |s| TextStyle {
        white_space: s.white_space,
        word_break: s.word_break,
        overflow_wrap: s.overflow_wrap,
    })
}

/// What `decide` reads of node `x`.
fn node_info(arena: &Arena, styles: &impl StyleFns, x: usize) -> NodeInfo {
    let class = match arena.kind(x) {
        ExecKind::Document { .. } => NodeClass::Document,
        ExecKind::Element { .. } => NodeClass::Element,
        ExecKind::Text { .. } => NodeClass::Text,
        _ => NodeClass::Other,
    };
    let style = styles.style(x);
    NodeInfo {
        class,
        display: style.map(|s| s.display),
        contents: styles.display_contents(x),
        replaced: replaced(arena, x).is_some(),
        line_break: is_html(arena, x, "br") || is_html(arena, x, "wbr"),
        marker: style.is_some_and(|s| s.list_style_type != ListStyleType::None),
    }
}

/// The boxes of a principal box of kind `p` for element `x`, appended to
/// `parent`; returns the principal box.
fn principal(
    tree: &mut BoxTree,
    arena: &Arena,
    styles: &impl StyleFns,
    ordinals: &[i64],
    x: usize,
    parent: BoxId,
    p: Principal,
) -> BoxId {
    let kind = match p {
        Principal::Block { .. } => BoxKind::Block,
        Principal::InlineBlock => BoxKind::InlineBlock,
        Principal::Inline => BoxKind::Inline(Fragment::WHOLE),
        Principal::Table { inline } => BoxKind::Table { inline },
        Principal::RowGroup(g) => BoxKind::RowGroup(g),
        Principal::Row => BoxKind::Row,
        Principal::Cell => BoxKind::Cell,
        Principal::ColumnGroup => BoxKind::ColumnGroup,
        Principal::Column => BoxKind::Column,
        Principal::Caption => BoxKind::Caption,
        Principal::Replaced { inline } => match replaced(arena, x) {
            Some(what) => BoxKind::Replaced { what, inline },
            // `decide` saw a replaced element; unreachable otherwise.
            None => BoxKind::Inline(Fragment::WHOLE),
        },
        Principal::Break => {
            let wbr = is_html(arena, x, "wbr");
            let mut style = text_style(styles.style(x));
            if !wbr {
                style.white_space = WhiteSpace::Pre;
            }
            BoxKind::Text(TextRun {
                text: if wbr { "\u{200B}" } else { "\n" }.to_owned(),
                style,
                units: Vec::new(),
            })
        }
    };
    let id = tree.add_child(parent, kind, Some(x));
    if let Principal::Block { marker: true } = p {
        let style_type = styles
            .style(x)
            .map_or(ListStyleType::None, |s| s.list_style_type.clone());
        let ordinal = ordinals.get(x).copied().unwrap_or(0);
        if let Some(text) = marker::text(&style_type, ordinal) {
            tree.add_child(
                id,
                BoxKind::Marker(Marker {
                    style_type,
                    ordinal,
                    text,
                }),
                Some(x),
            );
        }
    }
    id
}

/// The boxes the nodes of `arena` generate, with no anonymous box yet: the
/// root box, the root element's principal box under it, and every other
/// node's boxes under its nearest ancestor's (§9.2).
pub fn generate(arena: &Arena, styles: &impl StyleFns) -> BoxTree {
    let mut tree = BoxTree::new();
    let n = arena.len();
    if n == 0 {
        return tree;
    }
    let ordinals = marker::ordinals(arena, |x| {
        styles
            .style(x)
            .is_some_and(|s| s.display == Display::ListItem)
    });
    let mut seen = vec![false; n];
    let mut stack = vec![Frame {
        node: 0,
        parent: BoxTree::ROOT,
    }];
    for _ in 0..n.saturating_add(1) {
        let Some(frame) = stack.pop() else { break };
        match seen.get_mut(frame.node) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let x = frame.node;
        let decision = decide(node_info(arena, styles, x));
        let walk = walk_step(frame, decision, tree.boxes.len());
        match decision {
            Decision::Nothing | Decision::Contents => {}
            Decision::Text => {
                if let ExecKind::Text { data } = arena.kind(x) {
                    let style = text_style(arena.parent(x).and_then(|p| styles.style(p)));
                    let run = TextRun {
                        text: string(data),
                        style,
                        units: Vec::new(),
                    };
                    tree.add_child(frame.parent, BoxKind::Text(run), Some(x));
                }
            }
            Decision::Element(p) => {
                principal(&mut tree, arena, styles, &ordinals, x, frame.parent, p);
            }
        }
        if let Some(under) = walk.children_under {
            stack.extend(arena.children(x).iter().rev().map(|&c| Frame {
                node: c,
                parent: under,
            }));
        }
    }
    tree
}
