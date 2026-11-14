//! The box tree: its boxes, in an arena, and the operations the passes use
//! on it (phase-5.md item 5.13).
//!
//! Source: CSS 2.1 (W3C Recommendation, 7 June 2011,
//! <https://www.w3.org/TR/2011/REC-CSS2-20110607/>), §9.2 "Controlling box
//! generation", §12.5 "Lists", §17.2 "The CSS table model" and §17.4
//! "Tables in the visual formatting model"; HTML §15.4 and §15.5 for
//! replaced elements (`replaced.rs`).
//!
//! Modelling choices:
//!
//! - **An arena of boxes** indexed by [`BoxId`], each with its parent and
//!   its children in order. A pass that removes a box only unlinks it from
//!   its parent; [`BoxTree::compact`] then renumbers the boxes reachable
//!   from the root in tree order (preorder), so that a finished tree has no
//!   unreachable box and every box's id is greater than its parent's.
//! - **The root box** ([`BoxKind::Root`]) stands for the initial containing
//!   block (CSS 2.1 §10.1, "the containing block in which the root element
//!   lives"). It is a block container whose only child, if any, is the root
//!   element's principal box (and the boxes the passes wrap around it).
//! - **Each box records the node that generated it** ([`LayoutBox::node`]):
//!   an element for its principal box and the additional boxes it generates
//!   (a list item's marker, a table's table box beside its wrapper, the
//!   fragments of a split inline), a text node (or a `br` or `wbr` element)
//!   for a text run, and `None` for an anonymous box (§9.2.1.1, §9.2.2.1,
//!   §17.2.1). An anonymous box's inherited properties are those of the
//!   nearest ancestor box with a node, and its other properties have their
//!   initial values (§9.2.1.1: "The properties of anonymous boxes are
//!   inherited from the enclosing non-anonymous box"); layout (item 5.14)
//!   applies that, so no style is stored here.

use clazel_style::cascade::computed::ListStyleType;

use super::replaced::Replaced;
use crate::text::{TextStyle, Unit};

/// The index of a box in its [`BoxTree`].
pub type BoxId = usize;

/// Which of a table's row groups (CSS 2.1 §17.2: "row group box").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum RowGroup {
    /// `table-header-group`.
    Header,
    /// `table-row-group`.
    Body,
    /// `table-footer-group`.
    Footer,
}

/// Where an inline box stands among the fragments a split made of it (CSS
/// 2.1 §9.2.1.1: "splitting the inline box into two boxes (even if either
/// side is empty), one on each side of the block-level box(es)"). An inline
/// box that was not split is both its first and its last fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Fragment {
    /// The first fragment: its start edge (left border, padding and margin)
    /// is drawn.
    pub first: bool,
    /// The last fragment: its end edge is drawn.
    pub last: bool,
}

impl Fragment {
    /// An inline box that is not split.
    pub const WHOLE: Fragment = Fragment {
        first: true,
        last: true,
    };
}

/// A text node's text after CSS Text 3 §4.1.1 Phase I (item 5.12's
/// [`crate::text::collapse`]), within its inline formatting context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextRun {
    /// The text as the DOM holds it (for a `br`, a line feed; for a `wbr`, a
    /// zero width space). [`Unit::offset`] indexes it.
    pub text: String,
    /// The style its parent element gives it (CSS Text 3 §3, §5.1, §5.4).
    pub style: TextStyle,
    /// What remains of it after Phase I, in order: empty until the Phase I
    /// pass runs. [`Unit::item`] is this run's index among the items of its
    /// inline formatting context (text runs and atomic inlines, in order).
    pub units: Vec<Unit>,
}

/// A list item's marker box (CSS 2.1 §12.5, CSS Lists 3 §3†).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Marker {
    /// The list item's computed `list-style-type`.
    pub style_type: ListStyleType,
    /// Its ordinal: the value of the `list-item` counter (`marker.rs`).
    pub ordinal: i64,
    /// The marker's text (`marker.rs`).
    pub text: String,
}

/// What kind of box a box is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoxKind {
    /// The initial containing block (the tree's root; a block container).
    Root,
    /// A block box (§9.2.1): block-level and a block container. `display:
    /// block` or `list-item` (a list item's principal box), or anonymous.
    Block,
    /// An inline-level block container (`display: inline-block`, §9.2.2:
    /// an atomic inline-level box).
    InlineBlock,
    /// An inline box (§9.2.2: `display: inline`), or one fragment of one.
    Inline(Fragment),
    /// A text run: a text node's text, after Phase I.
    Text(TextRun),
    /// A replaced element (`replaced.rs`), block-level or atomic
    /// inline-level.
    Replaced {
        /// Which element, with what HTML gives for its size.
        what: Replaced,
        /// Inline-level (an atomic inline), else block-level.
        inline: bool,
    },
    /// A list item's marker box (§12.5): always its list item's first child.
    Marker(Marker),
    /// A table wrapper box (§17.4: "a principal block container box called
    /// the table wrapper box that contains the table box itself and any
    /// caption boxes"): block-level, or atomic inline-level for
    /// `inline-table`.
    TableWrapper {
        /// For `inline-table`.
        inline: bool,
    },
    /// A table box (§17.2: `table`, or `inline-table` when `inline`).
    Table {
        /// For `inline-table`.
        inline: bool,
    },
    /// A row group box.
    RowGroup(RowGroup),
    /// `table-row`.
    Row,
    /// `table-cell` (a block container).
    Cell,
    /// `table-column-group`.
    ColumnGroup,
    /// `table-column`.
    Column,
    /// `table-caption` (a block container).
    Caption,
}

/// The class of a box that the passes' rules read: its kind without its
/// data. A step function takes these, so its Kani harness can take any.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Class {
    /// [`BoxKind::Root`].
    Root,
    /// [`BoxKind::Block`].
    Block,
    /// [`BoxKind::InlineBlock`].
    InlineBlock,
    /// [`BoxKind::Inline`].
    Inline,
    /// [`BoxKind::Text`], with whether its text is only white space (CSS
    /// Text 3 §4: spaces, tabs, segment breaks and carriage returns).
    Text {
        /// Only white space.
        white: bool,
    },
    /// [`BoxKind::Replaced`].
    Replaced {
        /// Inline-level.
        inline: bool,
    },
    /// [`BoxKind::Marker`].
    Marker,
    /// [`BoxKind::TableWrapper`].
    TableWrapper {
        /// For `inline-table`.
        inline: bool,
    },
    /// [`BoxKind::Table`].
    Table {
        /// For `inline-table`.
        inline: bool,
    },
    /// [`BoxKind::RowGroup`].
    RowGroup,
    /// [`BoxKind::Row`].
    Row,
    /// [`BoxKind::Cell`].
    Cell,
    /// [`BoxKind::ColumnGroup`].
    ColumnGroup,
    /// [`BoxKind::Column`].
    Column,
    /// [`BoxKind::Caption`].
    Caption,
}

/// CSS Text 3 §4: "document white space characters" (spaces, tabs and
/// segment breaks) and carriage returns, which "are treated identically to
/// spaces".
pub fn is_white(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r')
}

impl BoxKind {
    /// Its [`Class`].
    pub fn class(&self) -> Class {
        match self {
            BoxKind::Root => Class::Root,
            BoxKind::Block => Class::Block,
            BoxKind::InlineBlock => Class::InlineBlock,
            BoxKind::Inline(_) => Class::Inline,
            BoxKind::Text(run) => Class::Text {
                white: run.text.chars().all(is_white),
            },
            BoxKind::Replaced { inline, .. } => Class::Replaced { inline: *inline },
            BoxKind::Marker(_) => Class::Marker,
            BoxKind::TableWrapper { inline } => Class::TableWrapper { inline: *inline },
            BoxKind::Table { inline } => Class::Table { inline: *inline },
            BoxKind::RowGroup(_) => Class::RowGroup,
            BoxKind::Row => Class::Row,
            BoxKind::Cell => Class::Cell,
            BoxKind::ColumnGroup => Class::ColumnGroup,
            BoxKind::Column => Class::Column,
            BoxKind::Caption => Class::Caption,
        }
    }
}

impl Class {
    /// §9.2.1: a block-level box ("'block', 'list-item', and 'table'"; for a
    /// table, its wrapper, §17.4). A block-level replaced element too. The
    /// table-internal boxes are neither block-level nor inline-level; after
    /// §17.2.1 they occur only inside tables.
    pub fn is_block_level(self) -> bool {
        matches!(
            self,
            Class::Block
                | Class::Replaced { inline: false }
                | Class::TableWrapper { inline: false }
                | Class::Table { inline: false }
        )
    }

    /// §9.2.2: an inline-level box ("'inline', 'inline-table', and
    /// 'inline-block'"), a text run (§9.2.2.1's anonymous inline boxes) or
    /// an inline-level replaced element.
    pub fn is_inline_level(self) -> bool {
        matches!(
            self,
            Class::Inline
                | Class::InlineBlock
                | Class::Text { .. }
                | Class::Replaced { inline: true }
                | Class::TableWrapper { inline: true }
                | Class::Table { inline: true }
        )
    }

    /// §9.2.2: an atomic inline-level box ("replaced inline-level elements,
    /// inline-block elements, and inline-table elements").
    pub fn is_atomic_inline(self) -> bool {
        matches!(
            self,
            Class::InlineBlock
                | Class::Replaced { inline: true }
                | Class::TableWrapper { inline: true }
                | Class::Table { inline: true }
        )
    }

    /// §9.2.1: a block container box ("either contains only block-level
    /// boxes or establishes an inline formatting context"): a block box, a
    /// non-replaced inline block or table cell, a table caption (§17.4), and
    /// the root.
    pub fn is_block_container(self) -> bool {
        matches!(
            self,
            Class::Root | Class::Block | Class::InlineBlock | Class::Cell | Class::Caption
        )
    }
}

/// One box.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LayoutBox {
    /// What it is.
    pub kind: BoxKind,
    /// The node that generated it; `None` for an anonymous box.
    pub node: Option<usize>,
    /// Its parent; `None` for the root and for a box no longer in the tree.
    pub parent: Option<BoxId>,
    /// Its children, in order.
    pub children: Vec<BoxId>,
}

/// A box tree: the boxes, with the root at [`BoxTree::ROOT`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoxTree {
    /// The boxes. After [`BoxTree::compact`], every box is in the tree and
    /// the ids are in tree order.
    pub boxes: Vec<LayoutBox>,
}

impl Default for BoxTree {
    fn default() -> Self {
        BoxTree::new()
    }
}

impl BoxTree {
    /// The root box's id.
    pub const ROOT: BoxId = 0;

    /// A tree with only the root box.
    pub fn new() -> BoxTree {
        BoxTree {
            boxes: vec![LayoutBox {
                kind: BoxKind::Root,
                node: None,
                parent: None,
                children: Vec::new(),
            }],
        }
    }

    /// The box `id`, if there is one.
    pub fn get(&self, id: BoxId) -> Option<&LayoutBox> {
        self.boxes.get(id)
    }

    /// The children of `id` (none for an id out of range).
    pub fn children(&self, id: BoxId) -> &[BoxId] {
        self.boxes.get(id).map_or(&[], |b| b.children.as_slice())
    }

    /// The class of `id`; [`Class::Root`] for an id out of range (no pass
    /// asks for one).
    pub fn class(&self, id: BoxId) -> Class {
        self.boxes.get(id).map_or(Class::Root, |b| b.kind.class())
    }

    /// A new box with no parent and no children.
    pub fn add(&mut self, kind: BoxKind, node: Option<usize>) -> BoxId {
        let id = self.boxes.len();
        self.boxes.push(LayoutBox {
            kind,
            node,
            parent: None,
            children: Vec::new(),
        });
        id
    }

    /// Makes `child` the last child of `parent`.
    pub fn append(&mut self, parent: BoxId, child: BoxId) {
        if let Some(c) = self.boxes.get_mut(child) {
            c.parent = Some(parent);
        }
        if let Some(p) = self.boxes.get_mut(parent) {
            p.children.push(child);
        }
    }

    /// A new box, appended as the last child of `parent`.
    pub fn add_child(&mut self, parent: BoxId, kind: BoxKind, node: Option<usize>) -> BoxId {
        let id = self.add(kind, node);
        self.append(parent, id);
        id
    }

    /// Replaces the children of `parent` with `children`, each of which
    /// then has `parent` as its parent. The old children not among the new
    /// ones are left without a parent.
    pub fn set_children(&mut self, parent: BoxId, children: Vec<BoxId>) {
        let old = self
            .boxes
            .get_mut(parent)
            .map(|p| std::mem::take(&mut p.children))
            .unwrap_or_default();
        for c in old {
            if let Some(b) = self.boxes.get_mut(c) {
                b.parent = None;
            }
        }
        for &c in &children {
            if let Some(b) = self.boxes.get_mut(c) {
                b.parent = Some(parent);
            }
        }
        if let Some(p) = self.boxes.get_mut(parent) {
            p.children = children;
        }
    }

    /// The boxes reachable from the root, in tree order (preorder), each at
    /// most once. Iterative: at most `boxes.len() + 1` steps, each popping
    /// one id and, if it is in range and not seen before, pushing its
    /// children (the same walk as `clazel_style::cascade::preorder`).
    pub fn preorder(&self) -> Vec<BoxId> {
        clazel_style::cascade::preorder(self.boxes.len(), |id| self.children(id))
    }

    /// Renumbers the boxes reachable from the root in tree order and drops
    /// the others.
    pub fn compact(&mut self) {
        let order = self.preorder();
        let mut new_id: Vec<Option<BoxId>> = vec![None; self.boxes.len()];
        for (i, &old) in order.iter().enumerate() {
            if let Some(slot) = new_id.get_mut(old) {
                *slot = Some(i);
            }
        }
        let renumber = |id: BoxId| new_id.get(id).copied().flatten();
        let mut boxes = Vec::with_capacity(order.len());
        for &old in &order {
            let Some(b) = self.boxes.get(old) else {
                continue;
            };
            boxes.push(LayoutBox {
                kind: b.kind.clone(),
                node: b.node,
                parent: b.parent.and_then(renumber),
                children: b.children.iter().filter_map(|&c| renumber(c)).collect(),
            });
        }
        self.boxes = boxes;
    }
}
