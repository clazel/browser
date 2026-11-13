//! CSS 2.1 §17.2.1 "Anonymous table objects", in its three stages, and
//! §17.4's table wrapper box (phase-5.md item 5.13).
//!
//! Source: CSS 2.1 (W3C Recommendation, 7 June 2011), §17.2.1
//! <https://www.w3.org/TR/2011/REC-CSS2-20110607/tables.html#anonymous-boxes>
//! and §17.4 <https://www.w3.org/TR/2011/REC-CSS2-20110607/tables.html#model>.
//! The section's three stages are numbered 1 to 3 and their rules 1.1 to
//! 3.2 in the order the text lists them; its terms are functions here:
//! [`is_row_group`], [`is_proper_table_child`],
//! [`is_proper_table_row_parent`], [`is_internal`], [`is_tabular_container`]
//! and [`is_proper_table_descendant`].
//!
//! Modelling choices:
//!
//! - **"An anonymous inline box that contains only white space"** is a text
//!   run whose text is only spaces, tabs, line feeds and carriage returns
//!   (CSS Text 3 §4's document white space, [`super::tree::is_white`]),
//!   before Phase I, whatever its `white-space`. Every text run counts,
//!   including one inside an inline element (CSS 2.1 calls only text
//!   directly in a block container an anonymous inline, §9.2.2.1, but the
//!   rules are about the boxes between table boxes, which a text run in an
//!   inline element also is).
//! - **"Treated as if it had 'display: none'"**: the box is removed with its
//!   subtree.
//! - **Each stage runs over the whole tree, top down** (a box's children
//!   are regrouped before the walk goes into them), so the anonymous rows
//!   rule 2.1 makes get rule 2.3's anonymous cells, and rule 3.1's rows are
//!   then wrapped by rule 3.2 in the same parent. Within stage 1, rules 1.1
//!   and 1.2 apply first, and rules 1.3 and 1.4 read the siblings that
//!   remain.
//! - **"Consecutive"** allows "an anonymous inline containing only white
//!   spaces" between siblings. Stage 1 has already removed every such box
//!   between two internal table or caption boxes (rule 1.4), so in stages 2
//!   and 3 a white-space-only run between two boxes a rule wraps is itself
//!   a box that rule wraps (rules 2.1 to 2.3) or one that rule 1.4 removed
//!   (rules 3.1 and 3.2); grouping maximal runs of wrapped siblings is the
//!   same thing.
//! - **Out-of-flow elements** ("represented as inline elements of zero width
//!   and height") do not occur: there is no positioning or floating in the
//!   subset.
//! - **§17.4's table wrapper** is made for every table box after the three
//!   stages: it takes the table box's place, with the table's captions
//!   (moved out of the table box, in order) and then the table box as its
//!   children. `caption-side` is not in the subset, so every caption is
//!   above the table (`top`, its initial value).

use super::state::{Group, Place, group_step};
use super::tree::{BoxId, BoxKind, BoxTree, Class};

/// "row group box: A 'table-row-group', 'table-header-group', or
/// 'table-footer-group'".
pub fn is_row_group(c: Class) -> bool {
    c == Class::RowGroup
}

/// "proper table child: A 'table-row' box, row group box, 'table-column'
/// box, 'table-column-group' box, or 'table-caption' box."
pub fn is_proper_table_child(c: Class) -> bool {
    matches!(
        c,
        Class::Row | Class::Column | Class::ColumnGroup | Class::Caption
    ) || is_row_group(c)
}

/// "proper table row parent: A 'table' or 'inline-table' box or row group
/// box".
pub fn is_proper_table_row_parent(c: Class) -> bool {
    matches!(c, Class::Table { .. }) || is_row_group(c)
}

/// "internal table box: A 'table-cell' box, 'table-row' box, row group box,
/// 'table-column' box, or 'table-column-group' box."
pub fn is_internal(c: Class) -> bool {
    matches!(
        c,
        Class::Cell | Class::Row | Class::Column | Class::ColumnGroup
    ) || is_row_group(c)
}

/// "tabular container: A 'table-row' box or proper table row parent".
pub fn is_tabular_container(c: Class) -> bool {
    c == Class::Row || is_proper_table_row_parent(c)
}

/// Rule 1.3's "A box D is a proper table descendant of A if D can be a
/// descendant of A without causing the generation of any intervening
/// 'table' or 'inline-table' boxes": for an internal table or caption box
/// D and a tabular container A, whether stages 2 and 3 can place D under A
/// with only anonymous rows and cells between them. A row takes cells; a
/// row group takes rows and (through an anonymous row) cells; a table takes
/// every proper table child and (through an anonymous row) cells.
pub fn is_proper_table_descendant(d: Class, a: Class) -> bool {
    match a {
        Class::Row => d == Class::Cell,
        Class::RowGroup => matches!(d, Class::Row | Class::Cell),
        Class::Table { .. } => is_proper_table_child(d) || d == Class::Cell,
        _ => false,
    }
}

/// Whether `c` is an anonymous inline box containing only white space (the
/// module's modelling choices).
fn white(c: Class) -> bool {
    c == Class::Text { white: true }
}

/// Stage 1 rules 1.1 and 1.2: whether child `c` of `parent` "is treated as
/// if it had 'display: none'", whatever its siblings.
pub fn irrelevant_1(parent: Class, c: Class) -> bool {
    // 1.1 "All child boxes of a 'table-column' parent are treated as if they
    // had 'display: none'."
    parent == Class::Column
        // 1.2 "If a child C of a 'table-column-group' parent is not a
        // 'table-column' box, then it is treated as if it had 'display:
        // none'."
        || (parent == Class::ColumnGroup && c != Class::Column)
}

/// Stage 1 rules 1.3 and 1.4: whether child `c` of `parent`, whose
/// immediately preceding and following siblings are `before` and `after`,
/// is treated as if it had `display: none`.
pub fn irrelevant_2(parent: Class, c: Class, before: Option<Class>, after: Option<Class>) -> bool {
    let caption_or_internal = |s: Class| s == Class::Caption || is_internal(s);
    // 1.3 "If a child C of a tabular container P is an anonymous inline box
    // that contains only white space, and its immediately preceding and
    // following siblings, if any, are proper table descendants of P and are
    // either 'table-caption' or internal table boxes, then it is treated as
    // if it had 'display: none'."
    let qualifies = |s: Option<Class>| {
        s.is_none_or(|s| caption_or_internal(s) && is_proper_table_descendant(s, parent))
    };
    let rule_3 = is_tabular_container(parent) && white(c) && qualifies(before) && qualifies(after);
    // 1.4 "If a box B is an anonymous inline containing only white space,
    // and is between two immediate siblings each of which is either an
    // internal table box or a 'table-caption' box then B is treated as if
    // it had 'display: none'."
    let rule_4 = white(c)
        && before.is_some_and(caption_or_internal)
        && after.is_some_and(caption_or_internal);
    rule_3 || rule_4
}

/// Stage 2, "Generate missing child wrappers": the anonymous box that wraps
/// child `c` of `parent`, if a rule wraps it.
pub fn wrapper_2(parent: Class, c: Class) -> Option<BoxKind> {
    match parent {
        // 2.1 "If a child C of a 'table' or 'inline-table' box is not a
        // proper table child, then generate an anonymous 'table-row' box
        // around C and all consecutive siblings of C that are not proper
        // table children."
        Class::Table { .. } if !is_proper_table_child(c) => Some(BoxKind::Row),
        // 2.2 "If a child C of a row group box is not a 'table-row' box, then
        // generate an anonymous 'table-row' box around C and all consecutive
        // siblings of C that are not 'table-row' boxes."
        Class::RowGroup if c != Class::Row => Some(BoxKind::Row),
        // 2.3 "If a child C of a 'table-row' box is not a 'table-cell', then
        // generate an anonymous 'table-cell' box around C and all
        // consecutive siblings of C that are not 'table-cell' boxes."
        Class::Row if c != Class::Cell => Some(BoxKind::Cell),
        _ => None,
    }
}

/// Stage 3 rule 3.1: "For each 'table-cell' box C in a sequence of
/// consecutive internal table and 'table-caption' siblings, if C's parent
/// is not a 'table-row' then generate an anonymous 'table-row' box around C
/// and all consecutive siblings of C that are 'table-cell' boxes." (A cell
/// is itself such a sequence.)
pub fn wrapper_3_1(parent: Class, c: Class) -> Option<BoxKind> {
    (c == Class::Cell && parent != Class::Row).then_some(BoxKind::Row)
}

/// Rule 3.2's "misparented": whether proper table child `c` is misparented
/// under `parent`.
pub fn is_misparented(parent: Class, c: Class) -> bool {
    let table = matches!(parent, Class::Table { .. });
    match c {
        // "A 'table-row' is misparented if its parent is neither a row group
        // box nor a 'table' or 'inline-table' box."
        Class::Row => !is_row_group(parent) && !table,
        // "A 'table-column' box is misparented if its parent is neither a
        // 'table-column-group' box nor a 'table' or 'inline-table' box."
        Class::Column => parent != Class::ColumnGroup && !table,
        // "A row group box, 'table-column-group' box, or 'table-caption' box
        // is misparented if its parent is neither a 'table' box nor an
        // 'inline-table' box."
        Class::RowGroup | Class::ColumnGroup | Class::Caption => !table,
        _ => false,
    }
}

/// Stage 3 rule 3.2: "For each proper table child C in a sequence of
/// consecutive proper table children, if C is misparented then generate an
/// anonymous 'table' or 'inline-table' box T around C and all consecutive
/// siblings of C that are proper table children. (If C's parent is an
/// 'inline' box, then T must be an 'inline-table' box; otherwise it must be
/// a 'table' box.)"
///
/// The siblings a misparented child is grouped with are proper table
/// children of the same parent, and so misparented too: whether a proper
/// table child is misparented depends only on its kind and its parent's,
/// and a parent under which some proper table child is misparented (any box
/// but a table, a row group or a column group) has every proper table child
/// misparented except a row under a row group and a column under a column
/// group, which stages 1 and 2 leave as the only children those can have.
pub fn wrapper_3_2(parent: Class, c: Class) -> Option<BoxKind> {
    (is_proper_table_child(c) && is_misparented(parent, c)).then_some(BoxKind::Table {
        inline: parent == Class::Inline,
    })
}

/// Regroups the children of `parent`: each maximal run of consecutive
/// children that `wrapper` wraps goes into a new anonymous box of the kind
/// it gives for the run's first ([`group_step`]).
fn regroup(tree: &mut BoxTree, parent: BoxId, wrapper: impl Fn(Class) -> Option<BoxKind>) {
    let children = tree.children(parent).to_vec();
    let mut list: Vec<BoxId> = Vec::with_capacity(children.len());
    let mut moves: Vec<(BoxId, BoxId)> = Vec::new();
    let mut state = Group::START;
    let mut current: Option<BoxId> = None;
    for c in children {
        let kind = wrapper(tree.class(c));
        let (place, next) = group_step(state, kind.is_some());
        match (place, kind, current) {
            (Place::Open, Some(kind), _) => {
                let w = tree.add(kind, None);
                list.push(w);
                moves.push((w, c));
                current = Some(w);
            }
            (Place::Join, _, Some(w)) => moves.push((w, c)),
            // `Keep`, and the cases `group_step`'s contract excludes.
            _ => list.push(c),
        }
        state = next;
    }
    tree.set_children(parent, list);
    for (w, c) in moves {
        tree.append(w, c);
    }
}

/// Stage 1, "Remove irrelevant boxes", over the whole tree.
pub fn stage_1(tree: &mut BoxTree) {
    for parent in tree.preorder() {
        let p = tree.class(parent);
        // 1.1 and 1.2.
        let kept: Vec<BoxId> = tree
            .children(parent)
            .iter()
            .copied()
            .filter(|&c| !irrelevant_1(p, tree.class(c)))
            .collect();
        // 1.3 and 1.4, with the siblings that remain.
        let classes: Vec<Class> = kept.iter().map(|&c| tree.class(c)).collect();
        let mut out = Vec::with_capacity(kept.len());
        for (i, &c) in kept.iter().enumerate() {
            let before = i.checked_sub(1).and_then(|j| classes.get(j)).copied();
            let after = i.checked_add(1).and_then(|j| classes.get(j)).copied();
            let class = classes.get(i).copied().unwrap_or(Class::Root);
            if !irrelevant_2(p, class, before, after) {
                out.push(c);
            }
        }
        if out.len() != tree.children(parent).len() {
            tree.set_children(parent, out);
        }
    }
}

/// Runs `regroup` with `wrapper` on every box, top down: a box's children
/// are regrouped before the walk goes into them (and into the wrappers).
/// Iterative; every box is visited once, and a wrapper is a new box.
fn top_down(tree: &mut BoxTree, wrapper: impl Fn(Class, Class) -> Option<BoxKind>) {
    let mut stack = vec![BoxTree::ROOT];
    let mut seen: Vec<bool> = Vec::new();
    // Each box is pushed once, by its parent; a wrapper made here is pushed
    // once too, so the loop ends when the stack is empty.
    while let Some(b) = stack.pop() {
        if seen.len() < tree.boxes.len() {
            seen.resize(tree.boxes.len(), false);
        }
        match seen.get_mut(b) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        let p = tree.class(b);
        regroup(tree, b, |c| wrapper(p, c));
        stack.extend(tree.children(b).iter().rev());
    }
}

/// Stage 2, "Generate missing child wrappers", over the whole tree.
pub fn stage_2(tree: &mut BoxTree) {
    top_down(tree, wrapper_2);
}

/// Stage 3, "Generate missing parents", over the whole tree: rule 3.1 then
/// rule 3.2 on each box's children.
pub fn stage_3(tree: &mut BoxTree) {
    top_down(tree, wrapper_3_1);
    top_down(tree, wrapper_3_2);
}

/// §17.4: a table wrapper box around every table box, holding the table's
/// captions and then the table box.
pub fn wrappers(tree: &mut BoxTree) {
    for table in tree.preorder() {
        let Some(BoxKind::Table { inline }) = tree.get(table).map(|b| b.kind.clone()) else {
            continue;
        };
        let Some(parent) = tree.get(table).and_then(|b| b.parent) else {
            continue;
        };
        let node = tree.get(table).and_then(|b| b.node);
        let wrapper = tree.add(BoxKind::TableWrapper { inline }, node);
        let siblings: Vec<BoxId> = tree
            .children(parent)
            .iter()
            .map(|&c| if c == table { wrapper } else { c })
            .collect();
        tree.set_children(parent, siblings);
        let (captions, rest): (Vec<BoxId>, Vec<BoxId>) = tree
            .children(table)
            .iter()
            .partition(|&&c| tree.class(c) == Class::Caption);
        tree.set_children(table, rest);
        for c in captions {
            tree.append(wrapper, c);
        }
        tree.append(wrapper, table);
    }
}

/// §17.2.1's three stages, then §17.4's wrappers.
pub fn anonymous_table_objects(tree: &mut BoxTree) {
    stage_1(tree);
    stage_2(tree);
    stage_3(tree);
    wrappers(tree);
}
