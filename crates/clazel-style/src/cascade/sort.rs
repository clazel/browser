//! CSS Cascade 4 §6.1 "Cascade Sorting Order", and the rollback of §7.3.4 `revert` (with
//! CSS Cascade 5 §7.3.5's `revert-layer`), over the declarations of one property on one
//! element.
//!
//! CSS Cascade 4, W3C Candidate Recommendation Snapshot of 13 January 2022,
//! <https://www.w3.org/TR/2022/CR-css-cascade-4-20220113/>; CSS Cascade 5 of the same date,
//! <https://www.w3.org/TR/2022/CR-css-cascade-5-20220113/>, for `revert-layer` only.
//!
//! §6.1: "The cascade sorts declarations according to the following criteria, in descending
//! order of priority: Origin and Importance ... Context ... Specificity ... Order of
//! Appearance". A [`Priority`] holds the four criteria, and its derived order is that
//! sort: two priorities compare by their [`Level`] first, then (one encapsulation context,
//! so the second criterion never separates two declarations) whether they are
//! element-attached, then specificity, then order of appearance. The winning declaration
//! of a property is the greatest.

use crate::values::Wide;

/// §6.1 "Origin and Importance", with §6.4's presentational hint origin, ascending (a later
/// variant wins). From §6.1: "The precedence of the various origins is, in descending
/// order: Transition declarations, Important user agent declarations, Important user
/// declarations, Important author declarations, Animation declarations, Normal author
/// declarations, Normal user declarations, Normal user agent declarations". There are no
/// transitions, animations or user style sheets in Phase 5 (the user origin is empty, see
/// `cascade/mod.rs`), and presentational hints are never important (HTML §15.2 gives them
/// as declarations without `!important`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Level {
    /// Normal user agent declarations.
    UaNormal,
    /// §6.4: "a special-purpose author presentational hint origin between the regular user
    /// origin and the author origin". (CSS 2.1 §6.4.4 instead treats hints "as if they were
    /// inserted at the start of the author style sheet" with specificity zero; nothing in
    /// the subset tells the two apart, since a hint is never important and every author
    /// rule follows it.)
    Hint,
    /// Normal author declarations.
    AuthorNormal,
    /// Important author declarations.
    AuthorImportant,
    /// Important user agent declarations.
    UaImportant,
}

impl Level {
    /// The level of a declaration from a user agent (`ua`) or author style sheet, with its
    /// `!important` flag (§6.3).
    pub fn of(ua: bool, important: bool) -> Level {
        match (ua, important) {
            (true, false) => Level::UaNormal,
            (true, true) => Level::UaImportant,
            (false, false) => Level::AuthorNormal,
            (false, true) => Level::AuthorImportant,
        }
    }

    /// True for the user agent origin.
    pub fn is_ua(self) -> bool {
        matches!(self, Level::UaNormal | Level::UaImportant)
    }
}

/// A selector's specificity (Selectors 4 §17†), compared A, then B, then C.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Specificity {
    /// IDs.
    pub a: u32,
    /// Classes, attributes and pseudo-classes.
    pub b: u32,
    /// Types and pseudo-elements.
    pub c: u32,
}

/// A declaration's place in §6.1's sort. The derived order compares the fields in the order
/// they are declared, which is the order of §6.1's criteria.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Priority {
    /// "Origin and Importance".
    pub level: Level,
    /// "Specificity", first part: "declarations that do not belong to a style rule (such as
    /// the contents of a style attribute) are considered to have a specificity higher than
    /// any selector". True for a `style` attribute's declarations (CSS Style Attributes §4).
    pub attached: bool,
    /// "Specificity": "Each declaration has the same specificity as the style rule it
    /// appears in." Zero for declarations that belong to no rule.
    pub specificity: Specificity,
    /// "Order of Appearance": "The last declaration in document order wins." The position of
    /// the declaration in the order [`super::rules`] reads the sources: the user agent
    /// sheets, the hints, then the author sheets in the order `sources::Sources::rules_for`
    /// gives ("concatenated in linking order"), then the `style` attribute ("all placed
    /// after any style sheets"). It only ever separates declarations of one level.
    pub order: u32,
}

/// One declared value of one property on one element: its priority and whether it is a
/// CSS-wide keyword that rolls the cascade back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Candidate {
    /// Its place in the sort.
    pub priority: Priority,
    /// The CSS-wide keyword it is, if any.
    pub wide: Option<Wide>,
}

/// Sort `list` by priority, ascending, so that the winner is last (§6.1). Stable, so equal
/// priorities (which [`Priority::order`] never gives two declarations) keep their order.
pub fn sort(list: &mut [Candidate]) {
    list.sort_by_key(|c| c.priority);
}

/// The declarations a rollback has set aside: §7.3.4 and §7.3.5 calculate the specified
/// value "as if no ... rules were specified" in some origins or layers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
struct Excluded {
    /// Every author declaration and every presentational hint (`revert` from the author
    /// origin, which "for the purpose of the revert keyword ... is considered part of the
    /// author origin", §6.4).
    author_and_hints: bool,
    /// Every author declaration, but not the hints (`revert-layer` from the author origin:
    /// §6.4 makes the hint origin "an independent origin" for the cascade, and CSS Cascade 5
    /// §7.3.5's note: "If there are no lower-priority declarations in the same cascade
    /// origin as the revert-layer value, the cascaded value will roll back to the previous
    /// origin").
    author: bool,
    /// The important `style` attribute declarations (`revert-layer` there: "For
    /// revert-layer in important element-attached styles, however, it only reverts the
    /// element-attached styles and the intervening animation origin, and not any of the
    /// intervening author-origin important rules").
    attached_important: bool,
}

impl Excluded {
    fn excludes(self, p: Priority) -> bool {
        let author = matches!(p.level, Level::AuthorNormal | Level::AuthorImportant);
        (self.author_and_hints && (author || p.level == Level::Hint))
            || (self.author && author)
            || (self.attached_important && p.level == Level::AuthorImportant && p.attached)
    }
}

/// The most rollbacks one cascade can need: each sets aside a strictly larger set of
/// [`Excluded`]'s three, and a rollback in the user agent origin ends the walk.
const MAX_ROLLBACKS: usize = 4;

/// §4.2 "Cascaded Values": "the declared value that wins the cascade", given every declared
/// value of the property on the element in `sorted` (ascending, as [`sort`] leaves it), with
/// §7.3.4 `revert` and §7.3.5 `revert-layer` resolved by rolling the cascade back. The index
/// of the winner, which is never `revert` or `revert-layer`; `None` if there is none ("the
/// cascade does not result in a value", §7), so the property is defaulted. A rollback
/// "Equivalent to unset" is `None` too, which defaulting makes `unset`.
pub fn cascaded(sorted: &[Candidate]) -> Option<usize> {
    let mut excluded = Excluded::default();
    for _ in 0..MAX_ROLLBACKS {
        // The greatest declaration not set aside.
        let i = sorted
            .iter()
            .rposition(|c| !excluded.excludes(c.priority))?;
        let c = sorted.get(i)?;
        match c.wide {
            // §7.3.4: "If the cascaded value of a property is the revert keyword, the
            // behavior depends on the cascade origin to which the declaration belongs":
            Some(Wide::Revert) => {
                if c.priority.level.is_ua() {
                    // "user-agent origin: Equivalent to unset."
                    return None;
                }
                // "author origin: Rolls back the cascaded value to the user level, so that
                // the specified value is calculated as if no author-origin rules were
                // specified for this property on this element." (The user level is empty,
                // so this reaches the user agent's declarations.)
                excluded.author_and_hints = true;
            }
            // CSS Cascade 5 §7.3.5: "the cascaded value is rolled back to the layer below,
            // so that the specified value is calculated as if no rules were specified in the
            // current cascade layer—or between its normal and important levels in the
            // cascade—for this property on this element." With no `@layer` rules, each
            // origin's declarations are one layer (CSS Cascade 5's implicit outer layer).
            Some(Wide::RevertLayer) => {
                if c.priority.level.is_ua() {
                    // The user agent origin is the last: nothing is below it.
                    return None;
                }
                if c.priority.level == Level::AuthorImportant && c.priority.attached {
                    excluded.attached_important = true;
                } else {
                    excluded.author = true;
                }
            }
            _ => return Some(i),
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cand(level: Level, attached: bool, spec: (u32, u32, u32), order: u32) -> Candidate {
        Candidate {
            priority: Priority {
                level,
                attached,
                specificity: Specificity {
                    a: spec.0,
                    b: spec.1,
                    c: spec.2,
                },
                order,
            },
            wide: None,
        }
    }

    fn winner(mut list: Vec<Candidate>) -> Option<u32> {
        sort(&mut list);
        cascaded(&list)
            .and_then(|i| list.get(i))
            .map(|c| c.priority.order)
    }

    #[test]
    fn origin_importance_specificity_order() {
        use Level::*;
        // Specificity beats order; order breaks ties.
        assert_eq!(
            winner(vec![
                cand(AuthorNormal, false, (0, 1, 0), 1),
                cand(AuthorNormal, false, (0, 0, 1), 2),
            ]),
            Some(1)
        );
        assert_eq!(
            winner(vec![
                cand(AuthorNormal, false, (0, 1, 0), 1),
                cand(AuthorNormal, false, (0, 1, 0), 2),
            ]),
            Some(2)
        );
        // A style attribute beats any selector; !important beats both.
        assert_eq!(
            winner(vec![
                cand(AuthorNormal, false, (9, 9, 9), 1),
                cand(AuthorNormal, true, (0, 0, 0), 2),
            ]),
            Some(2)
        );
        assert_eq!(
            winner(vec![
                cand(AuthorImportant, false, (0, 0, 1), 1),
                cand(AuthorNormal, true, (0, 0, 0), 2),
            ]),
            Some(1)
        );
        // Hints lose to any author rule, and beat the user agent's normal rules; the user
        // agent's important rules beat everything.
        assert_eq!(
            winner(vec![
                cand(Hint, false, (0, 1, 1), 1),
                cand(AuthorNormal, false, (0, 0, 0), 2),
                cand(UaNormal, false, (1, 0, 0), 3),
            ]),
            Some(2)
        );
        assert_eq!(
            winner(vec![
                cand(UaImportant, false, (0, 0, 1), 1),
                cand(AuthorImportant, true, (0, 0, 0), 2),
            ]),
            Some(1)
        );
    }

    #[test]
    fn revert_and_revert_layer() {
        use Level::*;
        let with = |mut c: Candidate, w: Wide| {
            c.wide = Some(w);
            c
        };
        let ua = cand(UaNormal, false, (0, 0, 1), 1);
        let hint = cand(Hint, false, (0, 1, 1), 2);
        let author = cand(AuthorNormal, false, (0, 1, 0), 3);
        // `revert` from the author origin skips the hints (part of the author origin for
        // `revert`) and reaches the user agent's rule.
        let r = with(cand(AuthorNormal, false, (0, 2, 0), 4), Wide::Revert);
        assert_eq!(winner(vec![ua, hint, author, r]), Some(1));
        // `revert-layer` from the author origin stops at the hints.
        let rl = with(cand(AuthorNormal, false, (0, 2, 0), 4), Wide::RevertLayer);
        assert_eq!(winner(vec![ua, hint, author, rl]), Some(2));
        // `revert` in the user agent origin is `unset`.
        let ur = with(cand(UaNormal, false, (0, 1, 0), 5), Wide::Revert);
        assert_eq!(winner(vec![ua, ur]), None);
        // Important `revert-layer` in a `style` attribute reverts only the attribute.
        let sheet = cand(AuthorImportant, false, (0, 1, 0), 6);
        let attr = with(cand(AuthorImportant, true, (0, 0, 0), 7), Wide::RevertLayer);
        assert_eq!(winner(vec![ua, author, sheet, attr]), Some(6));
        // A chain of rollbacks ends.
        let r2 = with(cand(UaImportant, false, (0, 0, 0), 8), Wide::RevertLayer);
        assert_eq!(winner(vec![ua, rl, r2]), None);
        // Other keywords win as values, to be defaulted later.
        let inh = with(cand(AuthorNormal, false, (0, 0, 0), 9), Wide::Inherit);
        assert_eq!(winner(vec![ua, inh]), Some(9));
    }
}
