//! The cascade, inheritance and computed values (phase-5.md item 5.7).
//!
//! [`cascade`] gives every element of a document its computed values for the subset: it
//! finds the declarations that apply to the element (from the user agent style sheet, the
//! presentational hints, the author style sheets and its `style` attribute), sorts them as
//! CSS Cascade 4 §6.1 says, takes each property's winner (rolling back for `revert`),
//! defaults the properties with no winner or a CSS-wide keyword (§7), and computes each
//! value (§4.4), parents before children. The result is a [`ComputedTable`], one entry per
//! node id, which items 5.13 to 5.16 (layout) and 5.20 (the renderer) read.
//!
//! The standards, each pinned in the module that transcribes it:
//!
//! - CSS Cascade 4, W3C Candidate Recommendation Snapshot of 13 January 2022
//!   (<https://www.w3.org/TR/2022/CR-css-cascade-4-20220113/>): §4 value processing, §5
//!   filtering ([`rules`]), §6.1 the sorting order, §6.2 origins, §6.3 importance, §6.4
//!   presentational hints ([`sort`]), §7 defaulting ([`compute`]); CSS Cascade 5 of the same
//!   date for `revert-layer` only. Sections marked † in other modules are from documents
//!   read at their current drafts, not at a pinned commit (phase-5.md's convention).
//! - CSS 2.1 §6.4.4 (presentational hints) and the property definition tables of the
//!   specifications `values/` cites ([`computed`], [`compute`]).
//! - HTML at commit 4c54fae1 (`data/html-4c54fae1/`): §15's user agent style sheet
//!   ([`ua`]), presentational hints ([`hints`]) and the microsyntaxes they use ([`legacy`]).
//! - CSS Logical Properties 1 for the flow-relative properties the user agent sheet uses
//!   ([`logical`]).
//!
//! # Modelling choices
//!
//! - **Origins.** The user agent origin holds HTML §15's sheet; the **user origin is
//!   empty** (Clazel has no user style sheets yet), so "Important user declarations" and
//!   "Normal user declarations" never occur, and `revert` from the author origin reaches the
//!   user agent's declarations. There are no animations or transitions.
//! - **One encapsulation context** (§6.1 "Context"): no shadow trees, so the context
//!   criterion never separates two declarations.
//! - **Presentational hints** enter the cascade in §6.4's "author presentational hint
//!   origin", between the user and author origins, with **specificity zero** (CSS 2.1
//!   §6.4.4: "given a specificity equal to zero"), the hints of the standard's CSS blocks
//!   (`data/hints.css`) before those of its prose ([`hints`]). Nothing in the subset tells
//!   §6.4's origin from CSS 2.1's "start of the author style sheet".
//! - **Order of appearance** is the order the sources are read: the user agent sheet, its
//!   quirks-mode rules, the rules HTML gives in prose ([`ua::prose`]), the hints, the author
//!   sheets in `sources::Sources::rules_for`'s order, and the `style` attribute last. Only
//!   declarations of one level and specificity are ever compared by it.
//! - **Filtering** (§5): a declaration outside the subset (unknown property or value outside
//!   its grammar) is dropped, as CSS Syntax says; a rule whose selector list
//!   `clazel-selectors` cannot parse is dropped.
//! - **Inheritance** follows the element tree: an element's parent element is its parent
//!   node if that is an element; the document element inherits initial values (§7.2).
//!   Elements in a `template`'s contents are not in the document tree and get no style.
//! - **Computed colours are resolved**: `currentcolor` in `background-color`, the border
//!   colours and `text-decoration-color` computes to the element's `color`. CSS Color 4
//!   keeps the keyword as the computed value, so that a descendant inheriting one of these
//!   (only through `inherit`, since none is inherited) would see its own colour; that case
//!   is the one difference, and nothing in the subset's exit page uses it.
//! - **Writing mode** is `horizontal-tb` and `ltr` everywhere ([`logical`], and `text-align:
//!   match-parent`).
//! - **Lengths** are 1/64 px in an `i32`, as `values/` converts them; computed lengths are
//!   rounded there once.
//! - **The walk is iterative**, with an explicit stack and at most one step per node, and
//!   visits each node at most once ([`preorder`]).

pub mod computed;
pub mod sort;
