//! Kani harnesses (Tier 1) for the media query evaluator. Compiled only under `cargo kani`.
//!
//! Each harness runs one operation on **every** input within the bound in its comment. Kani
//! checks that no panic, arithmetic overflow or read outside a slice is reachable. The
//! bounds, times and peak memory are also in the crate's README.
//!
//! - **The logic** ([`kleene_any`]): §3.1's three-valued `not`, `and` and `or`, on every pair
//!   of values, with the laws Kleene's logic has.
//! - **A feature** ([`feature_any`]): any `<media-feature>` the parser can build or not (any
//!   name, prefix, test, comparison, number, unit and identifier) on any device: the length
//!   conversions and comparisons of `width` and `height`, and `orientation`.
//!
//! Not done, each exceeding 8 GB of memory locally even at small bounds (or, for the parser,
//! 12 minutes without finishing), so covered only by the unit tests and the WPT conformance
//! test:
//!
//! - `evaluate_condition` on any postfix list of ops: four ops, with every feature's name
//!   unknown so that no length arithmetic is reached, peaked above 8 GB in 69 s;
//! - `evaluate_query_tri` on any query with up to three ops (above 8 GB in 118 s), and
//!   `evaluate` on any list of up to three queries of one op each (above 8 GB at 686 s);
//! - `parse_media_query_list` on any list of up to four tokens over three code points (still
//!   running after 12 minutes);
//! - [`super::tokens::Toks`] and [`super::media::parse`], which call `clazel-css`'s
//!   tokenizer (too slow under Kani even at one code point, as in `values/`; the tokenizer
//!   is proven by Verus in that crate); serialization; and the style sheet walk and
//!   document collection (`sheet.rs`, `mod.rs`), which call the tokenizer and the parser.
//!
//! The evaluator's loops are over the op list and the stack, each bounded by the list's
//! length, and every operation in them is a total match on small enums; the parser's
//! recursion is bounded by `MAX_DEPTH`.

use super::media::{Device, Name, Prefix, Test, Tri, evaluate_feature};

/// §3.1's logic on every pair of values: `not` is an involution, `and` and `or` commute and
/// are related by De Morgan's laws, and only `true` holds as a boolean.
#[kani::proof]
fn kleene_any() {
    let a: Tri = kani::any();
    let b: Tri = kani::any();
    assert!(a.negate().negate() == a);
    assert!(a.and(b) == b.and(a) && a.or(b) == b.or(a));
    assert!(a.and(b).negate() == a.negate().or(b.negate()));
    assert!(a.or(b).negate() == a.negate().and(b.negate()));
    assert!(Tri::False.and(a) == Tri::False && Tri::True.or(a) == Tri::True);
    assert!(a.holds() == (a == Tri::True));
}

/// [`evaluate_feature`] on any feature and any device; an unknown name is unknown, and
/// `(width)` and `(height)` are true exactly when the viewport's side is not 0 (§2.4.2).
#[kani::proof]
fn feature_any() {
    let f: super::media::Feature = kani::any();
    let d: Device = kani::any();
    let r = evaluate_feature(f, d);
    if let Name::Unknown(_) = f.name {
        assert!(r == Tri::Unknown);
    }
    if f.prefix == Prefix::None && f.test == Test::Boolean {
        match f.name {
            Name::Width => assert!(r == Tri::of(d.width_px64 != 0)),
            Name::Height => assert!(r == Tri::of(d.height_px64 != 0)),
            Name::Orientation => assert!(r == Tri::True),
            Name::Unknown(_) => {}
        }
    }
}
