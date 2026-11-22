//! Lemmas for the proofs of Annex B.1.1's HTML-like comments in
//! [`super::exec`] (`scan_html_close`, `lex_slash_comment`, `lex_lt`,
//! `lex_html_open`, `lex_start`).
//!
//! [`super::spec`]'s `HTMLCloseComment` is `WhiteSpaceSequence?
//! SingleLineDelimitedCommentSequence? --> SingleLineCommentChars?`, and its
//! parts are existentially split. Here:
//!
//! - [`lemma_sl_chars`] and [`lemma_sldc_equiv`] give a `SingleLine
//!   DelimitedComment` a closed form, [`block_close_ok`] with no line
//!   terminator (so its end is the first `*/`, [`lemma_block_close_unique`]);
//! - [`hc_pre`] is the code before the `-->` of an `HTMLCloseComment`: white
//!   space and delimited comments, one after the other. It is tied to the
//!   spec's split by [`lemma_html_close_equiv`], and shown deterministic:
//!   whatever the split, the `-->` is at one place ([`lemma_hc_stuck`],
//!   which says where a scan that cannot go on is);
//! - [`lemma_annex_b_ml`] gives Annex B's `MultiLineComment` (which is
//!   `/* FirstCommentLine? LineTerminator MultiLineCommentChars? */
//!   HTMLCloseComment?`) its closed form: it ends at the first `*/` and holds
//!   a line terminator before it, and then an `HTMLCloseComment` may follow;
//! - the `lemma_html_cm_*` lemmas say which alternatives of Annex B's
//!   `Comment` can start with which code points.
//!
//! Nothing here changes [`super::spec`]; these are facts about it.

#[cfg(verus_only)]
use super::equivalence::{lemma_comment_chars, lemma_is_lit, no_star_slash};
#[cfg(verus_only)]
use super::exec::block_close_ok;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every code point of `s[a..b)` is a `SourceCharacter` that is not a
/// `LineTerminator`.
pub open spec fn no_lt_src(s: Seq<u32>, a: int, b: int) -> bool {
    forall|k: int| a <= k < b ==> is_not_line_terminator(#[trigger] s[k])
}

/// `-->` starts at `b` (and is inside the source text).
pub open spec fn arrow_at(s: Seq<u32>, b: int) -> bool {
    0 <= b && b + 3 <= s.len() && s[b] == 0x2D && s[b + 1] == 0x2D && s[b + 2] == 0x3E
}

/// `SingleLineDelimitedCommentChars` is "no `*/` inside, no line terminator",
/// and `SingleLinePostAsteriskCommentChars` is the same after a `*`: the first
/// code point is not `/`. Both on a non-empty range, by induction on its
/// length (as for `MultiLineCommentChars`, [`lemma_comment_chars`]).
pub proof fn lemma_sl_chars(s: Seq<u32>, a: int, b: int)
    ensures
        single_line_delimited_comment_chars(s, a, b) <==> (0 <= a && a < b && b <= s.len()
            && no_lt_src(s, a, b) && no_star_slash(s, a, b)),
        single_line_post_asterisk_comment_chars(s, a, b) <==> (0 <= a && a < b && b <= s.len()
            && no_lt_src(s, a, b) && s[a] != 0x2F && no_star_slash(s, a, b)),
    decreases b - a,
{
    if 0 <= a && a + 1 < b && b <= s.len() {
        lemma_sl_chars(s, a + 1, b);
        assert(no_star_slash(s, a, b) <==> (no_star_slash(s, a + 1, b) && !(s[a] == 0x2A && s[a
            + 1] == 0x2F))) by {
            if no_star_slash(s, a, b) {
                assert forall|k: int| a + 1 <= k < b - 1 implies !(#[trigger] s[k] == 0x2A && s[k
                    + 1] == 0x2F) by {
                    assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                }
            }
            if no_star_slash(s, a + 1, b) && !(s[a] == 0x2A && s[a + 1] == 0x2F) {
                assert forall|k: int| a <= k < b - 1 implies !(#[trigger] s[k] == 0x2A && s[k
                    + 1] == 0x2F) by {
                    if k > a {
                        assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                    }
                }
            }
        }
        assert(no_lt_src(s, a, b) <==> (is_not_line_terminator(s[a]) && no_lt_src(s, a + 1, b)))
            by {
            if no_lt_src(s, a + 1, b) && is_not_line_terminator(s[a]) {
                assert forall|k: int| a <= k < b implies is_not_line_terminator(#[trigger] s[k]) by {
                    if k > a {
                        assert(is_not_line_terminator(s[k]));
                    }
                }
            }
        }
    }
    if 0 <= a && a + 1 == b && b <= s.len() {
        assert(no_star_slash(s, a, b));
        if is_not_line_terminator(s[a]) {
            assert(no_lt_src(s, a, b)) by {
                assert forall|k: int| a <= k < b implies is_not_line_terminator(#[trigger] s[k]) by {
                    assert(k == a);
                }
            }
        }
        if no_lt_src(s, a, b) {
            assert(is_not_line_terminator(s[a]));
        }
    }
}

/// Annex B's `SingleLineDelimitedComment` is `/*` and the first `*/` with no
/// `LineTerminator` and only `SourceCharacter`s between ([`block_close_ok`]
/// without `multi_line`).
pub proof fn lemma_sldc_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        single_line_delimited_comment(s, i, j) <==> (0 <= i && i + 4 <= j && j <= s.len() && s[i]
            == 0x2F && s[i + 1] == 0x2A && block_close_ok(s, i + 2, j, false)),
{
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_is_lit(s, j - 2, j, seq!['*', '/']);
    if 0 <= i && i + 4 <= j && j <= s.len() {
        if i + 2 < j - 2 {
            lemma_sl_chars(s, i + 2, j - 2);
        }
        if single_line_delimited_comment(s, i, j) {
            assert(block_close_ok(s, i + 2, j, false)) by {
                assert forall|m: int| i + 2 <= m < j - 2 implies (#[trigger] s[m] <= 0x10FFFF
                    && !(s[m] == 0x2A && s[m + 1] == 0x2F) && !is_line_terminator(s[m])) by {
                    assert(no_lt_src(s, i + 2, j - 2));
                    if m < j - 3 {
                        assert(no_star_slash(s, i + 2, j - 2));
                    } else {
                        assert(s[j - 2] == 0x2A);
                    }
                }
            }
        }
        if s[i] == 0x2F && s[i + 1] == 0x2A && block_close_ok(s, i + 2, j, false) {
            if i + 2 < j - 2 {
                assert(no_lt_src(s, i + 2, j - 2)) by {
                    assert forall|k: int| i + 2 <= k < j - 2 implies is_not_line_terminator(
                        #[trigger] s[k],
                    ) by {
                        assert(s[k] <= 0x10FFFF && !is_line_terminator(s[k]));
                    }
                }
                assert(no_star_slash(s, i + 2, j - 2)) by {
                    assert forall|k: int| i + 2 <= k < j - 3 implies !(#[trigger] s[k] == 0x2A
                        && s[k + 1] == 0x2F) by {
                        assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                    }
                }
            }
        }
    }
}

/// A block comment's closing `*/` is the first one.
pub proof fn lemma_block_close_unique(s: Seq<u32>, k: int, e1: int, e2: int, multi_line: bool)
    requires
        block_close_ok(s, k, e1, multi_line),
        block_close_ok(s, k, e2, multi_line),
    ensures
        e1 == e2,
{
    if e1 < e2 {
        assert(k <= e1 - 2 < e2 - 2);
        assert(s[e1 - 2] == 0x2A && s[e1 - 1] == 0x2F);
    }
    if e2 < e1 {
        assert(k <= e2 - 2 < e1 - 2);
        assert(s[e2 - 2] == 0x2A && s[e2 - 1] == 0x2F);
    }
}

/// A closing `*/` that no line terminator is before is the closing `*/` of
/// the version that allows them.
pub proof fn lemma_block_close_single_to_multi(s: Seq<u32>, k: int, e: int)
    requires
        block_close_ok(s, k, e, false),
    ensures
        block_close_ok(s, k, e, true),
{
}

/// The `/*` of a delimited comment, and a delimited comment's end is unique.
pub proof fn lemma_sldc_start(s: Seq<u32>, i: int, a: int)
    requires
        single_line_delimited_comment(s, i, a),
    ensures
        0 <= i,
        i + 4 <= a,
        a <= s.len(),
        s[i] == 0x2F,
        s[i + 1] == 0x2A,
{
    lemma_sldc_equiv(s, i, a);
}

/// A delimited comment from `i` ends at one place.
pub proof fn lemma_sldc_unique(s: Seq<u32>, i: int, a1: int, a2: int)
    requires
        single_line_delimited_comment(s, i, a1),
        single_line_delimited_comment(s, i, a2),
    ensures
        a1 == a2,
{
    lemma_sldc_equiv(s, i, a1);
    lemma_sldc_equiv(s, i, a2);
    lemma_block_close_unique(s, i + 2, a1, a2, false);
}

// ---------------------------------------------------------------------
// The code before the `-->` of an HTMLCloseComment.
// ---------------------------------------------------------------------

/// White space and delimited comments, one after the other, from `i` to `b`:
/// what an `HTMLCloseComment` has before its `-->`.
pub open spec fn hc_pre(s: Seq<u32>, i: int, b: int) -> bool
    decreases b - i,
{
    0 <= i && i <= b && b <= s.len() && (i == b || (white_space(s, i, i + 1) && hc_pre(
        s,
        i + 1,
        b,
    )) || exists|a: int|
        #![trigger single_line_delimited_comment(s, i, a)]
        i < a && a <= b && single_line_delimited_comment(s, i, a) && hc_pre(s, a, b))
}

/// What the first step of [`hc_pre`] is when it is not empty.
pub proof fn lemma_hc_first(s: Seq<u32>, i: int, b: int)
    requires
        hc_pre(s, i, b),
        i < b,
    ensures
        (white_space(s, i, i + 1) && hc_pre(s, i + 1, b)) || (exists|a: int|
            #![trigger single_line_delimited_comment(s, i, a)]
            i < a && a <= b && single_line_delimited_comment(s, i, a) && hc_pre(s, a, b)),
{
}

/// A run of white space is [`hc_pre`].
pub proof fn lemma_hc_ws_run(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        forall|k: int| i <= k < j ==> #[trigger] white_space(s, k, k + 1),
    ensures
        hc_pre(s, i, j),
    decreases j - i,
{
    if i < j {
        assert(white_space(s, i, i + 1));
        lemma_hc_ws_run(s, i + 1, j);
    }
}

/// A delimited comment is [`hc_pre`].
pub proof fn lemma_hc_sldc(s: Seq<u32>, i: int, a: int)
    requires
        single_line_delimited_comment(s, i, a),
    ensures
        hc_pre(s, i, a),
{
    lemma_sldc_start(s, i, a);
    assert(hc_pre(s, a, a));
}

/// [`hc_pre`] is closed under concatenation.
pub proof fn lemma_hc_cat(s: Seq<u32>, i: int, m: int, j: int)
    requires
        hc_pre(s, i, m),
        hc_pre(s, m, j),
    ensures
        hc_pre(s, i, j),
    decreases m - i,
{
    if i < m {
        if white_space(s, i, i + 1) {
            lemma_hc_first_ws(s, i, m);
            lemma_hc_cat(s, i + 1, m, j);
        } else {
            lemma_hc_first_sldc(s, i, m);
            let a = choose|a: int|
                i < a && a <= m && single_line_delimited_comment(s, i, a) && hc_pre(s, a, m);
            lemma_hc_cat(s, a, m, j);
            assert(i < a && a <= j && single_line_delimited_comment(s, i, a) && hc_pre(s, a, j));
        }
    }
}

/// A white space code point is not `/` or `-`.
pub proof fn lemma_ws_not_slash_dash(s: Seq<u32>, i: int)
    requires
        white_space(s, i, i + 1),
    ensures
        s[i] != 0x2F,
        s[i] != 0x2D,
{
}

/// A non-empty [`hc_pre`] that starts with white space goes on after it.
pub proof fn lemma_hc_first_ws(s: Seq<u32>, i: int, b: int)
    requires
        hc_pre(s, i, b),
        i < b,
        white_space(s, i, i + 1),
    ensures
        hc_pre(s, i + 1, b),
{
    lemma_hc_first(s, i, b);
    lemma_ws_not_slash_dash(s, i);
    if !hc_pre(s, i + 1, b) {
        let a = choose|a: int|
            i < a && a <= b && single_line_delimited_comment(s, i, a) && hc_pre(s, a, b);
        lemma_sldc_start(s, i, a);
        assert(false);
    }
}

/// A non-empty [`hc_pre`] that does not start with white space starts with a
/// delimited comment.
pub proof fn lemma_hc_first_sldc(s: Seq<u32>, i: int, b: int)
    requires
        hc_pre(s, i, b),
        i < b,
        !white_space(s, i, i + 1),
    ensures
        exists|a: int|
            #![trigger single_line_delimited_comment(s, i, a)]
            i < a && a <= b && single_line_delimited_comment(s, i, a) && hc_pre(s, a, b),
{
    lemma_hc_first(s, i, b);
}

/// The first step of a non-empty [`hc_pre`] starts with white space or `/*`.
pub proof fn lemma_hc_start(s: Seq<u32>, i: int, b: int)
    requires
        hc_pre(s, i, b),
        i < b,
    ensures
        white_space(s, i, i + 1) || (s[i] == 0x2F && s[i + 1] == 0x2A),
{
    lemma_hc_first(s, i, b);
    if !white_space(s, i, i + 1) {
        let a = choose|a: int|
            i < a && a <= b && single_line_delimited_comment(s, i, a) && hc_pre(s, a, b);
        lemma_sldc_start(s, i, a);
    }
}

/// If `s[i..x)` and `s[i..y)` are both [`hc_pre`], so is `s[x..y)`: the
/// steps are determined by the code points that start them.
pub proof fn lemma_hc_prefix(s: Seq<u32>, i: int, x: int, y: int)
    requires
        hc_pre(s, i, x),
        hc_pre(s, i, y),
        x <= y,
    ensures
        hc_pre(s, x, y),
    decreases x - i,
{
    if i < x {
        if white_space(s, i, i + 1) {
            lemma_hc_first_ws(s, i, x);
            lemma_hc_first_ws(s, i, y);
            lemma_hc_prefix(s, i + 1, x, y);
        } else {
            lemma_hc_first_sldc(s, i, x);
            lemma_hc_first_sldc(s, i, y);
            let a1 = choose|a: int|
                i < a && a <= x && single_line_delimited_comment(s, i, a) && hc_pre(s, a, x);
            let a2 = choose|a: int|
                i < a && a <= y && single_line_delimited_comment(s, i, a) && hc_pre(s, a, y);
            lemma_sldc_unique(s, i, a1, a2);
            lemma_hc_prefix(s, a1, x, y);
        }
    }
}

/// Where a scan of an `HTMLCloseComment` that is at `j` finds the `-->`.
/// The code before the `-->` is [`hc_pre`] to `j`, and the code point at `j`
/// is not white space and no delimited comment starts there (so the scan
/// cannot go on); then every `-->` that follows [`hc_pre`] code from `i` is
/// the one at `j` if there is one.
pub proof fn lemma_hc_stuck(s: Seq<u32>, i: int, j: int, b: int)
    requires
        hc_pre(s, i, j),
        hc_pre(s, i, b),
        arrow_at(s, b),
        !white_space(s, j, j + 1),
        forall|a: int| !single_line_delimited_comment(s, j, a),
    ensures
        b == j,
{
    if b < j {
        lemma_hc_prefix(s, i, b, j);
        lemma_hc_start(s, b, j);
        if white_space(s, b, b + 1) {
            lemma_ws_not_slash_dash(s, b);
        }
    }
    if j < b {
        lemma_hc_prefix(s, i, j, b);
        lemma_hc_first_sldc(s, j, b);
        let a = choose|a: int|
            j < a && a <= b && single_line_delimited_comment(s, j, a) && hc_pre(s, a, b);
        assert(false);
    }
}

/// The part of `HTMLCloseComment` after the `-->`: no line terminator up to
/// `j`.
pub open spec fn hc_tail(s: Seq<u32>, b: int, j: int) -> bool {
    b + 3 <= j && j <= s.len() && no_lt_src(s, b + 3, j)
}

/// A `WhiteSpaceSequence` is white space throughout.
pub proof fn lemma_wss_ws(s: Seq<u32>, i: int, j: int)
    requires
        white_space_sequence(s, i, j),
    ensures
        forall|k: int| i <= k < j ==> #[trigger] white_space(s, k, k + 1),
    decreases j - i,
{
    if j > i + 1 {
        lemma_wss_ws(s, i + 1, j);
    }
    assert forall|k: int| i <= k < j implies #[trigger] white_space(s, k, k + 1) by {
        if k > i {
            assert(white_space_sequence(s, i + 1, j));
        }
    }
}

/// A `SingleLineDelimitedCommentSequence` is [`hc_pre`].
pub proof fn lemma_sldcs_hc(s: Seq<u32>, i: int, j: int)
    requires
        single_line_delimited_comment_sequence(s, i, j),
    ensures
        hc_pre(s, i, j),
    decreases j - i,
{
    let (a, b) = choose|a: int, b: int|
        i < a && a <= b && b <= j && single_line_delimited_comment(s, i, a) && opt(
            a,
            b,
            white_space_sequence(s, a, b),
        ) && opt(b, j, single_line_delimited_comment_sequence(s, b, j));
    lemma_hc_sldc(s, i, a);
    if a < b {
        lemma_wss_ws(s, a, b);
        lemma_hc_ws_run(s, a, b);
    }
    assert(hc_pre(s, a, b));
    lemma_hc_cat(s, i, a, b);
    if b < j {
        lemma_sldcs_hc(s, b, j);
        lemma_hc_cat(s, i, b, j);
    }
}

/// [`hc_pre`] is a split of the spec: `WhiteSpaceSequence?` then
/// `SingleLineDelimitedCommentSequence?`.
pub proof fn lemma_hc_split(s: Seq<u32>, i: int, b: int)
    requires
        hc_pre(s, i, b),
    ensures
        exists|a: int|
            i <= a && a <= b && opt(i, a, white_space_sequence(s, i, a)) && opt(
                a,
                b,
                single_line_delimited_comment_sequence(s, a, b),
            ),
    decreases b - i,
{
    if i == b {
        assert(i <= b && opt(i, b, white_space_sequence(s, i, b)) && opt(
            b,
            b,
            single_line_delimited_comment_sequence(s, b, b),
        ));
    } else {
        if white_space(s, i, i + 1) {
            lemma_hc_first_ws(s, i, b);
            lemma_hc_split(s, i + 1, b);
            let a = choose|a: int|
                i + 1 <= a && a <= b && opt(i + 1, a, white_space_sequence(s, i + 1, a)) && opt(
                    a,
                    b,
                    single_line_delimited_comment_sequence(s, a, b),
                );
            assert(nonempty(s, i, a));
            assert(opt(i, a, white_space_sequence(s, i, a)));
            assert(i <= a && a <= b && opt(i, a, white_space_sequence(s, i, a)) && opt(
                a,
                b,
                single_line_delimited_comment_sequence(s, a, b),
            ));
        } else {
            lemma_hc_first_sldc(s, i, b);
            let a1 = choose|a: int|
                i < a && a <= b && single_line_delimited_comment(s, i, a) && hc_pre(s, a, b);
            lemma_hc_split(s, a1, b);
            let a2 = choose|a: int|
                a1 <= a && a <= b && opt(a1, a, white_space_sequence(s, a1, a)) && opt(
                    a,
                    b,
                    single_line_delimited_comment_sequence(s, a, b),
                );
            assert(nonempty(s, i, b));
            assert(i < a1 && a1 <= a2 && a2 <= b && single_line_delimited_comment(s, i, a1) && opt(
                a1,
                a2,
                white_space_sequence(s, a1, a2),
            ) && opt(a2, b, single_line_delimited_comment_sequence(s, a2, b)));
            assert(single_line_delimited_comment_sequence(s, i, b));
            assert(opt(i, i, white_space_sequence(s, i, i)));
        }
    }
}

/// `HTMLCloseComment` as a closed form: [`hc_pre`] code from `i` to a `-->`
/// at `b`, and then no line terminator to `j`.
pub proof fn lemma_html_close_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        html_close_comment(s, i, j) <==> (0 <= i && i < j && j <= s.len() && exists|b: int|
            #![trigger arrow_at(s, b)]
            hc_pre(s, i, b) && arrow_at(s, b) && hc_tail(s, b, j)),
{
    if html_close_comment(s, i, j) {
        let (a, b) = choose|a: int, b: int| html_close_comment_split(s, i, a, b, j);
        lemma_is_lit(s, b, b + 3, seq!['-', '-', '>']);
        if i < a {
            lemma_wss_ws(s, i, a);
            lemma_hc_ws_run(s, i, a);
        } else {
            assert(hc_pre(s, i, a));
        }
        if a < b {
            lemma_sldcs_hc(s, a, b);
        } else {
            assert(hc_pre(s, a, b));
        }
        lemma_hc_cat(s, i, a, b);
        assert(arrow_at(s, b));
        assert(hc_tail(s, b, j)) by {
            if b + 3 < j {
                assert(no_lt_src(s, b + 3, j));
            }
        }
    }
    if 0 <= i && i < j && j <= s.len() {
        if exists|b: int| #![trigger arrow_at(s, b)] hc_pre(s, i, b) && arrow_at(s, b) && hc_tail(
            s,
            b,
            j,
        ) {
            let b = choose|b: int|
                #![trigger arrow_at(s, b)]
                hc_pre(s, i, b) && arrow_at(s, b) && hc_tail(s, b, j);
            lemma_hc_split(s, i, b);
            let a = choose|a: int|
                i <= a && a <= b && opt(i, a, white_space_sequence(s, i, a)) && opt(
                    a,
                    b,
                    single_line_delimited_comment_sequence(s, a, b),
                );
            lemma_is_lit(s, b, b + 3, seq!['-', '-', '>']);
            assert(is_lit(s, b, b + 3, seq!['-', '-', '>']));
            if b + 3 < j {
                assert(single_line_comment_chars(s, b + 3, j));
            }
            assert(html_close_comment_split(s, i, a, b, j));
        }
    }
}

// ---------------------------------------------------------------------
// Annex B's MultiLineComment.
// ---------------------------------------------------------------------

/// The first line terminator of a range that has one.
pub proof fn lemma_first_lt(s: Seq<u32>, lo: int, hi: int)
    requires
        contains_line_terminator(s, lo, hi),
    ensures
        exists|a: int|
            lo <= a < hi && is_line_terminator(s[a]) && forall|k: int|
                lo <= k < a ==> !is_line_terminator(#[trigger] s[k]),
    decreases hi - lo,
{
    if is_line_terminator(s[lo]) {
        assert(lo <= lo < hi && is_line_terminator(s[lo]));
    } else {
        let k = choose|k: int| lo <= k < hi && is_line_terminator(#[trigger] s[k]);
        assert(lo + 1 <= k);
        assert(contains_line_terminator(s, lo + 1, hi));
        lemma_first_lt(s, lo + 1, hi);
        let a = choose|a: int|
            lo + 1 <= a < hi && is_line_terminator(s[a]) && forall|k: int|
                lo + 1 <= k < a ==> !is_line_terminator(#[trigger] s[k]);
        assert forall|k: int| lo <= k < a implies !is_line_terminator(#[trigger] s[k]) by {
            if k > lo {
                assert(!is_line_terminator(s[k]));
            }
        }
    }
}

/// An Annex B `MultiLineComment` is `/*` to a closing `*/`, with a line
/// terminator before it.
pub proof fn lemma_annex_b_close(s: Seq<u32>, i: int, j: int)
    requires
        annex_b_multi_line_comment(s, i, j),
    ensures
        0 <= i,
        i + 1 < s.len(),
        s[i] == 0x2F,
        s[i + 1] == 0x2A,
        exists|e: int|
            #![trigger block_close_ok(s, i + 2, e, true)]
            block_close_ok(s, i + 2, e, true) && contains_line_terminator(s, i + 2, e - 2) && e <= j
                && j <= s.len() && opt(e, j, html_close_comment(s, e, j)),
{
    let (a, c) = choose|a: int, c: int| annex_b_multi_line_comment_split(s, i, a, c, j);
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_is_lit(s, c, c + 2, seq!['*', '/']);
    if i + 2 < a {
        lemma_sl_chars(s, i + 2, a);
    }
    if a + 1 < c {
        lemma_comment_chars(s, a + 1, c);
    }
    assert(block_close_ok(s, i + 2, c + 2, true)) by {
        assert forall|m: int| i + 2 <= m < c implies (#[trigger] s[m] <= 0x10FFFF && !(s[m] == 0x2A
            && s[m + 1] == 0x2F)) by {
            if m < a {
                assert(no_lt_src(s, i + 2, a));
                if m < a - 1 {
                    assert(no_star_slash(s, i + 2, a));
                }
            } else if m > a {
                assert(a + 1 < c);
                if m < c - 1 {
                    assert(no_star_slash(s, a + 1, c));
                }
            }
        }
    }
    assert(contains_line_terminator(s, i + 2, c)) by {
        assert(i + 2 <= a < c && is_line_terminator(s[a]));
    }
}

/// An Annex B `MultiLineComment` from a `/*` whose first closing `*/` ends
/// at `e` (the closing `*/` is the first one): it has a line terminator
/// before the `*/`, and then ends there or after an `HTMLCloseComment`.
pub proof fn lemma_annex_b_ml(s: Seq<u32>, i: int, e: int, j: int)
    requires
        0 <= i,
        i + 1 < s.len(),
        s[i] == 0x2F,
        s[i + 1] == 0x2A,
        block_close_ok(s, i + 2, e, true),
    ensures
        annex_b_multi_line_comment(s, i, j) <==> (contains_line_terminator(s, i + 2, e - 2) && e
            <= j && j <= s.len() && opt(e, j, html_close_comment(s, e, j))),
{
    if annex_b_multi_line_comment(s, i, j) {
        lemma_annex_b_close(s, i, j);
        let e2 = choose|e2: int|
            #![trigger block_close_ok(s, i + 2, e2, true)]
            block_close_ok(s, i + 2, e2, true) && contains_line_terminator(s, i + 2, e2 - 2)
                && e2 <= j && j <= s.len() && opt(e2, j, html_close_comment(s, e2, j));
        lemma_block_close_unique(s, i + 2, e, e2, true);
    }
    if contains_line_terminator(s, i + 2, e - 2) && e <= j && j <= s.len() && opt(
        e,
        j,
        html_close_comment(s, e, j),
    ) {
        lemma_first_lt(s, i + 2, e - 2);
        let a = choose|a: int|
            i + 2 <= a < e - 2 && is_line_terminator(s[a]) && forall|k: int|
                i + 2 <= k < a ==> !is_line_terminator(#[trigger] s[k]);
        let c = e - 2;
        lemma_is_lit(s, i, i + 2, seq!['/', '*']);
        lemma_is_lit(s, c, c + 2, seq!['*', '/']);
        if i + 2 < a {
            lemma_sl_chars(s, i + 2, a);
            assert(no_lt_src(s, i + 2, a)) by {
                assert forall|k: int| i + 2 <= k < a implies is_not_line_terminator(
                    #[trigger] s[k],
                ) by {
                    assert(s[k] <= 0x10FFFF && !is_line_terminator(s[k]));
                }
            }
            assert(no_star_slash(s, i + 2, a)) by {
                assert forall|k: int| i + 2 <= k < a - 1 implies !(#[trigger] s[k] == 0x2A && s[k
                    + 1] == 0x2F) by {
                    assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                }
            }
        }
        if a + 1 < c {
            lemma_comment_chars(s, a + 1, c);
            assert(no_star_slash(s, a + 1, c)) by {
                assert forall|k: int| a + 1 <= k < c - 1 implies !(#[trigger] s[k] == 0x2A && s[k
                    + 1] == 0x2F) by {
                    assert(!(s[k] == 0x2A && s[k + 1] == 0x2F));
                }
            }
            assert(crate::equivalence::all_source(s, a + 1, c)) by {
                assert forall|k: int| a + 1 <= k < c implies #[trigger] s[k] <= 0x10FFFF by {
                    assert(s[k] <= 0x10FFFF);
                }
            }
        }
        assert(line_terminator(s, a, a + 1));
        assert(annex_b_multi_line_comment_split(s, i, a, c, j));
        assert(nonempty(s, i, j));
    }
}

// ---------------------------------------------------------------------
// Which alternatives of Annex B's `Comment` start with which code point.
// ---------------------------------------------------------------------

/// A `SingleLineHTMLCloseComment` starts with a line terminator, and is the
/// `LineTerminatorSequence`, then an `HTMLCloseComment`.
pub proof fn lemma_slhcc(s: Seq<u32>, i: int, a: int, j: int)
    requires
        line_terminator_sequence(s, i, a),
        forall|a2: int| line_terminator_sequence(s, i, a2) ==> a2 == a,
    ensures
        single_line_html_close_comment(s, i, j) <==> (a < j && j <= s.len() && html_close_comment(
            s,
            a,
            j,
        )),
{
    if a < j && j <= s.len() && html_close_comment(s, a, j) {
        assert(nonempty(s, i, j));
        assert(i < a && a < j && line_terminator_sequence(s, i, a) && html_close_comment(s, a, j));
    }
}

/// A `SingleLineHTMLCloseComment` starts with a line terminator.
pub proof fn lemma_slhcc_start(s: Seq<u32>, i: int, j: int)
    requires
        single_line_html_close_comment(s, i, j),
    ensures
        0 <= i < s.len(),
        is_line_terminator(s[i]),
{
    let a = choose|a: int|
        i < a && a < j && line_terminator_sequence(s, i, a) && html_close_comment(s, a, j);
}

/// Annex B's `Comment` that starts with `//` is the `SingleLineComment`, as
/// in §12.4.
pub proof fn lemma_html_cm_slash_slash(s: Seq<u32>, i: int, j: int, html: bool)
    requires
        0 <= i,
        i + 1 < s.len(),
        s[i] == 0x2F,
        s[i + 1] == 0x2F,
    ensures
        comment(s, i, j, html) <==> comment(s, i, j, false),
{
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_sldc_equiv(s, i, j);
    if html {
        if annex_b_multi_line_comment(s, i, j) {
            lemma_annex_b_close(s, i, j);
        }
        if single_line_html_close_comment(s, i, j) {
            lemma_slhcc_start(s, i, j);
        }
        lemma_is_lit(s, i, i + 4, seq!['<', '!', '-', '-']);
    }
    crate::equivalence::lemma_multi_line_comment_equiv(s, i, j);
}

/// Annex B's `Comment` that starts with `/*`, whose first closing `*/` ends
/// at `e`: a delimited comment (no line terminator), or a `MultiLineComment`
/// (a line terminator) and an optional `HTMLCloseComment`.
pub proof fn lemma_html_cm_slash_star(s: Seq<u32>, i: int, e: int, j: int)
    requires
        0 <= i,
        i + 1 < s.len(),
        s[i] == 0x2F,
        s[i + 1] == 0x2A,
        block_close_ok(s, i + 2, e, true),
    ensures
        comment(s, i, j, true) <==> (if contains_line_terminator(s, i + 2, e - 2) {
            e <= j && j <= s.len() && opt(e, j, html_close_comment(s, e, j))
        } else {
            j == e
        }),
{
    lemma_annex_b_ml(s, i, e, j);
    lemma_sldc_equiv(s, i, j);
    crate::equivalence::lemma_single_line_comment_equiv(s, i, j);
    lemma_is_lit(s, i, i + 4, seq!['<', '!', '-', '-']);
    if single_line_html_close_comment(s, i, j) {
        lemma_slhcc_start(s, i, j);
    }
    if single_line_delimited_comment(s, i, j) {
        lemma_block_close_single_to_multi(s, i + 2, j);
        lemma_block_close_unique(s, i + 2, e, j, true);
        assert(!contains_line_terminator(s, i + 2, e - 2)) by {
            if contains_line_terminator(s, i + 2, e - 2) {
                let k = choose|k: int| i + 2 <= k < e - 2 && is_line_terminator(#[trigger] s[k]);
            }
        }
    }
    if !contains_line_terminator(s, i + 2, e - 2) && j == e {
        assert(block_close_ok(s, i + 2, e, false)) by {
            assert forall|m: int| i + 2 <= m < e - 2 implies (#[trigger] s[m] <= 0x10FFFF && !(s[m]
                == 0x2A && s[m + 1] == 0x2F) && !is_line_terminator(s[m])) by {
                assert(!is_line_terminator(s[m]));
            }
        }
    }
}

/// Annex B's `Comment` that starts with `/*`, when no closing `*/` is
/// reachable, is none.
pub proof fn lemma_html_cm_slash_star_none(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i,
        i + 1 < s.len(),
        s[i] == 0x2F,
        s[i + 1] == 0x2A,
        forall|e: int| !#[trigger] block_close_ok(s, i + 2, e, true),
    ensures
        !comment(s, i, j, true),
{
    lemma_sldc_equiv(s, i, j);
    if single_line_delimited_comment(s, i, j) {
        lemma_block_close_single_to_multi(s, i + 2, j);
    }
    if annex_b_multi_line_comment(s, i, j) {
        lemma_annex_b_close(s, i, j);
    }
    crate::equivalence::lemma_single_line_comment_equiv(s, i, j);
    lemma_is_lit(s, i, i + 4, seq!['<', '!', '-', '-']);
    if single_line_html_close_comment(s, i, j) {
        lemma_slhcc_start(s, i, j);
    }
}

/// `SingleLineHTMLOpenComment`: `<!--` and no line terminator after it.
pub proof fn lemma_html_open_equiv(s: Seq<u32>, i: int, j: int)
    ensures
        single_line_html_open_comment(s, i, j) <==> (0 <= i && i + 4 <= j && j <= s.len() && s[i]
            == 0x3C && s[i + 1] == 0x21 && s[i + 2] == 0x2D && s[i + 3] == 0x2D && no_lt_src(
            s,
            i + 4,
            j,
        )),
{
    lemma_is_lit(s, i, i + 4, seq!['<', '!', '-', '-']);
    if i + 4 < j {
        assert(single_line_comment_chars(s, i + 4, j) <==> (0 <= i + 4 && j <= s.len() && no_lt_src(
            s,
            i + 4,
            j,
        )));
    }
}

/// Annex B's `Comment` that starts with `<!--` is the
/// `SingleLineHTMLOpenComment`.
pub proof fn lemma_html_cm_open(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i,
        i + 3 < s.len(),
        s[i] == 0x3C,
        s[i + 1] == 0x21,
        s[i + 2] == 0x2D,
        s[i + 3] == 0x2D,
    ensures
        comment(s, i, j, true) <==> (i + 4 <= j && j <= s.len() && no_lt_src(s, i + 4, j)),
{
    lemma_html_open_equiv(s, i, j);
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_sldc_equiv(s, i, j);
    crate::equivalence::lemma_single_line_comment_equiv(s, i, j);
    if annex_b_multi_line_comment(s, i, j) {
        lemma_annex_b_close(s, i, j);
    }
    if single_line_html_close_comment(s, i, j) {
        lemma_slhcc_start(s, i, j);
    }
}

/// Annex B's `Comment` that starts with a line terminator is the
/// `SingleLineHTMLCloseComment`.
pub proof fn lemma_html_cm_lt(s: Seq<u32>, i: int, a: int, j: int)
    requires
        line_terminator_sequence(s, i, a),
        forall|a2: int| line_terminator_sequence(s, i, a2) ==> a2 == a,
    ensures
        comment(s, i, j, true) <==> (a < j && j <= s.len() && html_close_comment(s, a, j)),
{
    lemma_slhcc(s, i, a, j);
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_sldc_equiv(s, i, j);
    crate::equivalence::lemma_single_line_comment_equiv(s, i, j);
    lemma_is_lit(s, i, i + 4, seq!['<', '!', '-', '-']);
    if annex_b_multi_line_comment(s, i, j) {
        lemma_annex_b_close(s, i, j);
    }
}

/// Annex B's `Comment` does not start with a code point that is not `/`,
/// not a line terminator, and does not start `<!--`.
pub proof fn lemma_html_cm_free(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        s[i] != 0x2F,
        !is_line_terminator(s[i]),
        !(i + 3 < s.len() && s[i] == 0x3C && s[i + 1] == 0x21 && s[i + 2] == 0x2D && s[i + 3]
            == 0x2D),
    ensures
        !comment(s, i, j, true),
{
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_sldc_equiv(s, i, j);
    crate::equivalence::lemma_single_line_comment_equiv(s, i, j);
    lemma_html_open_equiv(s, i, j);
    if annex_b_multi_line_comment(s, i, j) {
        lemma_annex_b_close(s, i, j);
    }
    if single_line_html_close_comment(s, i, j) {
        lemma_slhcc_start(s, i, j);
    }
}

/// An `HTMLCloseComment` starts with white space, `/`, or `-` (the first
/// code point of its `-->`).
pub proof fn lemma_html_close_start(s: Seq<u32>, i: int, j: int)
    requires
        html_close_comment(s, i, j),
    ensures
        0 <= i < s.len(),
        white_space(s, i, i + 1) || s[i] == 0x2F || s[i] == 0x2D,
{
    lemma_html_close_equiv(s, i, j);
    let b = choose|b: int|
        #![trigger arrow_at(s, b)]
        hc_pre(s, i, b) && arrow_at(s, b) && hc_tail(s, b, j);
    if i < b {
        lemma_hc_start(s, i, b);
    }
}

/// Annex B's `Comment` that starts with `/` and then neither `/` nor `*` is
/// none.
pub proof fn lemma_html_cm_slash_other(s: Seq<u32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        s[i] == 0x2F,
        !(i + 1 < s.len() && (s[i + 1] == 0x2F || s[i + 1] == 0x2A)),
    ensures
        !comment(s, i, j, true),
{
    lemma_is_lit(s, i, i + 2, seq!['/', '*']);
    lemma_sldc_equiv(s, i, j);
    crate::equivalence::lemma_single_line_comment_equiv(s, i, j);
    lemma_html_open_equiv(s, i, j);
    if annex_b_multi_line_comment(s, i, j) {
        lemma_annex_b_close(s, i, j);
    }
    if single_line_html_close_comment(s, i, j) {
        lemma_slhcc_start(s, i, j);
    }
}

} // verus!
