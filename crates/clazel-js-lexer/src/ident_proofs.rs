//! Lemmas about identifiers for [`super::exec`]'s proofs.
//!
//! [`super::independent`] reads an `IdentifierName` left to right as units
//! (`ind_unit_end`); [`super::equivalence`] proves that equal to
//! [`super::spec`]'s. Here:
//!
//! - [`name_end`] is the greedy end of that reading, and every derivation
//!   ends at or before it ([`lemma_name_from_le_end`]), so the greedy scan
//!   is the longest;
//! - [`name_cps`] is the IdentifierCodePoints of the left-to-right reading,
//!   and [`lemma_cps_unique`] shows the spec's relation determines them, so
//!   an early error is a property of the one list the scan builds;
//! - no `IdentifierName` or `PrivateIdentifier` starts where the first code
//!   point cannot start one ([`ident_absent`], [`private_absent`]);
//! - no white space or line terminator code point is an
//!   `IdentifierStartChar` ([`lemma_ws_lt_not_id_start`]), read from the
//!   generated Unicode table.

#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::unicode::{lemma_id_start_below, lemma_id_start_gap};
#[cfg(verus_only)]
use super::unicode_data::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The end of the units read greedily from `i`: the first unit is of the
/// start class when `first`, and each later one of the continue class.
/// With `first`, -1 when no unit starts at `i` (there is no name).
pub open spec fn name_end(s: Seq<u32>, i: int, first: bool) -> int
    decreases s.len() - i,
{
    let e = ind_unit_end(s, i, first);
    if i >= 0 && i < e && e <= s.len() {
        name_end(s, e, false)
    } else if first {
        -1
    } else {
        i
    }
}

/// A greedy end is at or after where it starts (after it, with `first`).
pub proof fn lemma_name_end_ge(s: Seq<u32>, i: int, first: bool)
    ensures
        first && name_end(s, i, first) >= 0 ==> name_end(s, i, first) > i,
        !first ==> name_end(s, i, first) >= i,
    decreases s.len() - i,
{
    let e = ind_unit_end(s, i, first);
    if e >= 0 {
        lemma_unit_end_bounds(s, i, first);
    }
    if i >= 0 && i < e && e <= s.len() {
        lemma_name_end_ge(s, e, false);
    }
}

/// The greedy end is the end of a derivation, after which no unit follows.
pub proof fn lemma_name_end_derives(s: Seq<u32>, i: int, first: bool)
    requires
        name_end(s, i, first) >= 0,
    ensures
        ind_name_from(s, i, name_end(s, i, first), first),
        ind_unit_end(s, name_end(s, i, first), false) < 0,
    decreases s.len() - i,
{
    let e = ind_unit_end(s, i, first);
    if e >= 0 {
        lemma_unit_end_bounds(s, i, first);
    }
    if i >= 0 && i < e && e <= s.len() {
        lemma_name_end_derives(s, e, false);
        lemma_name_end_ge(s, e, false);
    }
}

/// Every derivation from `i` ends at or before the greedy end.
pub proof fn lemma_name_from_le_end(s: Seq<u32>, i: int, j: int, first: bool)
    requires
        0 <= i,
        ind_name_from(s, i, j, first),
    ensures
        name_end(s, i, first) >= j,
    decreases j - i,
{
    lemma_name_end_ge(s, i, first);
    if i < j {
        let e = ind_unit_end(s, i, first);
        assert(i < e && e <= j && ind_name_from(s, e, j, false));
        lemma_unit_end_bounds(s, i, first);
        lemma_name_from_le_end(s, e, j, false);
    }
}

/// While a unit follows, the greedy end of the rest is the greedy end.
pub proof fn lemma_name_end_step(s: Seq<u32>, i: int, e: int, first: bool)
    requires
        ind_unit_end(s, i, first) == e,
        e >= 0,
    ensures
        name_end(s, i, first) == name_end(s, e, false),
{
    lemma_unit_end_bounds(s, i, first);
}

/// When no unit follows a continue position, it is the greedy end.
pub proof fn lemma_name_end_stop(s: Seq<u32>, i: int)
    requires
        ind_unit_end(s, i, false) < 0,
    ensures
        name_end(s, i, false) == i,
{
}

/// The IdentifierCodePoints of the left-to-right reading of `s[i..j)`.
pub open spec fn name_cps(s: Seq<u32>, i: int, j: int, first: bool) -> Seq<u32>
    decreases j - i,
{
    if i >= j {
        Seq::empty()
    } else {
        let e = ind_unit_end(s, i, first);
        if i < e && e <= j {
            seq![identifier_code_point(s, i, e)] + name_cps(s, e, j, false)
        } else {
            Seq::empty()
        }
    }
}

/// Appending one unit to a reading appends its code point.
pub proof fn lemma_name_cps_append(s: Seq<u32>, i: int, k: int, j: int, first: bool)
    requires
        ind_name_from(s, i, k, first),
        k < j,
        ind_unit_end(s, k, false) == j,
    ensures
        name_cps(s, i, j, first) =~= name_cps(s, i, k, first).push(identifier_code_point(s, k, j)),
    decreases k - i,
{
    if i < k {
        let e = ind_unit_end(s, i, first);
        assert(i < e && e <= k && ind_name_from(s, e, k, false));
        lemma_name_cps_append(s, e, k, j, false);
        assert(name_cps(s, i, j, first) == seq![identifier_code_point(s, i, e)] + name_cps(
            s,
            e,
            j,
            false,
        ));
        assert(name_cps(s, i, k, first) == seq![identifier_code_point(s, i, e)] + name_cps(
            s,
            e,
            k,
            false,
        ));
    } else {
        assert(i == k && !first);
        assert(name_cps(s, i, j, first) == seq![identifier_code_point(s, i, j)] + name_cps(
            s,
            j,
            j,
            false,
        ));
    }
}

/// An `IdentifierName`'s code points are not empty.
pub proof fn lemma_cps_nonempty(s: Seq<u32>, i: int, j: int, cps: Seq<u32>)
    requires
        identifier_name_cps(s, i, j, cps),
    ensures
        cps.len() >= 1,
{
}

/// A derivation of `IdentifierName` with code points `cps`: its reading
/// left to right, and `cps` is that reading's.
pub proof fn lemma_cps_unique(s: Seq<u32>, i: int, j: int, cps: Seq<u32>)
    requires
        identifier_name_cps(s, i, j, cps),
    ensures
        ind_name_from(s, i, j, true),
        cps =~= name_cps(s, i, j, true),
    decreases j - i,
{
    lemma_unit_equiv(s, i, j);
    if identifier_start(s, i, j) && cps =~= seq![identifier_code_point(s, i, j)] {
        assert(ind_unit_end(s, i, true) == j);
        assert(ind_name_from(s, j, j, false));
        assert(name_cps(s, i, j, true) == seq![identifier_code_point(s, i, j)] + name_cps(
            s,
            j,
            j,
            false,
        ));
    } else {
        assert(cps.len() >= 2 && exists|k: int| #![auto]
            i < k < j && identifier_name_cps(s, i, k, cps.drop_last())
                && identifier_part(s, k, j) && cps.last() == identifier_code_point(s, k, j));
        let k = choose|k: int| #![auto]
            i < k < j && identifier_name_cps(s, i, k, cps.drop_last())
                && identifier_part(s, k, j) && cps.last() == identifier_code_point(s, k, j);
        lemma_cps_unique(s, i, k, cps.drop_last());
        lemma_unit_equiv(s, k, j);
        lemma_name_from_append(s, i, k, j, true);
        lemma_name_cps_append(s, i, k, j, true);
        assert(cps =~= cps.drop_last().push(cps.last()));
    }
}

/// The spec's code points of a name are the reading's (any two derivations
/// agree).
pub proof fn lemma_cps_agree(s: Seq<u32>, i: int, j: int, c1: Seq<u32>, c2: Seq<u32>)
    requires
        identifier_name_cps(s, i, j, c1),
        identifier_name_cps(s, i, j, c2),
    ensures
        c1 =~= c2,
{
    lemma_cps_unique(s, i, j, c1);
    lemma_cps_unique(s, i, j, c2);
}

/// Extending a name's code points by an `IdentifierPart`.
pub proof fn lemma_cps_extend(s: Seq<u32>, i: int, m: int, m2: int, cps: Seq<u32>)
    requires
        identifier_name_cps(s, i, m, cps),
        identifier_part(s, m, m2),
    ensures
        identifier_name_cps(s, i, m2, cps.push(identifier_code_point(s, m, m2))),
{
    let ext = cps.push(identifier_code_point(s, m, m2));
    lemma_cps_nonempty(s, i, m, cps);
    assert(ext.drop_last() =~= cps);
    assert(ext.len() >= 2);
    assert(i < m < m2);
    assert(identifier_name_cps(s, i, m, ext.drop_last()));
    assert(ext.last() == identifier_code_point(s, m, m2));
}

/// The start of a name: a start unit gives a one-code-point name.
pub proof fn lemma_cps_start(s: Seq<u32>, i: int, e: int)
    requires
        identifier_start(s, i, e),
    ensures
        identifier_name_cps(s, i, e, seq![identifier_code_point(s, i, e)]),
{
}

/// No `IdentifierName` derives a range from `pos`.
#[verifier::opaque]
pub open spec fn ident_absent(s: Seq<u32>, pos: int) -> bool {
    forall|j: int| !identifier_name(s, pos, j)
}

/// No `PrivateIdentifier` derives a range from `pos`.
#[verifier::opaque]
pub open spec fn private_absent(s: Seq<u32>, pos: int) -> bool {
    forall|j: int| !private_identifier(s, pos, j)
}

/// An `IdentifierName` starts with `\` or an `IdentifierStartChar`.
pub proof fn lemma_ident_start(s: Seq<u32>, i: int, j: int)
    requires
        identifier_name(s, i, j),
    ensures
        0 <= i < s.len(),
        s[i] == 0x5C || is_identifier_start_char(s[i]),
{
    lemma_identifier_name_equiv(s, i, j);
    assert(ind_identifier_name(s, i, j));
    lemma_name_cps_to_ind(s, i, j, choose|cps: Seq<u32>| identifier_name_cps(s, i, j, cps));
    let e = ind_unit_end(s, i, true);
    assert(e >= 0);
    lemma_unit_end_bounds(s, i, true);
    if s[i] != 0x5C {
        lemma_id_char_equiv(s[i]);
    }
}

/// No `IdentifierName` starts at a code point that is neither `\` nor an
/// `IdentifierStartChar`.
pub proof fn lemma_ident_absent_from_class(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        !(s[i] == 0x5C || is_identifier_start_char(s[i])),
    ensures
        ident_absent(s, i),
{
    reveal(ident_absent);
    assert forall|j: int| !identifier_name(s, i, j) by {
        if identifier_name(s, i, j) {
            lemma_ident_start(s, i, j);
        }
    }
}

/// No `PrivateIdentifier` starts at a code point other than `#`.
pub proof fn lemma_private_absent_from_class(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        s[i] != 0x23,
    ensures
        private_absent(s, i),
{
    reveal(private_absent);
}

/// No `PrivateIdentifier` starts at a `#` followed by a code point that
/// starts no `IdentifierName`.
pub proof fn lemma_private_absent_from_next(s: Seq<u32>, i: int)
    requires
        ident_absent(s, i + 1),
    ensures
        private_absent(s, i),
{
    reveal(private_absent);
    reveal(ident_absent);
    assert forall|j: int| !private_identifier(s, i, j) by {
        if private_identifier(s, i, j) {
            assert(identifier_name(s, i + 1, j));
        }
    }
}

/// A scan that finds no unit at `i` shows no `IdentifierName` starts there.
pub proof fn lemma_ident_absent_from_scan(s: Seq<u32>, i: int)
    requires
        ind_unit_end(s, i, true) < 0,
    ensures
        ident_absent(s, i),
{
    reveal(ident_absent);
    assert forall|j: int| !identifier_name(s, i, j) by {
        if identifier_name(s, i, j) {
            lemma_identifier_name_equiv(s, i, j);
            let cps = choose|cps: Seq<u32>| identifier_name_cps(s, i, j, cps);
            lemma_cps_unique(s, i, j, cps);
            assert(j > i);
        }
    }
}

/// A plain code point (not `\`) does not change whether a name has an escape.
pub proof fn lemma_has_escape_plain(s: Seq<u32>, k: int, j: int)
    requires
        0 <= k <= j < s.len(),
        s[j] != 0x5C,
    ensures
        identifier_has_escape(s, k, j + 1) == identifier_has_escape(s, k, j),
{
    if identifier_has_escape(s, k, j + 1) {
        let t = choose|t: int| k <= t < j + 1 && s[t] == 0x5C;
        assert(k <= t < j && s[t] == 0x5C);
    }
    if identifier_has_escape(s, k, j) {
        let t = choose|t: int| k <= t < j && s[t] == 0x5C;
        assert(k <= t < j + 1 && s[t] == 0x5C);
    }
}

/// A `\` inside the range makes the name have an escape.
pub proof fn lemma_has_escape_esc(s: Seq<u32>, k: int, j: int, j2: int)
    requires
        0 <= k <= j < j2,
        j < s.len(),
        s[j] == 0x5C,
    ensures
        identifier_has_escape(s, k, j2),
{
    assert(k <= j < j2 && s[j] == 0x5C);
}

/// The early errors of a name one code point longer.
pub proof fn lemma_early_push(cps: Seq<u32>, cp: u32)
    requires
        cps.len() >= 1,
    ensures
        identifier_early_errors_ok(cps.push(cp)) == (identifier_early_errors_ok(cps)
            && is_identifier_part_char(cp)),
{
    let ext = cps.push(cp);
    if identifier_early_errors_ok(cps) && is_identifier_part_char(cp) {
        assert forall|k: int| 1 <= k < ext.len() implies is_identifier_part_char(
            #[trigger] ext[k],
        ) by {
            if k < cps.len() {
                assert(ext[k] == cps[k]);
            } else {
                assert(ext[k] == cp);
            }
        }
        assert(ext[0] == cps[0]);
    }
    if identifier_early_errors_ok(ext) {
        assert(ext[0] == cps[0]);
        assert forall|k: int| 1 <= k < cps.len() implies is_identifier_part_char(
            #[trigger] cps[k],
        ) by {
            assert(ext[k] == cps[k]);
        }
        assert(ext[cps.len() as int] == cp);
    }
}

/// The early errors of a one-code-point name.
pub proof fn lemma_early_one(cp: u32)
    ensures
        identifier_early_errors_ok(seq![cp]) == is_identifier_start_char(cp),
{
}

/// The early errors of a name are those of its one list of code points.
pub proof fn lemma_name_valid_iff(s: Seq<u32>, i: int, j: int, cps: Seq<u32>)
    requires
        identifier_name_cps(s, i, j, cps),
    ensures
        identifier_name_valid(s, i, j) == identifier_early_errors_ok(cps),
{
    if identifier_name_valid(s, i, j) {
        let c2 = choose|c2: Seq<u32>| #![auto] identifier_name_cps(s, i, j, c2)
            && identifier_early_errors_ok(c2);
        lemma_cps_agree(s, i, j, cps, c2);
    }
}

/// An `IdentifierName` from `i` ends at or before the greedy end `e`.
pub proof fn lemma_name_longest(s: Seq<u32>, i: int, j: int, e: int)
    requires
        0 <= i,
        name_end(s, i, true) == e,
        identifier_name(s, i, j) || (i >= 1 && private_identifier(s, i - 1, j)),
    ensures
        j <= e,
{
    lemma_identifier_name_equiv(s, i, j);
    lemma_name_from_le_end(s, i, j, true);
}

/// White space and line terminator code points are not
/// `IdentifierStartChar`s (Unicode 18.0.0's `ID_Start`, from the
/// generated table).
pub proof fn lemma_ws_lt_not_id_start(c: u32)
    requires
        c == 0x0009 || c == 0x000B || c == 0x000C || c == 0xFEFF || unicode_space_separator(c)
            || is_line_terminator(c),
    ensures
        !is_identifier_start_char(c),
{
    if c >= 0x80 {
        reveal(ID_START_0);
        reveal(ID_START_1);
        assert(id_start_at(191).last == 0x167F && id_start_at(192).first == 0x1681);
        assert(id_start_at(249).last == 0x1FFC && id_start_at(250).first == 0x2071);
        assert(id_start_at(282).last == 0x2DDE && id_start_at(283).first == 0x3005);
        assert(id_start_at(368).last == 0xFEFC && id_start_at(369).first == 0xFF21);
        assert(id_start_at(0).first == 0xAA);
        if c == 0xA0 {
            lemma_id_start_below(c);
        } else if c == 0x1680 {
            lemma_id_start_gap(191, c);
        } else if c == 0x3000 {
            lemma_id_start_gap(282, c);
        } else if c == 0xFEFF {
            lemma_id_start_gap(368, c);
        } else {
            lemma_id_start_gap(249, c);
        }
    }
}

} // verus!
