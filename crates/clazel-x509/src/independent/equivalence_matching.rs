//! RFC 9525 `dns_match` (`spec.rs`) against RFC 6125 `domain_name_matches`
//! (`independent/matching.rs`) under [`cautious_choices`], which are the
//! answers `spec.rs` gives: wildcards only as a whole left-most label over
//! one label, no partial label, no Common Name.
//!
//! - [`theorem_dns_match_is_rfc_6125`]: on the stated domain the two agree.
//! - [`theorem_dns_match_implies_rfc_6125`]: **with no domain at all**, what
//!   `dns_match` accepts, RFC 6125 accepts. Every disagreement is `spec.rs`
//!   being the stricter one.
//!
//! The domain ([`host_in_domain`]). Outside it `spec.rs` refuses and RFC 6125
//! may accept:
//! 1. **The reference is in preferred name syntax** (`dns_name_shape`): RFC 6125
//!    6.4 sets no alphabet, `a_b.example.com` compares like any other name.
//! 2. **The presented name is too**, or `*.` before one: the same, and a bare
//!    `*` (RFC 6125 6.4.3 gives it no rule of its own, so one label matches).
//! 3. **A wildcard's suffix is not an ICANN public suffix.** `*.com` matches
//!    under RFC 6125, whose 7.2 lists it as an ambiguity and sets no rule, and
//!    is refused by `spec.rs` as browser policy.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::matching::*;
#[cfg(verus_only)]
use crate::spec as h;

verus! {

// ---------------------------------------------------------------------
// Octets.
// ---------------------------------------------------------------------

/// The two ways of folding ASCII case.
pub proof fn lemma_fold(c: u8)
    ensures
        h::ascii_fold(c) as int == ascii_lower(c),
{
    if 0x41 <= c && c <= 0x5A {
        assert((c | 0x20u8) == (c + 0x20u8) as u8) by (bit_vector)
            requires
                0x41 <= c,
                c <= 0x5A,
        ;
    }
}

/// `same_octets`, one position at a time.
pub proof fn lemma_same_at(a: Seq<u8>, i: nat, b: Seq<u8>, j: nat, n: nat, m: nat)
    requires
        same_octets(a, i, b, j, n),
        m < n,
    ensures
        i + m < a.len(),
        j + m < b.len(),
        ascii_lower(a[(i + m) as int]) == ascii_lower(b[(j + m) as int]),
    decreases n,
{
    if m > 0 {
        lemma_same_at(a, i + 1, b, j + 1, (n - 1) as nat, (m - 1) as nat);
    }
}

/// `same_octets` over `n` is over `m` and then the rest.
pub proof fn lemma_same_split(a: Seq<u8>, i: nat, b: Seq<u8>, j: nat, m: nat, n: nat)
    requires
        m <= n,
    ensures
        same_octets(a, i, b, j, n) == (same_octets(a, i, b, j, m) && same_octets(
            a,
            i + m,
            b,
            j + m,
            (n - m) as nat,
        )),
    decreases m,
{
    if m > 0 {
        lemma_same_split(a, i + 1, b, j + 1, (m - 1) as nat, (n - 1) as nat);
    }
}

/// `same_octets` of two slices is of the whole.
pub proof fn lemma_same_slices(a: Seq<u8>, i: nat, e1: nat, b: Seq<u8>, j: nat, e2: nat, x: nat, n: nat)
    requires
        i <= e1 <= a.len(),
        j <= e2 <= b.len(),
        i + x + n <= e1,
        j + x + n <= e2,
    ensures
        same_octets(a.subrange(i as int, e1 as int), x, b.subrange(j as int, e2 as int), x, n)
            == same_octets(a, i + x, b, j + x, n),
    decreases n,
{
    if n > 0 {
        assert(a.subrange(i as int, e1 as int)[x as int] == a[(i + x) as int]);
        assert(b.subrange(j as int, e2 as int)[x as int] == b[(j + x) as int]);
        lemma_same_slices(a, i, e1, b, j, e2, x + 1, (n - 1) as nat);
    }
}

/// `folded_equal_from` is `same_octets`.
pub proof fn lemma_folded(a: Seq<u8>, b: Seq<u8>, k: nat)
    requires
        a.len() == b.len(),
        k <= a.len(),
    ensures
        h::folded_equal_from(a, b, k as int) == same_octets(b, k, a, k, (a.len() - k) as nat),
    decreases a.len() - k,
{
    if k < a.len() {
        lemma_fold(a[k as int]);
        lemma_fold(b[k as int]);
        lemma_folded(a, b, k + 1);
    }
}

/// `first_dot` is `next_dot`.
pub proof fn lemma_first_dot(s: Seq<u8>, i: nat)
    ensures
        h::first_dot(s, i as int) == next_dot(s, i) as int || i > s.len(),
    decreases s.len() - i,
{
    if i < s.len() && s[i as int] != 0x2E {
        lemma_first_dot(s, i + 1);
    }
}

// ---------------------------------------------------------------------
// Labels.
// ---------------------------------------------------------------------

/// `next_dot` finds the first dot.
pub proof fn lemma_next_dot(s: Seq<u8>, i: nat)
    requires
        i <= s.len(),
    ensures
        i <= next_dot(s, i) <= s.len(),
        next_dot(s, i) < s.len() ==> s[next_dot(s, i) as int] == 0x2E,
        forall|k: int| i <= k < next_dot(s, i) ==> #[trigger] s[k] != 0x2E,
    decreases s.len() - i,
{
    if i < s.len() && s[i as int] != 0x2E {
        lemma_next_dot(s, i + 1);
    }
}

/// `labels_from`, one label off.
pub proof fn lemma_labels_step(s: Seq<u8>, i: nat)
    requires
        i <= s.len(),
    ensures
        ({
            let dot = next_dot(s, i);
            let head = s.subrange(i as int, dot as int);
            if dot >= s.len() {
                labels_from(s, i) == seq![head]
            } else {
                labels_from(s, i) == seq![head] + labels_from(s, dot + 1)
            }
        }),
{
    lemma_next_dot(s, i);
}

/// `labels_from` has a label.
pub proof fn lemma_labels_len(s: Seq<u8>, i: nat)
    requires
        i <= s.len(),
    ensures
        labels_from(s, i).len() >= 1,
{
    lemma_labels_step(s, i);
}

/// No `*` in `s` from `i`.
pub open spec fn no_star(s: Seq<u8>, i: nat) -> bool {
    forall|k: int| i <= k < s.len() ==> #[trigger] s[k] != 0x2A
}

/// `star_count` of a name with no `*`.
pub proof fn lemma_star_count_zero(s: Seq<u8>, i: nat)
    requires
        no_star(s, i),
    ensures
        star_count(s, i) == 0,
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_star_count_zero(s, i + 1);
    }
}

/// `no_wildcard_from` is `no_star`.
pub proof fn lemma_no_wildcard(s: Seq<u8>, i: nat)
    requires
        h::no_wildcard_from(s, i as int),
    ensures
        no_star(s, i),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_no_wildcard(s, i + 1);
    }
}

/// A shaped name has no `*`.
pub proof fn lemma_shape_no_star(s: Seq<u8>, i: nat)
    requires
        h::valid_name_from(s, i as int),
        i <= s.len(),
    ensures
        no_star(s, i),
    decreases s.len() - i,
{
    if i + 1 < s.len() {
        lemma_shape_no_star(s, i + 1);
    }
}

/// A shaped name stays shaped up to the next dot.
pub proof fn lemma_shape_walk(s: Seq<u8>, i: nat, k: nat)
    requires
        h::valid_name_from(s, i as int),
        i <= k < s.len(),
        forall|m: int| i <= m < k ==> #[trigger] s[m] != 0x2E,
    ensures
        h::valid_name_from(s, k as int),
    decreases k - i,
{
    if i < k {
        lemma_shape_walk(s, i + 1, k);
    }
}

/// `labels_non_empty` past one more label at the front.
pub proof fn lemma_non_empty_shift(x: Seq<u8>, l: Seq<Seq<u8>>, k: nat)
    ensures
        labels_non_empty(seq![x] + l, k + 1) == labels_non_empty(l, k),
    decreases l.len() - k,
{
    let f = seq![x] + l;
    if k < l.len() {
        assert(f[(k + 1) as int] == l[k as int]);
        lemma_non_empty_shift(x, l, k + 1);
    }
}

/// A shaped name, from the start of a label, has no empty label.
pub proof fn lemma_shape_labels(s: Seq<u8>, i: nat)
    requires
        h::valid_name_from(s, i as int),
        i < s.len(),
        s[i as int] != 0x2E,
    ensures
        labels_non_empty(labels_from(s, i), 0),
    decreases s.len() - i,
{
    lemma_labels_step(s, i);
    lemma_next_dot(s, i);
    let dot = next_dot(s, i);
    let head = s.subrange(i as int, dot as int);
    assert(dot > i);
    assert(head.len() > 0);
    if dot >= s.len() {
        assert(labels_from(s, i)[0] == head);
        assert(labels_non_empty(labels_from(s, i), 1));
    } else {
        lemma_shape_walk(s, i, dot);
        assert(dot + 1 < s.len());
        assert(s[(dot + 1) as int] != 0x2E);
        assert(h::valid_name_from(s, (dot + 1) as int));
        lemma_shape_labels(s, dot + 1);
        lemma_non_empty_shift(head, labels_from(s, dot + 1), 0);
        assert(labels_from(s, i)[0] == head);
    }
}

/// `valid_name_from` from a dot's far side.
pub proof fn lemma_shape_starts(s: Seq<u8>)
    requires
        h::dns_name_shape(s),
    ensures
        s.len() > 0,
        s[0] != 0x2E,
{
}

/// `labels_from` of a suffix is of the whole.
pub proof fn lemma_labels_suffix(s: Seq<u8>, k: nat, i: nat)
    requires
        k + i <= s.len(),
    ensures
        labels_from(s.subrange(k as int, s.len() as int), i) == labels_from(s, k + i),
    decreases s.len() - k - i,
{
    let t = s.subrange(k as int, s.len() as int);
    lemma_next_dot_suffix(s, k, i);
    lemma_labels_step(t, i);
    lemma_labels_step(s, k + i);
    let dot = next_dot(t, i);
    lemma_next_dot(t, i);
    assert(t.subrange(i as int, dot as int) =~= s.subrange((k + i) as int, (k + dot) as int));
    if dot < t.len() {
        lemma_labels_suffix(s, k, dot + 1);
    }
}

/// `next_dot` of a suffix is of the whole.
pub proof fn lemma_next_dot_suffix(s: Seq<u8>, k: nat, i: nat)
    requires
        k + i <= s.len(),
    ensures
        next_dot(s.subrange(k as int, s.len() as int), i) + k == next_dot(s, k + i),
    decreases s.len() - k - i,
{
    let t = s.subrange(k as int, s.len() as int);
    if k + i < s.len() {
        assert(t[i as int] == s[(k + i) as int]);
        if t[i as int] != 0x2E {
            lemma_next_dot_suffix(s, k, i + 1);
        }
    }
}

// ---------------------------------------------------------------------
// Lists of labels against whole names.
// ---------------------------------------------------------------------

/// `remaining_labels_match` past one more label on each side.
pub proof fn lemma_remaining_shift(
    c: MatchChoices,
    x: Seq<u8>,
    p: Seq<Seq<u8>>,
    i: nat,
    y: Seq<u8>,
    r: Seq<Seq<u8>>,
    j: nat,
)
    ensures
        remaining_labels_match(c, seq![x] + p, i + 1, seq![y] + r, j + 1) == remaining_labels_match(
            c,
            p,
            i,
            r,
            j,
        ),
    decreases p.len() - i,
{
    let fp = seq![x] + p;
    let fr = seq![y] + r;
    if i < p.len() && j < r.len() {
        assert(fp[(i + 1) as int] == p[i as int]);
        assert(fr[(j + 1) as int] == r[j as int]);
        lemma_remaining_shift(c, x, p, i + 1, y, r, j + 1);
    }
}

/// A label with no `*` matches as `same_label`.
pub proof fn lemma_plain_label(a: Seq<u8>, r: Seq<u8>, beyond: bool)
    requires
        no_star(a, 0),
    ensures
        label_matches(cautious_choices(), a, r, beyond) == same_label(a, r),
{
    lemma_star_count_zero(a, 0);
}

/// The `.` is the one octet that folds to `.`.
pub proof fn lemma_dot_fold(a: u8, b: u8)
    requires
        ascii_lower(a) == ascii_lower(b),
    ensures
        (a == 0x2E) == (b == 0x2E),
{
}

/// **Label lists against whole names.** With no `*` in `p`, comparing the
/// labels is comparing the octets: `.` folds only to itself, so the separators
/// fall in the same places.
#[verifier::spinoff_prover]
pub proof fn lemma_plain_labels(p: Seq<u8>, i: nat, r: Seq<u8>, j: nat)
    requires
        i <= p.len(),
        j <= r.len(),
        no_star(p, i),
    ensures
        remaining_labels_match(cautious_choices(), labels_from(p, i), 0, labels_from(r, j), 0) == (p.len()
            - i == r.len() - j && same_octets(p, i, r, j, (p.len() - i) as nat)),
    decreases p.len() - i,
{
    let c = cautious_choices();
    let n = (p.len() - i) as nat;
    let dp = next_dot(p, i);
    let dr = next_dot(r, j);
    lemma_next_dot(p, i);
    lemma_next_dot(r, j);
    lemma_labels_step(p, i);
    lemma_labels_step(r, j);
    let a = p.subrange(i as int, dp as int);
    let b = r.subrange(j as int, dr as int);
    let lp = labels_from(p, i);
    let lr = labels_from(r, j);
    assert(lp[0] == a);
    assert(lr[0] == b);
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] a[k] != 0x2A by {
        assert(a[k] == p[i + k]);
    }
    lemma_plain_label(a, b, true);
    assert(remaining_labels_match(c, lp, 0, lr, 0) == (same_label(a, b) && remaining_labels_match(
        c,
        lp,
        1,
        lr,
        1,
    )));
    if a.len() == b.len() {
        lemma_same_slices(p, i, dp, r, j, dr, 0, a.len());
    }
    if dp >= p.len() {
        // `p` has one label left.
        assert(lp.len() == 1);
        if dr >= r.len() {
            assert(lr.len() == 1);
        } else {
            lemma_labels_len(r, dr + 1);
            assert(lr.len() >= 2);
            if p.len() - i == r.len() - j && same_octets(p, i, r, j, n) {
                let m = (dr - j) as nat;
                lemma_same_at(p, i, r, j, n, m);
                lemma_dot_fold(p[(i + m) as int], r[(j + m) as int]);
                assert(p[(i + m) as int] != 0x2E);
            }
        }
    } else {
        let rest_p = labels_from(p, dp + 1);
        assert(lp == seq![a] + rest_p);
        lemma_labels_len(p, dp + 1);
        if dr >= r.len() {
            assert(lr.len() == 1);
            assert(lp.len() >= 2);
            if p.len() - i == r.len() - j && same_octets(p, i, r, j, n) {
                let m = (dp - i) as nat;
                lemma_same_at(p, i, r, j, n, m);
                lemma_dot_fold(p[(i + m) as int], r[(j + m) as int]);
                assert(r[(j + m) as int] != 0x2E);
            }
        } else {
            let rest_r = labels_from(r, dr + 1);
            assert(lr == seq![b] + rest_r);
            lemma_remaining_shift(c, a, rest_p, 0, b, rest_r, 0);
            assert(no_star(p, dp + 1));
            lemma_plain_labels(p, dp + 1, r, dr + 1);
            let m = (dp - i) as nat;
            if p.len() - i == r.len() - j && same_octets(p, i, r, j, n) {
                // The first dots fall together.
                let m2 = (dr - j) as nat;
                if m < m2 {
                    lemma_same_at(p, i, r, j, n, m);
                    lemma_dot_fold(p[(i + m) as int], r[(j + m) as int]);
                    assert(r[(j + m) as int] != 0x2E);
                } else if m2 < m {
                    lemma_same_at(p, i, r, j, n, m2);
                    lemma_dot_fold(p[(i + m2) as int], r[(j + m2) as int]);
                    assert(p[(i + m2) as int] != 0x2E);
                }
                assert(a.len() == b.len());
                lemma_same_split(p, i, r, j, m, n);
                lemma_same_split(p, i + m, r, j + m, 1, (n - m) as nat);
                assert(same_octets(p, dp + 1, r, dr + 1, (p.len() - (dp + 1)) as nat));
            }
            if same_label(a, b) && p.len() - (dp + 1) == r.len() - (dr + 1) && same_octets(
                p,
                dp + 1,
                r,
                dr + 1,
                (p.len() - (dp + 1)) as nat,
            ) {
                lemma_same_split(p, i, r, j, m, n);
                lemma_same_split(p, i + m, r, j + m, 1, (n - m) as nat);
                assert(ascii_lower(p[dp as int]) == ascii_lower(r[dr as int]));
                assert(same_octets(p, dp, r, dr, 1)) by {
                    assert(same_octets(p, dp + 1, r, dr + 1, 0));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The theorems.
// ---------------------------------------------------------------------

/// A plain name: `label_lists_match` is `remaining_labels_match` from 0.
pub proof fn lemma_plain_lists(p: Seq<u8>, r: Seq<u8>)
    requires
        p.len() > 0,
        r.len() > 0,
        no_star(p, 0),
    ensures
        label_lists_match(cautious_choices(), labels(p), labels(r)) == remaining_labels_match(
            cautious_choices(),
            labels(p),
            0,
            labels(r),
            0,
        ),
{
    lemma_labels_len(p, 0);
    lemma_labels_len(r, 0);
    lemma_labels_step(p, 0);
    lemma_next_dot(p, 0);
    let a = labels(p)[0];
    assert(a == p.subrange(0, next_dot(p, 0) as int));
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] a[k] != 0x2A by {
        assert(a[k] == p[k]);
    }
    lemma_plain_label(a, labels(r)[0], false);
    lemma_plain_label(a, labels(r)[0], true);
}

/// A presented name `spec.rs` compares as written.
#[verifier::spinoff_prover]
pub proof fn lemma_match_plain(reference: Seq<u8>, presented: Seq<u8>)
    requires
        h::dns_name_shape(reference),
        h::dns_name_shape(presented),
    ensures
        h::dns_match(reference, presented) == domain_name_matches(cautious_choices(), presented, reference),
{
    lemma_shape_starts(reference);
    lemma_shape_starts(presented);
    lemma_shape_no_star(presented, 0);
    lemma_shape_no_star(reference, 0);
    lemma_star_count_zero(reference, 0);
    lemma_shape_labels(reference, 0);
    lemma_shape_labels(presented, 0);
    lemma_plain_lists(presented, reference);
    lemma_plain_labels(presented, 0, reference, 0);
    if reference.len() == presented.len() {
        lemma_folded(reference, presented, 0);
    }
    assert(h::folded_equal_from(reference, presented, 0) ==> reference.len() == presented.len());
}

/// The labels of `*.suffix`.
pub proof fn lemma_wildcard_labels(p: Seq<u8>)
    requires
        p.len() > 2,
        p[0] == 0x2A,
        p[1] == 0x2E,
    ensures
        next_dot(p, 0) == 1,
        labels(p) == seq![p.subrange(0, 1)] + labels_from(p, 2),
{
    assert(next_dot(p, 1) == 1);
    assert(next_dot(p, 0) == 1);
    lemma_labels_step(p, 0);
}

/// The whole-label `*` matches any non-empty label.
pub proof fn lemma_star_label(a: Seq<u8>, r: Seq<u8>)
    requires
        a.len() == 1,
        a[0] == 0x2A,
    ensures
        label_matches(cautious_choices(), a, r, false) == (r.len() > 0),
{
    assert(star_count(a, 1) == 0);
    assert(star_count(a, 0) == 1);
}

/// A presented wildcard `spec.rs` compares.
#[verifier::spinoff_prover]
pub proof fn lemma_match_wildcard(reference: Seq<u8>, presented: Seq<u8>)
    requires
        h::dns_name_shape(reference),
        presented.len() > 2,
        presented[0] == 0x2A,
        presented[1] == 0x2E,
        h::dns_name_shape(presented.subrange(2, presented.len() as int)),
        !h::wildcard_suffix_is_icann_suffix(presented.subrange(2, presented.len() as int)),
    ensures
        h::dns_match(reference, presented) == domain_name_matches(cautious_choices(), presented, reference),
{
    hide(h::wildcard_suffix_is_icann_suffix);
    let c = cautious_choices();
    let p = presented;
    let r = reference;
    let suffix = p.subrange(2, p.len() as int);
    lemma_shape_starts(reference);
    lemma_shape_starts(suffix);
    lemma_shape_no_star(reference, 0);
    lemma_star_count_zero(reference, 0);
    lemma_shape_labels(reference, 0);
    lemma_shape_labels(suffix, 0);
    lemma_shape_no_star(suffix, 0);
    assert(no_star(p, 2)) by {
        assert forall|k: int| 2 <= k < p.len() implies #[trigger] p[k] != 0x2A by {
            assert(suffix[k - 2] == p[k]);
        }
    }
    lemma_no_wildcard_back(p, 2);
    assert(!h::dns_name_shape(p)) by {
        // `*` is not a name character.
        assert(p[0] != 0x2E);
        assert(!h::valid_name_from(p, 0));
    }
    // The presented labels.
    lemma_wildcard_labels(p);
    lemma_labels_suffix(p, 2, 0);
    let star = p.subrange(0, 1);
    let lp = labels(p);
    let rest_p = labels_from(p, 2);
    assert(rest_p == labels(suffix));
    assert(labels_non_empty(lp, 0)) by {
        lemma_non_empty_shift(star, rest_p, 0);
        assert(lp[0] == star);
    }
    // The reference labels.
    lemma_labels_step(r, 0);
    lemma_next_dot(r, 0);
    let dot = next_dot(r, 0);
    let lr = labels(r);
    let head = r.subrange(0, dot as int);
    lemma_first_dot(r, 0);
    assert(h::first_dot(r, 0) == dot as int);
    assert(lp[0] == star);
    assert(lr[0] == head);
    lemma_star_label(star, head);
    assert(dot > 0);
    if dot >= r.len() {
        // One reference label, at least two presented.
        lemma_labels_len(p, 2);
        assert(lr.len() == 1);
        assert(lp.len() >= 2);
        assert(!remaining_labels_match(c, lp, 1, lr, 1));
    } else {
        let rest_r = labels_from(r, dot + 1);
        assert(lr == seq![head] + rest_r);
        assert(lp == seq![star] + rest_p);
        lemma_remaining_shift(c, star, rest_p, 0, head, rest_r, 0);
        lemma_plain_labels(p, 2, r, dot + 1);
        let tail = r.subrange((dot + 1) as int, r.len() as int);
        let n = (p.len() - 2) as nat;
        if tail.len() == suffix.len() {
            lemma_folded(tail, suffix, 0);
            lemma_same_slices(p, 2, p.len(), r, dot + 1, r.len(), 0, n);
        }
        assert(h::folded_equal_from(tail, suffix, 0) ==> tail.len() == suffix.len());
    }
}

/// `no_star` is `no_wildcard_from`.
pub proof fn lemma_no_wildcard_back(s: Seq<u8>, i: nat)
    requires
        no_star(s, i),
    ensures
        h::no_wildcard_from(s, i as int),
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_no_wildcard_back(s, i + 1);
    }
}

/// The presented names of the domain.
pub open spec fn host_in_domain(presented: Seq<u8>) -> bool {
    h::dns_name_shape(presented) || {
        &&& presented.len() > 2
        &&& presented[0] == 0x2A
        &&& presented[1] == 0x2E
        &&& h::dns_name_shape(presented.subrange(2, presented.len() as int))
        &&& !h::wildcard_suffix_is_icann_suffix(presented.subrange(2, presented.len() as int))
    }
}

/// **The two agree on the domain.**
pub proof fn theorem_dns_match_is_rfc_6125(reference: Seq<u8>, presented: Seq<u8>)
    requires
        h::dns_name_shape(reference),
        host_in_domain(presented),
    ensures
        h::dns_match(reference, presented) == domain_name_matches(cautious_choices(), presented, reference),
{
    if h::dns_name_shape(presented) {
        lemma_match_plain(reference, presented);
    } else {
        lemma_match_wildcard(reference, presented);
    }
}

/// **With no domain: what `dns_match` accepts, RFC 6125 accepts.** Every
/// disagreement has `spec.rs` as the stricter side.
pub proof fn theorem_dns_match_implies_rfc_6125(reference: Seq<u8>, presented: Seq<u8>)
    ensures
        h::dns_match(reference, presented) ==> domain_name_matches(cautious_choices(), presented, reference),
{
    if h::dns_match(reference, presented) {
        assert(h::dns_name_shape(reference));
        assert(host_in_domain(presented));
        theorem_dns_match_is_rfc_6125(reference, presented);
    }
}

} // verus!
