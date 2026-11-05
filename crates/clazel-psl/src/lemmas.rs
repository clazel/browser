//! Facts proven about the spec. The first group is what the executable
//! functions rely on (the prevailing rule matches; a suffix equals the
//! domain only when it has all its labels); the others are evidence that
//! the spec says what the standard means.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`rule_matches_from`] is "for every pair" of the rule's labels from the
/// `k`-th from the right.
pub proof fn lemma_rule_matches_from_forall(rule: Rule, d: Seq<Seq<u32>>, k: nat)
    requires
        rule.labels.len() <= d.len(),
    ensures
        rule_matches_from(rule, d, k) <==> forall|j: int|
            k <= j < rule.labels.len() ==> label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - j], d[d.len() - 1 - j]),
    decreases rule.labels.len() - k,
{
    if k < rule.labels.len() {
        lemma_rule_matches_from_forall(rule, d, k + 1);
        if rule_matches_from(rule, d, k) {
            assert forall|j: int| k <= j < rule.labels.len() implies label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - j], d[d.len() - 1 - j]) by {
                if j > k {
                    assert(k + 1 <= j);
                }
            }
        }
    }
}

/// "A domain is said to match a rule" exactly as the standard words it: the
/// domain has as many or more labels, and for every pair, counting from the
/// right, the labels are identical or the rule's is "*".
pub proof fn lemma_rule_matches_forall(rule: Rule, d: Seq<Seq<u32>>)
    ensures
        rule_matches(rule, d) <==> (rule.labels.len() <= d.len() && forall|k: int|
            0 <= k < rule.labels.len() ==> label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - k], d[d.len() - 1 - k])),
{
    if rule.labels.len() <= d.len() {
        lemma_rule_matches_from_forall(rule, d, 0);
    }
}

/// [`has_empty_label_from`] is "some label from the `k`-th on is empty".
pub proof fn lemma_has_empty_label_from_exists(labels: Seq<Seq<u32>>, k: nat)
    ensures
        has_empty_label_from(labels, k) <==> exists|j: int| k <= j < labels.len() && (#[trigger] labels[j]).len() == 0,
    decreases labels.len() - k,
{
    if k < labels.len() {
        lemma_has_empty_label_from_exists(labels, k + 1);
        if labels[k as int].len() != 0 && has_empty_label_from(labels, k) {
            let j = choose|j: int| k + 1 <= j < labels.len() && (#[trigger] labels[j]).len() == 0;
            assert(k <= j);
        }
    }
}

/// An empty label somewhere in `labels`.
pub proof fn lemma_has_empty_label_exists(labels: Seq<Seq<u32>>)
    ensures
        has_empty_label(labels) <==> exists|k: int| 0 <= k < labels.len() && (#[trigger] labels[k]).len() == 0,
{
    lemma_has_empty_label_from_exists(labels, 0);
}

/// The rule that prevails among the first `n` matches the domain.
pub proof fn lemma_prevailing_matches(rules: Seq<Rule>, d: Seq<Seq<u32>>, n: nat)
    requires
        n <= rules.len(),
    ensures
        match prevailing_from(rules, d, n) {
            Some(p) => p < n && rule_matches(rules[p as int], d),
            None => true,
        },
    decreases n,
{
    if n > 0 {
        lemma_prevailing_matches(rules, d, (n - 1) as nat);
    }
}

/// The public suffix has at least one label, and at most the domain's.
pub proof fn lemma_suffix_label_count_bounds(rules: Seq<Rule>, d: Seq<Seq<u32>>)
    requires
        d.len() >= 1,
    ensures
        1 <= suffix_label_count(rules, d) <= d.len(),
{
    lemma_prevailing_matches(rules, d, rules.len());
}

/// A domain is its labels joined, with its trailing dot: the labels are a
/// non-empty list without ".".
pub proof fn lemma_domain_labels_join(domain: Seq<u32>)
    ensures
        domain_labels(domain).len() >= 1,
        forall|k: int| 0 <= k < domain_labels(domain).len() ==> clazel_url::host::lemmas::free_of(#[trigger] domain_labels(domain)[k], 0x2E),
        labels_string(domain_labels(domain), has_trailing_dot(domain)) == domain,
{
    super::join::lemma_split_join_round_trip(strip_trailing_dot(domain));
    if has_trailing_dot(domain) {
        assert(domain =~= strip_trailing_dot(domain) + seq![0x2Eu32]);
    }
}

/// A suffix of a domain with `k` of its labels is the domain itself
/// exactly when `k` is all of them.
pub proof fn lemma_label_suffix_is_domain(domain: Seq<u32>, k: nat)
    requires
        1 <= k <= domain_labels(domain).len(),
    ensures
        (label_suffix(domain_labels(domain), has_trailing_dot(domain), k) == domain) <==> (k == domain_labels(domain).len()),
{
    let d = domain_labels(domain);
    let td = has_trailing_dot(domain);
    lemma_domain_labels_join(domain);
    let tail = if td {
        seq![0x2Eu32]
    } else {
        seq![]
    };
    let a = d.skip(d.len() - k);
    if k == d.len() {
        assert(a =~= d);
    } else {
        if label_suffix(d, td, k) == domain {
            let x = clazel_url::host::lemmas::split_join(a, 0x2E);
            let y = clazel_url::host::lemmas::split_join(d, 0x2E);
            assert(x + tail == y + tail);
            assert(x.len() == y.len());
            assert forall|i: int| 0 <= i < x.len() implies x[i] == y[i] by {
                assert((x + tail)[i] == (y + tail)[i]);
            }
            assert(x =~= y);
            assert forall|j: int| 0 <= j < a.len() implies clazel_url::host::lemmas::free_of(#[trigger] a[j], 0x2E) by {
                assert(a[j] == d[d.len() - k + j]);
            }
            super::join::lemma_join_injective(a, d);
            assert(a.len() == d.len());
        }
    }
}

// ---------------------------------------------------------------------
// Suffixes in labels and the cookie root (items 2.4 and 2.9).
// ---------------------------------------------------------------------

/// A suffix of `d` with `m` labels is a string suffix of `d`.
pub proof fn lemma_label_suffix_is_string_suffix(d: Seq<u32>, m: nat)
    requires
        1 <= m <= domain_labels(d).len(),
    ensures
        label_suffix(domain_labels(d), has_trailing_dot(d), m).is_suffix_of(d),
{
    let dl = domain_labels(d);
    let td = has_trailing_dot(d);
    let n = dl.len();
    lemma_domain_labels_join(d);
    let tail = if td {
        seq![0x2Eu32]
    } else {
        seq![]
    };
    let s = label_suffix(dl, td, m);
    if m == n {
        assert(dl.skip(0) =~= dl);
        assert(s == d);
    } else {
        let pre = dl.take((n - m) as int);
        let sub = dl.skip((n - m) as int);
        assert(dl =~= pre + sub);
        assert(pre.len() >= 1);
        assert(sub.len() >= 1);
        super::join::lemma_split_join_concat(pre, sub);
        let jp = clazel_url::host::lemmas::split_join(pre, 0x2E);
        let js = clazel_url::host::lemmas::split_join(sub, 0x2E);
        assert(d =~= (jp + seq![0x2Eu32]) + (js + tail));
        assert(s =~= js + tail);
    }
}

/// The labels of a suffix of `d` with `m` labels are the last `m` labels
/// of `d`, with the same trailing dot.
pub proof fn lemma_label_suffix_labels(d: Seq<u32>, m: nat)
    requires
        1 <= m <= domain_labels(d).len(),
    ensures
        domain_labels(label_suffix(domain_labels(d), has_trailing_dot(d), m)) == domain_labels(d).skip(domain_labels(d).len() - m),
        has_trailing_dot(label_suffix(domain_labels(d), has_trailing_dot(d), m)) == has_trailing_dot(d),
{
    let dl = domain_labels(d);
    let td = has_trailing_dot(d);
    lemma_domain_labels_join(d);
    lemma_label_suffix_is_string_suffix(d, m);
    let s = label_suffix(dl, td, m);
    let sub = dl.skip((dl.len() - m) as int);
    let js = clazel_url::host::lemmas::split_join(sub, 0x2E);
    assert(sub.len() >= 1);
    assert forall|k: int| 0 <= k < sub.len() implies clazel_url::host::lemmas::free_of(#[trigger] sub[k], 0x2E) by {
        assert(sub[k] == dl[dl.len() - m + k]);
    }
    if td {
        assert(s =~= js + seq![0x2Eu32]);
        assert(has_trailing_dot(s));
        assert(strip_trailing_dot(s) =~= js);
    } else {
        assert(s =~= js);
        if s.len() > 0 {
            assert(s.last() == d.last());
        }
        assert(!has_trailing_dot(s));
        assert(strip_trailing_dot(s) =~= js);
    }
    clazel_url::host::lemmas::lemma_strictly_split_join(sub, 0x2E);
}

/// A suffix of a suffix: the `k` last labels of the suffix of `d` with `m`
/// labels are the `k` last labels of `d`.
pub proof fn lemma_label_suffix_of_suffix(d: Seq<u32>, m: nat, k: nat)
    requires
        1 <= k <= m <= domain_labels(d).len(),
    ensures
        label_suffix(
            domain_labels(label_suffix(domain_labels(d), has_trailing_dot(d), m)),
            has_trailing_dot(label_suffix(domain_labels(d), has_trailing_dot(d), m)),
            k,
        ) == label_suffix(domain_labels(d), has_trailing_dot(d), k),
{
    let dl = domain_labels(d);
    lemma_label_suffix_labels(d, m);
    let sub = dl.skip((dl.len() - m) as int);
    assert(sub.skip((m - k) as int) =~= dl.skip((dl.len() - k) as int));
}

/// The search for the cookie root from `k` on, in the suffix `s` of `d`
/// with `m` labels, finds what the search in `d` finds, once `s` is not a
/// public suffix (or is `d`).
pub proof fn lemma_root_from_suffix(rules: Seq<Rule>, d: Seq<u32>, m: nat, k: nat)
    requires
        1 <= k <= m <= domain_labels(d).len(),
        m == domain_labels(d).len() || !is_public_suffix(rules, label_suffix(domain_labels(d), has_trailing_dot(d), m)),
    ensures
        cookie_root_from(rules, label_suffix(domain_labels(d), has_trailing_dot(d), m), k) == cookie_root_from(rules, d, k),
    decreases m - k,
{
    let dl = domain_labels(d);
    let td = has_trailing_dot(d);
    let s = label_suffix(dl, td, m);
    lemma_label_suffix_labels(d, m);
    let sl = domain_labels(s);
    assert(sl.len() == m);
    if m == dl.len() {
        lemma_label_suffix_is_domain(d, m);
        assert(s == d);
    } else {
        lemma_label_suffix_of_suffix(d, m, k);
        if k == m {
            assert(label_suffix(dl, td, k) == s);
            assert(cookie_root_from(rules, s, k) == s);
            assert(cookie_root_from(rules, d, k) == s);
        } else {
            lemma_root_from_suffix(rules, d, m, k + 1);
            assert(label_suffix(sl, has_trailing_dot(s), k) == label_suffix(dl, td, k));
        }
    }
}

/// The cookie root of a suffix of a domain that is not a public suffix.
/// Statement: [`root_of_suffix_statement`].
pub proof fn lemma_root_of_suffix(rules: Seq<Rule>, d: Seq<u32>, s: Seq<u32>)
    ensures
        root_of_suffix_statement(rules, d, s),
{
    if is_label_suffix(d, s) && !is_public_suffix(rules, s) {
        let m = choose|k: nat| 1 <= k <= domain_labels(d).len() && s == label_suffix(domain_labels(d), has_trailing_dot(d), k);
        lemma_root_from_suffix(rules, d, m, 1);
        lemma_root_is_label_suffix(rules, s);
    }
}

/// The cookie root of a domain is a suffix of it, in labels.
pub proof fn lemma_root_from_is_label_suffix(rules: Seq<Rule>, d: Seq<u32>, k: nat)
    requires
        1 <= k,
    ensures
        is_label_suffix(d, cookie_root_from(rules, d, k)),
    decreases domain_labels(d).len() - k,
{
    let dl = domain_labels(d);
    let td = has_trailing_dot(d);
    lemma_domain_labels_join(d);
    if k >= dl.len() {
        lemma_label_suffix_is_domain(d, dl.len());
        assert(label_suffix(dl, td, dl.len()) == d);
    } else if !is_public_suffix(rules, label_suffix(dl, td, k)) {
        assert(label_suffix(dl, td, k) == cookie_root_from(rules, d, k));
    } else {
        lemma_root_from_is_label_suffix(rules, d, k + 1);
    }
}

/// The cookie root of a domain is a suffix of it, in labels.
pub proof fn lemma_root_is_label_suffix(rules: Seq<Rule>, d: Seq<u32>)
    ensures
        is_label_suffix(d, cookie_root_of_domain(rules, d)),
{
    lemma_root_from_is_label_suffix(rules, d, 1);
}

/// The cookie root is either the domain itself or not a public suffix.
pub proof fn lemma_root_from_not_public(rules: Seq<Rule>, d: Seq<u32>, k: nat)
    requires
        1 <= k,
    ensures
        cookie_root_from(rules, d, k) == d || !is_public_suffix(rules, cookie_root_from(rules, d, k)),
    decreases domain_labels(d).len() - k,
{
    let dl = domain_labels(d);
    if k >= dl.len() {
    } else if !is_public_suffix(rules, label_suffix(dl, has_trailing_dot(d), k)) {
    } else {
        lemma_root_from_not_public(rules, d, k + 1);
    }
}

/// The cookie root of a domain is the domain or not a public suffix.
pub proof fn lemma_root_not_public_or_domain(rules: Seq<Rule>, d: Seq<u32>)
    ensures
        cookie_root_of_domain(rules, d) == d || !is_public_suffix(rules, cookie_root_of_domain(rules, d)),
{
    lemma_root_from_not_public(rules, d, 1);
}

/// The cookie root of a cookie root is itself.
pub proof fn lemma_root_idempotent(rules: Seq<Rule>, d: Seq<u32>)
    ensures
        cookie_root_of_domain(rules, cookie_root_of_domain(rules, d)) == cookie_root_of_domain(rules, d),
{
    let r = cookie_root_of_domain(rules, d);
    lemma_root_not_public_or_domain(rules, d);
    lemma_root_is_label_suffix(rules, d);
    if r != d {
        lemma_root_of_suffix(rules, d, r);
    }
}

/// A non-empty domain string that domain-matches the host is a suffix of it
/// in labels.
pub proof fn lemma_domain_match_is_label_suffix(h: Seq<u32>, c: Seq<u32>)
    requires
        c.len() > 0,
        domain_match_u32(h, c),
    ensures
        is_label_suffix(h, c),
{
    if h == c {
        lemma_domain_labels_join(h);
        lemma_label_suffix_is_domain(h, domain_labels(h).len());
        assert(label_suffix(domain_labels(h), has_trailing_dot(h), domain_labels(h).len()) == h);
    } else {
        let p = h.subrange(0, (h.len() - c.len() - 1) as int);
        assert(h =~= p + seq![0x2Eu32] + c);
        let td = has_trailing_dot(c);
        assert(has_trailing_dot(h) == td);
        lemma_domain_labels_join(c);
        let cl = domain_labels(c);
        super::join::lemma_split_join_round_trip(p);
        let pl = clazel_url::host::spec::strictly_split(p, 0x2E);
        let all = pl + cl;
        super::join::lemma_split_join_concat(pl, cl);
        assert forall|k: int| 0 <= k < all.len() implies clazel_url::host::lemmas::free_of(#[trigger] all[k], 0x2E) by {
            if k < pl.len() {
                assert(all[k] == pl[k]);
            } else {
                assert(all[k] == cl[k - pl.len()]);
            }
        }
        let sc = strip_trailing_dot(c);
        assert(strip_trailing_dot(h) =~= p + seq![0x2Eu32] + sc) by {
            if td {
                assert(h.drop_last() =~= p + seq![0x2Eu32] + c.drop_last());
            }
        }
        assert(clazel_url::host::lemmas::split_join(all, 0x2E) =~= strip_trailing_dot(h));
        clazel_url::host::lemmas::lemma_strictly_split_join(all, 0x2E);
        assert(domain_labels(h) == all);
        assert(all.skip(all.len() - cl.len()) =~= cl);
        assert(label_suffix(all, td, cl.len()) =~= c);
    }
}

/// A non-empty cookie domain that domain-matches a host, and is not a
/// public suffix, has the host's cookie root. Statement:
/// [`domain_match_root_statement`].
pub proof fn lemma_domain_match_same_root(rules: Seq<Rule>, h: Seq<u32>, c: Seq<u32>)
    ensures
        domain_match_root_statement(rules, h, c),
{
    if c.len() > 0 && domain_match_u32(h, c) && !is_public_suffix(rules, c) {
        lemma_domain_match_is_label_suffix(h, c);
        lemma_root_of_suffix(rules, h, c);
    }
}

/// The same for hosts: for a domain-matching cookie domain that is the
/// host itself or not a public suffix, the cookie roots of the two hosts
/// are equal.
pub proof fn lemma_domain_match_same_cookie_root(rules: Seq<Rule>, h: Seq<u32>, c: Seq<u32>)
    requires
        c.len() > 0,
        domain_match_u32(h, c),
        h == c || !is_public_suffix(rules, c),
    ensures
        cookie_root(rules, clazel_url::host::spec::Host::Domain(c)) == cookie_root(rules, clazel_url::host::spec::Host::Domain(h)),
{
    if h != c {
        lemma_domain_match_same_root(rules, h, c);
    }
}

/// The ICANN section is a proper prefix of the list: it leaves the private
/// section's rules out, and keeps the rest as they are.
pub proof fn lemma_icann_rules_are_a_proper_prefix()
    ensures
        super::table::psl_icann_rules().len() < super::table::psl_rules().len(),
        forall|i: int|
            0 <= i < super::table::psl_icann_rules().len() ==> #[trigger] super::table::psl_icann_rules()[i]
                == super::table::psl_rules()[i],
{
    assert(super::data::PSL_ICANN_RULES_LEN < super::data::PSL_RULES_LEN);
}

} // verus!
