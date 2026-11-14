//! The executable Public Suffix List lookups, each proven to meet its
//! contract in [`super::contract`] relative to the generated tables.
//!
//! The lookup scans every rule once, in list order, as the spec's
//! [`prevailing_from`] does. (It does not bisect: the proofs do not assume
//! the generated tables are sorted, which Verus cannot see through the
//! opaque constants, so a scan is what is provably the standard's "match
//! domain against all rules". A rule that cannot beat the best so far is
//! skipped before it is matched.)

use super::data::*;
#[allow(unused_imports)]
use super::spec::*;
use super::tables::*;
use clazel_url::host::ipv4::strictly_split_exec;
use clazel_url::host::record::{ParsedHost, append, copy};
use clazel_url::url::record::clone_host;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Row `first + j` of the labels table.
fn labels_row_at(first: u32, j: u32) -> (r: LabelRow)
    ensures
        r == super::data::psl_labels_at(first as int + j as int),
{
    match first.checked_add(j) {
        Some(i) => psl_labels_at_exec(i as usize),
        // Past u32::MAX is past the table, where the row is the dummy.
        None => psl_labels_at_exec(usize::MAX),
    }
}

/// Character `start + c` of the characters table.
fn chars_at_sum(start: u32, c: u32) -> (r: u8)
    ensures
        r == super::data::psl_chars_at(start as int + c as int),
{
    match start.checked_add(c) {
        Some(i) => psl_chars_at_exec(i as usize),
        // Past u32::MAX is past the table, where the character is 0.
        None => psl_chars_at_exec(usize::MAX),
    }
}

/// The label of `row` equals `label`.
fn row_equals(row: LabelRow, label: &[u32]) -> (r: bool)
    ensures
        r == (super::table::label_row_text(row) == label@),
{
    if row.len as usize != label.len() {
        return false;
    }
    let mut c: usize = 0;
    while c < label.len()
        invariant
            c <= label.len(),
            label.len() == row.len as usize,
            forall|i: int| 0 <= i < c ==> super::data::psl_chars_at(row.start as int + i) as u32 == label@[i],
        decreases label.len() - c,
    {
        let ch = chars_at_sum(row.start, c as u32);
        let expected = match label.get(c) {
            Some(e) => *e,
            // Unreachable: c < label.len().
            None => 0,
        };
        if ch as u32 != expected {
            proof {
                assert(super::table::label_row_text(row)[c as int] == super::data::psl_chars_at(row.start as int + c as int) as u32);
                assert(super::table::label_row_text(row) != label@);
            }
            return false;
        }
        c = c.saturating_add(1);
    }
    proof {
        assert(super::table::label_row_text(row) =~= label@);
    }
    true
}

/// The label of `row` is `*`.
fn row_is_star(row: LabelRow) -> (r: bool)
    ensures
        r == (super::table::label_row_text(row) == star_label()),
{
    if row.len != 1 {
        return false;
    }
    let ch = chars_at_sum(row.start, 0);
    let r = ch == 0x2A;
    proof {
        assert(super::table::label_row_text(row).len() == 1);
        assert(super::table::label_row_text(row) == star_label() <==> super::table::label_row_text(row)[0] == 0x2Au32) by {
            if super::table::label_row_text(row)[0] == 0x2Au32 {
                assert(super::table::label_row_text(row) =~= star_label());
            }
        }
    }
    r
}

/// The rule of `row` matches the domain with labels `d`.
fn row_matches(row: RuleRow, d: &[Vec<u32>]) -> (r: bool)
    ensures
        r == rule_matches(super::table::rule_of_row(row), clazel_url::host::record::parts_view(d@)),
{
    let n = row.count as usize;
    if n > d.len() {
        return false;
    }
    proof {
        super::lemmas::lemma_rule_matches_forall(super::table::rule_of_row(row), clazel_url::host::record::parts_view(d@));
    }
    let ghost dv = clazel_url::host::record::parts_view(d@);
    let ghost rule = super::table::rule_of_row(row);
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == row.count as usize,
            n <= d.len(),
            dv == clazel_url::host::record::parts_view(d@),
            rule == super::table::rule_of_row(row),
            rule.labels.len() == n,
            forall|i: int|
                0 <= i < k ==> label_matches(#[trigger] rule.labels[n - 1 - i], dv[d.len() - 1 - i]),
        decreases n - k,
    {
        // Never saturate: k < n, and n <= u32::MAX.
        let j: u32 = row.count.saturating_sub(1).saturating_sub(k as u32);
        let label_row = labels_row_at(row.first, j);
        let at = d.len().saturating_sub(1).saturating_sub(k);
        match d.get(at) {
            Some(l) => {
                proof {
                    assert(l@ == dv[d.len() - 1 - k as int]);
                    assert(rule.labels[n - 1 - k as int] == super::table::label_row_text(super::data::psl_labels_at(row.first as int + (n - 1 - k) as int)));
                }
                if !(row_equals(label_row, l.as_slice()) || row_is_star(label_row)) {
                    proof {
                        assert(!label_matches(rule.labels[n - 1 - k as int], dv[d.len() - 1 - k as int]));
                        super::lemmas::lemma_rule_matches_forall(rule, dv);
                        let kk = k as int;
                        assert(rule.labels.len() - 1 - kk == n - 1 - kk);
                        assert(!label_matches(rule.labels[rule.labels.len() - 1 - kk], dv[d.len() - 1 - kk]));
                        assert(!rule_matches(rule, dv));
                    }
                    return false;
                }
            },
            // Unreachable: at < d.len().
            None => {
                return false;
            },
        }
        k = k.saturating_add(1);
    }
    true
}

/// How many labels the public suffix has, for the domain with labels `d`,
/// scanning every rule of the list.
fn suffix_label_count_exec(d: &[Vec<u32>]) -> (k: usize)
    ensures
        k as nat == suffix_label_count(super::table::psl_rules(), clazel_url::host::record::parts_view(d@)),
{
    proof {
        assert(super::table::psl_rules().take(PSL_RULES_LEN as int) =~= super::table::psl_rules());
    }
    suffix_label_count_upto(d, PSL_RULES_LEN)
}

/// [`suffix_label_count_exec`] over the list's first `limit` rules.
fn suffix_label_count_upto(d: &[Vec<u32>], limit: usize) -> (k: usize)
    requires
        limit <= PSL_RULES_LEN,
    ensures
        k as nat == suffix_label_count(super::table::psl_rules().take(limit as int), clazel_url::host::record::parts_view(d@)),
{
    let ghost rules = super::table::psl_rules().take(limit as int);
    let ghost dv = clazel_url::host::record::parts_view(d@);
    let mut best: Option<RuleRow> = None;
    let mut i: usize = 0;
    while i < limit
        invariant
            i <= limit,
            limit <= PSL_RULES_LEN,
            rules == super::table::psl_rules().take(limit as int),
            rules.len() == limit,
            dv == clazel_url::host::record::parts_view(d@),
            (prevailing_from(rules, dv, i as nat) is None) == (best is None),
            best matches Some(b) ==> prevailing_from(rules, dv, i as nat) is Some && super::table::rule_of_row(b)
                == rules[prevailing_from(rules, dv, i as nat)->Some_0 as int],
        decreases limit - i,
    {
        let row = psl_rules_at_exec(i);
        proof {
            assert(rules[i as int] == super::table::psl_rules()[i as int]);
            assert(rules[i as int] == super::table::rule_of_row(row));
            assert(prevailing_from(rules, dv, (i + 1) as nat) == if rule_matches(rules[i as int], dv) && (
            prevailing_from(rules, dv, i as nat) is None || beats(
                rules[i as int],
                rules[prevailing_from(rules, dv, i as nat)->Some_0 as int],
            )) {
                Some(i as nat)
            } else {
                prevailing_from(rules, dv, i as nat)
            });
        }
        let worth = match best {
            None => true,
            Some(b) => (row.exception && !b.exception) || (!row.exception && !b.exception && row.count > b.count),
        };
        if worth && row_matches(row, d) {
            best = Some(row);
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(i == rules.len());
        match best {
            Some(b) => {
                super::lemmas::lemma_prevailing_matches(rules, dv, rules.len());
            },
            None => {},
        }
    }
    match best {
        None => 1,
        Some(b) => {
            if b.exception && b.count > 1 {
                (b.count as usize).saturating_sub(1)
            } else if b.count > 0 {
                b.count as usize
            } else {
                1
            }
        },
    }
}

/// `label` is empty somewhere in `labels`.
fn has_empty_label_exec(labels: &[Vec<u32>]) -> (r: bool)
    ensures
        r == has_empty_label(clazel_url::host::record::parts_view(labels@)),
{
    proof {
        super::lemmas::lemma_has_empty_label_exists(clazel_url::host::record::parts_view(labels@));
    }
    let mut i: usize = 0;
    while i < labels.len()
        invariant
            i <= labels.len(),
            forall|k: int| 0 <= k < i ==> clazel_url::host::record::parts_view(labels@)[k].len() != 0,
        decreases labels.len() - i,
    {
        match labels.get(i) {
            Some(l) if l.is_empty() => {
                proof {
                    assert(clazel_url::host::record::parts_view(labels@)[i as int].len() == 0);
                    super::lemmas::lemma_has_empty_label_exists(clazel_url::host::record::parts_view(labels@));
                    assert(has_empty_label(clazel_url::host::record::parts_view(labels@)));
                }
                return true;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    false
}

/// The last labels of `labels` from `from`, joined with ".", and with a
/// trailing dot if `trailing_dot`.
fn join_exec(labels: &[Vec<u32>], from: usize, trailing_dot: bool) -> (out: Vec<u32>)
    requires
        from < labels.len(),
    ensures
        out@ == labels_string(clazel_url::host::record::parts_view(labels@).skip(from as int), trailing_dot),
{
    let ghost lv = clazel_url::host::record::parts_view(labels@);
    let mut out: Vec<u32> = match labels.get(from) {
        Some(l) => copy(l.as_slice()),
        // Unreachable: from < labels.len().
        None => Vec::new(),
    };
    proof {
        assert(lv.subrange(from as int, from as int + 1) =~= seq![lv[from as int]]);
        assert(clazel_url::host::lemmas::split_join(lv.subrange(from as int, from as int + 1), 0x2E) =~= lv[from as int]) by {
            let s = lv.subrange(from as int, from as int + 1);
            assert(s.drop_first() =~= Seq::<Seq<u32>>::empty());
        }
    }
    let mut i: usize = from.saturating_add(1);
    while i < labels.len()
        invariant
            from < i <= labels.len(),
            lv == clazel_url::host::record::parts_view(labels@),
            out@ == clazel_url::host::lemmas::split_join(lv.subrange(from as int, i as int), 0x2E),
        decreases labels.len() - i,
    {
        let ghost before = lv.subrange(from as int, i as int);
        if let Some(l) = labels.get(i) {
            {
                out.push(0x2E);
                append(&mut out, l.as_slice());
                proof {
                    assert(l@ == lv[i as int]);
                    assert(lv.subrange(from as int, i as int + 1) =~= before.push(lv[i as int]));
                    super::join::lemma_split_join_push(before, lv[i as int]);
                    assert(out@ =~= clazel_url::host::lemmas::split_join(before, 0x2E) + seq![0x2Eu32] + lv[i as int]);
                }
            }
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(lv.subrange(from as int, labels.len() as int) =~= lv.skip(from as int));
    }
    if trailing_dot {
        out.push(0x2E);
        proof {
            assert(out@ =~= clazel_url::host::lemmas::split_join(lv.skip(from as int), 0x2E) + seq![0x2Eu32]);
        }
    } else {
        proof {
            assert(out@ =~= clazel_url::host::lemmas::split_join(lv.skip(from as int), 0x2E) + Seq::<u32>::empty());
        }
    }
    out
}

/// The domain's labels (with the trailing dot set aside) and whether it
/// had one.
fn split_domain(domain: &[u32]) -> (r: (Vec<Vec<u32>>, bool))
    ensures
        clazel_url::host::record::parts_view(r.0@) == domain_labels(domain@),
        r.1 == has_trailing_dot(domain@),
{
    let mut stripped = copy(domain);
    let td = match domain.get(domain.len().saturating_sub(1)) {
        Some(c) => !domain.is_empty() && *c == 0x2E,
        None => false,
    };
    if td {
        stripped.pop();
    }
    proof {
        assert(stripped@ == strip_trailing_dot(domain@));
    }
    let labels = strictly_split_exec(stripped.as_slice(), 0x2E);
    (labels, td)
}

/// Whether two code point strings are equal.
fn equal_exec(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) if *x != *y => {
                return false;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// URL §3.2 "obtain the public suffix of a host", for a domain.
pub fn public_suffix_of_domain_exec(domain: &[u32]) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::public_suffix_of_domain_ensures(domain@, clazel_url::host::record::opt_seq(output)),
{
    let (labels, td) = split_domain(domain);
    proof {
        super::lemmas::lemma_domain_labels_join(domain@);
    }
    if has_empty_label_exec(labels.as_slice()) {
        return None;
    }
    let k = suffix_label_count_exec(labels.as_slice());
    proof {
        super::lemmas::lemma_suffix_label_count_bounds(super::table::psl_rules(), clazel_url::host::record::parts_view(labels@));
    }
    // Never saturates: k <= labels.len().
    let from = labels.len().saturating_sub(k);
    Some(join_exec(labels.as_slice(), from, td))
}

/// URL §3.2 "obtain the registrable domain of a host", for a domain.
pub fn registrable_domain_of_domain_exec(domain: &[u32]) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::registrable_domain_of_domain_ensures(domain@, clazel_url::host::record::opt_seq(output)),
{
    let (labels, td) = split_domain(domain);
    proof {
        super::lemmas::lemma_domain_labels_join(domain@);
    }
    if has_empty_label_exec(labels.as_slice()) {
        return None;
    }
    let k = suffix_label_count_exec(labels.as_slice());
    proof {
        super::lemmas::lemma_suffix_label_count_bounds(super::table::psl_rules(), clazel_url::host::record::parts_view(labels@));
        super::lemmas::lemma_label_suffix_is_domain(domain@, k as nat);
    }
    if k >= labels.len() {
        // The public suffix is the domain: step 1.
        return None;
    }
    // Never saturates: k < labels.len().
    let from = labels.len().saturating_sub(k).saturating_sub(1);
    Some(join_exec(labels.as_slice(), from, td))
}

/// Whether `domain` is "a public suffix": obtaining its public suffix
/// returns it.
pub fn is_public_suffix_exec(domain: &[u32]) -> (output: bool)
    ensures
        super::contract::is_public_suffix_ensures(domain@, output),
{
    match public_suffix_of_domain_exec(domain) {
        None => false,
        Some(ps) => equal_exec(ps.as_slice(), domain),
    }
}

/// Whether `domain` is a public suffix under the list's ICANN section alone.
pub fn is_icann_public_suffix_exec(domain: &[u32]) -> (output: bool)
    ensures
        super::contract::is_icann_public_suffix_ensures(domain@, output),
{
    let (labels, td) = split_domain(domain);
    proof {
        super::lemmas::lemma_domain_labels_join(domain@);
    }
    if has_empty_label_exec(labels.as_slice()) {
        return false;
    }
    let k = suffix_label_count_upto(labels.as_slice(), PSL_ICANN_RULES_LEN);
    proof {
        super::lemmas::lemma_suffix_label_count_bounds(super::table::psl_icann_rules(), clazel_url::host::record::parts_view(labels@));
    }
    // Never saturates: k <= labels.len().
    let from = labels.len().saturating_sub(k);
    let suffix = join_exec(labels.as_slice(), from, td);
    equal_exec(suffix.as_slice(), domain)
}

/// The cookie root of a domain: the shortest suffix, in labels, that is
/// not a public suffix, or the domain itself.
pub fn cookie_root_of_domain_exec(domain: &[u32]) -> (output: Vec<u32>)
    ensures
        super::contract::cookie_root_of_domain_ensures(domain@, output@),
{
    let (labels, td) = split_domain(domain);
    let m = labels.len();
    let ghost rules = super::table::psl_rules();
    let mut k: usize = 1;
    while k < m
        invariant
            1 <= k,
            rules == super::table::psl_rules(),
            m == labels.len(),
            m == domain_labels(domain@).len(),
            td == has_trailing_dot(domain@),
            clazel_url::host::record::parts_view(labels@) == domain_labels(domain@),
            cookie_root_from(rules, domain@, 1) == cookie_root_from(rules, domain@, k as nat),
        decreases m - k,
    {
        // Never saturates: k < m.
        let from = m.saturating_sub(k);
        assert(m - k >= 1);
        let suffix = join_exec(labels.as_slice(), from, td);
        proof {
            assert(suffix@ == label_suffix(domain_labels(domain@), td, k as nat));
        }
        let is_ps = is_public_suffix_exec(suffix.as_slice());
        proof {
            let d = domain_labels(domain@);
            assert(is_ps == is_public_suffix(super::table::psl_rules(), suffix@));
            assert(is_ps == is_public_suffix(rules, label_suffix(d, td, k as nat)));
            assert(k < d.len());
            assert(cookie_root_from(rules, domain@, k as nat) == if !is_public_suffix(rules, label_suffix(d, td, k as nat)) {
                label_suffix(d, td, k as nat)
            } else {
                cookie_root_from(rules, domain@, (k + 1) as nat)
            });
        }
        if !is_ps {
            proof {
                assert(suffix@ == cookie_root_from(rules, domain@, k as nat));
                assert(cookie_root_from(rules, domain@, 1) == cookie_root_from(rules, domain@, k as nat));
            }
            return suffix;
        }
        k = k.saturating_add(1);
        proof {
            assert(k as nat == (k - 1) as nat + 1);
            assert(cookie_root_from(rules, domain@, (k - 1) as nat) == cookie_root_from(rules, domain@, k as nat));
        }
    }
    copy(domain)
}

/// URL §3.2 "obtain the public suffix of a host".
pub fn public_suffix_exec(host: &ParsedHost) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::public_suffix_ensures(host@, clazel_url::host::record::opt_seq(output)),
{
    match host {
        ParsedHost::Domain(s) => public_suffix_of_domain_exec(s.as_slice()),
        _ => None,
    }
}

/// URL §3.2 "obtain the registrable domain of a host".
pub fn registrable_domain_exec(host: &ParsedHost) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::registrable_domain_ensures(host@, clazel_url::host::record::opt_seq(output)),
{
    match host {
        ParsedHost::Domain(s) => registrable_domain_of_domain_exec(s.as_slice()),
        _ => None,
    }
}

/// The cookie root of a host.
pub fn cookie_root_exec(host: &ParsedHost) -> (output: ParsedHost)
    ensures
        super::contract::cookie_root_ensures(host@, output@),
{
    match host {
        ParsedHost::Domain(s) => ParsedHost::Domain(cookie_root_of_domain_exec(s.as_slice())),
        _ => clone_host(host),
    }
}

} // verus!
