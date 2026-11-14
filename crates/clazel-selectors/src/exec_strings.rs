//! The string tests of matching (§6, §6.6, §7, §15.2), proven equal to their spec functions.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The code point at `i`.
fn at(s: &[u32], i: usize) -> (c: u32)
    requires
        i < s.len(),
    ensures
        c == s@[i as int],
{
    *super::exec_types::item(s, i)
}

/// True if the two strings are identical.
pub fn same(a: &[u32], b: &[u32]) -> (r: bool)
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
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if at(a, i) != at(b, i) {
            return false;
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// The ASCII lowercase of `s`.
pub fn lowered(s: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == to_ascii_lowercase(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> out@[j] == ascii_lowercase(s@[j]),
        decreases s.len() - i,
    {
        out.push(clazel_css::parser::exec_declaration::lowercase(at(s, i)));
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= to_ascii_lowercase(s@));
    }
    out
}

/// True if the lowercase of `name` is `target`.
pub fn lowered_is(name: &[u32], target: &[u32]) -> (r: bool)
    ensures
        r == (to_ascii_lowercase(name@) == target@),
{
    let l = lowered(name);
    same(l.as_slice(), target)
}

/// Selectors' white space.
pub fn is_white(c: u32) -> (r: bool)
    ensures
        r == is_selector_whitespace(c),
{
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x0C
}

/// [`occurs_at`].
pub fn occurs(v: &[u32], s: &[u32], i: usize) -> (r: bool)
    ensures
        r == occurs_at(v@, s@, i as int),
{
    if s.len() > v.len() || i > v.len().saturating_sub(s.len()) {
        return false;
    }
    let mut k: usize = 0;
    while k < s.len()
        invariant
            k <= s.len(),
            i + s.len() <= v.len(),
            forall|j: int| 0 <= j < k ==> v@[i + j] == s@[j],
        decreases s.len() - k,
    {
        if at(v, i.saturating_add(k)) != at(s, k) {
            proof {
                assert(v@.subrange(i as int, i + s.len() as int)[k as int] != s@[k as int]);
            }
            return false;
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(v@.subrange(i as int, i + s.len() as int) =~= s@);
    }
    true
}

/// [`no_whitespace_from`] at 0.
pub fn has_no_white(s: &[u32]) -> (r: bool)
    ensures
        r == no_whitespace_from(s@, 0),
{
    let mut i = s.len();
    proof {
        assert(no_whitespace_from(s@, i as int));
    }
    while i > 0
        invariant
            i <= s.len(),
            no_whitespace_from(s@, i as int),
        decreases i,
    {
        i = i.saturating_sub(1);
        if is_white(at(s, i)) {
            proof {
                lemma_white_stops(s@, 0, i as int);
            }
            return false;
        }
    }
    true
}

/// A white space code point at `k` makes [`no_whitespace_from`] false from any earlier `i`.
proof fn lemma_white_stops(s: Seq<u32>, i: int, k: int)
    requires
        0 <= i <= k < s.len(),
        is_selector_whitespace(s[k]),
    ensures
        !no_whitespace_from(s, i),
    decreases k - i,
{
    if i < k {
        lemma_white_stops(s, i + 1, k);
    }
}

/// [`occurs_up_to`] at `v.len() - s.len()`: `s` occurs somewhere in `v`.
pub fn occurs_anywhere(v: &[u32], s: &[u32]) -> (r: bool)
    ensures
        r == occurs_up_to(v@, s@, v.len() - s.len()),
{
    if s.len() > v.len() {
        return false;
    }
    let last = v.len().saturating_sub(s.len());
    let mut i: usize = 0;
    let mut found = false;
    while i < last
        invariant
            last == v.len() - s.len(),
            i <= last,
            found == occurs_up_to(v@, s@, i - 1),
        decreases last - i,
    {
        found = found || occurs(v, s, i);
        i = i.saturating_add(1);
    }
    found || occurs(v, s, last)
}

/// [`word_up_to`] at `v.len() - s.len()`.
pub fn word_anywhere(v: &[u32], s: &[u32]) -> (r: bool)
    ensures
        r == word_up_to(v@, s@, v.len() - s.len()),
{
    if s.len() > v.len() {
        return false;
    }
    let last = v.len().saturating_sub(s.len());
    let mut i: usize = 0;
    let mut found = false;
    while i <= last
        invariant
            last == v.len() - s.len(),
            i <= last + 1,
            found == word_up_to(v@, s@, i - 1),
        decreases last + 1 - i,
    {
        let here = word_at(v, s, i);
        found = found || here;
        if i == last {
            return found;
        }
        i = i.saturating_add(1);
    }
    found
}

/// One step of [`word_up_to`]: `s` occurs at `i` with white space or an end on each side.
fn word_at(v: &[u32], s: &[u32], i: usize) -> (r: bool)
    requires
        i + s.len() <= v.len(),
    ensures
        r == (occurs_at(v@, s@, i as int) && (i == 0 || is_selector_whitespace(v@[i - 1])) && (
        i + s.len() == v.len() || is_selector_whitespace(v@[i + s.len()]))),
{
    let end = i.saturating_add(s.len());
    occurs(v, s, i) && (i == 0 || is_white(at(v, i.saturating_sub(1)))) && (end == v.len()
        || is_white(at(v, end)))
}

/// [`is_one_of_the_words`].
pub fn one_of_the_words(v: &[u32], s: &[u32]) -> (r: bool)
    ensures
        r == is_one_of_the_words(v@, s@),
{
    !s.is_empty() && has_no_white(s) && word_anywhere(v, s)
}

/// [`value_matches`].
pub fn value_test(matcher: AttrMatcher, v: &[u32], s: &[u32]) -> (r: bool)
    ensures
        r == value_matches(matcher, v@, s@),
{
    match matcher {
        AttrMatcher::Equals => same(v, s),
        AttrMatcher::Includes => one_of_the_words(v, s),
        AttrMatcher::DashMatch => same(v, s) || (occurs(v, s, 0) && s.len() < v.len() && at(
            v,
            s.len(),
        ) == 0x2D),
        AttrMatcher::Prefix => !s.is_empty() && occurs(v, s, 0),
        AttrMatcher::Suffix => !s.is_empty() && s.len() <= v.len() && occurs(
            v,
            s,
            v.len().saturating_sub(s.len()),
        ),
        AttrMatcher::Substring => !s.is_empty() && occurs_anywhere(v, s),
    }
}

/// [`all_whitespace`] at 0.
pub fn all_white(data: &[u32]) -> (r: bool)
    ensures
        r == all_whitespace(data@, 0),
{
    let mut i = data.len();
    proof {
        assert(all_whitespace(data@, i as int));
    }
    while i > 0
        invariant
            i <= data.len(),
            all_whitespace(data@, i as int),
        decreases i,
    {
        i = i.saturating_sub(1);
        if !is_white(at(data, i)) {
            proof {
                lemma_not_white_stops(data@, 0, i as int);
            }
            return false;
        }
    }
    true
}

/// A code point that is not white space at `k` makes [`all_whitespace`] false from any
/// earlier `i`.
proof fn lemma_not_white_stops(s: Seq<u32>, i: int, k: int)
    requires
        0 <= i <= k < s.len(),
        !is_selector_whitespace(s[k]),
    ensures
        !all_whitespace(s, i),
    decreases k - i,
{
    if i < k {
        lemma_not_white_stops(s, i + 1, k);
    }
}

/// HTML §4.16.2's list ([`is_case_insensitive_attribute`]).
pub fn case_insensitive_name(name: &[u32]) -> (r: bool)
    ensures
        r == is_case_insensitive_attribute(name@),
{
    same(name, &[0x61, 0x63, 0x63, 0x65, 0x70, 0x74])
        || same(name, &[0x61, 0x63, 0x63, 0x65, 0x70, 0x74, 0x2D, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74])
        || same(name, &[0x61, 0x6C, 0x69, 0x67, 0x6E])
        || same(name, &[0x61, 0x6C, 0x69, 0x6E, 0x6B])
        || same(name, &[0x61, 0x78, 0x69, 0x73])
        || same(name, &[0x62, 0x67, 0x63, 0x6F, 0x6C, 0x6F, 0x72])
        || same(name, &[0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74])
        || same(name, &[0x63, 0x68, 0x65, 0x63, 0x6B, 0x65, 0x64])
        || same(name, &[0x63, 0x6C, 0x65, 0x61, 0x72])
        || same(name, &[0x63, 0x6F, 0x64, 0x65, 0x74, 0x79, 0x70, 0x65])
        || same(name, &[0x63, 0x6F, 0x6C, 0x6F, 0x72])
        || same(name, &[0x63, 0x6F, 0x6D, 0x70, 0x61, 0x63, 0x74])
        || same(name, &[0x64, 0x65, 0x63, 0x6C, 0x61, 0x72, 0x65])
        || same(name, &[0x64, 0x65, 0x66, 0x65, 0x72])
        || same(name, &[0x64, 0x69, 0x72])
        || same(name, &[0x64, 0x69, 0x72, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E])
        || same(name, &[0x64, 0x69, 0x73, 0x61, 0x62, 0x6C, 0x65, 0x64])
        || same(name, &[0x65, 0x6E, 0x63, 0x74, 0x79, 0x70, 0x65])
        || same(name, &[0x66, 0x61, 0x63, 0x65])
        || same(name, &[0x66, 0x72, 0x61, 0x6D, 0x65])
        || same(name, &[0x68, 0x72, 0x65, 0x66, 0x6C, 0x61, 0x6E, 0x67])
        || same(name, &[0x68, 0x74, 0x74, 0x70, 0x2D, 0x65, 0x71, 0x75, 0x69, 0x76])
        || same(name, &[0x6C, 0x61, 0x6E, 0x67])
        || same(name, &[0x6C, 0x61, 0x6E, 0x67, 0x75, 0x61, 0x67, 0x65])
        || same(name, &[0x6C, 0x69, 0x6E, 0x6B])
        || same(name, &[0x6D, 0x65, 0x64, 0x69, 0x61])
        || same(name, &[0x6D, 0x65, 0x74, 0x68, 0x6F, 0x64])
        || same(name, &[0x6D, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x6C, 0x65])
        || same(name, &[0x6E, 0x6F, 0x68, 0x72, 0x65, 0x66])
        || same(name, &[0x6E, 0x6F, 0x72, 0x65, 0x73, 0x69, 0x7A, 0x65])
        || same(name, &[0x6E, 0x6F, 0x73, 0x68, 0x61, 0x64, 0x65])
        || same(name, &[0x6E, 0x6F, 0x77, 0x72, 0x61, 0x70])
        || same(name, &[0x72, 0x65, 0x61, 0x64, 0x6F, 0x6E, 0x6C, 0x79])
        || same(name, &[0x72, 0x65, 0x6C])
        || same(name, &[0x72, 0x65, 0x76])
        || same(name, &[0x72, 0x75, 0x6C, 0x65, 0x73])
        || same(name, &[0x73, 0x63, 0x6F, 0x70, 0x65])
        || same(name, &[0x73, 0x63, 0x72, 0x6F, 0x6C, 0x6C, 0x69, 0x6E, 0x67])
        || same(name, &[0x73, 0x65, 0x6C, 0x65, 0x63, 0x74, 0x65, 0x64])
        || same(name, &[0x73, 0x68, 0x61, 0x70, 0x65])
        || same(name, &[0x74, 0x61, 0x72, 0x67, 0x65, 0x74])
        || same(name, &[0x74, 0x65, 0x78, 0x74])
        || same(name, &[0x74, 0x79, 0x70, 0x65])
        || same(name, &[0x76, 0x61, 0x6C, 0x69, 0x67, 0x6E])
        || same(name, &[0x76, 0x61, 0x6C, 0x75, 0x65, 0x74, 0x79, 0x70, 0x65])
        || same(name, &[0x76, 0x6C, 0x69, 0x6E, 0x6B])
}

} // verus!
