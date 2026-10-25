//! Executable string helpers: octet classes, tokens, field names,
//! whitespace and field values, each proven to meet [`super::contract`].
//! The step comments are in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A copy of `s`.
pub fn copy(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// Append `s` to `out`.
pub fn append(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost start = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == start + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c);
        }
        assert(s@.subrange(0, i as int).push(s@[i as int]) =~= s@.subrange(0, i as int + 1));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
}

/// The octet at `position`, if `position` is not past the end.
pub fn at(input: &[u8], position: usize) -> (r: Option<u8>)
    ensures
        position < input.len() ==> r == Some(input@[position as int]),
        position >= input.len() ==> r is None,
{
    if let Some(c) = input.get(position) {
        return Some(*c);
    }
    None
}

/// `is_tchar` (§5.6.2).
pub fn is_tchar_exec(c: u8) -> (r: bool)
    ensures
        r == is_tchar(c),
{
    c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27
        || c == 0x2A || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F
        || c == 0x60 || c == 0x7C || c == 0x7E || (0x30..=0x39).contains(&c)
        || (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c)
}

/// Does `c` belong to `class`?
pub fn in_class_exec(class: &Class, c: u8) -> (r: bool)
    ensures
        r == in_class(*class, c),
{
    match class {
        Class::Tchar => is_tchar_exec(c),
        Class::Digit => (0x30..=0x39).contains(&c),
        Class::Ows => c == 0x09 || c == 0x20,
        Class::FieldContent => c == 0x09 || c == 0x20 || (0x21..=0x7E).contains(&c) || c >= 0x80,
        Class::QuotedPair => c == 0x09 || c == 0x20 || (0x21..=0x7E).contains(&c) || c >= 0x80,
    }
}

/// The length of the longest prefix of `s` of octets in `class`.
pub fn run_len_exec(class: &Class, s: &[u8]) -> (n: usize)
    ensures
        n == run_len(*class, s@),
        n <= s.len(),
{
    assert(s@.skip(0) =~= s@);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            run_len(*class, s@) == i + run_len(*class, s@.skip(i as int)),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => return i,
        };
        assert(s@.skip(i as int)[0] == s@[i as int]);
        assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
        if !in_class_exec(class, c) {
            return i;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.skip(i as int).len() == 0);
    i
}

/// Does every octet of `s` belong to `class`?
pub fn all_in_exec(s: &[u8], class: &Class) -> (r: bool)
    ensures
        r == all_in(s@, *class),
{
    proof {
        super::lemmas::lemma_all_in_run_len(s@, *class);
    }
    run_len_exec(class, s) == s.len()
}

/// Are `a` and `b` the same string?
pub fn slice_eq(a: &[u8], b: &[u8]) -> (r: bool)
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
        if at(a, i) != at(b, i) {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// `is_token` (§5.6.2).
pub fn is_token(s: &[u8]) -> (r: bool)
    ensures
        super::contract::is_token_ensures(s@, r),
{
    !s.is_empty() && all_in_exec(s, &Class::Tchar)
}

/// `is_field_name` (§5.1).
pub fn is_field_name(s: &[u8]) -> (r: bool)
    ensures
        super::contract::is_field_name_ensures(s@, r),
{
    is_token(s)
}

/// ASCII lowercase of one octet.
fn lower(c: u8) -> (r: u8)
    ensures
        r == (if 0x41 <= c <= 0x5A { (c + 0x20) as u8 } else { c }),
{
    if (0x41..=0x5A).contains(&c) {
        // Never saturates: c <= 0x5A.
        c.saturating_add(0x20)
    } else {
        c
    }
}

/// `field_name_eq` (§5.1): equal after ASCII lowercase.
pub fn field_name_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        super::contract::field_name_eq_ensures(a@, b@, r),
{
    if a.len() != b.len() {
        proof {
            assert(ascii_lowercase(a@).len() != ascii_lowercase(b@).len());
        }
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] ascii_lowercase(a@)[k] == ascii_lowercase(b@)[k],
        decreases a.len() - i,
    {
        let (x, y) = match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => (*x, *y),
            _ => return false,
        };
        if lower(x) != lower(y) {
            proof {
                assert(ascii_lowercase(a@)[i as int] != ascii_lowercase(b@)[i as int]);
            }
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(ascii_lowercase(a@) =~= ascii_lowercase(b@));
    true
}

/// `is_ows` (§5.6.3).
pub fn is_ows(s: &[u8]) -> (r: bool)
    ensures
        super::contract::is_ows_ensures(s@, r),
{
    all_in_exec(s, &Class::Ows)
}

/// `is_rws` (§5.6.3).
pub fn is_rws(s: &[u8]) -> (r: bool)
    ensures
        super::contract::is_rws_ensures(s@, r),
{
    !s.is_empty() && all_in_exec(s, &Class::Ows)
}

/// `is_bws` (§5.6.3).
pub fn is_bws(s: &[u8]) -> (r: bool)
    ensures
        super::contract::is_bws_ensures(s@, r),
{
    is_ows(s)
}

/// Is `s[i]` an OWS octet?
fn ows_at(s: &[u8], i: usize) -> (r: bool)
    requires
        i < s.len(),
    ensures
        r == is_ows_octet(s@[i as int]),
{
    match s.get(i) {
        Some(c) => *c == 0x09 || *c == 0x20,
        None => false,
    }
}

/// `s` without its trailing OWS.
pub fn strip_trailing_ows_exec(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == strip_trailing_ows(s@),
{
    let mut end = s.len();
    assert(s@.subrange(0, end as int) =~= s@);
    // Never saturates: end > 0.
    while end > 0 && ows_at(s, end.saturating_sub(1))
        invariant
            end <= s.len(),
            strip_trailing_ows(s@) == strip_trailing_ows(s@.subrange(0, end as int)),
        decreases end,
    {
        let last = end.saturating_sub(1);
        assert(s@.subrange(0, end as int).last() == s@[last as int]);
        assert(s@.subrange(0, end as int).drop_last() =~= s@.subrange(0, last as int));
        end = last;
    }
    if end > 0 {
        assert(s@.subrange(0, end as int).last() == s@[end - 1]);
    }
    let out = copy(vstd::slice::slice_subrange(s, 0, end));
    assert(out@ =~= s@.subrange(0, end as int));
    out
}

/// `strip_ows` (§5.5, §5.6.3): `s` without leading and trailing OWS.
pub fn strip_ows(s: &[u8]) -> (out: Vec<u8>)
    ensures
        super::contract::strip_ows_ensures(s@, out@),
{
    let start = run_len_exec(&Class::Ows, s);
    let rest = vstd::slice::slice_subrange(s, start, s.len());
    assert(rest@ == strip_leading_ows(s@));
    strip_trailing_ows_exec(rest)
}

/// `is_field_vchar` (§5.5).
fn is_field_vchar_exec(c: u8) -> (r: bool)
    ensures
        r == is_field_vchar(c),
{
    (0x21..=0x7E).contains(&c) || c >= 0x80
}

/// `is_field_value` (§5.5).
pub fn is_field_value(s: &[u8]) -> (r: bool)
    ensures
        super::contract::is_field_value_ensures(s@, r),
{
    let (first, last) = match (s.first(), s.last()) {
        (Some(f), Some(l)) => (*f, *l),
        _ => return true,
    };
    is_field_vchar_exec(first) && is_field_vchar_exec(last) && all_in_exec(s, &Class::FieldContent)
}

} // verus!
