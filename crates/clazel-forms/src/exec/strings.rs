//! The executable string functions of the form data set: each is proven
//! equal to the spec function it names (see [`crate::contract`]).

#[cfg(verus_only)]
use crate::contract::*;
#[allow(unused_imports)]
use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`ascii_lower_cp`].
pub fn lower_cp(c: u32) -> (r: u32)
    ensures
        r == ascii_lower_cp(c),
{
    if c >= 0x41 && c <= 0x5A {
        // Never saturates: c <= 0x5A.
        c.saturating_add(0x20)
    } else {
        c
    }
}

/// [`ci_eq`]: ASCII case-insensitive match with a lowercase ASCII keyword.
pub fn ci_eq_exec(s: &[u32], k: &[u8]) -> (r: bool)
    ensures
        ci_eq_ensures(s@, k@, r),
{
    if s.len() != k.len() {
        proof {
            assert(ascii_lower(s@).len() == s@.len());
            assert(ascii(k@).len() == k@.len());
        }
        return false;
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s.len() == k.len(),
            forall|j: int| 0 <= j < i ==> ascii_lower_cp(#[trigger] s@[j]) == k@[j] as u32,
        decreases s.len() - i,
    {
        match (s.get(i), k.get(i)) {
            (Some(a), Some(b)) => {
                if lower_cp(*a) != *b as u32 {
                    proof {
                        assert(ascii_lower(s@)[i as int] == ascii_lower_cp(s@[i as int]));
                        assert(ascii(k@)[i as int] == k@[i as int] as u32);
                    }
                    return false;
                }
            },
            _ => {
                return false;
            },
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(ascii_lower(s@) =~= ascii(k@));
    }
    true
}

/// Exact equality of `s` with an ASCII keyword.
pub fn eq_ascii(s: &[u32], k: &[u8]) -> (r: bool)
    ensures
        r == (s@ == ascii(k@)),
{
    if s.len() != k.len() {
        proof {
            assert(ascii(k@).len() == k@.len());
        }
        return false;
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s.len() == k.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] s@[j]) == k@[j] as u32,
        decreases s.len() - i,
    {
        match (s.get(i), k.get(i)) {
            (Some(a), Some(b)) => {
                if *a != *b as u32 {
                    proof {
                        assert(ascii(k@)[i as int] == k@[i as int] as u32);
                    }
                    return false;
                }
            },
            _ => {
                return false;
            },
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(s@ =~= ascii(k@));
    }
    true
}

/// [`strip_newlines`].
pub fn strip_newlines_exec(s: &[u32]) -> (r: Vec<u32>)
    ensures
        strip_newlines_ensures(s@, r@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            out@ + strip_newlines(s@.skip(i as int)) == strip_newlines(s@),
        decreases s.len() - i,
    {
        let ghost before = out@;
        if let Some(c) = s.get(i) {
            proof {
                assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                assert(s@.skip(i as int)[0] == s@[i as int]);
            }
            if *c != 0x0A && *c != 0x0D {
                out.push(*c);
                proof {
                    assert(out@ =~= before.push(*c));
                }
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    out
}

/// [`normalize_newlines`].
pub fn normalize_newlines_exec(s: &[u32]) -> (r: Vec<u32>)
    ensures
        normalize_newlines_ensures(s@, r@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            out@ + normalize_newlines(s@.skip(i as int)) == normalize_newlines(s@),
        decreases s.len() - i,
    {
        let ghost before = out@;
        if let Some(c) = s.get(i) {
            let c = *c;
            proof {
                assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                assert(s@.skip(i as int)[0] == s@[i as int]);
            }
            if c == 0x0D {
                out.push(0x0A);
                // Never saturates: i < s.len().
                let next = i.saturating_add(1);
                let crlf = match s.get(next) {
                    Some(d) => *d == 0x0A,
                    None => false,
                };
                proof {
                    assert(out@ =~= before.push(0x0A));
                    assert(s@.skip(i as int).len() == s@.len() - i);
                    if next < s.len() {
                        assert(s@.skip(i as int).skip(2) =~= s@.skip(i as int + 2));
                        assert(s@.skip(i as int)[1] == s@[i as int + 1]);
                    }
                }
                if crlf {
                    // Never saturates: next < s.len().
                    i = next.saturating_add(1);
                } else {
                    i = next;
                }
            } else {
                out.push(c);
                proof {
                    assert(out@ =~= before.push(c));
                }
                // Never saturates: i < s.len().
                i = i.saturating_add(1);
            }
        }
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    out
}

/// The index of the first code point of `s` that is not ASCII whitespace
/// (or `s.len()`): `trim_start(s)` is `s` from there.
pub fn skip_whitespace(s: &[u32]) -> (a: usize)
    ensures
        a <= s.len(),
        trim_start(s@) == s@.skip(a as int),
{
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            trim_start(s@) == trim_start(s@.skip(i as int)),
        decreases s.len() - i,
    {
        match s.get(i) {
            Some(c) => {
                let c = *c;
                proof {
                    assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                    assert(s@.skip(i as int)[0] == s@[i as int]);
                }
                if c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20 {
                    // Never saturates: i < s.len().
                    i = i.saturating_add(1);
                } else {
                    return i;
                }
            },
            None => {
                return i;
            },
        }
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    i
}

/// A copy of `s[a..b]`.
pub fn copy_range(s: &[u32], a: usize, b: usize) -> (r: Vec<u32>)
    requires
        a <= b <= s.len(),
    ensures
        r@ == s@.subrange(a as int, b as int),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = a;
    while i < b
        invariant
            a <= i <= b <= s.len(),
            out@ == s@.subrange(a as int, i as int),
        decreases b - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c);
        }
        proof {
            assert(s@.subrange(a as int, i as int + 1) =~= s@.subrange(a as int, i as int).push(s@[i as int]));
        }
        // Never saturates: i < b.
        i = i.saturating_add(1);
    }
    out
}

/// [`strip_whitespace`].
pub fn strip_whitespace_exec(s: &[u32]) -> (r: Vec<u32>)
    ensures
        strip_whitespace_ensures(s@, r@),
{
    let a = skip_whitespace(s);
    let mut b: usize = s.len();
    proof {
        assert(s@.skip(a as int) =~= s@.subrange(a as int, s.len() as int));
    }
    while b > a
        invariant
            a <= b <= s.len(),
            trim_start(s@) == s@.skip(a as int),
            trim_end(s@.skip(a as int)) == trim_end(s@.subrange(a as int, b as int)),
        decreases b - a,
    {
        let last = b - 1;
        match s.get(last) {
            Some(c) => {
                let c = *c;
                proof {
                    let t = s@.subrange(a as int, b as int);
                    assert(t[t.len() - 1] == s@[last as int]);
                    assert(t.drop_last() =~= s@.subrange(a as int, last as int));
                }
                if c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20 {
                    b = last;
                } else {
                    proof {
                        let t = s@.subrange(a as int, b as int);
                        assert(trim_end(t) == t);
                        assert(trim_start(s@) == s@.skip(a as int));
                        assert(strip_whitespace(s@) == trim_end(trim_start(s@)));
                        assert(strip_whitespace(s@) == t);
                    }
                    return copy_range(s, a, b);
                }
            },
            None => {
                return copy_range(s, a, b);
            },
        }
    }
    proof {
        let t = s@.subrange(a as int, b as int);
        assert(t =~= Seq::<u32>::empty());
    }
    copy_range(s, a, b)
}

/// [`wrap_from`] with `col` = 0, as the textarea wrapping transformation
/// breaks lines.
pub fn wrap_hard(s: &[u32], cols: usize) -> (r: Vec<u32>)
    ensures
        wrap_hard_ensures(s@, cols, r@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut col: usize = 0;
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            col <= i,
            out@ + wrap_from(s@.skip(i as int), cols as nat, col as nat) == wrap_from(s@, cols as nat, 0),
        decreases s.len() - i,
    {
        let ghost before = out@;
        if let Some(c) = s.get(i) {
            let c = *c;
            proof {
                assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                assert(s@.skip(i as int)[0] == s@[i as int]);
            }
            if c == 0x0A {
                out.push(c);
                col = 0;
                proof {
                    assert(out@ =~= before.push(c));
                }
            } else if col >= cols {
                out.push(0x0A);
                out.push(c);
                col = 1;
                proof {
                    assert(out@ =~= before.push(0x0A).push(c));
                    assert(seq![0x0Au32, c] =~= seq![0x0Au32].push(c));
                }
            } else {
                out.push(c);
                // Never saturates: col <= i < s.len().
                col = col.saturating_add(1);
                proof {
                    assert(out@ =~= before.push(c));
                }
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    out
}

/// Append [`decimal`]`(n)` to `out`.
pub fn decimal_into(n: u32, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + decimal(n as nat),
    decreases n,
{
    if n >= 10 {
        decimal_into(n / 10, out);
        // n % 10 < 10, so the sum is a digit.
        out.push(0x30u32.saturating_add(n % 10));
        proof {
            assert(decimal(n as nat) == decimal((n / 10) as nat) + seq![(0x30 + (n as nat) % 10) as u32]);
        }
    } else {
        out.push(0x30u32.saturating_add(n));
    }
}

/// [`decimal`].
pub fn decimal_exec(n: u32) -> (r: Vec<u32>)
    ensures
        decimal_ensures(n, r@),
{
    let mut out: Vec<u32> = Vec::new();
    decimal_into(n, &mut out);
    out
}

/// Position `j` of `s` holds an ASCII digit.
pub fn digit_at(s: &[u32], j: usize) -> (r: bool)
    ensures
        r == (j < s@.len() && 0x30 <= s@[j as int] <= 0x39),
{
    match s.get(j) {
        Some(c) => *c >= 0x30 && *c <= 0x39,
        None => false,
    }
}

/// The view of an optional slice.
pub open spec fn opt_slice_view(a: Option<&[u32]>) -> Option<Seq<u32>> {
    match a {
        Some(s) => Some(s@),
        None => None,
    }
}

/// [`digits_value`] never goes below its accumulator.
proof fn lemma_digits_value_ge(s: Seq<u32>, acc: nat)
    ensures
        digits_value(s, acc) >= acc,
    decreases s.len(),
{
    if s.len() > 0 && 0x30 <= s[0] <= 0x39 {
        lemma_digits_value_ge(s.drop_first(), acc * 10 + (s[0] - 0x30) as nat);
    }
}

/// [`character_width`]'s attribute reading: [`width_of`], cut off at
/// `usize::MAX`.
pub fn character_width(a: Option<&[u32]>) -> (r: usize)
    ensures
        character_width_ensures(opt_slice_view(a), r),
{
    let s = match a {
        None => {
            return 20;
        },
        Some(s) => s,
    };
    let start = skip_whitespace(s);
    let mut i = start;
    let mut negative = false;
    match s.get(i) {
        Some(c) => {
            if *c == 0x2D {
                negative = true;
                // Never saturates: i < s.len().
                i = i.saturating_add(1);
            } else if *c == 0x2B {
                i = i.saturating_add(1);
            }
        },
        None => {},
    }
    proof {
        let t = s@.skip(start as int);
        assert(trim_start(s@) == t);
        if start < s.len() {
            assert(t.len() > 0 && t[0] == s@[start as int]);
        }
        if i > start {
            assert(i == start + 1);
            assert(t.drop_first() =~= s@.skip(i as int));
        } else {
            assert(i == start);
            assert(!negative);
        }
        assert(parse_non_negative(s@) == parse_after_sign(s@.skip(i as int), negative));
    }
    // The first digit.
    let first_digit = match s.get(i) {
        Some(c) => *c >= 0x30 && *c <= 0x39,
        None => false,
    };
    if !first_digit {
        proof {
            let u = s@.skip(i as int);
            assert(!starts_with_digit(u));
            if i < s.len() {
                assert(u[0] == s@[i as int]);
            }
        }
        return 20;
    }
    let ghost u = s@.skip(i as int);
    let mut j = i;
    let mut acc: usize = 0;
    let mut big = false;
    let ghost mut acc_s: nat = 0;
    proof {
        assert(u =~= s@.skip(i as int));
    }
    while j < s.len() && !big && digit_at(s, j)
        invariant
            i <= j <= s.len(),
            u == s@.skip(i as int),
            big ==> acc_s > usize::MAX as nat,
            !big ==> acc as nat == acc_s,
            digits_value(u, 0) == digits_value(s@.skip(j as int), acc_s),
        decreases s.len() - j,
    {
        let c = match s.get(j) {
            Some(c) => *c,
            None => 0,
        };
        proof {
            assert(s@.skip(j as int)[0] == s@[j as int]);
            assert(s@.skip(j as int).drop_first() =~= s@.skip(j as int + 1));
        }
        let d = c.saturating_sub(0x30) as usize;
        proof {
            acc_s = acc_s * 10 + d as nat;
        }
        if acc > (usize::MAX - d) / 10 {
            big = true;
            proof {
                assert(acc as nat * 10 + d as nat > usize::MAX as nat) by (nonlinear_arith)
                    requires
                        acc > (usize::MAX - d) / 10,
                        d <= 9,
                ;
            }
        } else {
            proof {
                assert(acc as nat * 10 + d as nat <= usize::MAX as nat) by (nonlinear_arith)
                    requires
                        acc <= (usize::MAX - d) / 10,
                        d <= 9,
                ;
            }
            acc = acc * 10 + d;
        }
        // Never saturates: j < s.len().
        j = j.saturating_add(1);
    }
    proof {
        if j >= s.len() {
            assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
            assert(digits_value(s@.skip(j as int), acc_s) == acc_s);
        } else if !big {
            assert(s@.skip(j as int)[0] == s@[j as int]);
            assert(digits_value(s@.skip(j as int), acc_s) == acc_s);
        }
        if big {
            lemma_digits_value_ge(s@.skip(j as int), acc_s);
        }
        assert(starts_with_digit(u)) by {
            assert(u[0] == s@[i as int]);
        }
    }
    if big {
        // The value exceeds usize::MAX: never negative zero, so a "-" gives
        // an error, and otherwise the width is cut off.
        return if negative { 20 } else { usize::MAX };
    }
    // The value is acc, below usize::MAX.
    proof {
        assert(digits_value(u, 0) == acc as nat);
    }
    if negative && acc != 0 {
        return 20;
    }
    if acc > 0 { acc } else { 20 }
}

} // verus!
