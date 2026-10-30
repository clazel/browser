//! The executable encoding sniffing algorithm, proven to meet
//! [`super::contract`]. Each function mirrors one spec function in
//! [`super::spec`] and is proven equal to it, so the step comments live
//! there. Every loop is iterative (no recursion over the input).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_encoding::labels::spec::Encoding;

verus! {

/// The byte at `i`, or `None` past the end.
fn at(b: &[u8], i: usize) -> (r: Option<u8>)
    ensures
        match r {
            Some(c) => i < b@.len() && c == b@[i as int],
            None => i >= b@.len(),
        },
{
    Some(*b.get(i)?)
}

fn is_space_exec(c: u8) -> (r: bool)
    ensures
        r == is_space(c),
{
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

fn lower_exec(c: u8) -> (r: u8)
    ensures
        r == lower(c),
{
    if (0x41..=0x5A).contains(&c) {
        proof {
            assert(0x41 <= c <= 0x5A ==> c | 0x20 == c + 0x20) by (bit_vector);
        }
        c | 0x20
    } else {
        c
    }
}

/// Whether `a` and `b` are the same bytes.
fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
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

/// Whether `b` from `pos` starts with `pattern`.
fn starts_at_exec(b: &[u8], pos: usize, pattern: &[u8]) -> (r: bool)
    ensures
        r == starts_at(b@, pos as nat, pattern@),
{
    // Never saturates: the subtraction runs only when pattern.len() <= b.len().
    if pattern.len() > b.len() || pos > b.len().saturating_sub(pattern.len()) {
        return false;
    }
    let mut k: usize = 0;
    while k < pattern.len()
        invariant
            pos + pattern.len() <= b.len(),
            k <= pattern.len(),
            forall|t: int| 0 <= t < k ==> b@[pos + t] == pattern@[t],
        decreases pattern.len() - k,
    {
        // Neither saturates: pos + k < pos + pattern.len() <= b.len().
        if at(b, pos.saturating_add(k)) != at(pattern, k) {
            proof {
                assert(b@.subrange(pos as int, (pos + pattern.len()) as int)[k as int] != pattern@[k as int]);
            }
            return false;
        }
        k = k.saturating_add(1);
    }
    assert(b@.subrange(pos as int, (pos + pattern.len()) as int) =~= pattern@);
    true
}

fn starts_meta_exec(b: &[u8], pos: usize) -> (r: bool)
    ensures
        r == starts_meta(b@, pos as nat),
{
    // Never saturates: the subtraction runs only when pos <= b.len().
    if pos > b.len() || b.len().saturating_sub(pos) < 6 {
        return false;
    }
    // Never saturate: pos + 5 < b.len().
    let c0 = at(b, pos);
    let c1 = at(b, pos.saturating_add(1));
    let c2 = at(b, pos.saturating_add(2));
    let c3 = at(b, pos.saturating_add(3));
    let c4 = at(b, pos.saturating_add(4));
    let c5 = at(b, pos.saturating_add(5));
    match (c0, c1, c2, c3, c4, c5) {
        (Some(c0), Some(c1), Some(c2), Some(c3), Some(c4), Some(c5)) => c0 == 0x3C && (c1 == 0x4D || c1 == 0x6D)
            && (c2 == 0x45 || c2 == 0x65) && (c3 == 0x54 || c3 == 0x74) && (c4 == 0x41 || c4 == 0x61) && (
        is_space_exec(c5) || c5 == 0x2F),
        _ => false,
    }
}

fn is_letter_exec(c: u8) -> (r: bool)
    ensures
        r == is_letter(c),
{
    (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c)
}

fn starts_tag_exec(b: &[u8], pos: usize) -> (r: bool)
    ensures
        r == starts_tag(b@, pos as nat),
{
    if pos >= b.len() {
        return false;
    }
    let c1 = at(b, pos.saturating_add(1));
    let c2 = at(b, pos.saturating_add(2));
    let first = at(b, pos) == Some(0x3C);
    let one = match c1 {
        Some(c) => is_letter_exec(c),
        None => false,
    };
    let two = c1 == Some(0x2F) && match c2 {
        Some(c) => is_letter_exec(c),
        None => false,
    };
    first && (one || two)
}

fn find_comment_end_exec(b: &[u8], q: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => find_comment_end(b@, q as nat) == Some(p as nat) && q <= p < b.len(),
            None => find_comment_end(b@, q as nat) is None,
        },
{
    let mut p = q;
    while p < b.len()
        invariant
            q <= p,
            find_comment_end(b@, q as nat) == find_comment_end(b@, p as nat),
        decreases b.len() - p,
    {
        // Neither subtraction saturates: p >= 2.
        if p >= 2 && at(b, p) == Some(0x3E) && at(b, p.saturating_sub(1)) == Some(0x2D) && at(b, p.saturating_sub(2))
            == Some(0x2D) {
            return Some(p);
        }
        // Never saturates: p < b.len().
        p = p.saturating_add(1);
    }
    None
}

fn find_gt_exec(b: &[u8], q: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => find_gt(b@, q as nat) == Some(p as nat) && q <= p < b.len(),
            None => find_gt(b@, q as nat) is None,
        },
{
    let mut p = q;
    while p < b.len()
        invariant
            q <= p,
            find_gt(b@, q as nat) == find_gt(b@, p as nat),
        decreases b.len() - p,
    {
        if at(b, p) == Some(0x3E) {
            return Some(p);
        }
        // Never saturates: p < b.len().
        p = p.saturating_add(1);
    }
    None
}

fn find_tag_end_exec(b: &[u8], q: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => find_tag_end(b@, q as nat) == Some(p as nat) && q <= p < b.len(),
            None => find_tag_end(b@, q as nat) is None,
        },
{
    let mut p = q;
    while p < b.len()
        invariant
            q <= p,
            find_tag_end(b@, q as nat) == find_tag_end(b@, p as nat),
        ensures
            q <= p,
            find_tag_end(b@, q as nat) == find_tag_end(b@, p as nat),
            p >= b.len(),
        decreases b.len() - p,
    {
        let c = match at(b, p) {
            Some(c) => c,
            None => break,
        };
        if is_space_exec(c) || c == 0x3E {
            return Some(p);
        }
        // Never saturates: p < b.len().
        p = p.saturating_add(1);
    }
    None
}

fn find_byte_exec(s: &[u8], k: usize, c: u8) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => find_byte(s@, k as nat, c) == Some(p as nat) && k <= p < s.len(),
            None => find_byte(s@, k as nat, c) is None,
        },
{
    let mut p = k;
    while p < s.len()
        invariant
            k <= p,
            find_byte(s@, k as nat, c) == find_byte(s@, p as nat, c),
        decreases s.len() - p,
    {
        if at(s, p) == Some(c) {
            return Some(p);
        }
        // Never saturates: p < s.len().
        p = p.saturating_add(1);
    }
    None
}

fn skip_spaces_exec(s: &[u8], k: usize) -> (r: usize)
    ensures
        r == skip_spaces(s@, k as nat),
        k <= r,
        k <= s.len() ==> r <= s.len(),
{
    let mut p = k;
    while p < s.len()
        invariant
            k <= p,
            skip_spaces(s@, k as nat) == skip_spaces(s@, p as nat),
            k <= s.len() ==> p <= s.len(),
        ensures
            k <= p,
            skip_spaces(s@, k as nat) == skip_spaces(s@, p as nat),
            k <= s.len() ==> p <= s.len(),
            p >= s.len(),
        decreases s.len() - p,
    {
        let c = match at(s, p) {
            Some(c) => c,
            None => break,
        };
        if !is_space_exec(c) {
            return p;
        }
        // Never saturates: p < s.len().
        p = p.saturating_add(1);
    }
    p
}

fn skip_controls_exec(b: &[u8], k: usize) -> (r: usize)
    ensures
        r == skip_controls(b@, k as nat),
        k <= r,
{
    let mut p = k;
    while p < b.len()
        invariant
            k <= p,
            skip_controls(b@, k as nat) == skip_controls(b@, p as nat),
        ensures
            k <= p,
            skip_controls(b@, k as nat) == skip_controls(b@, p as nat),
            p >= b.len(),
        decreases b.len() - p,
    {
        let c = match at(b, p) {
            Some(c) => c,
            None => break,
        };
        if c > 0x20 {
            return p;
        }
        // Never saturates: p < b.len().
        p = p.saturating_add(1);
    }
    p
}

fn find_value_end_exec(s: &[u8], k: usize) -> (r: usize)
    requires
        k <= s.len(),
    ensures
        r == find_value_end(s@, k as nat),
        k <= r <= s.len(),
{
    let mut p = k;
    while p < s.len()
        invariant
            k <= p <= s.len(),
            find_value_end(s@, k as nat) == find_value_end(s@, p as nat),
        ensures
            k <= p <= s.len(),
            find_value_end(s@, k as nat) == find_value_end(s@, p as nat),
            p >= s.len(),
        decreases s.len() - p,
    {
        let c = match at(s, p) {
            Some(c) => c,
            None => break,
        };
        if is_space_exec(c) || c == 0x3B {
            return p;
        }
        // Never saturates: p < s.len().
        p = p.saturating_add(1);
    }
    p
}

/// Whether "charset" starts at `k` (ASCII case-insensitively).
fn charset_at_exec(s: &[u8], k: usize) -> (r: bool)
    ensures
        r == charset_at(s@, k as nat),
{
    // Never saturates: the subtraction runs only when k <= s.len().
    if k > s.len() || s.len().saturating_sub(k) < 7 {
        return false;
    }
    let word: [u8; 7] = [0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74];
    assert(word@ =~= charset_word());
    let mut t: usize = 0;
    while t < 7
        invariant
            k + 7 <= s.len(),
            t <= 7,
            word@ == charset_word(),
            charset_from(s@, k as nat, 0) == charset_from(s@, k as nat, t as nat),
        decreases 7 - t,
    {
        // Never saturates: k + t < k + 7 <= s.len().
        let c = match at(s, k.saturating_add(t)) {
            Some(c) => lower_exec(c),
            None => 0,
        };
        if Some(c) != at(&word, t) {
            return false;
        }
        t = t.saturating_add(1);
    }
    true
}

fn find_charset_exec(s: &[u8], k: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => find_charset(s@, k as nat) == Some(p as nat) && k <= p && p + 7 <= s.len(),
            None => find_charset(s@, k as nat) is None,
        },
{
    let mut p = k;
    // Never saturates: the subtraction runs only when p <= s.len().
    while p <= s.len() && s.len().saturating_sub(p) >= 7
        invariant
            k <= p,
            find_charset(s@, k as nat) == find_charset(s@, p as nat),
        decreases s.len() - p,
    {
        if charset_at_exec(s, p) {
            return Some(p);
        }
        // Never saturates: p + 7 <= s.len().
        p = p.saturating_add(1);
    }
    None
}

/// "Extracting a character encoding from a meta element": the substring
/// "get an encoding" is applied to, or `None` for "nothing".
pub fn extract_label_exec(s: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        match r {
            Some(v) => extract_label(s@) == Some(v@),
            None => extract_label(s@) is None,
        },
{
    let mut position: usize = 0;
    loop
        invariant
            position <= s.len(),
            extract_label(s@) == extract_label_from(s@, position as nat),
        decreases s.len() - position,
    {
        let k = find_charset_exec(s, position)?;
        // Never saturates: k + 7 <= s.len().
        let j = skip_spaces_exec(s, k.saturating_add(7));
        if j >= s.len() || at(s, j) != Some(0x3D) {
            position = j;
            continue;
        }
        // Never saturates: j < s.len().
        let v = skip_spaces_exec(s, j.saturating_add(1));
        let c = at(s, v)?;
        if c == 0x22 || c == 0x27 {
            return match find_byte_exec(s, v.saturating_add(1), c) {
                Some(e) => {
                    let out = slice_to_vec(s, v.saturating_add(1), e);
                    Some(out)
                },
                None => None,
            };
        } else {
            let e = find_value_end_exec(s, v);
            return Some(slice_to_vec(s, v, e));
        }
    }
}

/// `s[from .. to]`, copied.
fn slice_to_vec(s: &[u8], from: usize, to: usize) -> (r: Vec<u8>)
    requires
        from <= to <= s.len(),
    ensures
        r@ == s@.subrange(from as int, to as int),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i = from;
    while i < to
        invariant
            from <= i <= to <= s.len(),
            out@ == s@.subrange(from as int, i as int),
        decreases to - i,
    {
        if let Some(c) = at(s, i) {
            out.push(c);
        }
        // Never saturates: i < to.
        i = i.saturating_add(1);
        assert(out@ =~= s@.subrange(from as int, i as int));
    }
    out
}

/// The bytes as code points ("isomorphic decode").
fn to_string(v: &[u8]) -> (r: Vec<u32>)
    ensures
        r@ == as_string(v@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            out@ == as_string(v@.subrange(0, i as int)),
        decreases v.len() - i,
    {
        if let Some(c) = at(v, i) {
            out.push(c as u32);
        }
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
        assert(out@ =~= as_string(v@.subrange(0, i as int)));
    }
    assert(v@.subrange(0, i as int) =~= v@);
    out
}

/// "Get an encoding" of a byte string.
fn get_an_encoding_bytes(v: &[u8]) -> (r: Option<Encoding>)
    ensures
        r == clazel_encoding::labels::spec::get_an_encoding(as_string(v@)),
{
    let s = to_string(v);
    clazel_encoding::labels::exec::get_an_encoding(&s)
}

/// The algorithm for extracting a character encoding from a meta element.
fn extract_exec(s: &[u8]) -> (r: Option<Encoding>)
    ensures
        r == extract(s@),
{
    match extract_label_exec(s) {
        Some(label) => get_an_encoding_bytes(&label),
        None => None,
    }
}

/// What "get an attribute" gives, with vectors for strings.
enum AttrExec {
    Abort,
    NoAttr(usize),
    Some(Vec<u8>, Vec<u8>, usize),
}

/// The spec's view of an [`AttrExec`].
spec fn attr_view(a: AttrExec) -> Attr {
    match a {
        AttrExec::Abort => Attr::Abort,
        AttrExec::NoAttr(p) => Attr::None(p as nat),
        AttrExec::Some(n, v, p) => Attr::Some(n@, v@, p as nat),
    }
}

/// "Get an attribute" at `pos`, all of its steps.
fn get_attribute_exec(b: &[u8], pos: usize) -> (r: AttrExec)
    ensures
        attr_view(r) == get_attribute(b@, pos as nat),
        match r {
            AttrExec::Some(_, _, p) => pos < p <= b.len(),
            AttrExec::NoAttr(p) => pos <= p < b.len(),
            AttrExec::Abort => true,
        },
{
    // Steps 1 and 2.
    let mut p = pos;
    loop
        invariant
            pos <= p,
            get_attribute(b@, pos as nat) == get_attribute(b@, p as nat),
        ensures
            pos <= p < b.len(),
            !is_space(b@[p as int]) && b@[p as int] != 0x2F && b@[p as int] != 0x3E,
            get_attribute(b@, pos as nat) == get_attribute(b@, p as nat),
        decreases b.len() - p,
    {
        match at(b, p) {
            None => return AttrExec::Abort,
            Some(c) => {
                if is_space_exec(c) || c == 0x2F {
                    // Never saturates: p < b.len().
                    p = p.saturating_add(1);
                } else if c == 0x3E {
                    return AttrExec::NoAttr(p);
                } else {
                    break;
                }
            },
        }
    }
    // Steps 3 to 5: the name.
    let ghost start = p;
    let mut name: Vec<u8> = Vec::new();
    assert(name@ =~= Seq::<u8>::empty());
    loop
        invariant
            pos <= start <= p,
            start < b.len(),
            !is_space(b@[start as int]) && b@[start as int] != 0x2F && b@[start as int] != 0x3E,
            p > start ==> name@.len() > 0,
            get_attribute(b@, pos as nat) == attr_name(b@, p as nat, name@),
        decreases b.len() - p,
    {
        let c = match at(b, p) {
            None => return AttrExec::Abort,
            Some(c) => c,
        };
        if c == 0x3D && !name.is_empty() {
            // Never saturates: p < b.len().
            return attr_value_exec(b, p.saturating_add(1), name, Ghost(pos));
        } else if is_space_exec(c) {
            return attr_spaces_exec(b, p, name, Ghost(pos));
        } else if c == 0x2F || c == 0x3E {
            // p > pos: the first byte of a name is none of these (step 1, 2).
            return AttrExec::Some(name, Vec::new(), p);
        } else {
            name.push(lower_exec(c));
            // Never saturates: p < b.len().
            p = p.saturating_add(1);
        }
    }
}

/// "Get an attribute", steps 6 to 8.
fn attr_spaces_exec(b: &[u8], pos: usize, name: Vec<u8>, Ghost(start): Ghost<usize>) -> (r: AttrExec)
    requires
        start < pos,
    ensures
        attr_view(r) == attr_spaces(b@, pos as nat, name@),
        match r {
            AttrExec::Some(_, _, p) => start < p <= b.len(),
            AttrExec::NoAttr(_) => false,
            AttrExec::Abort => true,
        },
{
    let mut p = pos;
    loop
        invariant
            start < pos <= p,
            attr_spaces(b@, pos as nat, name@) == attr_spaces(b@, p as nat, name@),
        decreases b.len() - p,
    {
        let c = match at(b, p) {
            None => return AttrExec::Abort,
            Some(c) => c,
        };
        if is_space_exec(c) {
            // Never saturates: p < b.len().
            p = p.saturating_add(1);
        } else if c != 0x3D {
            return AttrExec::Some(name, Vec::new(), p);
        } else {
            return attr_value_exec(b, p.saturating_add(1), name, Ghost(start));
        }
    }
}

/// "Get an attribute", steps 9 to 12.
fn attr_value_exec(b: &[u8], pos: usize, name: Vec<u8>, Ghost(start): Ghost<usize>) -> (r: AttrExec)
    requires
        start < pos,
    ensures
        attr_view(r) == attr_value(b@, pos as nat, name@),
        match r {
            AttrExec::Some(_, _, p) => start < p <= b.len(),
            AttrExec::NoAttr(_) => false,
            AttrExec::Abort => true,
        },
{
    // Step 9.
    let mut p = skip_spaces_exec(b, pos);
    proof {
        lemma_attr_value_spaces(b@, pos as nat, name@);
        lemma_skip_spaces_stops(b@, pos as nat);
    }
    let c = match at(b, p) {
        None => return AttrExec::Abort,
        Some(c) => c,
    };
    // Step 10.
    let mut value: Vec<u8> = Vec::new();
    assert(value@ =~= Seq::<u8>::empty());
    if c == 0x22 || c == 0x27 {
        // Never saturates: p < b.len().
        p = p.saturating_add(1);
        loop
            invariant
                start < p,
                attr_value(b@, pos as nat, name@) == attr_quoted(b@, p as nat, name@, value@, c),
            decreases b.len() - p,
        {
            let d = match at(b, p) {
                None => return AttrExec::Abort,
                Some(d) => d,
            };
            // Never saturates: p < b.len().
            p = p.saturating_add(1);
            if d == c {
                return AttrExec::Some(name, value, p);
            }
            value.push(lower_exec(d));
        }
    } else if c == 0x3E {
        AttrExec::Some(name, value, p)
    } else {
        value.push(lower_exec(c));
        assert(value@ =~= seq![lower(c)]);
        // Never saturates: p < b.len().
        p = p.saturating_add(1);
        // Steps 11 and 12.
        loop
            invariant
                start < p,
                attr_value(b@, pos as nat, name@) == attr_unquoted(b@, p as nat, name@, value@),
            decreases b.len() - p,
        {
            let d = match at(b, p) {
                None => return AttrExec::Abort,
                Some(d) => d,
            };
            if is_space_exec(d) || d == 0x3E {
                return AttrExec::Some(name, value, p);
            }
            value.push(lower_exec(d));
            // Never saturates: p < b.len().
            p = p.saturating_add(1);
        }
    }
}

/// `skip_spaces` stops at the end or at a byte that is not a space.
proof fn lemma_skip_spaces_stops(s: Seq<u8>, k: nat)
    ensures
        skip_spaces(s, k) >= s.len() || !is_space(s[skip_spaces(s, k) as int]),
    decreases s.len() - k,
{
    if k < s.len() && is_space(s[k as int]) {
        lemma_skip_spaces_stops(s, k + 1);
    }
}

/// Step 9 skips what `skip_spaces` skips.
proof fn lemma_attr_value_spaces(b: Seq<u8>, pos: nat, name: Seq<u8>)
    ensures
        attr_value(b, pos, name) == attr_value(b, skip_spaces(b, pos), name),
    decreases b.len() - pos,
{
    if pos < b.len() && is_space(b[pos as int]) {
        lemma_attr_value_spaces(b, pos + 1, name);
    }
}

/// The `<meta>` steps' state, with vectors.
struct MetaExec {
    attribute_list: Vec<Vec<u8>>,
    got_pragma: bool,
    need_pragma: Option<bool>,
    charset: Charset,
}

/// The spec's view of a [`MetaExec`].
spec fn meta_view(m: MetaExec) -> Meta {
    Meta {
        attribute_list: m.attribute_list@.map_values(|v: Vec<u8>| v@),
        got_pragma: m.got_pragma,
        need_pragma: m.need_pragma,
        charset: m.charset,
    }
}

/// Whether `name` is in `list`.
fn in_list_exec(list: &[Vec<u8>], name: &[u8]) -> (r: bool)
    ensures
        r == in_list(list@.map_values(|v: Vec<u8>| v@), name@, 0),
{
    let ghost l = list@.map_values(|v: Vec<u8>| v@);
    let mut i: usize = 0;
    while i < list.len()
        invariant
            i <= list.len(),
            l == list@.map_values(|v: Vec<u8>| v@),
            in_list(l, name@, 0) == in_list(l, name@, i as nat),
        decreases list.len() - i,
    {
        let item = match list.get(i) {
            Some(item) => item,
            None => return false,
        };
        if bytes_eq(item.as_slice(), name) {
            return true;
        }
        // Never saturates: i < list.len().
        i = i.saturating_add(1);
    }
    false
}

/// The `<meta>` steps' step 9 for one attribute.
fn meta_attribute_exec(m: &mut MetaExec, name: &[u8], value: &[u8])
    ensures
        meta_view(*final(m)) == meta_attribute(meta_view(*old(m)), name@, value@),
{
    let http: [u8; 10] = [0x68, 0x74, 0x74, 0x70, 0x2D, 0x65, 0x71, 0x75, 0x69, 0x76];
    let content_word: [u8; 7] = [0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74];
    let content_type_word: [u8; 12] = [0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65];
    let charset_w: [u8; 7] = [0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74];
    assert(http@ =~= http_equiv());
    assert(content_word@ =~= content());
    assert(content_type_word@ =~= content_type());
    assert(charset_w@ =~= charset_name());
    if bytes_eq(name, &http) {
        if bytes_eq(value, &content_type_word) {
            m.got_pragma = true;
        }
    } else if bytes_eq(name, &content_word) {
        let found = extract_exec(value);
        if let (Some(e), Charset::Null) = (found, &m.charset) {
            m.charset = Charset::Encoding(e);
            m.need_pragma = Some(true);
        }
    } else if bytes_eq(name, &charset_w) {
        m.charset = match get_an_encoding_bytes(value) {
            Some(e) => Charset::Encoding(e),
            None => Charset::Failure,
        };
        m.need_pragma = Some(false);
    }
}

/// The spec's [`MetaResult`] with a machine position.
enum MetaResultExec {
    Return(Encoding),
    NextByte(usize),
    Abort,
}

spec fn meta_result_view(r: MetaResultExec) -> MetaResult {
    match r {
        MetaResultExec::Return(e) => MetaResult::Return(e),
        MetaResultExec::NextByte(p) => MetaResult::NextByte(p as nat),
        MetaResultExec::Abort => MetaResult::Abort,
    }
}

fn meta_processing_exec(m: &MetaExec, pos: usize) -> (r: MetaResultExec)
    ensures
        meta_result_view(r) == meta_processing(meta_view(*m), pos as nat),
        match r {
            MetaResultExec::NextByte(p) => p == pos,
            _ => true,
        },
{
    match m.need_pragma {
        None => MetaResultExec::NextByte(pos),
        Some(need) => {
            if need && !m.got_pragma {
                return MetaResultExec::NextByte(pos);
            }
            match m.charset {
                Charset::Encoding(e) => {
                    let e = match e {
                        Encoding::Utf16Be | Encoding::Utf16Le => Encoding::Utf8,
                        _ => e,
                    };
                    let e = match e {
                        Encoding::XUserDefined => Encoding::Windows1252,
                        _ => e,
                    };
                    MetaResultExec::Return(e)
                },
                _ => MetaResultExec::NextByte(pos),
            }
        },
    }
}

/// The `<meta>` steps from "Attributes" at `pos`.
fn meta_attributes_exec(b: &[u8], pos: usize) -> (r: MetaResultExec)
    ensures
        meta_result_view(r) == meta_attributes(
            b@,
            pos as nat,
            Meta { attribute_list: seq![], got_pragma: false, need_pragma: None, charset: Charset::Null },
        ),
        match r {
            MetaResultExec::NextByte(p) => pos <= p < b.len(),
            _ => true,
        },
{
    let mut m = MetaExec { attribute_list: Vec::new(), got_pragma: false, need_pragma: None, charset: Charset::Null };
    assert(meta_view(m) == Meta {
        attribute_list: seq![],
        got_pragma: false,
        need_pragma: None,
        charset: Charset::Null,
    }) by {
        assert(m.attribute_list@.map_values(|v: Vec<u8>| v@) =~= Seq::<Seq<u8>>::empty());
    }
    let mut p = pos;
    loop
        invariant
            pos <= p,
            meta_attributes(
                b@,
                pos as nat,
                Meta { attribute_list: seq![], got_pragma: false, need_pragma: None, charset: Charset::Null },
            ) == meta_attributes(b@, p as nat, meta_view(m)),
        decreases b.len() - p,
    {
        match get_attribute_exec(b, p) {
            AttrExec::Abort => return MetaResultExec::Abort,
            AttrExec::NoAttr(q) => return meta_processing_exec(&m, q),
            AttrExec::Some(name, value, q) => {
                if !in_list_exec(&m.attribute_list, &name) {
                    let ghost before = meta_view(m);
                    let ghost n = name@;
                    meta_attribute_exec(&mut m, &name, &value);
                    let ghost mid = m.attribute_list@;
                    m.attribute_list.push(name);
                    proof {
                        assert(m.attribute_list@.map_values(|v: Vec<u8>| v@) =~= mid.map_values(|v: Vec<u8>| v@).push(
                            n,
                        ));
                    }
                }
                p = q;
            },
        }
    }
}

/// "Repeatedly get an attribute until no further attributes can be found."
fn skip_attributes_exec(b: &[u8], pos: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => skip_attributes(b@, pos as nat) == Some(p as nat) && pos <= p < b.len(),
            None => skip_attributes(b@, pos as nat) is None,
        },
{
    let mut p = pos;
    loop
        invariant
            pos <= p,
            skip_attributes(b@, pos as nat) == skip_attributes(b@, p as nat),
        decreases b.len() - p,
    {
        match get_attribute_exec(b, p) {
            AttrExec::Abort => return None,
            AttrExec::NoAttr(q) => return Some(q),
            AttrExec::Some(_, _, q) => {
                p = q;
            },
        }
    }
}

/// The prescan's loop from position 0: `None` when it aborts.
fn prescan_loop_exec(b: &[u8]) -> (r: Option<Encoding>)
    ensures
        r == prescan_loop(b@, 0),
{
    let comment: [u8; 4] = [0x3C, 0x21, 0x2D, 0x2D];
    let bang: [u8; 2] = [0x3C, 0x21];
    let slash: [u8; 2] = [0x3C, 0x2F];
    let question: [u8; 2] = [0x3C, 0x3F];
    assert(comment@ =~= seq![0x3Cu8, 0x21u8, 0x2Du8, 0x2Du8]);
    assert(bang@ =~= seq![0x3Cu8, 0x21u8]);
    assert(slash@ =~= seq![0x3Cu8, 0x2Fu8]);
    assert(question@ =~= seq![0x3Cu8, 0x3Fu8]);
    let mut position: usize = 0;
    while position < b.len()
        invariant
            prescan_loop(b@, 0) == prescan_loop(b@, position as nat),
            comment@ == seq![0x3Cu8, 0x21u8, 0x2Du8, 0x2Du8],
            bang@ == seq![0x3Cu8, 0x21u8],
            slash@ == seq![0x3Cu8, 0x2Fu8],
            question@ == seq![0x3Cu8, 0x3Fu8],
        decreases b.len() - position,
    {
        let next = if starts_at_exec(b, position, &comment) {
            // Never saturates: position + 4 <= b.len().
            find_comment_end_exec(b, position.saturating_add(4))?
        } else if starts_meta_exec(b, position) {
            // Never saturates: position + 6 <= b.len().
            match meta_attributes_exec(b, position.saturating_add(5)) {
                MetaResultExec::Abort => return None,
                MetaResultExec::Return(e) => return Some(e),
                MetaResultExec::NextByte(p) => p,
            }
        } else if starts_tag_exec(b, position) {
            let q = find_tag_end_exec(b, position)?;
            skip_attributes_exec(b, q)?
        } else if starts_at_exec(b, position, &bang) || starts_at_exec(b, position, &slash) || starts_at_exec(
            b,
            position,
            &question,
        ) {
            // Never saturates: position < b.len().
            find_gt_exec(b, position.saturating_add(1))?
        } else {
            position
        };
        // Never saturates: next < b.len().
        position = next.saturating_add(1);
    }
    None
}

fn find_encoding_word_exec(b: &[u8], end: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(p) => find_encoding_word(b@, 0, end as nat) == Some(p as nat),
            None => find_encoding_word(b@, 0, end as nat) is None,
        },
{
    let word: [u8; 8] = [0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67];
    assert(word@ =~= seq![0x65u8, 0x6Eu8, 0x63u8, 0x6Fu8, 0x64u8, 0x69u8, 0x6Eu8, 0x67u8]);
    let mut k: usize = 0;
    while k < end
        invariant
            k <= end,
            word@ == seq![0x65u8, 0x6Eu8, 0x63u8, 0x6Fu8, 0x64u8, 0x69u8, 0x6Eu8, 0x67u8],
            find_encoding_word(b@, 0, end as nat) == find_encoding_word(b@, k as nat, end as nat),
        decreases end - k,
    {
        if starts_at_exec(b, k, &word) {
            return Some(k);
        }
        // Never saturates: k < end.
        k = k.saturating_add(1);
    }
    None
}

fn has_control_exec(s: &[u8]) -> (r: bool)
    ensures
        r == has_control(s@, 0),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            has_control(s@, 0) == has_control(s@, i as nat),
        ensures
            i <= s.len(),
            has_control(s@, 0) == has_control(s@, i as nat),
            i >= s.len(),
        decreases s.len() - i,
    {
        let c = match at(s, i) {
            Some(c) => c,
            None => break,
        };
        if c <= 0x20 {
            return true;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    false
}

/// "Get an XML encoding" of `b`.
fn get_xml_encoding_exec(b: &[u8]) -> (r: Option<Encoding>)
    ensures
        r == get_xml_encoding(b@),
{
    let xml: [u8; 5] = [0x3C, 0x3F, 0x78, 0x6D, 0x6C];
    assert(xml@ =~= seq![0x3Cu8, 0x3Fu8, 0x78u8, 0x6Du8, 0x6Cu8]);
    if !starts_at_exec(b, 0, &xml) {
        return None;
    }
    let end = find_gt_exec(b, 0)?;
    let k = find_encoding_word_exec(b, end)?;
    proof {
        lemma_find_encoding_word_bound(b@, 0, end as nat);
    }
    // Never saturates: k + 8 <= b.len().
    let p = skip_controls_exec(b, k.saturating_add(8));
    if at(b, p) != Some(0x3D) {
        return None;
    }
    // Never saturates: p < b.len().
    let q = skip_controls_exec(b, p.saturating_add(1));
    let quote = at(b, q)?;
    if !(quote == 0x22 || quote == 0x27) {
        return None;
    }
    let e = find_byte_exec(b, q.saturating_add(1), quote)?;
    let potential = slice_to_vec(b, q.saturating_add(1), e);
    if has_control_exec(&potential) {
        return None;
    }
    match get_an_encoding_bytes(&potential) {
        None => None,
        Some(Encoding::Utf16Be) | Some(Encoding::Utf16Le) => Some(Encoding::Utf8),
        Some(enc) => Some(enc),
    }
}

/// A found `encoding` lies within `b`.
proof fn lemma_find_encoding_word_bound(b: Seq<u8>, k: nat, end: nat)
    ensures
        match find_encoding_word(b, k, end) {
            Some(p) => p + 8 <= b.len(),
            None => true,
        },
    decreases end - k,
{
    if k < end && !starts_at(b, k, seq![0x65u8, 0x6Eu8, 0x63u8, 0x6Fu8, 0x64u8, 0x69u8, 0x6Eu8, 0x67u8]) {
        lemma_find_encoding_word_bound(b, k + 1, end);
    }
}

/// "Prescan a byte stream to determine its encoding" of `b` (the bytes up
/// to the end condition).
pub fn prescan(b: &[u8]) -> (r: Option<Encoding>)
    ensures
        super::contract::prescan_ensures(b@, r),
{
    let le: [u8; 6] = [0x3C, 0x00, 0x3F, 0x00, 0x78, 0x00];
    let be: [u8; 6] = [0x00, 0x3C, 0x00, 0x3F, 0x00, 0x78];
    assert(le@ =~= seq![0x3Cu8, 0x00u8, 0x3Fu8, 0x00u8, 0x78u8, 0x00u8]);
    assert(be@ =~= seq![0x00u8, 0x3Cu8, 0x00u8, 0x3Fu8, 0x00u8, 0x78u8]);
    if starts_at_exec(b, 0, &le) {
        Some(Encoding::Utf16Le)
    } else if starts_at_exec(b, 0, &be) {
        Some(Encoding::Utf16Be)
    } else {
        match prescan_loop_exec(b) {
            Some(e) => Some(e),
            None => get_xml_encoding_exec(b),
        }
    }
}

/// The encoding sniffing algorithm (HTML §13.2.3.2) for the whole body
/// `bytes`, given the transport layer's encoding: the encoding and the
/// confidence.
pub fn sniff(bytes: &[u8], transport: Option<Encoding>) -> (r: (Encoding, Confidence))
    ensures
        super::contract::sniff_ensures(bytes@, transport, r),
{
    if let Some(e) = clazel_encoding::hooks::decode::bom_sniff(bytes) {
        return (e, Confidence::Certain);
    }
    if let Some(e) = transport {
        return (e, Confidence::Certain);
    }
    let input = match bytes.split_at_checked(1024) {
        Some((head, _)) => head,
        None => bytes,
    };
    assert(input@ == prescan_input(bytes@));
    match prescan(input) {
        Some(e) => (e, Confidence::Tentative),
        None => (Encoding::Windows1252, Confidence::Tentative),
    }
}

/// The transport layer's encoding: "get an encoding" of the `charset`
/// parameter of the response's MIME type, if it has one.
pub fn transport_encoding(mime_type: &clazel_mime::mime_type::record::MimeType) -> (r: Option<Encoding>)
    ensures
        super::contract::transport_encoding_ensures(mime_type@, r),
{
    let ghost params = mime_type@.parameters;
    let word: [u32; 7] = [0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74];
    assert(word@ =~= seq![0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32]);
    let mut i: usize = 0;
    while i < mime_type.parameters.len()
        invariant
            i <= mime_type.parameters.len(),
            params == mime_type@.parameters,
            params.len() == mime_type.parameters.len(),
            word@ == seq![0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32],
            transport_from(params, 0) == transport_from(params, i as nat),
        decreases mime_type.parameters.len() - i,
    {
        let entry = mime_type.parameters.get(i)?;
        let (name, value) = (&entry.0, &entry.1);
        assert(params[i as int] == (name@, value@));
        if code_points_eq(name.as_slice(), &word) {
            return clazel_encoding::labels::exec::get_an_encoding(value.as_slice());
        }
        // Never saturates: i < the number of parameters.
        i = i.saturating_add(1);
    }
    None
}

/// Whether `a` and `b` are the same code points.
fn code_points_eq(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if a.get(i) != b.get(i) {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// §13.2.3.4 "change the encoding": `None` when only the confidence
/// becomes certain, or the encoding to parse again with, from the start,
/// confidence certain.
pub fn change_the_encoding(current: Encoding, new: Encoding) -> (r: Option<Encoding>)
    ensures
        super::contract::change_the_encoding_ensures(current, new, r),
{
    if matches!(current, Encoding::Utf16Be | Encoding::Utf16Le) {
        return None;
    }
    let new = match new {
        Encoding::Utf16Be | Encoding::Utf16Le => Encoding::Utf8,
        Encoding::XUserDefined => Encoding::Windows1252,
        e => e,
    };
    let same = clazel_encoding::labels::exec::number(new) == clazel_encoding::labels::exec::number(current);
    proof {
        clazel_encoding::labels::lemmas::lemma_number(new);
        clazel_encoding::labels::lemmas::lemma_number(current);
    }
    if same {
        None
    } else {
        Some(new)
    }
}

} // verus!
