//! The executable string functions of the encodings: scalar conversion,
//! newline replacement, splitting on ASCII whitespace, name escaping. Each
//! is proven equal to the spec function it names (see
//! [`crate::submit::contract`]).

use crate::exec::entry::ExecEntry;
#[cfg(verus_only)]
use crate::exec::entry::{entries_view, lemma_entries_push};
use crate::exec::strings::ci_eq_exec;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::submit::contract::*;
#[cfg(verus_only)]
use crate::submit::lemmas::lemma_split_step;
#[cfg(verus_only)]
use crate::submit::spec::*;
#[cfg(verus_only)]
use clazel_encoding::utf8::spec::is_scalar_value;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`to_scalar`] of one code point.
pub fn scalar_cp(c: u32) -> (r: u32)
    ensures
        r == (if is_scalar_value(c) {
            c
        } else {
            0xFFFDu32
        }),
{
    if c <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&c) {
        c
    } else {
        0xFFFD
    }
}

/// [`to_scalar`]: "convert to a scalar value string".
pub fn to_scalar_exec(s: &[u32]) -> (r: Vec<u32>)
    ensures
        to_scalar_ensures(s@, r@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> (#[trigger] out@[k]) == (if is_scalar_value(s@[k]) {
                s@[k]
            } else {
                0xFFFDu32
            }),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(scalar_cp(*c));
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= to_scalar(s@));
    }
    out
}

/// [`scalar_entries`].
pub fn scalar_entries_exec(es: &[ExecEntry]) -> (r: Vec<ExecEntry>)
    ensures
        scalar_entries_ensures(entries_view(es@), entries_view(r@)),
{
    let mut out: Vec<ExecEntry> = Vec::new();
    let mut i: usize = 0;
    let ghost all = entries_view(es@);
    proof {
        assert(all.skip(0) =~= all);
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
    }
    while i < es.len()
        invariant
            i <= es.len(),
            all == entries_view(es@),
            entries_view(out@) + scalar_entries(all.skip(i as int)) == scalar_entries(all),
        decreases es.len() - i,
    {
        if let Some(e) = es.get(i) {
            let ghost before = out@;
            let name = to_scalar_exec(e.name.as_slice());
            let value = to_scalar_exec(e.value.as_slice());
            proof {
                assert(all.skip(i as int).drop_first() =~= all.skip(i as int + 1));
                assert(all.skip(i as int)[0] == all[i as int]);
                assert(all[i as int] == es@[i as int]@);
            }
            out.push(ExecEntry { name, value });
            proof {
                lemma_entries_push(before, out@[before.len() as int]);
                assert(out@ =~= before.push(out@[before.len() as int]));
                assert(entries_view(out@) =~= entries_view(before).push(Entry {
                    name: to_scalar(es@[i as int].name@),
                    value: to_scalar(es@[i as int].value@),
                }));
                assert(entries_view(before).push(Entry {
                    name: to_scalar(es@[i as int].name@),
                    value: to_scalar(es@[i as int].value@),
                }) + scalar_entries(all.skip(i as int + 1)) =~= entries_view(before) + scalar_entries(
                    all.skip(i as int),
                ));
            }
        }
        // Never saturates: i < es.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(all.skip(es.len() as int) =~= Seq::<Entry>::empty());
    }
    out
}

/// [`crlf_newlines`]: "replace every occurrence of U+000D (CR) not
/// followed by U+000A (LF), and every occurrence of U+000A (LF) not
/// preceded by U+000D (CR), by a string consisting of U+000D (CR) and
/// U+000A (LF)".
pub fn crlf_newlines_exec(s: &[u32]) -> (r: Vec<u32>)
    ensures
        crlf_newlines_ensures(s@, r@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            out@ + crlf_newlines(s@.skip(i as int)) == crlf_newlines(s@),
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
                out.push(0x0D);
                out.push(0x0A);
                // Never saturates: i < s.len().
                let next = i.saturating_add(1);
                let lf = match s.get(next) {
                    Some(d) => *d == 0x0A,
                    None => false,
                };
                proof {
                    assert(out@ =~= before.push(0x0D).push(0x0A));
                    assert(s@.skip(i as int).len() == s@.len() - i);
                    if next < s.len() {
                        assert(s@.skip(i as int).skip(2) =~= s@.skip(i as int + 2));
                        assert(s@.skip(i as int)[1] == s@[i as int + 1]);
                    }
                    assert(before.push(0x0D).push(0x0A) =~= before + seq![0x0Du32, 0x0Au32]);
                }
                if lf {
                    // Never saturates: next < s.len().
                    i = next.saturating_add(1);
                } else {
                    i = next;
                }
            } else if c == 0x0A {
                out.push(0x0D);
                out.push(0x0A);
                proof {
                    assert(out@ =~= before + seq![0x0Du32, 0x0Au32]);
                }
                // Never saturates: i < s.len().
                i = i.saturating_add(1);
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

/// The view of a list of tokens.
pub open spec fn tokens_view(v: Seq<Vec<u32>>) -> Seq<Seq<u32>> {
    v.map_values(|t: Vec<u32>| t@)
}

/// [`split_ws`]: Infra "split a string on ASCII whitespace".
pub fn split_ws_exec(s: &[u32]) -> (r: Vec<Vec<u32>>)
    ensures
        split_ws_ensures(s@, tokens_view(r@)),
{
    let mut tokens: Vec<Vec<u32>> = Vec::new();
    let mut cur: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
        assert(tokens_view(tokens@) =~= Seq::<Seq<u32>>::empty());
    }
    while i < s.len()
        invariant
            i <= s.len(),
            split_ws(s@) == tokens_view(tokens@) + split_ws_acc(s@.skip(i as int), cur@),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            let c = *c;
            proof {
                assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                assert(s@.skip(i as int)[0] == s@[i as int]);
                lemma_split_step(s@.skip(i as int), cur@);
            }
            let ghost before_tokens = tokens@;
            let ghost before_cur = cur@;
            if c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20 {
                if !cur.is_empty() {
                    tokens.push(cur);
                    cur = Vec::new();
                    proof {
                        assert(tokens_view(tokens@) =~= tokens_view(before_tokens).push(before_cur));
                        assert(tokens_view(before_tokens).push(before_cur) + split_ws_acc(
                            s@.skip(i as int + 1),
                            Seq::empty(),
                        ) =~= tokens_view(before_tokens) + (seq![before_cur] + split_ws_acc(
                            s@.skip(i as int + 1),
                            Seq::empty(),
                        )));
                    }
                } else {
                    proof {
                        assert(cur@ =~= Seq::<u32>::empty());
                        assert(Seq::<Seq<u32>>::empty() + split_ws_acc(s@.skip(i as int + 1), Seq::empty())
                            =~= split_ws_acc(s@.skip(i as int + 1), Seq::empty()));
                    }
                }
            } else {
                cur.push(c);
                proof {
                    assert(cur@ =~= before_cur.push(c));
                }
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    if !cur.is_empty() {
        let ghost before_tokens = tokens@;
        let ghost before_cur = cur@;
        tokens.push(cur);
        proof {
            assert(tokens_view(tokens@) =~= tokens_view(before_tokens).push(before_cur));
            assert(tokens_view(before_tokens).push(before_cur) =~= tokens_view(before_tokens) + seq![before_cur]);
        }
    } else {
        proof {
            assert(tokens_view(tokens@) + Seq::<Seq<u32>>::empty() =~= tokens_view(tokens@));
        }
    }
    tokens
}

/// [`any_ci`]: some token is an ASCII case-insensitive match for `k`.
pub fn any_ci_exec(toks: &[Vec<u32>], k: &[u8]) -> (r: bool)
    ensures
        r == any_ci(tokens_view(toks@), k@),
{
    let ghost tv = tokens_view(toks@);
    let mut i: usize = 0;
    proof {
        assert(tv.skip(0) =~= tv);
    }
    while i < toks.len()
        invariant
            i <= toks.len(),
            tv == tokens_view(toks@),
            any_ci(tv, k@) == any_ci(tv.skip(i as int), k@),
        decreases toks.len() - i,
    {
        if let Some(t) = toks.get(i) {
            proof {
                assert(tv.skip(i as int).drop_first() =~= tv.skip(i as int + 1));
                assert(tv.skip(i as int)[0] == tv[i as int]);
                assert(tv[i as int] == toks@[i as int]@);
            }
            if ci_eq_exec(t.as_slice(), k) {
                return true;
            }
        }
        // Never saturates: i < toks.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(tv.skip(toks.len() as int) =~= Seq::<Seq<u32>>::empty());
    }
    false
}

/// [`wf_boundary`].
pub fn wf_boundary_exec(b: &[u8]) -> (r: bool)
    ensures
        wf_boundary_ensures(b@, r),
{
    if b.is_empty() || b.len() > 70 {
        return false;
    }
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b.len(),
            1 <= b.len() <= 70,
            forall|k: int| 0 <= k < i ==> is_bchar(#[trigger] b@[k]),
        decreases b.len() - i,
    {
        if let Some(c) = b.get(i) {
            let c = *c;
            let ok = (0x30..=0x39).contains(&c) || (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c) || c == 0x27
                || c == 0x28 || c == 0x29 || c == 0x2B || c == 0x5F || c == 0x2C || c == 0x2D || c == 0x2E
                || c == 0x2F || c == 0x3A || c == 0x3D || c == 0x3F;
            if !ok {
                return false;
            }
        }
        // Never saturates: i < b.len().
        i = i.saturating_add(1);
    }
    true
}

/// Append `s` to `out`.
pub fn append8(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost start = out@;
    let mut j: usize = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            out@ == start + s@.subrange(0, j as int),
        decreases s.len() - j,
    {
        if let Some(x) = s.get(j) {
            out.push(*x);
        }
        proof {
            assert(s@.subrange(0, j as int + 1) =~= s@.subrange(0, j as int).push(s@[j as int]));
        }
        // Never saturates: j < s.len().
        j = j.saturating_add(1);
    }
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
    }
}

/// [`escape_name`]: LF, CR and `"` become `%0A`, `%0D` and `%22`.
pub fn escape_name_exec(b: &[u8]) -> (r: Vec<u8>)
    ensures
        escape_name_ensures(b@, r@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(b@.skip(0) =~= b@);
    }
    while i < b.len()
        invariant
            i <= b.len(),
            out@ + escape_name(b@.skip(i as int)) == escape_name(b@),
        decreases b.len() - i,
    {
        let ghost before = out@;
        if let Some(c) = b.get(i) {
            let c = *c;
            proof {
                assert(b@.skip(i as int).drop_first() =~= b@.skip(i as int + 1));
                assert(b@.skip(i as int)[0] == b@[i as int]);
            }
            if c == 0x0A {
                append8(&mut out, b"%0A");
            } else if c == 0x0D {
                append8(&mut out, b"%0D");
            } else if c == 0x22 {
                append8(&mut out, b"%22");
            } else {
                out.push(c);
                proof {
                    assert(out@ =~= before.push(c));
                }
            }
        }
        // Never saturates: i < b.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(b@.skip(b.len() as int) =~= Seq::<u8>::empty());
    }
    out
}

} // verus!
