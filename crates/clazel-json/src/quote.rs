//! The executable QuoteJSONString, proven to meet [`super::contract`].
//!
//! The code follows QuoteJSONString (ECMA-262 §25.5.2.3†) step by step; the
//! steps and their quotes live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A lowercase hexadecimal digit as a code unit.
fn hex_digit_lower(n: u16) -> (r: u16)
    requires
        n < 16,
    ensures
        r == super::spec::hex_digit_lower(n as nat),
{
    if n < 10 {
        // Never saturates: 0x30 + n < 0x3A.
        0x30u16.saturating_add(n)
    } else {
        // Never saturates: n >= 10, and 0x61 + (n - 10) < 0x67.
        0x61u16.saturating_add(n.saturating_sub(10))
    }
}

/// UnicodeEscape (C): appends `\u` and the four lowercase hex digits.
fn push_unicode_escape(out: &mut Vec<u16>, unit: u16)
    ensures
        final(out)@ == old(out)@ + unicode_escape(unit),
{
    out.push(0x5C);
    out.push(0x75);
    out.push(hex_digit_lower((unit / 4096) % 16));
    out.push(hex_digit_lower((unit / 256) % 16));
    out.push(hex_digit_lower((unit / 16) % 16));
    out.push(hex_digit_lower(unit % 16));
    proof {
        assert(out@ =~= old(out)@ + unicode_escape(unit));
    }
}

/// Appends a two-code-unit escape sequence `\` and `e`.
fn push_escape_pair(out: &mut Vec<u16>, e: u16)
    ensures
        final(out)@ == old(out)@ + seq![0x5Cu16, e],
{
    out.push(0x5C);
    out.push(e);
    proof {
        assert(out@ =~= old(out)@ + seq![0x5Cu16, e]);
    }
}

/// UTF16EncodeCodePoint (cp), for `cp <= 0x10FFFF`.
pub(crate) fn push_utf16(out: &mut Vec<u16>, cp: u32)
    requires
        cp <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + utf16_encode_code_point(cp),
{
    if cp <= 0xFFFF {
        out.push(cp as u16);
    } else {
        // cp - 0x10000 does not underflow: cp > 0xFFFF.
        let offset = cp.saturating_sub(0x10000);
        // offset <= 0xFFFFF, so the high unit is at most 0x3FF + 0xD800.
        out.push((offset / 0x400).saturating_add(0xD800) as u16);
        out.push((offset % 0x400).saturating_add(0xDC00) as u16);
    }
    proof {
        assert(out@ =~= old(out)@ + utf16_encode_code_point(cp));
    }
}

/// Step 2 for one code point C, for `c <= 0x10FFFF`.
fn push_code_point(out: &mut Vec<u16>, c: u32)
    requires
        c <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + quote_code_point(c),
{
    if c == 0x08 {
        push_escape_pair(out, 0x62);
    } else if c == 0x09 {
        push_escape_pair(out, 0x74);
    } else if c == 0x0A {
        push_escape_pair(out, 0x6E);
    } else if c == 0x0C {
        push_escape_pair(out, 0x66);
    } else if c == 0x0D {
        push_escape_pair(out, 0x72);
    } else if c == 0x22 {
        push_escape_pair(out, 0x22);
    } else if c == 0x5C {
        push_escape_pair(out, 0x5C);
    } else if c < 0x20 || (0xD800..=0xDFFF).contains(&c) {
        push_unicode_escape(out, c as u16);
    } else {
        push_utf16(out, c);
    }
}

/// QuoteJSONString (value).
pub fn quote(value: &[u16]) -> (out: Vec<u16>)
    ensures
        super::contract::quote_ensures(value@, out@),
{
    // 1. product = U+0022
    let mut out: Vec<u16> = Vec::new();
    out.push(0x22);
    // 2. For each code point C of StringToCodePoints(value)
    let mut i: usize = 0;
    proof {
        assert(out@ =~= seq![0x22u16]);
        assert(seq![0x22u16] + quote_loop(value@, 0) =~= out@ + quote_loop(value@, 0));
    }
    loop
        invariant
            i <= value.len(),
            seq![0x22u16] + quote_loop(value@, 0) == out@ + quote_loop(value@, i as nat),
        ensures
            i >= value.len(),
        decreases value.len() - i,
    {
        let first = match value.get(i) {
            Some(&u) => u,
            None => {
                // `get` is `None` only past the end.
                proof {
                    assert(i >= value.len());
                }
                break;
            },
        };
        // CodePointAt: a leading surrogate followed by a trailing one is one
        // code point of two code units, anything else is its own.
        let next = i.saturating_add(1);
        let pair: Option<u16> = match value.get(next) {
            Some(&second) if (0xD800..=0xDBFF).contains(&first) && (0xDC00..=0xDFFF).contains(&second) => Some(
                second,
            ),
            _ => None,
        };
        proof {
            assert(i < value.len());
            assert(next == i + 1);
            assert(pair is Some <==> is_pair_at(value@, i as nat));
        }
        let ghost before = out@;
        match pair {
            Some(second) => {
                // (first - 0xD800) * 0x400 + (second - 0xDC00) + 0x10000
                let hi = first.saturating_sub(0xD800) as u32;
                let lo = second.saturating_sub(0xDC00) as u32;
                let c = hi.saturating_mul(0x400).saturating_add(lo).saturating_add(0x10000);
                proof {
                    assert(c == code_point_at(value@, i as nat).0);
                    assert(c <= 0x10FFFF);
                }
                push_code_point(&mut out, c);
                i = i.saturating_add(2);
                proof {
                    assert(quote_loop(value@, (i - 2) as nat) == quote_code_point(c) + quote_loop(value@, i as nat));
                    assert(before + (quote_code_point(c) + quote_loop(value@, i as nat)) =~= (before + quote_code_point(c))
                        + quote_loop(value@, i as nat));
                }
            },
            None => {
                push_code_point(&mut out, first as u32);
                i = next;
                proof {
                    assert(code_point_at(value@, (i - 1) as nat).0 == first as u32);
                    assert(quote_loop(value@, (i - 1) as nat) == quote_code_point(first as u32) + quote_loop(
                        value@,
                        i as nat,
                    ));
                    assert(before + (quote_code_point(first as u32) + quote_loop(value@, i as nat)) == (before
                        + quote_code_point(first as u32)) + quote_loop(value@, i as nat)) by {
                        assert(before + (quote_code_point(first as u32) + quote_loop(value@, i as nat)) =~= (before
                            + quote_code_point(first as u32)) + quote_loop(value@, i as nat));
                    }
                }
            },
        }
    }
    proof {
        assert(quote_loop(value@, i as nat) == Seq::<u16>::empty());
    }
    // 3. product = product + U+0022
    out.push(0x22);
    // 4. Return product.
    proof {
        assert(out@ =~= (seq![0x22u16] + quote_loop(value@, 0)) + seq![0x22u16]);
    }
    out
}

} // verus!
