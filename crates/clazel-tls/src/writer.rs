//! The executable writers of the presentation language (RFC 8446 §3):
//! append a number, a vector length and a vector's contents to a `Vec<u8>`.
//! Each one's contract is that the output is the old output followed by
//! what the spec's writer writes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §3.3: append the `width` bytes spelling `value` in network byte order,
/// most significant first ([`be_bytes`]'s recursion).
pub fn push_be(out: &mut Vec<u8>, value: u64, width: usize)
    requires
        (value as nat) < pow256(width as nat),
    ensures
        final(out)@ =~= old(out)@ + be_bytes(value as nat, width as nat),
    decreases width,
{
    if width == 0 {
        assert(be_bytes(value as nat, 0) =~= Seq::<u8>::empty());
        return ;
    }
    // Never saturates: width >= 1.
    let before = width.saturating_sub(1);
    assert(pow256(width as nat) == 256 * pow256(before as nat));
    assert(((value / 256) as nat) < pow256(before as nat)) by (nonlinear_arith)
        requires
            (value as nat) < 256 * pow256(before as nat),
    ;
    push_be(out, value / 256, before);
    out.push((value % 256) as u8);
    assert(out@ =~= old(out)@ + be_bytes(value as nat, width as nat));
}

/// §3.4: the width of a vector's length field for a ceiling below 2^24
/// ([`len_width`]).
pub fn len_width_of(ceil: usize) -> (w: usize)
    requires
        ceil < 16777216,
    ensures
        w == len_width(ceil as nat),
{
    if ceil <= 255 {
        1
    } else if ceil <= 65535 {
        2
    } else {
        3
    }
}

/// §3.4: append the length field of a vector whose contents are `len`
/// bytes and whose ceiling is `ceil`.
pub fn push_len(out: &mut Vec<u8>, len: usize, ceil: usize)
    requires
        ceil < 16777216,
        len <= ceil,
    ensures
        final(out)@ =~= old(out)@ + be_bytes(len as nat, len_width(ceil as nat)),
{
    proof {
        super::lemmas_pl::lemma_len_width_holds(ceil as nat);
    }
    let w = len_width_of(ceil);
    push_be(out, len as u64, w);
}

/// §3.4: append a variable-length vector's length field and contents
/// ([`write_vec`]); the contents are within the ceiling.
pub fn push_vec(out: &mut Vec<u8>, content: &[u8], ceil: usize)
    requires
        ceil < 16777216,
        content.len() <= ceil,
    ensures
        final(out)@ =~= old(out)@ + write_vec(content@, ceil as nat),
{
    push_len(out, content.len(), ceil);
    out.extend_from_slice(content);
    assert(out@ =~= old(out)@ + write_vec(content@, ceil as nat));
}

/// §3.3: append a `uint16`.
pub fn push_u16(out: &mut Vec<u8>, v: u16)
    ensures
        final(out)@ =~= old(out)@ + write_u16(v),
{
    proof {
        super::lemmas_pl::lemma_pow256_widths();
    }
    push_be(out, v as u64, 2);
}

} // verus!
