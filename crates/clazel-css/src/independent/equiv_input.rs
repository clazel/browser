//! The independent transcription of §3.2 ([`super::input`]) is the spec's
//! ([`crate::input::spec`]): the `XX` bytes, the declared label, the fallback
//! encoding and the decoding of a stylesheet's bytes agree, for every stream of
//! bytes, label and environment encoding.

#[cfg(verus_only)]
use super::*;
#[cfg(verus_only)]
use super::input::*;
#[cfg(verus_only)]
use super::equiv_base::ints;
#[cfg(verus_only)]
use crate::input::spec as s;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first 1024 bytes agree.
pub proof fn lemma_first_1024(b: Seq<u8>)
    ensures
        i_first_1024(b) == s::first_1024_bytes(b),
{
}

/// The `XX` bytes agree.
pub proof fn lemma_xx(b: u8)
    ensures
        i_xx(b) == s::is_xx_byte(b),
{
}

/// The end of the run of `XX` bytes agrees, from every position.
pub proof fn lemma_xx_end(h: Seq<u8>, p: nat)
    ensures
        i_xx_end(h, p) as int == s::skip_xx_bytes(h, p as int),
    decreases (if h.len() > p { h.len() - p } else { 0 }),
{
    if p < h.len() && i_xx(h[p as int]) {
        lemma_xx_end(h, p + 1);
    }
}

/// The declared label agrees: the independent one is the spec's, as the
/// ASCII string "interpreted as ASCII".
pub proof fn lemma_declared_label(b: Seq<u8>)
    ensures
        i_declared_label(b) == match s::declared_label(s::first_1024_bytes(b)) {
            Some(label) => Some(s::ascii_string(label)),
            None => None,
        },
{
    let h = i_first_1024(b);
    lemma_first_1024(b);
    assert(h == s::first_1024_bytes(b));
    assert(s::charset_prefix() == i_charset_prefix());
    if h.len() >= 10 && h.subrange(0, 10) == i_charset_prefix() {
        let e = i_xx_end(h, 10);
        lemma_xx_end(h, 10);
        assert(s::charset_prefix().len() == 10);
        if e + 1 < h.len() && h[e as int] == 0x22 && h[(e + 1) as int] == 0x3B {
            assert(s::declared_label(h) == Some(h.subrange(10, e as int)));
            assert(h.subrange(10, e as int).map_values(|x: u8| x as u32) == s::ascii_string(h.subrange(10, e as int)));
        }
    }
}

/// The fallback encoding agrees.
pub proof fn lemma_fallback(
    b: Seq<u8>,
    label: Option<Seq<u32>>,
    env: Option<clazel_encoding::labels::spec::Encoding>,
)
    ensures
        i_fallback_encoding(b, label, env) == s::determine_the_fallback_encoding(b, label, env),
{
    lemma_declared_label(b);
}

/// The decoded code points agree, as integers.
pub proof fn theorem_decode_bytes_equals(
    b: Seq<u8>,
    label: Option<Seq<u32>>,
    env: Option<clazel_encoding::labels::spec::Encoding>,
)
    ensures
        i_decode_bytes(b, label, env) == match s::decode_bytes(b, label, env) {
            Some(cs) => Some(ints(cs)),
            None => None,
        },
{
    lemma_fallback(b, label, env);
    if let Some(cs) = s::decode_bytes(b, label, env) {
        assert(cs.map_values(|c: u32| c as int) =~= ints(cs));
    }
}

} // verus!
