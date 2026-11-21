//! Facts proven about [`super::spec`]: evidence that the transcription is
//! right, not part of what an implementation must meet. Each lemma states a
//! property that the RFCs state or that follows from what they state, so a
//! slip in a spec table or step makes a lemma false (see `mutations.json`).
//! The tables and the checksum example are here; the rest is in
//! `lemmas_usable`, `lemmas_bounded`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// RFC 1951 §3.2.5: the two tables are consecutive ranges.
//
// The tables list, for each code, the smallest value and the number of extra
// bits, so code `c` covers `base(c) ..= base(c) + 2^extra(c) - 1` and the
// next code must start right after: this is what the RFC's "Length(s)" and
// "Dist" columns show, and it is independent of the numbers themselves.
// ---------------------------------------------------------------------------

/// `2^e` for the extra-bit counts the tables use (0 to 13), written out so
/// that a concrete evaluation needs no recursion; [`lemma_span_is_pow2`]
/// ties it to the power.
pub open spec fn span(e: nat) -> nat {
    if e == 0 { 1 } else if e == 1 { 2 } else if e == 2 { 4 } else if e == 3 { 8 }
    else if e == 4 { 16 } else if e == 5 { 32 } else if e == 6 { 64 } else if e == 7 { 128 }
    else if e == 8 { 256 } else if e == 9 { 512 } else if e == 10 { 1024 }
    else if e == 11 { 2048 } else if e == 12 { 4096 } else if e == 13 { 8192 } else { 0 }
}

/// `span` is the power of two.
pub proof fn lemma_span_is_pow2(e: nat)
    requires
        e <= 13,
    ensures
        span(e) == pow2(e),
{
    if e == 0 {} else if e == 1 {} else if e == 2 {} else if e == 3 {} else if e == 4 {} else if e == 5 {} else if e == 6 {} else if e == 7 {} else if e == 8 {} else if e == 9 {} else if e == 10 {} else if e == 11 {} else if e == 12 {} else if e == 13 {}
}

/// Length codes 257 to 283: the next code starts where this one ends.
pub proof fn lemma_len_chain(c: nat)
    requires
        257 <= c < 284,
    ensures
        len_base((c + 1) as nat) == len_base(c) + span(len_extra(c)),
{
    if c == 257 {} else if c == 258 {} else if c == 259 {} else if c == 260 {} else if c == 261 {} else if c == 262 {} else if c == 263 {} else if c == 264 {} else if c == 265 {} else if c == 266 {} else if c == 267 {} else if c == 268 {} else if c == 269 {} else if c == 270 {} else if c == 271 {} else if c == 272 {} else if c == 273 {} else if c == 274 {} else if c == 275 {} else if c == 276 {} else if c == 277 {} else if c == 278 {} else if c == 279 {} else if c == 280 {} else if c == 281 {} else if c == 282 {} else if c == 283 {}
}

/// The end of the length table: code 284 covers 227 to 258 by its 5 extra
/// bits, but "258" is code 285's alone (0 extra bits), so 284's range is
/// read as 227 to 257 (the RFC's own table says "227-257") and 285 is a
/// single length. Also the first code, 257, is length 3.
pub proof fn lemma_len_ends()
    ensures
        len_base(257) == 3,
        len_extra(284) == 5,
        len_base(284) + span(len_extra(284)) == 259,
        len_base(285) == 258,
        len_extra(285) == 0,
{
}

/// Distance codes 0 to 28: the next code starts where this one ends.
pub proof fn lemma_dist_chain(c: nat)
    requires
        c < 29,
    ensures
        dist_base((c + 1) as nat) == dist_base(c) + span(dist_extra(c)),
{
    if c == 0 {} else if c == 1 {} else if c == 2 {} else if c == 3 {} else if c == 4 {} else if c == 5 {} else if c == 6 {} else if c == 7 {} else if c == 8 {} else if c == 9 {} else if c == 10 {} else if c == 11 {} else if c == 12 {} else if c == 13 {} else if c == 14 {} else if c == 15 {} else if c == 16 {} else if c == 17 {} else if c == 18 {} else if c == 19 {} else if c == 20 {} else if c == 21 {} else if c == 22 {} else if c == 23 {} else if c == 24 {} else if c == 25 {} else if c == 26 {} else if c == 27 {} else if c == 28 {}
}

/// The end of the distance table: the first distance is 1 and the last
/// code, 29, ends at 32768 ("24577-32768").
pub proof fn lemma_dist_ends()
    ensures
        dist_base(0) == 1,
        dist_base(29) + span(dist_extra(29)) == 32769,
{
}

} // verus!
