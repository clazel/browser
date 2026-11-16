//! Adler-32 as a fold: the lemmas `adler::update` is proven with.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Adler-32 as a fold.
// ---------------------------------------------------------------------------

/// Appending a byte steps the fold once.
pub proof fn lemma_fold_push(s: (nat, nat), data: Seq<u8>, b: u8)
    ensures
        super::contract::adler_fold(s, data.push(b)) == super::contract::adler_step(super::contract::adler_fold(s, data), b),
    decreases data.len(),
{
    if data.len() == 0 {
        assert(data =~= Seq::<u8>::empty());
        assert(data.push(b).len() == 1);
        assert(data.push(b)[0] == b);
        assert(data.push(b).skip(1) =~= Seq::<u8>::empty());
        assert(super::contract::adler_fold(s, data) == s);
        assert(super::contract::adler_fold(super::contract::adler_step(s, b), Seq::<u8>::empty()) == super::contract::adler_step(s, b));
        assert(super::contract::adler_fold(s, data.push(b)) == super::contract::adler_fold(super::contract::adler_step(s, b), data.push(b).skip(1)));
    } else {
        let s2 = super::contract::adler_step(s, data[0]);
        assert(data.push(b)[0] == data[0]);
        assert(data.push(b).skip(1) =~= data.skip(1).push(b));
        assert(super::contract::adler_fold(s, data) == super::contract::adler_fold(s2, data.skip(1)));
        assert(super::contract::adler_fold(s, data.push(b)) == super::contract::adler_fold(s2, data.push(b).skip(1)));
        lemma_fold_push(s2, data.skip(1), b);
    }
}

/// [`adler_sums`] (the RFC's sums, one byte at a time from the end) is the
/// fold from `(1, 0)`.
pub proof fn lemma_sums_fold(data: Seq<u8>)
    ensures
        adler_sums(data) == super::contract::adler_fold((1nat, 0nat), data),
    decreases data.len(),
{
    if data.len() == 0 {
    } else {
        let d = data.drop_last();
        lemma_sums_fold(d);
        lemma_fold_push((1nat, 0nat), d, data.last());
        assert(d.push(data.last()) =~= data);
    }
}

} // verus!
