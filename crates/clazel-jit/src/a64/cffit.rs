//! **The size invariant** every displacement fits. A conditional branch
//! (`b.cond`, `cbz`, `cbnz`) has a 19-bit signed displacement in words, so it
//! reaches at most `2^20` bytes either way; `b` reaches `2^27`. [`labels_fit`]
//! says every label is far enough from every place in code of `size` bytes
//! that a conditional branch there reaches it; and a multiple of 4. The
//! invariant is closed under taking a piece of the code ([`lemma_fit_shift`]),
//! adding a label in front ([`lemma_fit_cons`]) and shrinking the size.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every label offset is a multiple of 4 and far enough from every byte of code
/// of `size` bytes that a 19-bit-word displacement reaches it: from a branch at
/// byte `p` with `0 <= p < size`, `-2^20 <= o - p < 2^20`.
pub open spec fn labels_fit(offs: Seq<int>, size: nat) -> bool {
    forall|l: int|
        0 <= l < offs.len() ==> #[trigger] offs[l] % 4 == 0 && -0x10_0000 + size + 8 <= offs[l]
            && offs[l] <= 0xF_FFF0
}

/// Labels seen from code that starts `d` bytes in (`d` a multiple of 4), for a
/// smaller piece.
pub proof fn lemma_fit_shift(offs: Seq<int>, d: nat, size: nat, size2: nat)
    requires
        labels_fit(offs, size),
        d % 4 == 0,
        d + size2 <= size,
    ensures
        labels_fit(shift(offs, d as int), size2),
{
    assert forall|l: int| 0 <= l < shift(offs, d as int).len() implies #[trigger] shift(
        offs,
        d as int,
    )[l] % 4 == 0 && -0x10_0000 + size2 + 8 <= shift(offs, d as int)[l] && shift(
        offs,
        d as int,
    )[l] <= 0xF_FFF0 by {
        super::cfcompose::lemma_shift_index(offs, d as int, l);
    }
}

/// A new label in front.
pub proof fn lemma_fit_cons(x: int, offs: Seq<int>, size: nat)
    requires
        labels_fit(offs, size),
        x % 4 == 0,
        -0x10_0000 + size + 8 <= x <= 0xF_FFF0,
    ensures
        labels_fit(seq![x] + offs, size),
{
    let all = seq![x] + offs;
    assert forall|l: int| 0 <= l < all.len() implies #[trigger] all[l] % 4 == 0 && -0x10_0000
        + size + 8 <= all[l] && all[l] <= 0xF_FFF0 by {
        if l > 0 {
            assert(all[l] == offs[l - 1]);
        }
    }
}

/// `labels_fit` for a smaller size.
pub proof fn lemma_fit_mono(offs: Seq<int>, size: nat, size2: nat)
    requires
        labels_fit(offs, size),
        size2 <= size,
    ensures
        labels_fit(offs, size2),
{
}

} // verus!
