//! `mem_rel` used: a machine read of bytes inside regions is LIR's `read_le` of
//! its memory, and a machine write of them gives a memory related to LIR's
//! `write_le`. The A64 counterpart of [`crate::cfmemrel`] (whose LIR-only
//! lemmas, [`crate::cfmemrel::lemma_write_le_byte`] and the rest, are shared).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfmemrel::{bytek, lemma_write_le_byte};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A byte of a region of a well-formed layout is a machine address.
pub proof fn lemma_region_lt(lay: lir::Layout, a: nat)
    requires
        lir::layout_wf(lay),
        in_regions(lay, a),
    ensures
        a < 0x1_0000_0000_0000_0000,
{
    let r = choose|r: int| 0 <= r < lay.len() && lay[r].base <= a && a < lay[r].base + lay[r].bound;
    assert(lay[r].base + lay[r].bound <= 0x1_0000_0000_0000_0000);
}

/// `mem_read` is below `2^(8n)`.
pub proof fn lemma_read_mem_range(mm: Map<int, u8>, a: int, n: nat, v: int)
    requires
        isa::mem_read(mm, a, n) == Some(v),
    ensures
        0 <= v < vstd::arithmetic::power2::pow2(8 * n) as int,
    decreases n,
{
    vstd::arithmetic::power2::lemma2_to64();
    if n > 0 {
        let n1 = (n - 1) as nat;
        match isa::mem_read(mm, a + 1, n1) {
            Some(rest) => {
                lemma_read_mem_range(mm, a + 1, n1, rest);
                vstd::arithmetic::power2::lemma_pow2_adds(8, 8 * n1);
                assert(8 * n == 8 + 8 * n1);
            },
            None => {},
        }
    }
}

/// **A read of bytes inside regions is LIR's read.**
pub proof fn lemma_read_rel(lay: lir::Layout, lm: lir::Mem, mm: Map<int, u8>, a: nat, n: nat)
    requires
        lir::layout_wf(lay),
        mem_rel(lay, lm, mm),
        forall|i: nat| i < n ==> in_regions(lay, #[trigger] (a + i)),
    ensures
        isa::mem_read(mm, a as int, n) == Some(lir::read_le(lm, a, n) as int),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        assert(in_regions(lay, a + 0));
        lemma_region_lt(lay, a);
        super::memlemmas::lemma_trunc64(a as int);
        assert forall|i: nat| i < n1 implies in_regions(lay, #[trigger] (a + 1 + i)) by {
            assert(in_regions(lay, a + (i + 1)));
        }
        lemma_read_rel(lay, lm, mm, a + 1, n1);
        assert((a + 1) as int == a as int + 1);
        assert(mm.dom().contains(a as int) && mm[a as int] == lir::byte_at(lm, a));
    }
}

/// `mem_set` puts byte `b - a` of `v` at `b` inside the range.
pub proof fn lemma_write_mem_byte(
    mm: Map<int, u8>,
    a: int,
    n: nat,
    v: int,
    mm2: Map<int, u8>,
    b: int,
)
    requires
        0 <= v,
        0 <= a,
        a + n < 0x1_0000_0000_0000_0000,
        isa::mem_set(mm, a, n, v) == Some(mm2),
        a <= b < a + n,
    ensures
        mm2[b] == bytek(v as nat, (b - a) as nat) as u8,
    decreases n,
{
    super::memlemmas::lemma_trunc64(a);
    let n1 = (n - 1) as nat;
    match isa::mem_set(mm, a + 1, n1, v / 256) {
        Some(m3) => {
            assert(mm2 == m3.insert(a, (v % 256) as u8));
            if b == a {
            } else {
                lemma_write_mem_byte(mm, a + 1, n1, v / 256, m3, b);
                assert(bytek(v as nat, (b - a) as nat) == bytek(
                    (v / 256) as nat,
                    (b - (a + 1)) as nat,
                ));
            }
        },
        None => {},
    }
}

/// **A write of bytes inside regions keeps the memories related.** The machine
/// writes the low `n` bytes of `v`, LIR the same.
pub proof fn lemma_write_rel(
    lay: lir::Layout,
    lm: lir::Mem,
    mm: Map<int, u8>,
    mm2: Map<int, u8>,
    a: nat,
    n: nat,
    v: nat,
)
    requires
        lir::layout_wf(lay),
        mem_rel(lay, lm, mm),
        forall|i: nat| i < n ==> in_regions(lay, #[trigger] (a + i)),
        isa::mem_set(mm, a as int, n, v as int) == Some(mm2),
        a + n < 0x1_0000_0000_0000_0000,
    ensures
        mem_rel(lay, lir::write_le(lm, a, v, n), mm2),
{
    super::memlemmas::lemma_mem_set_frame(mm, a as int, n, v as int, mm2);
    assert forall|b: nat| #[trigger] in_regions(lay, b) implies mm2.dom().contains(b as int)
        && mm2[b as int] == lir::byte_at(lir::write_le(lm, a, v, n), b) by {
        assert(mm.dom().contains(b as int) && mm[b as int] == lir::byte_at(lm, b));
        lemma_write_le_byte(lm, a, v, n, b);
        if a <= b && b < a + n {
            lemma_write_mem_byte(mm, a as int, n, v as int, mm2, b as int);
        }
    }
}

} // verus!
