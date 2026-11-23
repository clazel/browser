//! Facts about LIR's byte memory ([`lir::read_le`], [`lir::write_le`]) that
//! the frame accesses need: a store changes only the bytes it writes, and
//! reading back what was stored gives the value. Proven here because
//! `clazel-lir` states the semantics but proves no such lemma.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `256^n`, the number of values `n` bytes hold.
pub open spec fn p256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * p256((n - 1) as nat)
    }
}

/// Eight bytes hold `2^64` values.
pub proof fn lemma_p256_8()
    ensures
        p256(8) == 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(p256, 9);
}

/// A byte outside the written range is not changed by [`lir::write_le`].
pub proof fn lemma_write_le_other(m: lir::Mem, a: nat, v: nat, n: nat, b: nat)
    requires
        b < a || b >= a + n,
    ensures
        lir::byte_at(lir::write_le(m, a, v, n), b) == lir::byte_at(m, b),
    decreases n,
{
    if n > 0 {
        let m1 = m.insert(a, (v % 256) as u8);
        assert(lir::byte_at(m1, b) == lir::byte_at(m, b));
        lemma_write_le_other(m1, (a + 1) as nat, v / 256, (n - 1) as nat, b);
    }
}

/// Reading back `n` bytes just written gives the value, when it fits.
pub proof fn lemma_read_write_same(m: lir::Mem, a: nat, v: nat, n: nat)
    requires
        v < p256(n),
    ensures
        lir::read_le(lir::write_le(m, a, v, n), a, n) == v,
    decreases n,
{
    if n > 0 {
        let m1 = m.insert(a, (v % 256) as u8);
        let w = lir::write_le(m1, (a + 1) as nat, v / 256, (n - 1) as nat);
        assert(lir::write_le(m, a, v, n) == w);
        lemma_write_le_other(m1, (a + 1) as nat, v / 256, (n - 1) as nat, a);
        assert(lir::byte_at(m1, a) == (v % 256) as u8);
        assert(p256(n) == 256 * p256((n - 1) as nat));
        assert(v / 256 < p256((n - 1) as nat)) by (nonlinear_arith)
            requires
                v < 256 * p256((n - 1) as nat),
        ;
        lemma_read_write_same(m1, (a + 1) as nat, v / 256, (n - 1) as nat);
        assert(lir::read_le(w, a, n) == lir::byte_at(w, a) + 256 * lir::read_le(w, (a + 1) as nat, (n - 1) as nat));
        assert(v % 256 + 256 * (v / 256) == v) by (nonlinear_arith);
    }
}

/// Reading `k` bytes that do not overlap the written range gives what was
/// there before.
pub proof fn lemma_read_le_other(m: lir::Mem, a: nat, v: nat, n: nat, b: nat, k: nat)
    requires
        b + k <= a || b >= a + n,
    ensures
        lir::read_le(lir::write_le(m, a, v, n), b, k) == lir::read_le(m, b, k),
    decreases k,
{
    if k > 0 {
        lemma_write_le_other(m, a, v, n, b);
        lemma_read_le_other(m, a, v, n, (b + 1) as nat, (k - 1) as nat);
    }
}

/// Storing the 8 bytes of `v` in slot `j` of the value stack keeps the
/// relation, for the region with that slot set to `v`.
pub proof fn lemma_store_mem_rel(lay: lir::Layout, region: Seq<u64>, m: lir::Mem, j: int, v: u64)
    requires
        lay.len() >= 1,
        mem_rel(lay, region, m),
        0 <= j < region.len(),
    ensures
        mem_rel(lay, region.update(j, v), lir::write_le(m, slot_addr(lay, j), v as nat, 8)),
{
    let m2 = lir::write_le(m, slot_addr(lay, j), v as nat, 8);
    let r2 = region.update(j, v);
    assert forall|i: int| 0 <= i < r2.len() implies lir::read_le(m2, slot_addr(lay, i), 8) == #[trigger] r2[i] as nat by {
        if i == j {
            lemma_p256_8();
            lemma_read_write_same(m, slot_addr(lay, j), v as nat, 8);
        } else {
            assert(r2[i] == region[i]);
            assert(region[i] == region[i]);
            lemma_read_le_other(m, slot_addr(lay, j), v as nat, 8, slot_addr(lay, i), 8);
        }
    }
}

} // verus!
