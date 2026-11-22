//! `mem_rel` used: a machine read of bytes inside regions is LIR's `read_le`
//! of its memory, and a machine write of them gives a memory related to
//! LIR's `write_le`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The byte `k` of `v`, little-endian: `(v / 256^k) % 256`.
pub open spec fn bytek(v: nat, k: nat) -> nat
    decreases k,
{
    if k == 0 {
        v % 256
    } else {
        bytek(v / 256, (k - 1) as nat)
    }
}

/// `read_le` is below `2^(8n)`.
pub proof fn lemma_read_le_range(m: lir::Mem, a: nat, n: nat)
    ensures
        lir::read_le(m, a, n) < vstd::arithmetic::power2::pow2(8 * n),
    decreases n,
{
    vstd::arithmetic::power2::lemma2_to64();
    if n > 0 {
        let n1 = (n - 1) as nat;
        lemma_read_le_range(m, a + 1, n1);
        vstd::arithmetic::power2::lemma_pow2_adds(8, 8 * n1);
        assert(8 * n == 8 + 8 * n1);
        assert(lir::byte_at(m, a) < 256);
    }
}

/// `read_mem` is below `2^(8n)`.
pub proof fn lemma_read_mem_range(mm: Map<int, u8>, a: int, n: nat, v: int)
    requires
        x64::read_mem(mm, a, n) == Some(v),
    ensures
        0 <= v < vstd::arithmetic::power2::pow2(8 * n) as int,
    decreases n,
{
    vstd::arithmetic::power2::lemma2_to64();
    if n > 0 {
        let n1 = (n - 1) as nat;
        match x64::read_mem(mm, a + 1, n1) {
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
        mem_rel(lay, lm, mm),
        forall|i: nat| i < n ==> in_regions(lay, #[trigger] (a + i)),
    ensures
        x64::read_mem(mm, a as int, n) == Some(lir::read_le(lm, a, n) as int),
    decreases n,
{
    if n > 0 {
        let n1 = (n - 1) as nat;
        assert(in_regions(lay, a + 0));
        assert forall|i: nat| i < n1 implies in_regions(lay, #[trigger] (a + 1 + i)) by {
            assert(in_regions(lay, a + (i + 1)));
        }
        lemma_read_rel(lay, lm, mm, a + 1, n1);
        assert((a + 1) as int == a as int + 1);
        assert(mm.dom().contains(a as int) && mm[a as int] == lir::byte_at(lm, a));
    }
}

/// `write_le` changes byte `b` to byte `b - a` of `v` inside the range, and
/// nothing outside it.
pub proof fn lemma_write_le_byte(lm: lir::Mem, a: nat, v: nat, n: nat, b: nat)
    ensures
        lir::byte_at(lir::write_le(lm, a, v, n), b) == if a <= b && b < a + n {
            bytek(v, (b - a) as nat) as u8
        } else {
            lir::byte_at(lm, b)
        },
    decreases n,
{
    if n > 0 {
        let lm1 = lm.insert(a, (v % 256) as u8);
        lemma_write_le_byte(lm1, a + 1, v / 256, (n - 1) as nat, b);
        if b == a {
            assert(lir::byte_at(lm1, b) == (v % 256) as u8);
        } else if b > a && b < a + n {
            assert(bytek(v / 256, (b - (a + 1)) as nat) == bytek(v, (b - a) as nat));
        } else {
            assert(lir::byte_at(lm1, b) == lir::byte_at(lm, b));
        }
    }
}

/// `write_mem` puts byte `b - a` of `v` at `b` inside the range.
pub proof fn lemma_write_mem_byte(mm: Map<int, u8>, a: int, n: nat, v: int, mm2: Map<int, u8>, b: int)
    requires
        0 <= v,
        x64::write_mem(mm, a, n, v) == Some(mm2),
        a <= b < a + n,
    ensures
        mm2[b] == bytek(v as nat, (b - a) as nat) as u8,
    decreases n,
{
    let n1 = (n - 1) as nat;
    match x64::write_mem(mm, a + 1, n1, v / 256) {
        Some(m3) => {
            assert(mm2 == m3.insert(a, (v % 256) as u8));
            if b == a {
            } else {
                lemma_write_mem_byte(mm, a + 1, n1, v / 256, m3, b);
                assert(bytek(v as nat, (b - a) as nat) == bytek((v / 256) as nat, (b - (a + 1)) as nat));
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
        mem_rel(lay, lm, mm),
        forall|i: nat| i < n ==> in_regions(lay, #[trigger] (a + i)),
        x64::write_mem(mm, a as int, n, v as int) == Some(mm2),
    ensures
        mem_rel(lay, lir::write_le(lm, a, v, n), mm2),
{
    super::memlemmas::lemma_write_mem_frame(mm, a as int, n, v as int, mm2);
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
