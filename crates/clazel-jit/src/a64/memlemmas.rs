//! Facts about `clazel-a64`'s byte memory ([`isa::mem_read`], [`isa::mem_set`]):
//! what a write leaves alone, what a read of what was just written gives, and
//! that a read depends only on the bytes it touches. The A64 counterpart of
//! [`crate::memlemmas`]; the addresses are below `2^64`, so
//! [`isa::trunc`]`(64, _)` of each byte's address is the address.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The powers of two the proofs use, evaluated.
pub proof fn lemma_p2_consts()
    ensures
        isa::p2(0) == 1,
        isa::p2(5) == 32,
        isa::p2(6) == 64,
        isa::p2(8) == 256,
        isa::p2(16) == 0x1_0000,
        isa::p2(31) == 0x8000_0000,
        isa::p2(32) == 0x1_0000_0000,
        isa::p2(47) == 0x8000_0000_0000,
        isa::p2(48) == 0x1_0000_0000_0000,
        isa::p2(62) == 0x4000_0000_0000_0000,
        isa::p2(63) == 0x8000_0000_0000_0000,
        isa::p2(64) == 0x1_0000_0000_0000_0000,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// A number below `2^64` is its own low 64 bits.
pub proof fn lemma_trunc64(a: int)
    requires
        0 <= a < 0x1_0000_0000_0000_0000,
    ensures
        isa::trunc(64, a) == a,
{
    lemma_p2_consts();
    vstd::arithmetic::div_mod::lemma_small_mod(a as nat, 0x1_0000_0000_0000_0000nat);
}

/// A write that succeeds leaves the mapped addresses as they were and every
/// byte outside the written range as it was.
pub proof fn lemma_mem_set_frame(m: Map<int, u8>, addr: int, n: nat, v: int, m2: Map<int, u8>)
    requires
        isa::mem_set(m, addr, n, v) == Some(m2),
        0 <= addr,
        addr + n < 0x1_0000_0000_0000_0000,
    ensures
        m2.dom() =~= m.dom(),
        forall|b: int|
            #![trigger m2.dom().contains(b)]
            m.dom().contains(b) && (b < addr || addr + n <= b) ==> m2[b] == m[b],
    decreases n,
{
    if n > 0 {
        lemma_trunc64(addr);
        match isa::mem_set(m, addr + 1, (n - 1) as nat, v / 256) {
            Some(m3) => {
                lemma_mem_set_frame(m, addr + 1, (n - 1) as nat, v / 256, m3);
                assert(m2 == m3.insert(addr, (v % 256) as u8));
                assert(m.dom().contains(addr));
                assert(m2.dom() =~= m.dom());
            },
            None => {},
        }
    }
}

/// A write to mapped bytes succeeds.
pub proof fn lemma_mem_set_some(m: Map<int, u8>, addr: int, n: nat, v: int)
    requires
        0 <= addr,
        addr + n < 0x1_0000_0000_0000_0000,
        forall|i: int| 0 <= i < n ==> m.dom().contains(#[trigger] (addr + i)),
    ensures
        isa::mem_set(m, addr, n, v) is Some,
    decreases n,
{
    if n > 0 {
        lemma_trunc64(addr);
        assert(m.dom().contains(addr + 0));
        assert forall|i: int| 0 <= i < n - 1 implies m.dom().contains(#[trigger] (addr + 1 + i)) by {
            assert(m.dom().contains(addr + (i + 1)));
        }
        lemma_mem_set_some(m, addr + 1, (n - 1) as nat, v / 256);
    }
}

/// Inserting a byte outside a read's range does not change the read.
pub proof fn lemma_mem_read_insert_other(m: Map<int, u8>, a: int, n: nat, b: int, x: u8)
    requires
        0 <= a,
        a + n < 0x1_0000_0000_0000_0000,
        b < a || a + n <= b,
    ensures
        isa::mem_read(m.insert(b, x), a, n) == isa::mem_read(m, a, n),
    decreases n,
{
    if n > 0 {
        lemma_trunc64(a);
        lemma_mem_read_insert_other(m, a + 1, (n - 1) as nat, b, x);
        assert(m.insert(b, x).dom().contains(a) == m.dom().contains(a));
        if m.dom().contains(a) {
            assert(m.insert(b, x)[a] == m[a]);
        }
    }
}

/// Two memories that agree on the bytes of a read give the same read.
pub proof fn lemma_mem_read_congr(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: nat)
    requires
        0 <= a,
        a + n < 0x1_0000_0000_0000_0000,
        forall|i: int|
            0 <= i < n ==> (m.dom().contains(#[trigger] (a + i)) == m2.dom().contains(a + i)) && (
            m.dom().contains(a + i) ==> m[a + i] == m2[a + i]),
    ensures
        isa::mem_read(m, a, n) == isa::mem_read(m2, a, n),
    decreases n,
{
    if n > 0 {
        lemma_trunc64(a);
        assert forall|i: int| 0 <= i < n - 1 implies (m.dom().contains(#[trigger] (a + 1 + i))
            == m2.dom().contains(a + 1 + i)) && (m.dom().contains(a + 1 + i) ==> m[a + 1 + i]
            == m2[a + 1 + i]) by {
            assert(a + (i + 1) == a + 1 + i);
        }
        lemma_mem_read_congr(m, m2, a + 1, (n - 1) as nat);
        assert(a + 0 == a);
    }
}

/// Reading what was just written gives the value written (below `2^(8n)`).
pub proof fn lemma_read_after_write_same(
    m: Map<int, u8>,
    addr: int,
    n: nat,
    v: int,
    m2: Map<int, u8>,
)
    requires
        isa::mem_set(m, addr, n, v) == Some(m2),
        0 <= addr,
        addr + n < 0x1_0000_0000_0000_0000,
        0 <= v < vstd::arithmetic::power2::pow2(8 * n) as int,
    ensures
        isa::mem_read(m2, addr, n) == Some(v),
    decreases n,
{
    lemma_p2_consts();
    if n == 0 {
        vstd::arithmetic::power2::lemma2_to64();
        assert(v == 0);
    } else {
        lemma_trunc64(addr);
        match isa::mem_set(m, addr + 1, (n - 1) as nat, v / 256) {
            Some(m3) => {
                let n1 = (n - 1) as nat;
                assert(vstd::arithmetic::power2::pow2(8 * n) == 256 * vstd::arithmetic::power2::pow2(
                    8 * n1,
                )) by {
                    vstd::arithmetic::power2::lemma_pow2_adds(8, 8 * n1);
                    assert(8 * n == 8 + 8 * n1);
                }
                assert(0 <= v / 256 < vstd::arithmetic::power2::pow2(8 * n1) as int) by {
                    vstd::arithmetic::power2::lemma_pow2_pos(8 * n1);
                }
                lemma_read_after_write_same(m, addr + 1, (n - 1) as nat, v / 256, m3);
                assert(m2 == m3.insert(addr, (v % 256) as u8));
                lemma_mem_set_frame(m, addr + 1, (n - 1) as nat, v / 256, m3);
                lemma_mem_read_insert_other(m3, addr + 1, (n - 1) as nat, addr, (v % 256) as u8);
                assert(m3.dom().contains(addr));
                assert(m2.dom().contains(addr));
                assert(m2[addr] == (v % 256) as u8);
                assert(v == v % 256 + 256 * (v / 256));
            },
            None => {},
        }
    }
}

/// A read of bytes disjoint from a write is not changed by it.
pub proof fn lemma_read_after_write_disjoint(
    m: Map<int, u8>,
    addr: int,
    n: nat,
    v: int,
    m2: Map<int, u8>,
    b: int,
    k: nat,
)
    requires
        isa::mem_set(m, addr, n, v) == Some(m2),
        0 <= addr,
        addr + n < 0x1_0000_0000_0000_0000,
        0 <= b,
        b + k < 0x1_0000_0000_0000_0000,
        b + k <= addr || addr + n <= b,
    ensures
        isa::mem_read(m2, b, k) == isa::mem_read(m, b, k),
{
    lemma_mem_set_frame(m, addr, n, v, m2);
    assert forall|i: int| 0 <= i < k implies (m.dom().contains(#[trigger] (b + i))
        == m2.dom().contains(b + i)) && (m.dom().contains(b + i) ==> m[b + i] == m2[b + i]) by {
        assert(m2.dom().contains(b + i) == m.dom().contains(b + i));
    }
    lemma_mem_read_congr(m, m2, b, k);
}

} // verus!
