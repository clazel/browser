//! Facts about `clazel-x64`'s byte-addressed memory (`read_mem`,
//! `write_mem`), and about the 8-byte frame slots built on them. They are
//! what every template's proof uses to say "this store changed this slot and
//! no other byte".

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The concrete values of the powers of two the proofs use.
pub proof fn lemma_p2_consts()
    ensures
        x64::p2(8) == 256,
        x64::p2(32) == 0x1_0000_0000,
        x64::p2(47) == 0x8000_0000_0000,
        x64::p2(63) == 0x8000_0000_0000_0000,
        x64::p2(64) == 0x1_0000_0000_0000_0000,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// A write that succeeds touches only the bytes it writes, and maps nothing
/// new: the domain is unchanged and every byte outside `[addr, addr + n)` keeps
/// its value.
pub proof fn lemma_write_mem_frame(m: Map<int, u8>, addr: int, n: nat, v: int, m2: Map<int, u8>)
    requires
        x64::write_mem(m, addr, n, v) == Some(m2),
    ensures
        m2.dom() =~= m.dom(),
        forall|b: int|
            #![trigger m2.dom().contains(b)]
            m.dom().contains(b) && (b < addr || addr + n <= b) ==> m2[b] == m[b],
    decreases n,
{
    if n > 0 {
        match x64::write_mem(m, addr + 1, (n - 1) as nat, v / 256) {
            Some(m3) => {
                lemma_write_mem_frame(m, addr + 1, (n - 1) as nat, v / 256, m3);
                assert(m2 == m3.insert(addr, (v % 256) as u8));
                assert(m.dom().contains(addr));
                assert(m2.dom() =~= m.dom());
            },
            None => {},
        }
    }
}

/// A write succeeds when every byte it writes is mapped.
pub proof fn lemma_write_mem_some(m: Map<int, u8>, addr: int, n: nat, v: int)
    requires
        forall|i: int| 0 <= i < n ==> m.dom().contains(#[trigger] (addr + i)),
    ensures
        x64::write_mem(m, addr, n, v) is Some,
    decreases n,
{
    if n > 0 {
        assert(m.dom().contains(addr + 0));
        assert forall|i: int| 0 <= i < n - 1 implies m.dom().contains(#[trigger] (addr + 1 + i)) by {
            assert(m.dom().contains(addr + (i + 1)));
        }
        lemma_write_mem_some(m, addr + 1, (n - 1) as nat, v / 256);
    }
}

/// Inserting at an address outside the range read does not change the read.
pub proof fn lemma_read_mem_insert_other(m: Map<int, u8>, a: int, n: nat, b: int, x: u8)
    requires
        b < a || a + n <= b,
    ensures
        x64::read_mem(m.insert(b, x), a, n) == x64::read_mem(m, a, n),
    decreases n,
{
    if n > 0 {
        lemma_read_mem_insert_other(m, a + 1, (n - 1) as nat, b, x);
        assert(m.insert(b, x).dom().contains(a) == m.dom().contains(a));
        if m.dom().contains(a) {
            assert(m.insert(b, x)[a] == m[a]);
        }
    }
}

/// Two memories that agree on every byte of a range read the same there.
pub proof fn lemma_read_mem_congr(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: nat)
    requires
        forall|i: int|
            0 <= i < n ==> (m.dom().contains(#[trigger] (a + i)) == m2.dom().contains(a + i)) && (
            m.dom().contains(a + i) ==> m[a + i] == m2[a + i]),
    ensures
        x64::read_mem(m, a, n) == x64::read_mem(m2, a, n),
    decreases n,
{
    if n > 0 {
        assert forall|i: int| 0 <= i < n - 1 implies (m.dom().contains(#[trigger] (a + 1 + i))
            == m2.dom().contains(a + 1 + i)) && (m.dom().contains(a + 1 + i) ==> m[a + 1 + i]
            == m2[a + 1 + i]) by {
            assert(a + (i + 1) == a + 1 + i);
        }
        lemma_read_mem_congr(m, m2, a + 1, (n - 1) as nat);
        assert(a + 0 == a);
    }
}

/// Reading back what was just written: the `n` bytes at `addr` read as `v`,
/// for `v` below `2^(8n)`.
pub proof fn lemma_read_after_write_same(
    m: Map<int, u8>,
    addr: int,
    n: nat,
    v: int,
    m2: Map<int, u8>,
)
    requires
        x64::write_mem(m, addr, n, v) == Some(m2),
        0 <= v < vstd::arithmetic::power2::pow2(8 * n) as int,
    ensures
        x64::read_mem(m2, addr, n) == Some(v),
    decreases n,
{
    lemma_p2_consts();
    if n == 0 {
        vstd::arithmetic::power2::lemma2_to64();
        assert(v == 0);
    } else {
        match x64::write_mem(m, addr + 1, (n - 1) as nat, v / 256) {
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
                lemma_write_mem_frame(m, addr + 1, (n - 1) as nat, v / 256, m3);
                lemma_read_mem_insert_other(m3, addr + 1, (n - 1) as nat, addr, (v % 256) as u8);
                assert(m3.dom().contains(addr));
                assert(m2.dom().contains(addr));
                assert(m2[addr] == (v % 256) as u8);
                assert(v == v % 256 + 256 * (v / 256));
            },
            None => {},
        }
    }
}

/// A read of a range disjoint from a successful write sees the old bytes.
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
        x64::write_mem(m, addr, n, v) == Some(m2),
        b + k <= addr || addr + n <= b,
    ensures
        x64::read_mem(m2, b, k) == x64::read_mem(m, b, k),
{
    lemma_write_mem_frame(m, addr, n, v, m2);
    assert forall|i: int| 0 <= i < k implies (m.dom().contains(#[trigger] (b + i))
        == m2.dom().contains(b + i)) && (m.dom().contains(b + i) ==> m[b + i] == m2[b + i]) by {
        assert(m2.dom().contains(b + i) == m.dom().contains(b + i));
    }
    lemma_read_mem_congr(m, m2, b, k);
}

} // verus!
