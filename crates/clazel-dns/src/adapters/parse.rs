//! The executable adapter-buffer reader, proven to meet
//! [`super::contract`]. It follows [`super::spec`] function by function,
//! with the two list walks as loops.

use crate::spec::Addr;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `n`-octet little-endian field at `at`, `n` at most 8.
fn read_le(b: &[u8], at: usize, n: usize) -> (v: u64)
    requires
        at + n <= b.len(),
        n <= 8,
    ensures
        v as nat == super::spec::le_at(b@, at as nat, n as nat),
{
    // The octets are read from the last to the first: `acc` is the value
    // of the octets from `at + k` to `at + n`.
    let mut k: usize = n;
    let mut acc: u64 = 0;
    proof {
        assert(b@.subrange(at as int + n as int, at as int + n as int) =~= Seq::<u8>::empty());
    }
    while k > 0
        invariant
            k <= n,
            n <= 8,
            at + n <= b.len(),
            acc as nat == super::spec::le_value(b@.subrange(at as int + k as int, at as int + n as int)),
        decreases k,
    {
        // k > 0, so this does not saturate.
        k = k.saturating_sub(1);
        // at + k < b.len(), so this does not saturate.
        let byte = match b.get(at.saturating_add(k)) {
            Some(&c) => c,
            None => 0,
        };
        proof {
            let s = b@.subrange(at as int + k as int, at as int + n as int);
            let rest = b@.subrange(at as int + k as int + 1, at as int + n as int);
            assert(s.drop_first() =~= rest);
            assert(s[0] == b@[at as int + k as int]);
            super::lemmas::lemma_le_value_bound(rest);
            super::lemmas::lemma_pow256_up_to_8((n - k) as nat);
            assert(crate::lemmas::pow256((n - k) as nat) == 256 * crate::lemmas::pow256((n - k - 1) as nat));
            assert(acc as nat * 256 + 255 <= 0xFFFF_FFFF_FFFF_FFFF);
        }
        // acc * 256 + byte <= 2^64 - 1 (shown above): neither saturates.
        acc = acc.saturating_mul(256).saturating_add(byte as u64);
    }
    acc
}

/// The `n`-octet field at `pos` in network byte order, `n` at most 16.
fn read_be(b: &[u8], pos: usize, n: usize) -> (v: u128)
    requires
        pos + n <= b.len(),
        n <= 16,
    ensures
        v as nat == crate::spec::be_value(b@.subrange(pos as int, pos as int + n as int)),
{
    let mut k: usize = 0;
    let mut acc: u128 = 0;
    proof {
        assert(b@.subrange(pos as int, pos as int) =~= Seq::<u8>::empty());
    }
    while k < n
        invariant
            k <= n,
            n <= 16,
            pos + n <= b.len(),
            acc as nat == crate::spec::be_value(b@.subrange(pos as int, pos as int + k as int)),
        decreases n - k,
    {
        // pos + k < b.len(), so this does not saturate.
        let c = match b.get(pos.saturating_add(k)) {
            Some(&c) => c,
            None => 0,
        };
        proof {
            let s = b@.subrange(pos as int, pos as int + k as int + 1);
            let init = b@.subrange(pos as int, pos as int + k as int);
            assert(s.drop_last() =~= init);
            assert(s.last() == b@[pos as int + k as int]);
            crate::lemmas::lemma_be_value_bound(init);
            crate::lemmas::lemma_pow256_up_to_16(k as nat + 1);
            assert(crate::lemmas::pow256(k as nat + 1) == 256 * crate::lemmas::pow256(k as nat));
            assert(acc as nat * 256 + 255 <= 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF);
        }
        // acc * 256 + c <= 2^128 - 1 (shown above): neither saturates.
        acc = acc.saturating_mul(256).saturating_add(c as u128);
        k = k.saturating_add(1);
    }
    acc
}

/// The offset of the `need` octets that `p` points at, if they lie in `b`.
fn offset_of(b: &[u8], base: u64, p: u64, need: u64) -> (r: Option<usize>)
    ensures
        match r {
            Some(o) => super::spec::offset_of(b@, base as nat, p as nat, need as nat) == Some(o as nat),
            None => super::spec::offset_of(b@, base as nat, p as nat, need as nat) is None,
        },
{
    if p == 0 || p < base {
        return None;
    }
    // base <= p: this does not saturate.
    let off = p.saturating_sub(base);
    let len = b.len() as u64;
    if need > len {
        return None;
    }
    // need <= len: this does not saturate.
    if off > len.saturating_sub(need) {
        return None;
    }
    // off <= len, which is a `usize`.
    Some(off as usize)
}

/// [`super::spec::socket_address`].
fn socket_address(b: &[u8], base: u64, p: u64, len: u64) -> (r: Option<Addr>)
    ensures
        r == super::spec::socket_address(b@, base as nat, p as nat, len as nat),
{
    let o = offset_of(b, base, p, len)?;
    // o + len <= b.len(), and each read below is within the first `len`
    // octets, so no addition saturates.
    if len >= 16 && read_le(b, o, 2) == 2 {
        let v = read_be(b, o.saturating_add(4), 4);
        proof {
            assert(b@.subrange(o as int + 4, o as int + 4 + 4) =~= b@.subrange((o + super::spec::sin_addr_at()) as int, (o + super::spec::sin_addr_at() + 4) as int));
        }
        Some(Addr::V4(v as u32))
    } else if len >= 28 && read_le(b, o, 2) == 23 {
        let first = match b.get(o.saturating_add(8)) {
            Some(&c) => c,
            None => 0,
        };
        let second = match b.get(o.saturating_add(9)) {
            Some(&c) => c,
            None => 0,
        };
        let v = read_be(b, o.saturating_add(8), 16);
        proof {
            let a = b@.subrange((o + super::spec::sin6_addr_at()) as int, (o + super::spec::sin6_addr_at() + 16) as int);
            assert(a[0] == first);
            assert(a[1] == second);
            assert(b@.subrange(o as int + 8, o as int + 8 + 16) =~= a);
        }
        if first == 0xFE && second >= 0x80 {
            None
        } else {
            Some(Addr::V6(v))
        }
    } else {
        None
    }
}

/// [`super::spec::servers_from`], appending to `acc`. It recurses once per
/// server record, each at a higher offset than the last, so the depth is
/// below `b.len() / 28`.
fn servers_from(b: &[u8], base: u64, p: u64, after: usize, acc: &mut Vec<Addr>)
    requires
        after <= b.len(),
    ensures
        final(acc)@ == super::spec::servers_from(b@, base as nat, p as nat, after as nat, old(acc)@),
    decreases b.len() - after,
{
    let o = match offset_of(b, base, p, 28) {
        None => return,
        Some(o) => o,
    };
    if o <= after {
        // Not forward: the list ends.
        return;
    }
    // o + 28 <= b.len(): no addition below saturates.
    let sockaddr = read_le(b, o.saturating_add(16), 8);
    let sockaddr_len = read_le(b, o.saturating_add(24), 4);
    if let Some(a) = socket_address(b, base, sockaddr, sockaddr_len) {
        acc.push(a);
    }
    let next = read_le(b, o.saturating_add(8), 8);
    servers_from(b, base, next, o, acc);
}

/// The DNS servers of the adapters that are up, in the buffer `b` that
/// `GetAdaptersAddresses` filled at address `base`, in list order.
pub fn dns_servers(b: &[u8], base: u64) -> (out: Vec<Addr>)
    ensures
        super::contract::dns_servers_ensures(b@, base as nat, out@),
{
    let mut out: Vec<Addr> = Vec::new();
    let mut at: usize = 0;
    proof {
        assert(out@ =~= Seq::<Addr>::empty());
    }
    loop
        invariant
            at <= b.len(),
            super::spec::adapters_from(b@, base as nat, at as nat, out@) == super::spec::dns_servers(b@, base as nat),
        decreases b.len() - at,
    {
        // b.len() >= 108 when the subtraction runs: it does not saturate.
        if b.len() < 108 || at > b.len().saturating_sub(108) {
            // No whole adapter here.
            return out;
        }
        // at + 108 <= b.len(): no addition below saturates.
        if read_le(b, at.saturating_add(104), 4) == 1 {
            let first = read_le(b, at.saturating_add(48), 8);
            servers_from(b, base, first, at, &mut out);
        }
        let next = read_le(b, at.saturating_add(8), 8);
        match offset_of(b, base, next, 108) {
            None => return out,
            Some(o) => {
                if o <= at {
                    // Not forward: the list ends.
                    return out;
                }
                at = o;
            },
        }
    }
}

} // verus!
