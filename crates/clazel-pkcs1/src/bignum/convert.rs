//! Octet strings to limbs: RFC 8017 §4.2 OS2IP, computed by Horner's rule
//! (shift the limbs left by one octet, add the next octet), proven to meet
//! [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One step of `shl8_add`'s invariant.
proof fn lemma_shl8_step(
    vo: nat,
    p: nat,
    new: nat,
    c_new: nat,
    x: nat,
    c_old: nat,
    va: nat,
    byte: nat,
)
    requires
        x * 256 + c_old == new + c_new * base(),
        vo + c_old * p == va * 256 + byte,
    ensures
        (vo + new * p) + c_new * (p * base()) == (va + x * p) * 256 + byte,
{
    assert(c_new * (p * base()) + new * p == (x * 256 + c_old) * p) by (nonlinear_arith)
        requires
            x * 256 + c_old == new + c_new * base(),
    ;
    assert((x * 256 + c_old) * p == x * p * 256 + c_old * p) by (nonlinear_arith);
    assert((va + x * p) * 256 == va * 256 + x * p * 256) by (nonlinear_arith);
}

/// `a * 256 + byte`, in as many limbs as `a`, when that fits.
pub fn shl8_add(a: &[u64], byte: u8) -> (r: Vec<u64>)
    requires
        value(a@) * 256 + (byte as nat) < limb_pow(a@.len()),
    ensures
        r.len() == a.len(),
        value(r@) == value(a@) * 256 + byte as nat,
{
    let mut out: Vec<u64> = Vec::with_capacity(a.len());
    let mut carry: u64 = byte as u64;
    let mut i: usize = 0;
    proof {
        super::lemmas::lemma_value_empty();
        assert(a@.take(0) =~= Seq::<u64>::empty());
        assert(limb_pow(0) == 1);
    }
    while i < a.len()
        invariant
            i <= a.len(),
            out.len() == i,
            carry < 256,
            value(out@) + (carry as nat) * limb_pow(i as nat) == value(a@.take(i as int)) * 256
                + byte as nat,
        decreases a.len() - i,
    {
        let x = a.get(i).cloned().unwrap_or(0);
        // x = hi * 2^56 + lo; the shifted limb is lo * 256 + carry and the
        // new carry is hi.
        let lo = x % 0x0100_0000_0000_0000u64;
        let hi = x / 0x0100_0000_0000_0000u64;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 0x0100_0000_0000_0000);
            assert(hi < 256) by {
                assert(x <= 0xFFFF_FFFF_FFFF_FFFFu64);
            }
            assert(lo < 0x0100_0000_0000_0000u64);
        }
        // Never saturates: lo < 2^56, so lo * 256 + carry < 2^64.
        let limb = lo.saturating_mul(256).saturating_add(carry);
        proof {
            super::lemmas::lemma_value_push(out@, limb);
            super::lemmas::lemma_value_take_succ(a@, i as int);
            assert(x as nat * 256 + carry as nat == limb as nat + (hi as nat) * base());
            lemma_shl8_step(
                value(out@),
                limb_pow(i as nat),
                limb as nat,
                hi as nat,
                x as nat,
                carry as nat,
                value(a@.take(i as int)),
                byte as nat,
            );
            super::lemmas::lemma_limb_pow_succ(i as nat);
        }
        out.push(limb);
        carry = hi;
        // Never wraps: i < a.len().
        i = i.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_take_all(a@);
        super::lemmas::lemma_limb_pow_pos(a@.len());
        // value(out) + carry * base^len = value(a) 256 + byte < base^len,
        // so carry is zero.
        let pl = limb_pow(a@.len());
        assert(carry == 0) by (nonlinear_arith)
            requires
                value(out@) + (carry as nat) * pl == value(a@) * 256 + byte as nat,
                value(a@) * 256 + (byte as nat) < pl,
                pl > 0,
        ;
    }
    out
}

/// OS2IP of `bytes[start..]`, in `limbs` limbs (§4.2).
pub fn from_be_bytes(bytes: &[u8], start: usize, limbs: usize) -> (r: Vec<u64>)
    requires
        super::contract::from_be_bytes_requires(bytes@, start as nat, limbs as nat),
    ensures
        super::contract::from_be_bytes_ensures(bytes@, start as nat, limbs as nat, r@),
{
    let mut acc: Vec<u64> = vec![0u64;limbs];
    let mut i: usize = start;
    proof {
        assert(forall|k: int| 0 <= k < acc@.len() ==> acc@[k] == 0u64);
        super::lemmas::lemma_value_zeros(acc@);
        assert(bytes@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    }
    while i < bytes.len()
        invariant
            start <= i <= bytes.len(),
            bytes.len() - start <= 8 * limbs,
            acc.len() == limbs,
            value(acc@) == crate::spec::os2ip(bytes@.subrange(start as int, i as int)),
        decreases bytes.len() - i,
    {
        let b = bytes.get(i).cloned().unwrap_or(0);
        proof {
            let pre = bytes@.subrange(start as int, i as int);
            crate::lemmas::lemma_os2ip_bound(pre);
            crate::lemmas::lemma_os2ip_push(pre, b);
            assert(bytes@.subrange(start as int, i as int + 1) =~= pre.push(b));
            // os2ip(pre) < 256^k, so os2ip(pre) * 256 + b < 256^(k + 1) <=
            // 256^(8 limbs) = base^limbs.
            let k = pre.len();
            crate::lemmas::lemma_pow256_succ(k);
            crate::lemmas::lemma_pow256_monotone(k + 1, 8 * limbs as nat);
            crate::lemmas::lemma_pow256_limb(limbs as nat);
            let pk = crate::spec::pow256(k);
            assert(crate::spec::os2ip(pre) * 256 + (b as nat) < 256 * pk) by (nonlinear_arith)
                requires
                    crate::spec::os2ip(pre) < pk,
                    b < 256,
            ;
        }
        acc = shl8_add(acc.as_slice(), b);
        // Never wraps: i < bytes.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(bytes@.subrange(start as int, bytes@.len() as int) =~= bytes@.skip(start as int));
    }
    acc
}

} // verus!
