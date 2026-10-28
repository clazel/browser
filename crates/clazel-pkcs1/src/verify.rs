//! The executable RSASSA-PKCS1-V1_5-VERIFY (RFC 8017 §8.2.2) and
//! EMSA-PKCS1-v1_5-ENCODE (§9.2), proven to meet [`super::contract`].
//!
//! Public-key verification only: every input is public, so there is no
//! constant-time requirement and none is claimed. The step comments live
//! in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::bignum::arith::lt;
use crate::bignum::convert::from_be_bytes;
use crate::bignum::modular::mod_exp;

verus! {

/// `hLen` as an executable number.
fn hash_len_exec(h: HashId) -> (r: usize)
    ensures
        r as nat == hash_len(h),
{
    match h {
        HashId::Sha256 => 32,
        HashId::Sha384 => 48,
        HashId::Sha512 => 64,
    }
}

/// Appends §9.2 Note 1's `DigestInfo` prefix for `h`.
fn push_prefix(h: HashId, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + digest_info_prefix(h),
{
    let ghost start = out@;
    match h {
        HashId::Sha256 => {
            out.push(0x30);
            out.push(0x31);
            out.push(0x30);
            out.push(0x0d);
            out.push(0x06);
            out.push(0x09);
            out.push(0x60);
            out.push(0x86);
            out.push(0x48);
            out.push(0x01);
            out.push(0x65);
            out.push(0x03);
            out.push(0x04);
            out.push(0x02);
            out.push(0x01);
            out.push(0x05);
            out.push(0x00);
            out.push(0x04);
            out.push(0x20);
        },
        HashId::Sha384 => {
            out.push(0x30);
            out.push(0x41);
            out.push(0x30);
            out.push(0x0d);
            out.push(0x06);
            out.push(0x09);
            out.push(0x60);
            out.push(0x86);
            out.push(0x48);
            out.push(0x01);
            out.push(0x65);
            out.push(0x03);
            out.push(0x04);
            out.push(0x02);
            out.push(0x02);
            out.push(0x05);
            out.push(0x00);
            out.push(0x04);
            out.push(0x30);
        },
        HashId::Sha512 => {
            out.push(0x30);
            out.push(0x51);
            out.push(0x30);
            out.push(0x0d);
            out.push(0x06);
            out.push(0x09);
            out.push(0x60);
            out.push(0x86);
            out.push(0x48);
            out.push(0x01);
            out.push(0x65);
            out.push(0x03);
            out.push(0x04);
            out.push(0x02);
            out.push(0x03);
            out.push(0x05);
            out.push(0x00);
            out.push(0x04);
            out.push(0x40);
        },
    }
    assert(out@ =~= start + digest_info_prefix(h));
}

/// The view of an optional octet string.
pub open spec fn opt_view(r: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match r {
        Some(v) => Some(v@),
        None => None,
    }
}

/// §9.2 EMSA-PKCS1-v1_5-ENCODE, with the digest as input.
pub fn encode_message(digest: &[u8], em_len: usize, h: HashId) -> (r: Option<Vec<u8>>)
    ensures
        super::contract::encode_ensures(digest@, em_len as nat, h, opt_view(r)),
        r is Some ==> r->Some_0@.len() == em_len,
{
    // 1.
    let h_len = hash_len_exec(h);
    if digest.len() != h_len {
        return None;
    }
    // 2. tLen = 19 + hLen: Note 1's prefix is 19 octets.
    let t_len = h_len.saturating_add(19);
    // 3.
    if em_len < t_len.saturating_add(11) {
        return None;
    }
    // 4. PS is em_len - t_len - 3 >= 8 octets of 0xff.
    let ps_len = em_len.saturating_sub(t_len).saturating_sub(3);
    // 5. EM = 0x00 || 0x01 || PS || 0x00 || T.
    let mut em: Vec<u8> = Vec::with_capacity(em_len);
    em.push(0x00);
    em.push(0x01);
    let mut i: usize = 0;
    while i < ps_len
        invariant
            i <= ps_len,
            em@ =~= seq![0x00u8, 0x01u8] + Seq::new(i as nat, |j: int| 0xffu8),
        decreases ps_len - i,
    {
        proof {
            assert(Seq::new((i + 1) as nat, |j: int| 0xffu8) =~= Seq::new(i as nat, |j: int| 0xffu8).push(
                0xffu8,
            ));
        }
        em.push(0xff);
        // Never wraps: i < ps_len.
        i = i.saturating_add(1);
    }
    em.push(0x00);
    push_prefix(h, &mut em);
    em.extend_from_slice(digest);
    proof {
        let t = digest_info_prefix(h) + digest@;
        let ps = Seq::new((em_len - t.len() - 3) as nat, |j: int| 0xffu8);
        assert(em@ =~= seq![0x00u8, 0x01u8] + ps + seq![0x00u8] + t);
    }
    Some(em)
}

/// RSASSA-PKCS1-V1_5-VERIFY (§8.2.2). `n` is the modulus as a big-endian
/// octet string (leading zero octets are allowed and ignored), `e` the
/// public exponent, `digest` the hash of the message (the length of
/// `hash`'s output) and `signature` the octet string S. `true` is "valid
/// signature".
pub fn verify(n: &[u8], e: u64, digest: &[u8], hash: HashId, signature: &[u8]) -> (r: bool)
    ensures
        super::contract::verify_ensures(n@, e, digest@, hash, signature@, r),
{
    // Domain restriction: 3 <= e (e < 2^64 holds for a u64).
    if e < 3 {
        return false;
    }
    // k, the length in octets of the modulus: strip leading zero octets.
    let mut z: usize = 0;
    while z < n.len() && n.get(z).cloned().unwrap_or(1) == 0
        invariant
            z <= n.len(),
            forall|j: int| 0 <= j < z ==> n@[j] == 0,
        decreases n.len() - z,
    {
        // Never wraps: z < n.len().
        z = z.saturating_add(1);
    }
    if z >= n.len() {
        // n = 0: out of range.
        proof {
            crate::lemmas::lemma_os2ip_leading_zeros(n@, n@.len());
            assert(n@.skip(n@.len() as int) =~= Seq::<u8>::empty());
            crate::lemmas::lemma_two_to_pos(2047);
        }
        return false;
    }
    let k = n.len().saturating_sub(z);
    let b0 = n.get(z).cloned().unwrap_or(0);
    proof {
        crate::lemmas::lemma_os2ip_leading_zeros(n@, z as nat);
        crate::lemmas::lemma_modulus_range(n@.skip(z as int));
        assert(n@.skip(z as int)[0] == n@[z as int]);
    }
    // Domain restriction: 2048 to 8192 bits.
    let in_range = (k > 256 && k <= 1024) || (k == 256 && b0 >= 0x80);
    if !in_range {
        return false;
    }
    // 1. Length checking.
    if signature.len() != k {
        return false;
    }
    // 3. EMSA-PKCS1-v1_5 encoding (done first: the result does not depend
    // on the order of steps 2 and 3).
    let em = match encode_message(digest, k, hash) {
        Some(em) => em,
        None => {
            return false;
        },
    };
    // At most 1024 octets: no overflow.
    let limbs = k.saturating_add(7) / 8;
    // 2.(a) s = OS2IP(S), and the modulus as a number.
    let n_l = from_be_bytes(n, z, limbs);
    let s_l = from_be_bytes(signature, 0, limbs);
    proof {
        assert(signature@.skip(0) =~= signature@);
    }
    // 2.(b), 2.(c) RSAVP1 step 1: s must be below n.
    if !lt(s_l.as_slice(), n_l.as_slice()) {
        return false;
    }
    proof {
        crate::lemmas::lemma_modulus_gt_one(crate::spec::os2ip(n@));
    }
    // RSAVP1 step 2: m = s^e mod n.
    let m_l = mod_exp(s_l.as_slice(), e, n_l.as_slice());
    // 2.(d) and 4. EM' = I2OSP(m, k) equals EM exactly when m = OS2IP(EM).
    let em_l = from_be_bytes(em.as_slice(), 0, limbs);
    proof {
        assert(em@.skip(0) =~= em@);
    }
    proof {
        crate::lemmas::lemma_verify_final(
            crate::spec::os2ip(n@),
            e as nat,
            digest@,
            hash,
            signature@,
            em@,
        );
    }
    let ge = !lt(m_l.as_slice(), em_l.as_slice());
    let le = !lt(em_l.as_slice(), m_l.as_slice());
    ge && le
}

} // verus!
