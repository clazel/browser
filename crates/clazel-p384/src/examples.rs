//! Known answers, evaluated: small cases of the spec's functions whose
//! results were worked out independently of the spec (with a script that
//! re-implements the same rules in Python, see the commit notes) and are
//! proven here by evaluating the spec (`by (compute_only)`). They are facts
//! about the spec itself, evidence that the transcription computes what the
//! standards define, and the theorems the mutation certificates in
//! `mutations.json` will contradict.
//!
//! Most of them are on [`toy`], a 7-bit curve small enough for a whole
//! verification to be evaluated. On [`p384`] only what the evaluator can do
//! in reasonable time is here: the constants' consequences, a point
//! doubling, public key decoding, and verifications whose scalars `u` and
//! `v` are small, chosen first (a signature is built backwards from `u`, `v`
//! and a key, so that step 6 needs a handful of group operations and not
//! about 1,150).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `x` as `len` big-endian octets (SEC 1 §2.3.7 Integer-to-Octet-String; the
/// caller ensures `x < 256^len`, and the examples check `os2ip` of the
/// result).
pub open spec fn ex_octets(x: nat, len: nat) -> Seq<u8> {
    Seq::new(len, |i: int| ((x / two_to(8 * (len - 1 - i) as nat)) % 256) as u8)
}

/// The ECPoint `04 || X || Y` of the affine point (x, y) with `len` octets
/// per coordinate.
pub open spec fn ex_ecpoint(x: nat, y: nat, len: nat) -> Seq<u8> {
    seq![0x04u8] + ex_octets(x, len) + ex_octets(y, len)
}

/// The base point of [`toy`], (1, 31).
pub open spec fn toy_g() -> Point {
    Point::Affine { x: 1, y: 31 }
}

/// The toy public key Q = [23]G = (44, 39) as an ECPoint.
pub open spec fn toy_q() -> Seq<u8> {
    seq![0x04u8, 44u8, 39u8]
}


/// Conversions: SEC 1 §2.3.8, §2.3.2, FIPS 186-5 B.2.1, `⌈log2 n⌉`.
pub proof fn lemma_conversion_examples()
    ensures
        os2ip(seq![1u8, 2u8]) == 258nat,
        os2ip(seq![0x12u8, 0x34u8, 0x56u8]) == 0x123456nat,
        os2ip(Seq::<u8>::empty()) == 0nat,
        os2ip(ex_octets(0x0102nat, 2nat)) == 0x0102nat,
        octets_to_bits(seq![0xB5u8]) == seq![true, false, true, true, false, true, false, true],
        octets_to_bits(Seq::<u8>::empty()) == Seq::<bool>::empty(),
        bits_to_int(seq![true, false, true]) == 5nat,
        bits_to_int(Seq::<bool>::empty()) == 0nat,
        ceil_log2(1nat) == 0nat,
        ceil_log2(2nat) == 1nat,
        ceil_log2(3nat) == 2nat,
        ceil_log2(4nat) == 2nat,
        ceil_log2(5nat) == 3nat,
        ceil_log2(64nat) == 6nat,
        ceil_log2(65nat) == 7nat,
        ceil_log2(toy().n) == 7nat,
{
    assert(os2ip(seq![1u8, 2u8]) == 258nat) by (compute_only);
    assert(os2ip(seq![0x12u8, 0x34u8, 0x56u8]) == 0x123456nat) by (compute_only);
    assert(os2ip(Seq::<u8>::empty()) == 0nat) by (compute_only);
    assert(os2ip(ex_octets(0x0102nat, 2nat)) == 0x0102nat) by (compute_only);
    assert(octets_to_bits(seq![0xB5u8]) == seq![true, false, true, true, false, true, false, true])
        by (compute_only);
    assert(octets_to_bits(Seq::<u8>::empty()) == Seq::<bool>::empty()) by (compute_only);
    assert(bits_to_int(seq![true, false, true]) == 5nat) by (compute_only);
    assert(bits_to_int(Seq::<bool>::empty()) == 0nat) by (compute_only);
    assert(ceil_log2(1nat) == 0nat) by (compute_only);
    assert(ceil_log2(2nat) == 1nat) by (compute_only);
    assert(ceil_log2(3nat) == 2nat) by (compute_only);
    assert(ceil_log2(4nat) == 2nat) by (compute_only);
    assert(ceil_log2(5nat) == 3nat) by (compute_only);
    assert(ceil_log2(64nat) == 6nat) by (compute_only);
    assert(ceil_log2(65nat) == 7nat) by (compute_only);
    assert(ceil_log2(toy().n) == 7nat) by (compute_only);
}


/// Step 3 on [`toy`] (n has 7 bits, so a digest is cut to its leftmost 7
/// bits, not to whole octets) and on [`p384`] (a 48-octet digest is kept
/// whole, a 64-octet one is cut to its leftmost 384 bits, a shorter one is
/// kept whole). `0xB5 = 1011 0101`, whose leftmost 7 bits `1011010` are 90.
pub proof fn lemma_derive_e_examples()
    ensures
        derive_e(toy(), seq![0xB5u8]) == 90nat,
        derive_e(toy(), seq![0xB4u8]) == 90nat,
        derive_e(toy(), seq![0xB5u8, 0x12u8]) == 90nat,
        derive_e(toy(), seq![0xB4u8, 0x00u8]) == 90nat,
        derive_e(toy(), seq![0xB6u8]) == 91nat,
        derive_e(toy(), seq![0x01u8]) == 0nat,
        derive_e(toy(), seq![0x02u8]) == 1nat,
        derive_e(toy(), seq![0x7Fu8]) == 63nat,
        derive_e(toy(), seq![0xFFu8, 0xFFu8]) == 127nat,
        derive_e(toy(), Seq::<u8>::empty()) == 0nat,
        derive_e(p384(), ex_octets(0x0123456789abcdefnat, 48nat)) == 0x0123456789abcdefnat,
        derive_e(p384(), ex_octets(0x0123456789abcdefnat, 32nat)) == 0x0123456789abcdefnat,
        derive_e(p384(), Seq::<u8>::empty()) == 0nat,
        derive_e(p384(), ex_octets(two_to(500nat) + 12345nat, 64nat)) == two_to(372nat),
        derive_e(p384(), ex_octets(two_to(500nat) + 12345nat, 64nat) + seq![0xFFu8])
            == two_to(372nat),
{
    assert(derive_e(toy(), seq![0xB5u8]) == 90nat) by (compute_only);
    assert(derive_e(toy(), seq![0xB4u8]) == 90nat) by (compute_only);
    assert(derive_e(toy(), seq![0xB5u8, 0x12u8]) == 90nat) by (compute_only);
    assert(derive_e(toy(), seq![0xB4u8, 0x00u8]) == 90nat) by (compute_only);
    assert(derive_e(toy(), seq![0xB6u8]) == 91nat) by (compute_only);
    assert(derive_e(toy(), seq![0x01u8]) == 0nat) by (compute_only);
    assert(derive_e(toy(), seq![0x02u8]) == 1nat) by (compute_only);
    assert(derive_e(toy(), seq![0x7Fu8]) == 63nat) by (compute_only);
    assert(derive_e(toy(), seq![0xFFu8, 0xFFu8]) == 127nat) by (compute_only);
    assert(derive_e(toy(), Seq::<u8>::empty()) == 0nat) by (compute_only);
    assert(derive_e(p384(), ex_octets(0x0123456789abcdefnat, 48nat)) == 0x0123456789abcdefnat)
        by (compute_only);
    assert(derive_e(p384(), ex_octets(0x0123456789abcdefnat, 32nat)) == 0x0123456789abcdefnat)
        by (compute_only);
    assert(derive_e(p384(), Seq::<u8>::empty()) == 0nat) by (compute_only);
    assert(derive_e(p384(), ex_octets(two_to(500nat) + 12345nat, 64nat)) == two_to(372nat))
        by (compute_only);
    assert(derive_e(p384(), ex_octets(two_to(500nat) + 12345nat, 64nat) + seq![0xFFu8])
        == two_to(372nat)) by (compute_only);
}

/// The inverse (modelling choice 3): [`inv`] and the reference routine
/// [`b1_inverse`] (FIPS 186-5 B.1) agree, and both refuse 0 and the modulus.
/// `5 · 27 = 135 = 2 · 67 + 1`, `2 · 42 = 84 = 83 + 1`.
pub proof fn lemma_inverse_examples()
    ensures
        inv(67nat, 5nat) == Some(27nat),
        b1_inverse(5nat, 67nat) == Some(27nat),
        inv(83nat, 2nat) == Some(42nat),
        b1_inverse(2nat, 83nat) == Some(42nat),
        inv(83nat, 1nat) == Some(1nat),
        b1_inverse(1nat, 83nat) == Some(1nat),
        inv(83nat, 82nat) == Some(82nat),
        b1_inverse(82nat, 83nat) == Some(82nat),
        inv(83nat, 0nat) is None,
        inv(83nat, 83nat) is None,
        b1_inverse(0nat, 83nat) is None,
        b1_inverse(83nat, 83nat) is None,
        b1_inverse(1nat, 1nat) is None,
        // A composite modulus: 6 has no inverse mod 9, and neither routine
        // finds one (Fermat's check fails; B.1 step 8).
        b1_inverse(6nat, 9nat) is None,
        inv(9nat, 6nat) is None,
        inv(p384().p, 2nat) == Some((p384().p + 1) / 2),
        b1_inverse(2nat, p384().p) == Some((p384().p + 1) / 2),
        inv(p384().n, 2nat) == Some((p384().n + 1) / 2),
        b1_inverse(2nat, p384().n) == Some((p384().n + 1) / 2),
{
    assert(inv(67nat, 5nat) == Some(27nat)) by (compute_only);
    assert(b1_inverse(5nat, 67nat) == Some(27nat)) by (compute_only);
    assert(inv(83nat, 2nat) == Some(42nat)) by (compute_only);
    assert(b1_inverse(2nat, 83nat) == Some(42nat)) by (compute_only);
    assert(inv(83nat, 1nat) == Some(1nat)) by (compute_only);
    assert(b1_inverse(1nat, 83nat) == Some(1nat)) by (compute_only);
    assert(inv(83nat, 82nat) == Some(82nat)) by (compute_only);
    assert(b1_inverse(82nat, 83nat) == Some(82nat)) by (compute_only);
    assert(inv(83nat, 0nat) is None) by (compute_only);
    assert(inv(83nat, 83nat) is None) by (compute_only);
    assert(b1_inverse(0nat, 83nat) is None) by (compute_only);
    assert(b1_inverse(83nat, 83nat) is None) by (compute_only);
    assert(b1_inverse(1nat, 1nat) is None) by (compute_only);
    assert(b1_inverse(6nat, 9nat) is None) by (compute_only);
    assert(inv(9nat, 6nat) is None) by (compute_only);
    assert(inv(p384().p, 2nat) == Some((p384().p + 1) / 2)) by (compute_only);
    assert(b1_inverse(2nat, p384().p) == Some((p384().p + 1) / 2)) by (compute_only);
    assert(inv(p384().n, 2nat) == Some((p384().n + 1) / 2)) by (compute_only);
    assert(b1_inverse(2nat, p384().n) == Some((p384().n + 1) / 2)) by (compute_only);
}


/// The group law and scalar multiplication on [`toy`], and the facts a
/// reader can check by hand: `2G`, `3G` from rules 5 and 4, `G + (-G) = O`
/// (rule 3), the identity rules (1 and 2), `[0]G = O`, `[66]G = -G` and
/// `[67]G = O` (so G has order n), and `[23]G = Q`. The multiples were
/// computed with an independent script.
pub proof fn lemma_toy_group_examples()
    ensures
        ({
            &&& base_point(toy()) == toy_g()
            // 5. doubling.
            &&& ec_add(toy(), toy_g(), toy_g()) == Some(Point::Affine { x: 81nat, y: 52nat })
            // 4. different x-coordinates.
            &&& ec_add(toy(), Point::Affine { x: 81nat, y: 52nat }, toy_g())
                == Some(Point::Affine { x: 50nat, y: 63nat })
            &&& ec_add(toy(), toy_g(), Point::Affine { x: 81nat, y: 52nat })
                == Some(Point::Affine { x: 50nat, y: 63nat })
            // 3. P + (-P) = O.
            &&& ec_add(toy(), toy_g(), Point::Affine { x: 1nat, y: 52nat }) == Some(Point::Infinity)
            &&& ec_add(toy(), Point::Affine { x: 1nat, y: 52nat }, toy_g()) == Some(Point::Infinity)
            // 1. and 2.
            &&& ec_add(toy(), Point::Infinity, Point::Infinity) == Some(Point::Infinity)
            &&& ec_add(toy(), Point::Infinity, toy_g()) == Some(toy_g())
            &&& ec_add(toy(), toy_g(), Point::Infinity) == Some(toy_g())
            // [k]G.
            &&& scalar_mul(toy(), 0nat, toy_g()) == Some(Point::Infinity)
            &&& scalar_mul(toy(), 1nat, toy_g()) == Some(toy_g())
            &&& scalar_mul(toy(), 2nat, toy_g()) == Some(Point::Affine { x: 81nat, y: 52nat })
            &&& scalar_mul(toy(), 3nat, toy_g()) == Some(Point::Affine { x: 50nat, y: 63nat })
            &&& scalar_mul(toy(), 4nat, toy_g()) == Some(Point::Affine { x: 55nat, y: 54nat })
            &&& scalar_mul(toy(), 5nat, toy_g()) == Some(Point::Affine { x: 60nat, y: 53nat })
            &&& scalar_mul(toy(), 23nat, toy_g()) == Some(Point::Affine { x: 44nat, y: 39nat })
            &&& scalar_mul(toy(), 66nat, toy_g()) == Some(Point::Affine { x: 1nat, y: 52nat })
            &&& scalar_mul(toy(), 67nat, toy_g()) == Some(Point::Infinity)
            &&& scalar_mul(toy(), 68nat, toy_g()) == Some(toy_g())
            &&& scalar_mul(toy(), 5nat, Point::Infinity) == Some(Point::Infinity)
        }),
{
    assert(base_point(toy()) == toy_g()) by (compute_only);
    assert(ec_add(toy(), toy_g(), toy_g()) == Some(Point::Affine { x: 81nat, y: 52nat })) by (compute_only);
    assert(ec_add(toy(), Point::Affine { x: 81nat, y: 52nat }, toy_g())
        == Some(Point::Affine { x: 50nat, y: 63nat })) by (compute_only);
    assert(ec_add(toy(), toy_g(), Point::Affine { x: 81nat, y: 52nat })
        == Some(Point::Affine { x: 50nat, y: 63nat })) by (compute_only);
    assert(ec_add(toy(), toy_g(), Point::Affine { x: 1nat, y: 52nat }) == Some(Point::Infinity)) by (compute_only);
    assert(ec_add(toy(), Point::Affine { x: 1nat, y: 52nat }, toy_g()) == Some(Point::Infinity)) by (compute_only);
    assert(ec_add(toy(), Point::Infinity, Point::Infinity) == Some(Point::Infinity)) by (compute_only);
    assert(ec_add(toy(), Point::Infinity, toy_g()) == Some(toy_g())) by (compute_only);
    assert(ec_add(toy(), toy_g(), Point::Infinity) == Some(toy_g())) by (compute_only);
    assert(scalar_mul(toy(), 0nat, toy_g()) == Some(Point::Infinity)) by (compute_only);
    assert(scalar_mul(toy(), 1nat, toy_g()) == Some(toy_g())) by (compute_only);
    assert(scalar_mul(toy(), 2nat, toy_g()) == Some(Point::Affine { x: 81nat, y: 52nat }))
        by (compute_only);
    assert(scalar_mul(toy(), 3nat, toy_g()) == Some(Point::Affine { x: 50nat, y: 63nat }))
        by (compute_only);
    assert(scalar_mul(toy(), 4nat, toy_g()) == Some(Point::Affine { x: 55nat, y: 54nat }))
        by (compute_only);
    assert(scalar_mul(toy(), 5nat, toy_g()) == Some(Point::Affine { x: 60nat, y: 53nat }))
        by (compute_only);
    assert(scalar_mul(toy(), 23nat, toy_g()) == Some(Point::Affine { x: 44nat, y: 39nat }))
        by (compute_only);
    assert(scalar_mul(toy(), 66nat, toy_g()) == Some(Point::Affine { x: 1nat, y: 52nat }))
        by (compute_only);
    assert(scalar_mul(toy(), 67nat, toy_g()) == Some(Point::Infinity)) by (compute_only);
    assert(scalar_mul(toy(), 68nat, toy_g()) == Some(toy_g())) by (compute_only);
    assert(scalar_mul(toy(), 5nat, Point::Infinity) == Some(Point::Infinity)) by (compute_only);
}

/// The group law on [`p384`]: G satisfies the curve equation and is a valid
/// public key, and `2G` and `3G` (computed with an independent script, also
/// checked there against `[n]G = O`).
pub proof fn lemma_p384_group_examples()
    ensures
        satisfies_equation(p384(), p384().gx, p384().gy),
        public_key_valid(p384(), base_point(p384())),
        ec_add(p384(), base_point(p384()), base_point(p384())) == Some(
            Point::Affine {
                x: 0x8d999057ba3d2d969260045c55b97f089025959a6f434d651d207d19fb96e9e4fe0e86ebe0e64f85b96a9c75295df61nat,
                y: 0x8e80f1fa5b1b3cedb7bfe8dffd6dba74b275d875bc6cc43e904e505f256ab4255ffd43e94d39e22d61501e700a940e80nat,
            },
        ),
        scalar_mul(p384(), 3nat, base_point(p384())) == Some(
            Point::Affine {
                x: 0x077a41d4606ffa1464793c7e5fdc7d98cb9d3910202dcd06bea4f240d3566da6b408bbae5026580d02d7e5c70500c831nat,
                y: 0xc995f7ca0b0c42837d0bbe9602a9fc998520b41c85115aa5f7684c0edc111eacc24abd6be4b5d298b65f28600a2f1df1nat,
            },
        ),
{
    assert(satisfies_equation(p384(), p384().gx, p384().gy)) by (compute_only);
    assert(public_key_valid(p384(), base_point(p384()))) by (compute_only);
    assert(ec_add(p384(), base_point(p384()), base_point(p384())) == Some(
        Point::Affine {
            x: 0x8d999057ba3d2d969260045c55b97f089025959a6f434d651d207d19fb96e9e4fe0e86ebe0e64f85b96a9c75295df61nat,
            y: 0x8e80f1fa5b1b3cedb7bfe8dffd6dba74b275d875bc6cc43e904e505f256ab4255ffd43e94d39e22d61501e700a940e80nat,
        },
    )) by (compute_only);
    assert(scalar_mul(p384(), 3nat, base_point(p384())) == Some(
        Point::Affine {
            x: 0x077a41d4606ffa1464793c7e5fdc7d98cb9d3910202dcd06bea4f240d3566da6b408bbae5026580d02d7e5c70500c831nat,
            y: 0xc995f7ca0b0c42837d0bbe9602a9fc998520b41c85115aa5f7684c0edc111eacc24abd6be4b5d298b65f28600a2f1df1nat,
        },
    )) by (compute_only);
}


/// Public key decoding on [`toy`] (SEC 1 §2.3.4, §2.3.6; SP 800-186 D.1.1.1).
/// `Q = (44, 39)` decodes. Refused: the point at infinity (`00`, decoded by
/// §2.3.4 step 1 and refused by D.1.1.1 step 1), compressed points
/// (`02`, `03`, modelling choice 7), hybrid `06` (§2.3.4 step 3.2), a
/// coordinate not below p (`127 = 44 + 83` and `122 = 39 + 83` satisfy the
/// equation mod p, but §2.3.6 requires [0, p-1]), a point off the curve, and
/// strings of the wrong length.
pub proof fn lemma_toy_decode_examples()
    ensures
        decode_public_key(toy(), toy_q()) == Some(Point::Affine { x: 44nat, y: 39nat }),
        decode_public_key(toy(), seq![0x04u8, 1u8, 31u8]) == Some(toy_g()),
        // -Q = (44, 44) is a valid key too.
        decode_public_key(toy(), seq![0x04u8, 44u8, 44u8]) == Some(Point::Affine { x: 44nat, y: 44nat }),
        // (0, 0) is in range but not on the curve (0 != 50).
        os2p(toy(), seq![0x04u8, 0u8, 0u8]) is None,
        os2p(toy(), seq![0x00u8]) == Some(Point::Infinity),
        decode_public_key(toy(), seq![0x00u8]) is None,
        os2p(toy(), seq![0x02u8, 44u8]) is None,
        os2p(toy(), seq![0x03u8, 44u8]) is None,
        os2p(toy(), seq![0x06u8, 44u8, 39u8]) is None,
        os2p(toy(), seq![0x07u8, 44u8, 39u8]) is None,
        os2p(toy(), seq![0x05u8, 44u8, 39u8]) is None,
        os2p(toy(), seq![0x04u8, 127u8, 39u8]) is None,
        os2p(toy(), seq![0x04u8, 44u8, 122u8]) is None,
        os2p(toy(), seq![0x04u8, 83u8, 39u8]) is None,
        os2p(toy(), seq![0x04u8, 255u8, 255u8]) is None,
        decode_public_key(toy(), seq![0x04u8, 44u8, 40u8]) is None,
        decode_public_key(toy(), seq![0x04u8, 44u8, 45u8]) is None,
        os2p(toy(), seq![0x04u8, 44u8]) is None,
        os2p(toy(), seq![0x04u8, 44u8, 39u8, 0u8]) is None,
        os2p(toy(), Seq::<u8>::empty()) is None,
        os2p(toy(), seq![0x00u8, 0x00u8]) is None,
{
    assert(decode_public_key(toy(), toy_q()) == Some(Point::Affine { x: 44nat, y: 39nat }))
        by (compute_only);
    assert(decode_public_key(toy(), seq![0x04u8, 1u8, 31u8]) == Some(toy_g())) by (compute_only);
    assert(decode_public_key(toy(), seq![0x04u8, 44u8, 44u8])
        == Some(Point::Affine { x: 44nat, y: 44nat })) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 0u8, 0u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x00u8]) == Some(Point::Infinity)) by (compute_only);
    assert(decode_public_key(toy(), seq![0x00u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x02u8, 44u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x03u8, 44u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x06u8, 44u8, 39u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x07u8, 44u8, 39u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x05u8, 44u8, 39u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 127u8, 39u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 44u8, 122u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 83u8, 39u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 255u8, 255u8]) is None) by (compute_only);
    assert(decode_public_key(toy(), seq![0x04u8, 44u8, 40u8]) is None) by (compute_only);
    assert(decode_public_key(toy(), seq![0x04u8, 44u8, 45u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 44u8]) is None) by (compute_only);
    assert(os2p(toy(), seq![0x04u8, 44u8, 39u8, 0u8]) is None) by (compute_only);
    assert(os2p(toy(), Seq::<u8>::empty()) is None) by (compute_only);
    assert(os2p(toy(), seq![0x00u8, 0x00u8]) is None) by (compute_only);
}

/// Public key decoding on [`p384`]: G decodes; a coordinate equal to p is
/// refused (the largest 48-octet value is `2^384 - 1 ≥ p`), as is a point off
/// the curve, a compressed point, a hybrid point, and the wrong lengths.
pub proof fn lemma_p384_decode_examples()
    ensures
        decode_public_key(p384(), ex_ecpoint(p384().gx, p384().gy, 48nat))
            == Some(base_point(p384())),
        ex_ecpoint(p384().gx, p384().gy, 48nat).len() == 97nat,
        decode_public_key(p384(), ex_ecpoint(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffnat, p384().gy, 48nat)) is None,
        decode_public_key(p384(), ex_ecpoint(p384().gx, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffnat, 48nat)) is None,
        decode_public_key(p384(), ex_ecpoint(p384().gx, (p384().gy + 1) as nat, 48nat)) is None,
        decode_public_key(p384(), ex_ecpoint(p384().gx, p384().gy, 48nat).subrange(0, 96)) is None,
        decode_public_key(p384(), ex_ecpoint(p384().gx, p384().gy, 48nat).subrange(0, 49)) is None,
        decode_public_key(p384(), seq![0x00u8]) is None,
        decode_public_key(
            p384(),
            seq![0x06u8] + ex_octets(p384().gx, 48nat) + ex_octets(p384().gy, 48nat),
        ) is None,
        decode_public_key(p384(), seq![0x02u8] + ex_octets(p384().gx, 48nat)) is None,
{
    assert(decode_public_key(p384(), ex_ecpoint(p384().gx, p384().gy, 48nat))
        == Some(base_point(p384()))) by (compute_only);
    assert(ex_ecpoint(p384().gx, p384().gy, 48nat).len() == 97nat) by (compute_only);
    assert(decode_public_key(p384(), ex_ecpoint(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffnat, p384().gy, 48nat)) is None) by (compute_only);
    assert(decode_public_key(p384(), ex_ecpoint(p384().gx, 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffffnat, 48nat)) is None) by (compute_only);
    assert(decode_public_key(p384(), ex_ecpoint(p384().gx, (p384().gy + 1) as nat, 48nat)) is None)
        by (compute_only);
    assert(decode_public_key(p384(), ex_ecpoint(p384().gx, p384().gy, 48nat).subrange(0, 96))
        is None) by (compute_only);
    assert(decode_public_key(p384(), ex_ecpoint(p384().gx, p384().gy, 48nat).subrange(0, 49))
        is None) by (compute_only);
    assert(decode_public_key(p384(), seq![0x00u8]) is None) by (compute_only);
    assert(decode_public_key(
        p384(),
        seq![0x06u8] + ex_octets(p384().gx, 48nat) + ex_octets(p384().gy, 48nat),
    ) is None) by (compute_only);
    assert(decode_public_key(p384(), seq![0x02u8] + ex_octets(p384().gx, 48nat)) is None)
        by (compute_only);
}

/// Whether `ecdsa_verify_steps` rejects at exactly `step`.
pub open spec fn ex_rejects(c: Curve, h: Seq<u8>, r: nat, s: nat, q: Seq<u8>, step: Step) -> bool {
    ecdsa_verify_steps(c, h, r, s, q) == Result::<(), Step>::Err(step)
}

/// Whole verifications on [`toy`] (FIPS 186-5 §6.4.2), with the step that
/// rejects. The key is Q = [23]G = (44, 39). The signature was made with
/// k = 2 (R = (81, 52)): digest `B5 12`, so `e = 90` (leftmost 7 bits),
/// `r = 81 mod 67 = 14` (step 9 reduces x_R = 81, which is at least n = 67,
/// so `r1 mod n` matters), and `s = k^-1 (e + r d) mod 67 = 5`. Then
/// `w = 5^-1 = 27`, `u = 90 · 27 mod 67 = 18`, `v = 14 · 27 mod 67 = 43`, and
/// `[18]G + [43]Q = [18 + 43 · 23]G = [1007 mod 67]G = [2]G = R`.
///
/// The other digests `B5` and `B4 00` have the same `e = 90`. Step 9 rejects
/// a digest with another `e`, another s, and another r. Step 1 rejects r or
/// s equal to 0, n or more than n (r = 81 = 14 + n would pass step 9 if the
/// range were not checked). Step 6 rejects `R1 = O`: with digest `02` (e = 1),
/// r = 32 and s = 5 we get w = 27, u = 27, v = 60, and `27 + 60 · 23 = 21 · 67`,
/// so `[27]G + [60]Q = O`. An invalid Q is `Key` whatever r and s are.
pub proof fn lemma_toy_verify_examples()
    ensures
        inv(67nat, 5nat) == Some(27nat),
        derive_e(toy(), seq![0xB5u8, 0x12u8]) * 27 % 67 == 18nat,
        14nat * 27 % 67 == 43nat,
        compute_r1(toy(), 18nat, 43nat, Point::Affine { x: 44nat, y: 39nat })
            == Some(Point::Affine { x: 81nat, y: 52nat }),
        ecdsa_verify_steps(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, toy_q())
            == Result::<(), Step>::Ok(()),
        // The R = O example's intermediate values.
        32nat * 27 % 67 == 60nat,
        compute_r1(toy(), 27nat, 60nat, Point::Affine { x: 44nat, y: 39nat }) == Some(Point::Infinity),
        ecdsa_verify(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, toy_q()),
        ecdsa_verify(toy(), seq![0xB5u8], 14nat, 5nat, toy_q()),
        ecdsa_verify(toy(), seq![0xB4u8, 0x00u8], 14nat, 5nat, toy_q()),
        ex_rejects(toy(), seq![0xB6u8], 14nat, 5nat, toy_q(), Step::S9),
        ex_rejects(toy(), Seq::<u8>::empty(), 14nat, 5nat, toy_q(), Step::S9),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 6nat, toy_q(), Step::S9),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 13nat, 5nat, toy_q(), Step::S9),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 15nat, 5nat, toy_q(), Step::S9),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 0nat, 5nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 67nat, 5nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 68nat, 5nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 81nat, 5nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 0nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 67nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 72nat, toy_q(), Step::S1),
        ex_rejects(toy(), seq![0x02u8], 32nat, 5nat, toy_q(), Step::S6),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 44u8, 40u8], Step::Key),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 0nat, 5nat, seq![0x04u8, 44u8, 40u8], Step::Key),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 127u8, 39u8], Step::Key),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 44u8, 122u8], Step::Key),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x02u8, 44u8], Step::Key),
        ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x00u8], Step::Key),
        !ecdsa_verify(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 44u8, 40u8]),
{
    assert(inv(67nat, 5nat) == Some(27nat)) by (compute_only);
    assert(derive_e(toy(), seq![0xB5u8, 0x12u8]) * 27 % 67 == 18nat) by (compute_only);
    assert(14nat * 27 % 67 == 43nat) by (compute_only);
    assert(compute_r1(toy(), 18nat, 43nat, Point::Affine { x: 44nat, y: 39nat })
        == Some(Point::Affine { x: 81nat, y: 52nat })) by (compute_only);
    assert(ecdsa_verify_steps(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, toy_q())
        == Result::<(), Step>::Ok(())) by (compute_only);
    assert(32nat * 27 % 67 == 60nat) by (compute_only);
    assert(compute_r1(toy(), 27nat, 60nat, Point::Affine { x: 44nat, y: 39nat })
        == Some(Point::Infinity)) by (compute_only);
    assert(ecdsa_verify(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, toy_q())) by (compute_only);
    assert(ecdsa_verify(toy(), seq![0xB5u8], 14nat, 5nat, toy_q())) by (compute_only);
    assert(ecdsa_verify(toy(), seq![0xB4u8, 0x00u8], 14nat, 5nat, toy_q())) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB6u8], 14nat, 5nat, toy_q(), Step::S9)) by (compute_only);
    assert(ex_rejects(toy(), Seq::<u8>::empty(), 14nat, 5nat, toy_q(), Step::S9)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 6nat, toy_q(), Step::S9)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 13nat, 5nat, toy_q(), Step::S9)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 15nat, 5nat, toy_q(), Step::S9)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 0nat, 5nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 67nat, 5nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 68nat, 5nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 81nat, 5nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 0nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 67nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 72nat, toy_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(toy(), seq![0x02u8], 32nat, 5nat, toy_q(), Step::S6)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 44u8, 40u8], Step::Key)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 0nat, 5nat, seq![0x04u8, 44u8, 40u8], Step::Key)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 127u8, 39u8], Step::Key)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 44u8, 122u8], Step::Key)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x02u8, 44u8], Step::Key)) by (compute_only);
    assert(ex_rejects(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x00u8], Step::Key)) by (compute_only);
    assert(!ecdsa_verify(toy(), seq![0xB5u8, 0x12u8], 14nat, 5nat, seq![0x04u8, 44u8, 40u8])) by (compute_only);
}

/// The public key Q = [d]G on [`p384`], d = 2^300 + 0x123456789abcdef
/// (computed with an independent script), as an ECPoint.
pub open spec fn p384_q() -> Seq<u8> {
    ex_ecpoint(
        0xf39445b953b052427d51cf8cf3b54cc01a88c516b6830b70b06bc59889871d4a24959921750eed4d695f0c049726386cnat,
        0x9d5d3ebe919597b047016925f5fd77eee99357c9ce0012650574fdd0f0cb9476541e7cc797332396ce321e452e735232nat,
        48,
    )
}

/// The key `-G = (Gx, p - Gy)`, as an ECPoint.
pub open spec fn p384_minus_g() -> Seq<u8> {
    ex_ecpoint(p384().gx, (p384().p - p384().gy) as nat, 48)
}

/// The signature `(r, s)` and the digest integer `e` made from `u = 3`,
/// `v = 2` and Q (see [`lemma_p384_verify_examples`]).
pub open spec fn p384_r() -> nat {
    0x682ab6965e1b69801aa65c3f7f4e123299a18cfa4336e3caeebb8b3fcb07a210e3c6b29f1ace36c95d0199d9fe4e2086nat
}

/// See [`p384_r`].
pub open spec fn p384_s() -> nat {
    0x34155b4b2f0db4c00d532e1fbfa709194cd0c67d219b71e5775dc59fe583d10871e3594f8d671b64ae80ccecff271043nat
}

/// See [`p384_r`]: the digest, as 48 octets.
pub open spec fn p384_digest() -> Seq<u8> {
    ex_octets(
        0x9c4011e18d291e4027f98a5f3ef51b4be672537764d255b0661950dfb08b731955aa0beea835522e0b8266c6fd7530c9nat,
        48,
    )
}

/// Whole verifications on [`p384`]. A signature is built backwards, so that
/// step 6 takes a handful of group operations and not about 1,150: pick
/// `u = 3` and `v = 2`, then `R = [3]G + [2]Q`, `r = x_R mod n` (here
/// `x_R < n`), `s = r · v^-1 mod n` and `e = u · s mod n`. The digest is `e`
/// as 48 octets (the leftmost 384 bits of a longer digest give the same
/// `e`). Steps 4 and 5 then give back `w = s^-1`, `e w = u` and `r w = v`.
/// It is a valid signature by the key Q for per-message secret
/// `k = u + v d mod n`, though no hash function produced the digest.
///
/// Rejections, equally cheap: step 9 for an `r` that is not `x_R` (built the
/// same way from `u = 3`, `v = 2` and another `r`, so that `[3]G + [2]Q` is
/// computed and is not `r`); step 6 for Q = -G with `u = v = 1`
/// (`[1]G + [1](-G) = O`, rule 3, no inversion); step 1 for r or s equal to
/// 0, n or n + 1; and a Q that is invalid.
pub proof fn lemma_p384_verify_examples()
    ensures
        ecdsa_verify_steps(p384(), p384_digest(), p384_r(), p384_s(), p384_q())
            == Result::<(), Step>::Ok(()),
        // A 64-octet digest with the same leftmost 48 octets has the same e.
        ecdsa_verify(
            p384(),
            p384_digest() + ex_octets(0x0123456789abcdefnat, 16),
            p384_r(),
            p384_s(),
            p384_q(),
        ),
        // Step 9.
        ex_rejects(
            p384(),
            ex_octets(
                0x7fffffffffffffffffffffffffffffffffffffffffffffffe3b1a6c0fa1b96efc75b888dfd5a08a411c48e6a3f6449a0nat,
                48,
            ),
            0x1234567890abcdef1234567890abcdefnat,
            0x7fffffffffffffffffffffffffffffffffffffffffffffffe3b1a6c0fa1b96efb52732156cae3ab4ff9037f1aeb87bb1nat,
            p384_q(),
            Step::S9,
        ),
        // Step 6.
        ex_rejects(
            p384(),
            ex_octets(0xabcdefnat, 48),
            0xabcdefnat,
            0xabcdefnat,
            p384_minus_g(),
            Step::S6,
        ),
        // Step 1.
        ex_rejects(p384(), p384_digest(), 0nat, p384_s(), p384_q(), Step::S1),
        ex_rejects(p384(), p384_digest(), p384_r(), 0nat, p384_q(), Step::S1),
        ex_rejects(p384(), p384_digest(), p384().n, p384_s(), p384_q(), Step::S1),
        ex_rejects(p384(), p384_digest(), p384_r(), p384().n, p384_q(), Step::S1),
        ex_rejects(p384(), p384_digest(), p384_r(), (p384().n + 1) as nat, p384_q(), Step::S1),
        // The public key.
        ex_rejects(p384(), p384_digest(), p384_r(), p384_s(), p384_q().subrange(0, 96), Step::Key),
        ex_rejects(p384(), p384_digest(), p384_r(), p384_s(), seq![0x00u8], Step::Key),
        ex_rejects(p384(), p384_digest(), 0nat, 0nat, seq![0x00u8], Step::Key),
{
    assert(ecdsa_verify_steps(p384(), p384_digest(), p384_r(), p384_s(), p384_q())
        == Result::<(), Step>::Ok(())) by (compute_only);
    assert(ecdsa_verify(
        p384(),
        p384_digest() + ex_octets(0x0123456789abcdefnat, 16),
        p384_r(),
        p384_s(),
        p384_q(),
    )) by (compute_only);
    assert(ex_rejects(
        p384(),
        ex_octets(
            0x7fffffffffffffffffffffffffffffffffffffffffffffffe3b1a6c0fa1b96efc75b888dfd5a08a411c48e6a3f6449a0nat,
            48,
        ),
        0x1234567890abcdef1234567890abcdefnat,
        0x7fffffffffffffffffffffffffffffffffffffffffffffffe3b1a6c0fa1b96efb52732156cae3ab4ff9037f1aeb87bb1nat,
        p384_q(),
        Step::S9,
    )) by (compute_only);
    assert(ex_rejects(
        p384(),
        ex_octets(0xabcdefnat, 48),
        0xabcdefnat,
        0xabcdefnat,
        p384_minus_g(),
        Step::S6,
    )) by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), 0nat, p384_s(), p384_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), p384_r(), 0nat, p384_q(), Step::S1)) by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), p384().n, p384_s(), p384_q(), Step::S1))
        by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), p384_r(), p384().n, p384_q(), Step::S1))
        by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), p384_r(), (p384().n + 1) as nat, p384_q(), Step::S1))
        by (compute_only);
    assert(ex_rejects(
        p384(),
        p384_digest(),
        p384_r(),
        p384_s(),
        p384_q().subrange(0, 96),
        Step::Key,
    )) by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), p384_r(), p384_s(), seq![0x00u8], Step::Key))
        by (compute_only);
    assert(ex_rejects(p384(), p384_digest(), 0nat, 0nat, seq![0x00u8], Step::Key)) by (compute_only);
}

} // verus!
