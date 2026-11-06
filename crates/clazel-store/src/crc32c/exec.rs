//! The executable CRC32C, proven to meet [`super::contract`]. It carries out
//! [`super::spec`]'s long division as written, one coefficient at a time:
//! the remainder is a `u32` whose bit 31 - j is coefficient j of the spec's
//! remainder (x^(31 - j)). That is eight steps per octet, slower than a
//! table, and every step is checked against the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// G(x) without its x^32 term: 0x11edc6f41 less 2^32.
const GENERATOR_BELOW_X32: u32 = 0x1edc6f41;

/// Bit `k` of a `u32` is the spec's [`bit_of_value`].
proof fn lemma_u32_bit(x: u32, k: nat)
    requires
        k < 32,
    ensures
        bit_of_value(x as nat, k) == ((x >> (k as u32)) & 1u32 == 1u32),
{
    vstd::bits::lemma_u32_shr_is_div(x, k as u32);
    let y = x >> (k as u32);
    assert((y & 1u32 == 1u32) == (y % 2 == 1)) by (bit_vector);
}

/// Bit `k` of a `u8` is the spec's [`bit_of_value`].
proof fn lemma_u8_bit(x: u8, k: nat)
    requires
        k < 8,
    ensures
        bit_of_value(x as nat, k) == ((x >> (k as u8)) & 1u8 == 1u8),
{
    vstd::bits::lemma_u8_shr_is_div(x, k as u8);
    let y = x >> (k as u8);
    assert((y & 1u8 == 1u8) == (y % 2 == 1)) by (bit_vector);
}

/// One division step on the `u32` remainder, as the executable code does it.
pub closed spec fn step_value(r: u32, next: u32) -> u32 {
    let shifted = (r << 1u32) | next;
    if (r >> 31u32) == 1u32 {
        shifted ^ GENERATOR_BELOW_X32
    } else {
        shifted
    }
}

/// The `u32` step is the spec's [`division_step`].
proof fn lemma_step(r: u32, next: u32)
    requires
        next <= 1,
    ensures
        word_bits(step_value(r, next) as nat) == division_step(word_bits(r as nat), next == 1),
{
    let w = word_bits(r as nat);
    let o = step_value(r, next);
    let shifted = w.drop_first().push(next == 1);
    let ds = division_step(w, next == 1);
    let g = 0x1edc6f41u32;
    let top = (r >> 31u32) == 1u32;
    // w[0] is bit 31 of r, which is the whole of r >> 31.
    lemma_u32_bit(r, 31);
    assert(((r >> 31u32) & 1u32 == 1u32) == ((r >> 31u32) == 1u32)) by (bit_vector);
    assert(w[0] == top);
    assert(ds == (if top { super::spec::add(shifted, generator_below_x32()) } else { shifted }));
    assert(o == (if top { ((r << 1u32) | next) ^ g } else { (r << 1u32) | next }));
    assert forall|j: int| 0 <= j < 32 implies #[trigger] word_bits(o as nat)[j] == ds[j] by {
        let k = (31 - j) as u32;
        lemma_u32_bit(o, k as nat);
        lemma_u32_bit(g, k as nat);
        // The bit the shift brings to position k: `next` at k = 0, bit k - 1
        // of r above.
        let from: bool = if k == 0 { next == 1 } else { w[j + 1] };
        assert(shifted[j] == from);
        if k == 0 {
            assert((((r << 1u32) | next) >> 0u32) & 1u32 == next) by (bit_vector) requires next <= 1u32;
            assert(((((r << 1u32) | next) ^ g) >> 0u32) & 1u32 == (next ^ ((g >> 0u32) & 1u32)))
                by (bit_vector) requires next <= 1u32;
            assert((next ^ 1u32 == 1u32) == !(next == 1u32)) by (bit_vector) requires next <= 1u32;
            assert((next ^ 0u32 == 1u32) == (next == 1u32)) by (bit_vector);
        } else {
            lemma_u32_bit(r, (k - 1) as nat);
            let rb = (r >> ((k - 1) as u32)) & 1u32;
            assert((((r << 1u32) | next) >> k) & 1u32 == rb) by (bit_vector)
                requires next <= 1u32, 1u32 <= k < 32u32, rb == (r >> ((k - 1) as u32)) & 1u32;
            assert(((((r << 1u32) | next) ^ g) >> k) & 1u32 == (rb ^ ((g >> k) & 1u32))) by (bit_vector)
                requires next <= 1u32, 1u32 <= k < 32u32, rb == (r >> ((k - 1) as u32)) & 1u32;
            assert(rb <= 1u32) by (bit_vector) requires rb == (r >> ((k - 1) as u32)) & 1u32;
            assert((rb ^ 1u32 == 1u32) == !(rb == 1u32)) by (bit_vector) requires rb <= 1u32;
            assert((rb ^ 0u32 == 1u32) == (rb == 1u32)) by (bit_vector);
            assert(w[j + 1] == (rb == 1u32));
        }
        assert(((g >> k) & 1u32 == 1u32) || ((g >> k) & 1u32 == 0u32)) by (bit_vector);
        assert(generator_below_x32()[j] == ((g >> k) & 1u32 == 1u32));
    }
    assert(word_bits(o as nat) =~= ds);
}

/// The spec's message bits: eight per octet, octet `j`'s bit `t` at
/// `8j + t`.
proof fn lemma_message_bits(data: Seq<u8>)
    ensures
        message_bits(data).len() == 8 * data.len(),
        forall|j: int, t: int|
            0 <= j < data.len() && 0 <= t < 8 ==> #[trigger] message_bits(data)[8 * j + t] == bit_of_value(
                data[j] as nat,
                t as nat,
            ),
    decreases data.len(),
{
    if data.len() > 0 {
        let rest = data.drop_first();
        lemma_message_bits(rest);
        assert forall|j: int, t: int| 0 <= j < data.len() && 0 <= t < 8 implies #[trigger] message_bits(data)[8 * j + t]
            == bit_of_value(data[j] as nat, t as nat) by {
            if j > 0 {
                assert(8 * j + t - 8 == 8 * (j - 1) + t);
                assert(rest[j - 1] == data[j]);
            }
        }
    }
}

/// Bringing down coefficient `i` of `d` is one [`division_step`].
proof fn lemma_remainder_take(d: Seq<bool>, i: int)
    requires
        0 <= i < d.len(),
    ensures
        remainder(d.take(i + 1)) == division_step(remainder(d.take(i)), d[i]),
{
    assert(d.take(i + 1).drop_last() =~= d.take(i));
    assert(d.take(i + 1).last() == d[i]);
}

/// The remainder of nothing is zero.
proof fn lemma_remainder_empty()
    ensures
        word_bits(0u32 as nat) == remainder(Seq::<bool>::empty()),
{
    assert forall|j: int| 0 <= j < 32 implies #[trigger] word_bits(0u32 as nat)[j] == false by {
        lemma_u32_bit(0u32, (31 - j) as nat);
        let k = (31 - j) as u32;
        assert((0u32 >> k) & 1u32 == 0u32) by (bit_vector);
    }
    assert(word_bits(0u32 as nat) =~= remainder(Seq::<bool>::empty()));
}

/// One division step.
fn division_step_u32(r: u32, next: u32) -> (out: u32)
    requires
        next <= 1,
    ensures
        out == step_value(r, next),
{
    let shifted = (r << 1u32) | next;
    if (r >> 31u32) == 1u32 {
        shifted ^ GENERATOR_BELOW_X32
    } else {
        shifted
    }
}

/// Bit `k` of `c`, as 0 or 1.
fn bit_at(c: u32, k: u32) -> (b: u32)
    requires
        k < 32,
    ensures
        b <= 1,
        (b == 1) == bit_of_value(c as nat, k as nat),
{
    proof {
        lemma_u32_bit(c, k as nat);
        assert((c >> k) & 1u32 <= 1u32) by (bit_vector);
    }
    (c >> k) & 1u32
}

/// Octet `k` of the digest word of `c` (bullet 6).
fn digest_octet(c: u32, k: u32) -> (b: u8)
    requires
        k < 4,
    ensures
        b as nat == octet_value(word_bits(c as nat).subrange(8 * k, 8 * k + 8)),
{
    // k < 4, so top is 7 to 31 and none of these saturates.
    let top = 31u32.saturating_sub(k.saturating_mul(8));
    let b0 = bit_at(c, top);
    let b1 = bit_at(c, top.saturating_sub(1));
    let b2 = bit_at(c, top.saturating_sub(2));
    let b3 = bit_at(c, top.saturating_sub(3));
    let b4 = bit_at(c, top.saturating_sub(4));
    let b5 = bit_at(c, top.saturating_sub(5));
    let b6 = bit_at(c, top.saturating_sub(6));
    let b7 = bit_at(c, top.saturating_sub(7));
    let v = b0 | (b1 << 1u32) | (b2 << 2u32) | (b3 << 3u32) | (b4 << 4u32) | (b5 << 5u32) | (b6 << 6u32) | (b7
        << 7u32);
    proof {
        assert(v == b0 + 2 * (b1 + 2 * (b2 + 2 * (b3 + 2 * (b4 + 2 * (b5 + 2 * (b6 + 2 * b7))))))) by (bit_vector)
            requires
                b0 <= 1u32,
                b1 <= 1u32,
                b2 <= 1u32,
                b3 <= 1u32,
                b4 <= 1u32,
                b5 <= 1u32,
                b6 <= 1u32,
                b7 <= 1u32,
                v == b0 | (b1 << 1u32) | (b2 << 2u32) | (b3 << 3u32) | (b4 << 4u32) | (b5 << 5u32) | (b6 << 6u32)
                    | (b7 << 7u32),
        ;
    }
    proof {
        let s = word_bits(c as nat).subrange(8 * k, 8 * k + 8);
        assert(s[0] == (b0 == 1));
        assert(s[1] == (b1 == 1));
        assert(s[2] == (b2 == 1));
        assert(s[3] == (b3 == 1));
        assert(s[4] == (b4 == 1));
        assert(s[5] == (b5 == 1));
        assert(s[6] == (b6 == 1));
        assert(s[7] == (b7 == 1));
        assert(s.drop_first() =~= s.subrange(1, 8));
        assert(s.subrange(1, 8).drop_first() =~= s.subrange(2, 8));
        assert(s.subrange(2, 8).drop_first() =~= s.subrange(3, 8));
        assert(s.subrange(3, 8).drop_first() =~= s.subrange(4, 8));
        assert(s.subrange(4, 8).drop_first() =~= s.subrange(5, 8));
        assert(s.subrange(5, 8).drop_first() =~= s.subrange(6, 8));
        assert(s.subrange(6, 8).drop_first() =~= s.subrange(7, 8));
        assert(s.subrange(7, 8).drop_first() =~= s.subrange(8, 8));
        assert(octet_value(s.subrange(8, 8)) == 0);
        assert(octet_value(s.subrange(7, 8)) == b7 as nat);
        assert(octet_value(s.subrange(6, 8)) == b6 as nat + 2 * octet_value(s.subrange(7, 8)));
        assert(octet_value(s.subrange(5, 8)) == b5 as nat + 2 * octet_value(s.subrange(6, 8)));
        assert(octet_value(s.subrange(4, 8)) == b4 as nat + 2 * octet_value(s.subrange(5, 8)));
        assert(octet_value(s.subrange(3, 8)) == b3 as nat + 2 * octet_value(s.subrange(4, 8)));
        assert(octet_value(s.subrange(2, 8)) == b2 as nat + 2 * octet_value(s.subrange(3, 8)));
        assert(octet_value(s.subrange(1, 8)) == b1 as nat + 2 * octet_value(s.subrange(2, 8)));
        assert(octet_value(s) == b0 as nat + 2 * octet_value(s.subrange(1, 8)));
    }
    v as u8
}

/// CRC32C of `data`: the four digest octets of RFC 7143 §13.1.
pub fn crc32c(data: &[u8]) -> (out: [u8; 4])
    ensures
        crate::crc32c::contract::crc32c_ensures(data@, out@),
{
    let ghost m = message_bits(data@);
    let ghost d = complement_first_32(m + Seq::new(32, |j: int| false));
    proof {
        lemma_message_bits(data@);
        lemma_remainder_empty();
        assert(d.take(0) =~= Seq::<bool>::empty());
    }
    let mut r: u32 = 0;
    // 1.-3. The message's coefficients, the first 32 complemented.
    let mut j: usize = 0;
    while j < data.len()
        invariant
            j <= data.len(),
            m.len() == 8 * data.len(),
            d.len() == 8 * data.len() + 32,
            d == complement_first_32(m + Seq::new(32, |j: int| false)),
            forall|jj: int, t: int|
                0 <= jj < data.len() && 0 <= t < 8 ==> #[trigger] m[8 * jj + t] == bit_of_value(
                    data@[jj] as nat,
                    t as nat,
                ),
            word_bits(r as nat) == remainder(d.take(8 * j as int)),
        decreases data.len() - j,
    {
        // j < data.len(): `get` finds the octet.
        let byte = match data.get(j) {
            Some(&b) => b,
            None => 0,
        };
        let mut t: u8 = 0;
        while t < 8
            invariant
                t <= 8,
                j < data.len(),
                byte == data@[j as int],
                m.len() == 8 * data.len(),
                d.len() == 8 * data.len() + 32,
                d == complement_first_32(m + Seq::new(32, |j: int| false)),
                forall|jj: int, tt: int|
                    0 <= jj < data.len() && 0 <= tt < 8 ==> #[trigger] m[8 * jj + tt] == bit_of_value(
                        data@[jj] as nat,
                        tt as nat,
                    ),
                word_bits(r as nat) == remainder(d.take(8 * j + t)),
            decreases 8 - t,
        {
            let bit = ((byte >> t) & 1u8) as u32;
            // Positions below 32 are complemented: 8j + t < 32 exactly when j < 4.
            let flip: u32 = if j < 4 { 1 } else { 0 };
            let next = bit ^ flip;
            proof {
                let i = 8 * j + t;
                lemma_u8_bit(byte, t as nat);
                assert((byte >> t) & 1u8 <= 1u8) by (bit_vector);
                assert(m[i] == bit_of_value(data@[j as int] as nat, t as nat));
                assert((m + Seq::new(32, |j: int| false))[i] == m[i]);
                assert(d[i] == (if i < 32 { !m[i] } else { m[i] }));
                assert((bit ^ 1u32) == (if bit == 1u32 { 0u32 } else { 1u32 })) by (bit_vector) requires bit <= 1u32;
                assert((bit ^ 0u32) == bit) by (bit_vector);
                assert(next <= 1 && (next == 1) == d[i]);
                lemma_remainder_take(d, i);
                lemma_step(r, next);
            }
            r = division_step_u32(r, next);
            // t < 8: this does not saturate.
            t = t.saturating_add(1);
        }
        proof {
            assert(8 * j + 8 == 8 * (j + 1));
        }
        // j < data.len(): this does not saturate.
        j = j.saturating_add(1);
    }
    // The 32 coefficients x**32 adds, all zero, complemented where they are
    // among the first 32.
    let mut z: u32 = 0;
    while z < 32
        invariant
            z <= 32,
            j == data.len(),
            m.len() == 8 * data.len(),
            d.len() == 8 * data.len() + 32,
            d == complement_first_32(m + Seq::new(32, |j: int| false)),
            word_bits(r as nat) == remainder(d.take(8 * data.len() + z)),
        decreases 32 - z,
    {
        // data.len() < 4 when the sum is taken: it does not saturate.
        let next: u32 = if data.len() < 4 && data.len().saturating_mul(8).saturating_add(z as usize) < 32 { 1 } else { 0 };
        proof {
            let i = 8 * data.len() + z;
            assert((m + Seq::new(32, |j: int| false))[i] == false);
            assert(d[i] == (i < 32));
            lemma_remainder_take(d, i);
            lemma_step(r, next);
        }
        r = division_step_u32(r, next);
        // z < 32: this does not saturate.
        z = z.saturating_add(1);
    }
    proof {
        assert(d.take(d.len() as int) =~= d);
    }
    // 4.-5. The remainder's coefficients, complemented.
    let c = !r;
    proof {
        assert forall|jj: int| 0 <= jj < 32 implies #[trigger] word_bits(c as nat)[jj] == complement(
            word_bits(r as nat),
        )[jj] by {
            let k = (31 - jj) as u32;
            lemma_u32_bit(c, k as nat);
            lemma_u32_bit(r, k as nat);
            assert(((!r >> k) & 1u32 == 1u32) == !((r >> k) & 1u32 == 1u32)) by (bit_vector) requires k < 32u32;
        }
        assert(word_bits(c as nat) =~= complement(word_bits(r as nat)));
    }
    // 6. The digest word.
    let out = [digest_octet(c, 0), digest_octet(c, 1), digest_octet(c, 2), digest_octet(c, 3)];
    proof {
        assert(out@ =~= digest_word(complement(remainder(d))));
    }
    out
}

} // verus!
