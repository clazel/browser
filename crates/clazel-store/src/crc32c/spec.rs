//! Executable-style specification of CRC32C, transcribed from RFC 7143
//! §13.1 "HeaderDigest and DataDigest"
//! (<https://www.rfc-editor.org/rfc/rfc7143#section-13.1>, April 2014,
//! which obsoletes RFC 3720 and keeps its §12.1 text). Nothing here runs; it
//! defines what "correct" means. Each `// N.` comment is the bullet number,
//! counted from the first, of the process §13.1 says the CRC "MUST be
//! calculated by a method that produces the same results as".
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - **Bit numbering.** §11 says "the most significant bit (within byte or
//!   field) is the lowest numbered bit", so iSCSI's bit 0 of a byte is the
//!   bit of value 128 and its bit 7 the bit of value 1. §13.1's "bit 7 of
//!   the lowest numbered byte is considered the most significant bit" is
//!   therefore the bit of value 1. Read this way, the process gives the
//!   examples of §A.4 (32 octets of zeros give `aa 36 91 8a`); read with bit
//!   7 as the bit of value 128 it does not. That was checked by computing
//!   both on 2026-11-03.
//! - **Polynomials.** A polynomial over GF(2) is a `Seq<bool>` of its
//!   coefficients, the highest degree first, so `s[0]` is the coefficient
//!   of x^(s.len() - 1).
//! - **Division.** "Divided by G(x) ... produces a remainder R(x)" is long
//!   division, one coefficient at a time, in [`remainder`]: the remainder is
//!   kept as its 32 coefficients x^31 to x^0, and bringing down the next
//!   coefficient subtracts G(x) (adds it: GF(2)) whenever the x^32
//!   coefficient would be one. This is the schoolbook algorithm, with no
//!   tables or reflection.
//! - **Bullets 2 and 3 in one.** "The most significant 32 bits are
//!   complemented" and then "multiplied by x^32": the 32 highest
//!   coefficients of M(x)·x^32 are complemented ([`complement_first_32`]).
//!   For a message of at least 32 bits this is the same as complementing
//!   M(x)'s 32 highest and then shifting. For a shorter message §13.1 does
//!   not say what to do, and this gives the usual CRC32C. The store never
//!   checks fewer than five octets (a record's commit number and operation
//!   list alone take five).
//! - **The digest word** (bullet 6) is a `Seq<u8>` of four octets.
//! - §13.1's last bullet (the remainder 0x1c2d19ed over a message followed
//!   by its CRC) is a property of the result, not a step. It is for a
//!   lemma, not this definition.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Whether the bit of value 2^i is set in `v` (`pow2` is vstd's, so its
/// lemmas relating shifts to division apply).
pub open spec fn bit_of_value(v: nat, i: nat) -> bool {
    (v / vstd::arithmetic::power2::pow2(i)) % 2 == 1
}

/// The eight coefficients one octet contributes to M(x), highest first:
/// iSCSI bit 7 (value 1) down to iSCSI bit 0 (value 128).
pub open spec fn byte_bits(b: u8) -> Seq<bool> {
    Seq::new(8, |t: int| bit_of_value(b as nat, t as nat))
}

/// 1. "The PDU bits are considered as the coefficients of a polynomial
/// M(x) of degree n - 1; bit 7 of the lowest numbered byte is considered
/// the most significant bit (x**n - 1), followed by bit 6 of the lowest
/// numbered byte through bit 0 of the highest numbered byte (x**0)."
pub open spec fn message_bits(data: Seq<u8>) -> Seq<bool>
    decreases data.len(),
{
    if data.len() == 0 {
        seq![]
    } else {
        byte_bits(data[0]) + message_bits(data.drop_first())
    }
}

/// The 32 coefficients x^31 to x^0 of the 32-bit number `w`.
pub open spec fn word_bits(w: nat) -> Seq<bool> {
    Seq::new(32, |j: int| bit_of_value(w, (31 - j) as nat))
}

/// The generator 0x11edc6f41 (§13.1's table: "CRC32C | 32-bit CRC |
/// 0x11edc6f41"), without its x^32 term: the coefficients x^31 to x^0.
pub open spec fn generator_below_x32() -> Seq<bool> {
    word_bits(0x1edc6f41)
}

/// Coefficient-wise sum over GF(2) of two polynomials of the same length.
pub open spec fn add(a: Seq<bool>, b: Seq<bool>) -> Seq<bool> {
    Seq::new(a.len(), |j: int| a[j] != b[j])
}

/// Coefficient-wise complement.
pub open spec fn complement(a: Seq<bool>) -> Seq<bool> {
    Seq::new(a.len(), |j: int| !a[j])
}

/// One step of long division: `r` is the remainder so far (x^31 to x^0),
/// and `next` the coefficient brought down. The new partial dividend is
/// r(x)·x + next, whose x^32 coefficient is `r[0]`; when that is one, G(x)
/// is subtracted, which removes it.
pub open spec fn division_step(r: Seq<bool>, next: bool) -> Seq<bool> {
    let shifted = r.drop_first().push(next);
    if r[0] {
        add(shifted, generator_below_x32())
    } else {
        shifted
    }
}

/// The remainder of the polynomial `d` divided by G(x): its 32
/// coefficients x^31 to x^0.
pub open spec fn remainder(d: Seq<bool>) -> Seq<bool>
    decreases d.len(),
{
    if d.len() == 0 {
        Seq::new(32, |j: int| false)
    } else {
        division_step(remainder(d.drop_last()), d.last())
    }
}

/// The 32 highest coefficients complemented, the rest unchanged.
pub open spec fn complement_first_32(s: Seq<bool>) -> Seq<bool> {
    Seq::new(s.len(), |j: int| if j < 32 { !s[j] } else { s[j] })
}

/// The value of eight coefficients mapped into one digest octet: the first
/// goes to iSCSI bit 7 (value 1), the last to iSCSI bit 0 (value 128).
pub open spec fn octet_value(s: Seq<bool>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] { 1nat } else { 0nat }) + 2 * octet_value(s.drop_first())
    }
}

/// 6. "The CRC bits are mapped into the digest word. The x**31 coefficient
/// is mapped to bit 7 of the lowest numbered byte of the digest, and the
/// mapping continues with successive coefficients and bits so that the
/// x**24 coefficient is mapped to bit 0 of the lowest numbered byte. The
/// mapping continues further with the x**23 coefficient mapped to bit 7 of
/// the next byte in the digest until the x**0 coefficient is mapped to bit
/// 0 of the highest numbered byte of the digest."
pub open spec fn digest_word(crc: Seq<bool>) -> Seq<u8> {
    Seq::new(4, |k: int| octet_value(crc.subrange(8 * k, 8 * k + 8)) as u8)
}

/// CRC32C of `data`, as its four digest octets.
pub open spec fn crc32c(data: Seq<u8>) -> Seq<u8> {
    // 1. M(x).
    let m = message_bits(data);
    // 2. "The most significant 32 bits are complemented." and
    // 3. "The polynomial is multiplied by x**32, then divided by G(x)."
    // (in one, see the modelling choices).
    let dividend = complement_first_32(m + Seq::new(32, |j: int| false));
    let r = remainder(dividend);
    // 4. "The coefficients of R(x) are formed into a 32-bit sequence." (`r`
    // is that sequence, x^31 first.)
    // 5. "The bit sequence is complemented, and the result is the CRC."
    let crc = complement(r);
    // 6. The digest word.
    digest_word(crc)
}

} // verus!
