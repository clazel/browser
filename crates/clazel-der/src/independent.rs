//! A second transcription of DER, from a different text: Burton S. Kaliski
//! Jr., "A Layman's Guide to a Subset of ASN.1, BER, and DER" (RSA
//! Laboratories Technical Note, revised 1 November 1993; the copy read is
//! <https://luca.ntop.org/Teaching/Appunti/asn1.html>), sections 2 to 5.
//! Its definitions (everything before the equivalence section at the end)
//! were written from the Guide alone, before `spec.rs` existed; they share no
//! definition with it. The one later change made them closer to the Guide,
//! not to the spec: the limits (tag number, arc) are checks on the finished
//! number, not early exits. The equivalence lemmas at the end necessarily
//! name the spec's functions, and only they do.
//!
//! ## What the Guide says and this file models
//!
//! - §3.1, "Identifier octets": a low-tag-number form (one octet: bits 8-7
//!   the class by Table 2, bit 6 primitive or constructed, bits 5-1 the tag
//!   number for numbers 0 to 30) and a high-tag-number form (the first octet
//!   as before with bits 5-1 all ones, then the tag number "base 128, most
//!   significant digit first, with as few digits as possible, and with the
//!   bit 8 of each octet except the last set to 1", for numbers 31 and
//!   greater). [`k_ident`].
//! - §3.1 and §4, "Length octets": the short form for 0 to 127, and for 128
//!   or more the long form "of length ... encoded in the minimum number of
//!   octets": a first octet with bit 8 set and bits 7-1 the number of
//!   additional octets, then the length base 256, most significant digit
//!   first. §3.3 gives the indefinite form (the single octet 0x80), which §4
//!   does not allow ("exactly one way to represent any ASN.1 value", and the
//!   definite-length methods only for the types it lists). The long form is
//!   "Two to 127 octets" in all, so at most 126 additional octets: the first
//!   octet 0xFF is not a length. [`k_length`].
//! - §5.7 INTEGER: "the value of the integer, base 256, in two's complement
//!   form, most significant digit first, with the minimum number of octets".
//!   Here that is not a rule about the first two octets but a fact about the
//!   value: the contents are accepted exactly when they equal the one
//!   minimal two's complement spelling of the value they denote
//!   ([`k_int_bytes`], [`k_integer_ok`]).
//! - §5.4 BIT STRING (DER): the first contents octet is the number of unused
//!   bits (0 to 7, the amount by which the length is below the next multiple
//!   of eight), the following octets hold the bits "padded with zero-valued
//!   bits". An empty bit string is the single octet 0 ([`k_bitstring_ok`]).
//! - §5.8 NULL: empty contents. §5.10 OCTET STRING, §5.6 IA5String, §5.11
//!   PrintableString, §5.17 UTCTime: DER takes the primitive form, the
//!   contents are the characters ([`k_primitive_string`]).
//! - §5.9 OBJECT IDENTIFIER: "The first octet has value 40 * value1 +
//!   value2 ... The following octets, if any, encode value3, ..., valuen.
//!   Each value is encoded base 128, most significant digit first, with as
//!   few digits as possible, and the most significant bit of each octet
//!   except the last in the value's encoding set to 1." [`k_oid`].
//! - §5.12 SEQUENCE and §5.14 SET: constructed, definite length (§4);
//!   §5.1 and §5.2: an implicitly tagged type changes the tag and keeps the
//!   form of the underlying type, an explicitly tagged type is constructed
//!   and holds the underlying encoding.
//!
//! ## What the Guide leaves out, and the limits shared with the spec
//!
//! - The Guide has no BOOLEAN, UTF8String or GeneralizedTime (X.690 §8.2,
//!   §11.1 and X.680 are the only sources for them here), so they have no
//!   second transcription and the equivalence lemmas do not mention them.
//! - Its first-octet rule for an OBJECT IDENTIFIER ("40 * value1 + value2",
//!   one octet) holds for values below 128; the equivalence lemma for OIDs
//!   is stated for contents whose first octet is below 128, which includes
//!   every arc pair under the roots 0 and 1 and 2.0 to 2.47.
//! - The Guide has no upper bound on a tag number, a length or an arc. This
//!   file stops at the same limits as the spec, which are choices of this
//!   project and not the Guide's: tag numbers below 2^14, at most 8 length
//!   octets, arcs below 2^64.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Numbers "base 128" and "base 256, most significant digit first".
// ---------------------------------------------------------------------------

/// The number spelled by the octets `b[from..to)` in the given radix, most
/// significant digit first, folded from the left starting from `acc`. For
/// radix 128 each octet contributes its low seven bits.
pub open spec fn k_digits(b: Seq<u8>, from: nat, to: nat, radix: nat, acc: nat) -> nat
    decreases to - from,
{
    if from >= to {
        acc
    } else {
        let o = b[from as int] as nat;
        let digit = if radix == 128 { o % 128 } else { o };
        k_digits(b, from + 1, to, radix, acc * radix + digit)
    }
}

// ---------------------------------------------------------------------------
// §3.1: identifier octets.
// ---------------------------------------------------------------------------

/// What an element's identifier says: Table 2's class bits (0 universal, 1
/// application, 2 context-specific, 3 private), whether the encoding is
/// constructed, and the tag number.
pub struct KIdent {
    /// Bits 8 and 7 of the first identifier octet (Table 2).
    pub class_bits: u8,
    /// Whether the encoding is constructed (bit 6).
    pub constructed: bool,
    /// The tag number.
    pub number: nat,
}

/// The high tag number's digits starting at octet `i`: "base 128, most
/// significant digit first, with as few digits as possible, and with the bit
/// 8 of each octet except the last set to 1". `first` is whether octet `i`
/// is the leading digit, which may not be zero (the "as few digits as
/// possible" rule). Returns the number and the index after the last octet.
pub open spec fn k_high_tag(b: Seq<u8>, i: nat, end: nat, acc: nat, first: bool) -> Option<(nat, nat)>
    decreases end - i,
{
    if i >= end {
        None
    } else {
        let o = b[i as int];
        let digit = (o % 128) as nat;
        if first && digit == 0 {
            None
        } else {
            let acc2 = acc * 128 + digit;
            if o >= 128 {
                k_high_tag(b, i + 1, end, acc2, false)
            } else {
                Some((acc2, i + 1))
            }
        }
    }
}

/// The identifier at octet `i`, and the index after it.
pub open spec fn k_ident(b: Seq<u8>, i: nat, end: nat) -> Option<(KIdent, nat)> {
    if i >= end {
        None
    } else {
        let o = b[i as int];
        let class_bits = o / 64;
        let constructed = (o / 32) % 2 == 1;
        let low = (o % 32) as nat;
        if low < 31 {
            // Low-tag-number form.
            Some((KIdent { class_bits, constructed, number: low }, i + 1))
        } else {
            // High-tag-number form: tag numbers 31 and greater.
            match k_high_tag(b, i + 1, end, 0, true) {
                Some((number, next)) => {
                    // 31 and greater; and below 2^14, a limit of this
                    // project.
                    if number >= 31 && number < 16384 {
                        Some((KIdent { class_bits, constructed, number }, next))
                    } else {
                        None
                    }
                },
                None => None,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §3.1 and §4: length octets.
// ---------------------------------------------------------------------------

/// The number of base-256 digits "with the minimum number of octets" that
/// spell `v`.
pub open spec fn k_octets_for(v: nat) -> nat
    decreases v,
{
    if v < 256 {
        1
    } else {
        1 + k_octets_for(v / 256)
    }
}

/// The length at octet `i`: its value and the index after it. DER: short
/// form for 0 to 127; for 128 and above the long form with the minimum
/// number of octets; never the indefinite form.
pub open spec fn k_length(b: Seq<u8>, i: nat, end: nat) -> Option<(nat, nat)> {
    if i >= end {
        None
    } else {
        let first = b[i as int];
        if first < 128 {
            // Short form: bit 8 is zero and bits 7-1 give the length.
            Some((first as nat, i + 1))
        } else {
            // Long form: bits 7-1 give the number of additional octets.
            let k = (first - 128) as nat;
            if k == 0 {
                // 0x80 is the indefinite form (§3.3): not DER.
                None
            } else if k > 8 {
                // At most 126 octets in the Guide (so never 0xFF); this
                // project stops at 8.
                None
            } else if i + 1 + k > end {
                None
            } else {
                let v = k_digits(b, i + 1, i + 1 + k, 256, 0);
                // §4: 128 or greater, and "the minimum number of octets".
                if v >= 128 && k == k_octets_for(v) {
                    Some((v, i + 1 + k))
                } else {
                    None
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §3.1: an element, identifier then length then contents.
// ---------------------------------------------------------------------------

/// One element at `i`: its identifier, the contents' first index and the
/// contents' end index (which is also where the next element starts, since
/// DER has no end-of-contents octets).
pub struct KElem {
    /// The identifier.
    pub ident: KIdent,
    /// Index of the first contents octet.
    pub content_start: nat,
    /// Index after the last contents octet.
    pub content_end: nat,
}

/// The element at `i`, definite length, contents inside `end`.
pub open spec fn k_element(b: Seq<u8>, i: nat, end: nat) -> Option<KElem> {
    match k_ident(b, i, end) {
        None => None,
        Some((ident, after_ident)) => match k_length(b, after_ident, end) {
            None => None,
            Some((len, content_start)) => {
                if content_start + len > end {
                    None
                } else {
                    Some(KElem { ident, content_start, content_end: content_start + len })
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// §5.7 INTEGER.
// ---------------------------------------------------------------------------

/// The value of contents octets read as base 256 two's complement, most
/// significant digit first: the first octet counts as negative when its bit
/// 8 is set, and each further octet shifts the running value by one digit.
pub open spec fn k_twos(c: Seq<u8>, j: nat, acc: int) -> int
    decreases c.len() - j,
{
    if j >= c.len() {
        acc
    } else {
        k_twos(c, j + 1, acc * 256 + c[j as int] as int)
    }
}

/// The integer the contents `c` denote (0 for no octets).
pub open spec fn k_integer_value(c: Seq<u8>) -> int {
    if c.len() == 0 {
        0
    } else {
        let first = c[0] as int;
        k_twos(c, 1, if first >= 128 { first - 256 } else { first })
    }
}

/// A measure for [`k_int_bytes`]: the distance of `v` from zero.
pub open spec fn k_abs(v: int) -> nat {
    if v >= 0 { v as nat } else { (-v) as nat }
}

/// "With the minimum number of octets": the shortest base 256 two's
/// complement spelling of `v`. One octet holds -128 to 127; otherwise the
/// spelling of `v` is the spelling of `v` divided by 256 (rounding down)
/// followed by the last digit.
pub open spec fn k_int_bytes(v: int) -> Seq<u8>
    decreases k_abs(v),
{
    if -128 <= v && v < 128 {
        seq![(v % 256) as u8]
    } else {
        k_int_bytes(v / 256) + seq![(v % 256) as u8]
    }
}

/// Contents are a DER INTEGER when they are the minimal spelling of the
/// value they denote ("The value 0 is encoded as a single 00 octet").
pub open spec fn k_integer_ok(c: Seq<u8>) -> bool {
    c.len() >= 1 && c =~= k_int_bytes(k_integer_value(c))
}

// ---------------------------------------------------------------------------
// §5.4 BIT STRING.
// ---------------------------------------------------------------------------

/// 2 to the power of a number of unused bits (0 to 7).
pub open spec fn k_pow2_small(u: u8) -> nat {
    if u == 0 {
        1
    } else if u == 1 {
        2
    } else if u == 2 {
        4
    } else if u == 3 {
        8
    } else if u == 4 {
        16
    } else if u == 5 {
        32
    } else if u == 6 {
        64
    } else {
        128
    }
}

/// Contents of a primitive DER BIT STRING: a first octet giving the unused
/// bits (0 to 7); with no further octets the string is empty and nothing is
/// unused; otherwise the unused bits are the low bits of the last octet,
/// "padded with zero-valued bits".
pub open spec fn k_bitstring_ok(c: Seq<u8>) -> bool {
    c.len() >= 1 && c[0] <= 7 && (c.len() == 1 ==> c[0] == 0) && (c.len() >= 2 ==> (c.last() as nat) % k_pow2_small(
        c[0],
    ) == 0)
}

// ---------------------------------------------------------------------------
// §5.8, §5.10, §5.6, §5.11, §5.17: NULL and the string types.
// ---------------------------------------------------------------------------

/// NULL: "Contents octets are empty".
pub open spec fn k_null_ok(c: Seq<u8>) -> bool {
    c.len() == 0
}

/// OCTET STRING, IA5String, PrintableString, UTCTime: DER requires the
/// primitive form and the contents are the characters, whatever they are.
pub open spec fn k_primitive_string(c: Seq<u8>) -> bool {
    true
}

// ---------------------------------------------------------------------------
// §5.9 OBJECT IDENTIFIER.
// ---------------------------------------------------------------------------

/// The value encoded base 128 at octet `i` of `c`: "most significant digit
/// first, with as few digits as possible, and the most significant bit of
/// each octet except the last set to 1". Returns the value and the index
/// after the last octet.
pub open spec fn k_base128_value(c: Seq<u8>, i: nat, acc: nat, first: bool) -> Option<(nat, nat)>
    decreases c.len() - i,
{
    if i >= c.len() {
        None
    } else {
        let o = c[i as int];
        // "As few digits as possible": a leading digit of zero is only the
        // whole value 0, never a padding digit before more digits.
        if first && o == 128 {
            None
        } else {
            let acc2 = acc * 128 + (o % 128) as nat;
            if o >= 128 {
                k_base128_value(c, i + 1, acc2, false)
            } else {
                Some((acc2, i + 1))
            }
        }
    }
}

/// The values value3, ..., valuen from octet `i` to the end of `c`, after
/// `found`. A value of 2^64 or more is refused (a limit of this project).
pub open spec fn k_rest_values(c: Seq<u8>, i: nat, found: Seq<nat>) -> Option<Seq<nat>>
    decreases c.len() - i,
    via k_rest_values_decreases
{
    if i >= c.len() {
        Some(found)
    } else {
        match k_base128_value(c, i, 0, true) {
            None => None,
            Some((v, next)) => {
                if v >= 0x1_0000_0000_0000_0000 {
                    None
                } else {
                    k_rest_values(c, next, found.push(v))
                }
            },
        }
    }
}

/// A value's digits end after they start and inside `c`.
pub proof fn k_base128_progress(c: Seq<u8>, i: nat, acc: nat, first: bool)
    ensures
        match k_base128_value(c, i, acc, first) {
            Some((_, next)) => i < next && next <= c.len(),
            None => true,
        },
    decreases c.len() - i,
{
    if i < c.len() {
        let o = c[i as int];
        if !(first && o == 128) {
            let acc2 = acc * 128 + (o % 128) as nat;
            if o >= 128 {
                k_base128_progress(c, i + 1, acc2, false);
            }
        }
    }
}

/// Termination of [`k_rest_values`].
#[via_fn]
pub proof fn k_rest_values_decreases(c: Seq<u8>, i: nat, found: Seq<nat>) {
    if i < c.len() {
        k_base128_progress(c, i, 0, true);
    }
}

/// The components of an object identifier whose encoding has a single first
/// octet, as the Guide states it: that octet is `40 * value1 + value2` with
/// `value1` limited to 0, 1 and 2 and `value2` below 40 for 0 and 1; the
/// remaining octets encode value3 to valuen. `None` when the first octet is
/// 128 or more (the Guide's rule does not cover it).
pub open spec fn k_oid(c: Seq<u8>) -> Option<Seq<nat>> {
    if c.len() == 0 || c[0] >= 128 {
        None
    } else {
        let f = c[0] as nat;
        let value1: nat = if f / 40 >= 2 { 2 } else { f / 40 };
        let value2: nat = (f - 40 * value1) as nat;
        k_rest_values(c, 1, seq![value1, value2])
    }
}

// ---------------------------------------------------------------------------
// §5: the types, as an element with the right identifier and contents.
// ---------------------------------------------------------------------------

/// The element at `i`, required to be universal class (bits 00), of the
/// given form and number.
pub open spec fn k_expect_universal(b: Seq<u8>, i: nat, end: nat, constructed: bool, number: nat) -> Option<KElem> {
    match k_element(b, i, end) {
        None => None,
        Some(e) => {
            if e.ident.class_bits == 0 && e.ident.constructed == constructed && e.ident.number == number {
                Some(e)
            } else {
                None
            }
        },
    }
}

/// The element at `i`, required to be context-specific (bits 10) with the
/// given number. §5.1: for an implicitly tagged type the form is the
/// underlying type's, so it is returned for the caller to inspect; §5.2: an
/// explicitly tagged type is constructed.
pub open spec fn k_expect_context(b: Seq<u8>, i: nat, end: nat, number: nat) -> Option<KElem> {
    match k_element(b, i, end) {
        None => None,
        Some(e) => {
            if e.ident.class_bits == 2 && e.ident.number == number {
                Some(e)
            } else {
                None
            }
        },
    }
}

/// An INTEGER (§5.7): a primitive universal element of tag number 2 whose
/// contents satisfy [`k_integer_ok`].
pub open spec fn k_read_integer(b: Seq<u8>, i: nat, end: nat) -> Option<KElem> {
    match k_expect_universal(b, i, end, false, 2) {
        None => None,
        Some(e) => {
            if k_integer_ok(b.subrange(e.content_start as int, e.content_end as int)) {
                Some(e)
            } else {
                None
            }
        },
    }
}

/// A BIT STRING (§5.4): tag number 3, contents satisfying [`k_bitstring_ok`].
pub open spec fn k_read_bit_string(b: Seq<u8>, i: nat, end: nat) -> Option<KElem> {
    match k_expect_universal(b, i, end, false, 3) {
        None => None,
        Some(e) => {
            if k_bitstring_ok(b.subrange(e.content_start as int, e.content_end as int)) {
                Some(e)
            } else {
                None
            }
        },
    }
}

/// NULL (§5.8): tag number 5, no contents.
pub open spec fn k_read_null(b: Seq<u8>, i: nat, end: nat) -> Option<KElem> {
    match k_expect_universal(b, i, end, false, 5) {
        None => None,
        Some(e) => {
            if k_null_ok(b.subrange(e.content_start as int, e.content_end as int)) {
                Some(e)
            } else {
                None
            }
        },
    }
}

/// A string type in the primitive form (§5.10 OCTET STRING is number 4,
/// §5.11 PrintableString 19, §5.6 IA5String 22, §5.17 UTCTime 23).
pub open spec fn k_read_string(b: Seq<u8>, i: nat, end: nat, number: nat) -> Option<KElem> {
    match k_expect_universal(b, i, end, false, number) {
        None => None,
        Some(e) => {
            if k_primitive_string(b.subrange(e.content_start as int, e.content_end as int)) {
                Some(e)
            } else {
                None
            }
        },
    }
}


// ===========================================================================
// The two transcriptions agree.
//
// What is proven, and on what class of inputs. The Guide covers INTEGER,
// BIT STRING, NULL, OCTET STRING, IA5String, PrintableString, UTCTime,
// OBJECT IDENTIFIER, SEQUENCE, SET and tagged types (not BOOLEAN, UTF8String
// or GeneralizedTime), so these are the types compared.
//
// - Identifier octets, length octets and the framing of an element: on every
//   input (`lemma_ident_equiv`, `lemma_length_equiv`, `lemma_element_equiv`).
// - INTEGER, BIT STRING and NULL contents: on every contents
//   (`lemma_integer_equiv`, `lemma_bitstring_equiv`, `lemma_null_equiv`).
// - OBJECT IDENTIFIER contents: on those whose first octet is below 128,
//   where the Guide's "first octet is 40 * value1 + value2" applies
//   (`lemma_oid_equiv`). For a first octet of 128 or more the Guide's rule
//   does not say how the first two components are encoded, so there is
//   nothing to compare.
// - The typed readers, built from the above, for the types listed: on every
//   input (`lemma_read_integer_equiv` and the others below).
// ===========================================================================

/// 128 to the power `n`.
pub open spec fn k_pow128(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        128 * k_pow128((n - 1) as nat)
    }
}

/// A base 128 number splits into its first digit, weighed by the number of
/// digits after it, and the number the rest spells.
pub proof fn lemma_k_cons128(b: Seq<u8>, from: nat, to: nat)
    requires
        from < to <= b.len(),
    ensures
        base128(b.subrange(from as int, to as int)) == (b[from as int] % 128) as nat * k_pow128((to - from - 1) as nat)
            + base128(b.subrange(from as int + 1, to as int)),
    decreases to - from,
{
    let s = b.subrange(from as int, to as int);
    if to - from == 1 {
        assert(b.subrange(from as int + 1, to as int) =~= Seq::<u8>::empty());
        assert(s =~= seq![b[from as int]]);
        super::lemmas_tlv::lemma_base128_single(b[from as int]);
        assert((to - from - 1) as nat == 0nat);
        assert(k_pow128(0) == 1);
        assert(base128(Seq::<u8>::empty()) == 0);
    } else {
        let t = (to - 1) as nat;
        assert(s.drop_last() =~= b.subrange(from as int, t as int));
        lemma_k_cons128(b, from, t);
        let tail = b.subrange(from as int + 1, to as int);
        assert(tail.drop_last() =~= b.subrange(from as int + 1, t as int));
        assert(s.last() == b[t as int]);
        assert(tail.last() == b[t as int]);
        let d = (b[from as int] % 128) as nat;
        let p = k_pow128((to - from - 2) as nat);
        let r = base128(b.subrange(from as int + 1, t as int));
        let l = (b[t as int] % 128) as nat;
        assert((t - from - 1) as nat == (to - from - 2) as nat);
        assert(base128(s) == base128(b.subrange(from as int, t as int)) * 128 + l);
        assert(base128(tail) == r * 128 + l);
        assert(base128(b.subrange(from as int, t as int)) == d * p + r);
        assert(k_pow128((to - from - 1) as nat) == 128 * p);
        assert((d * p + r) * 128 + l == d * (128 * p) + (r * 128 + l)) by (nonlinear_arith);
    }
}

/// The same for base 256.
pub proof fn lemma_k_cons256(b: Seq<u8>, from: nat, to: nat)
    requires
        from < to <= b.len(),
    ensures
        be_value(b.subrange(from as int, to as int)) == b[from as int] as nat * pow256((to - from - 1) as nat) + be_value(
            b.subrange(from as int + 1, to as int),
        ),
    decreases to - from,
{
    let s = b.subrange(from as int, to as int);
    if to - from == 1 {
        assert(b.subrange(from as int + 1, to as int) =~= Seq::<u8>::empty());
        assert(s =~= seq![b[from as int]]);
        super::lemmas_typed::lemma_be_value_single(b[from as int]);
        assert((to - from - 1) as nat == 0nat);
        assert(pow256(0) == 1);
        assert(be_value(Seq::<u8>::empty()) == 0);
    } else {
        let t = (to - 1) as nat;
        assert(s.drop_last() =~= b.subrange(from as int, t as int));
        lemma_k_cons256(b, from, t);
        let tail = b.subrange(from as int + 1, to as int);
        assert(tail.drop_last() =~= b.subrange(from as int + 1, t as int));
        assert(s.last() == b[t as int]);
        assert(tail.last() == b[t as int]);
        let d = b[from as int] as nat;
        let p = pow256((to - from - 2) as nat);
        let r = be_value(b.subrange(from as int + 1, t as int));
        let l = b[t as int] as nat;
        assert((t - from - 1) as nat == (to - from - 2) as nat);
        assert(be_value(s) == be_value(b.subrange(from as int, t as int)) * 256 + l);
        assert(be_value(tail) == r * 256 + l);
        assert(be_value(b.subrange(from as int, t as int)) == d * p + r);
        assert(pow256((to - from - 1) as nat) == 256 * p);
        assert((d * p + r) * 256 + l == d * (256 * p) + (r * 256 + l)) by (nonlinear_arith);
    }
}

/// Folding base 256 digits from the left, from `acc`, is `acc` shifted by
/// the digits plus the number they spell.
pub proof fn lemma_k_digits256(b: Seq<u8>, from: nat, to: nat, acc: nat)
    requires
        from <= to <= b.len(),
    ensures
        k_digits(b, from, to, 256, acc) == acc * pow256((to - from) as nat) + be_value(b.subrange(from as int, to as int)),
    decreases to - from,
{
    if from == to {
        assert(b.subrange(from as int, to as int) =~= Seq::<u8>::empty());
    } else {
        let o = b[from as int] as nat;
        lemma_k_digits256(b, from + 1, to, acc * 256 + o);
        lemma_k_cons256(b, from, to);
        let p = pow256((to - from - 1) as nat);
        let r = be_value(b.subrange(from as int + 1, to as int));
        assert(pow256((to - from) as nat) == 256 * p);
        assert((acc * 256 + o) * p + r == acc * (256 * p) + (o * p + r)) by (nonlinear_arith);
    }
}

/// A high tag number's digits: the series ends where the standard's does,
/// and the number is the digits' base 128 value (shifted by what came
/// before).
pub proof fn lemma_k_high_tag_run(b: Seq<u8>, i: nat, end: nat, acc: nat, first: bool)
    requires
        end <= b.len(),
    ensures
        k_high_tag(b, i, end, acc, first) == match series_end(b, i, end) {
            None => None,
            Some(j) => {
                if first && b[i as int] % 128 == 0 {
                    None
                } else {
                    Some((acc * k_pow128((j - i + 1) as nat) + base128(b.subrange(i as int, j as int + 1)), j + 1))
                }
            },
        },
    decreases end - i,
{
    if i < end {
        let o = b[i as int];
        if o < 128 {
            assert(b.subrange(i as int, i as int + 1) =~= seq![o]);
            super::lemmas_tlv::lemma_base128_single(o);
            assert(series_end(b, i, end) == Some(i));
            assert(k_pow128(0) == 1);
            assert(k_pow128(1) == 128);
            assert((i - i + 1) as nat == 1nat);
        } else {
            let acc2 = acc * 128 + (o % 128) as nat;
            lemma_k_high_tag_run(b, i + 1, end, acc2, false);
            super::lemmas_oid::lemma_series_end_props(b, i + 1, end);
            if let Some(j) = series_end(b, i + 1, end) {
                lemma_k_cons128(b, i, j + 1);
                let p = k_pow128((j - i) as nat);
                let d = (o % 128) as nat;
                assert(k_pow128((j - i + 1) as nat) == 128 * p);
                assert((acc * 128 + d) * p == acc * (128 * p) + d * p) by (nonlinear_arith);
            }
        }
    }
}

/// An OBJECT IDENTIFIER's value: the same for the series at `i` of `c`.
pub proof fn lemma_k_base128_run(c: Seq<u8>, i: nat, acc: nat, first: bool)
    ensures
        k_base128_value(c, i, acc, first) == match series_end(c, i, c.len()) {
            None => None,
            Some(j) => {
                if first && c[i as int] == 128 {
                    None
                } else {
                    Some((acc * k_pow128((j - i + 1) as nat) + base128(c.subrange(i as int, j as int + 1)), j + 1))
                }
            },
        },
    decreases c.len() - i,
{
    if i < c.len() {
        let o = c[i as int];
        if o < 128 {
            assert(c.subrange(i as int, i as int + 1) =~= seq![o]);
            super::lemmas_tlv::lemma_base128_single(o);
            assert(series_end(c, i, c.len()) == Some(i));
            assert(k_pow128(0) == 1);
            assert(k_pow128(1) == 128);
            assert((i - i + 1) as nat == 1nat);
        } else {
            let acc2 = acc * 128 + (o % 128) as nat;
            lemma_k_base128_run(c, i + 1, acc2, false);
            super::lemmas_oid::lemma_series_end_props(c, i + 1, c.len());
            if let Some(j) = series_end(c, i + 1, c.len()) {
                lemma_k_cons128(c, i, j + 1);
                let p = k_pow128((j - i) as nat);
                let d = (o % 128) as nat;
                assert(k_pow128((j - i + 1) as nat) == 128 * p);
                assert((acc * 128 + d) * p == acc * (128 * p) + d * p) by (nonlinear_arith);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Identifier octets.
// ---------------------------------------------------------------------------

/// The Guide's identifier octets and the standard's agree on every input:
/// the same class bits, form and number, ending at the same index.
pub proof fn lemma_ident_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_identifier(b, i, end) {
            Some((tag, n)) => k_ident(b, i, end) == Some(
                (
                    KIdent { class_bits: class_bits(tag.class), constructed: tag.constructed, number: tag.number as nat },
                    i + n,
                ),
            ),
            None => k_ident(b, i, end) is None,
        },
{
    if i < end {
        let o = b[i as int];
        assert(o / 64 <= 3);
        super::lemmas_tlv::lemma_class_from_bits_roundtrip(o / 64);
        if o % 32 == 31 {
            lemma_k_high_tag_run(b, i + 1, end, 0, true);
            super::lemmas::lemma_series_end_in_range(b, i + 1, end);
            if let Some(j) = series_end(b, i + 1, end) {
                assert(0 * k_pow128((j - (i + 1) + 1) as nat) == 0);
                let number = base128(b.subrange(i as int + 1, j as int + 1));
                assert(b[i as int + 1] == b[(i + 1) as int]);
                assert(k_high_tag(b, i + 1, end, 0, true) == if b[(i + 1) as int] % 128 == 0 {
                    None
                } else {
                    Some((number, j + 1))
                });
            }
        } else {
            assert(class_bits(class_from_bits(o / 64)) == o / 64);
        }
    }
}

// ---------------------------------------------------------------------------
// Length octets.
// ---------------------------------------------------------------------------

/// A number below 256^m takes at most m octets, and one of at least
/// 256^(m-1) takes exactly m.
pub proof fn lemma_octets_for_bounds(v: nat, m: nat)
    requires
        m >= 1,
    ensures
        v < pow256(m) ==> k_octets_for(v) <= m,
        (v >= pow256((m - 1) as nat) && v < pow256(m)) ==> k_octets_for(v) == m,
    decreases m,
{
    super::lemmas::lemma_pow256_8();
    assert(pow256(1) == 256);
    assert(pow256(0) == 1);
    if m >= 2 {
        let p = pow256((m - 1) as nat);
        assert(pow256(m) == 256 * p);
        lemma_octets_for_bounds(v / 256, (m - 1) as nat);
        super::lemmas_tlv::lemma_pow256_monotone(1, (m - 1) as nat);
        assert(pow256((m - 1) as nat) == 256 * pow256((m - 2) as nat));
    }
}

/// The Guide's length octets and the standard's agree on every input.
pub proof fn lemma_length_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_length(b, i, end) {
            Some((v, n)) => k_length(b, i, end) == Some((v, i + n)),
            None => k_length(b, i, end) is None,
        },
{
    super::lemmas::lemma_pow256_8();
    if i < end {
        let f = b[i as int];
        if f >= 129 && f <= 136 && i + 1 + ((f - 128) as nat) <= end {
            let k = (f - 128) as nat;
            let sub = b.subrange(i as int + 1, i as int + 1 + k as int);
            lemma_k_digits256(b, i + 1, i + 1 + k, 0);
            assert(0 * pow256(k) == 0);
            let v = be_value(sub);
            super::lemmas::lemma_be_value_bound(sub);
            assert(sub[0] == b[i as int + 1]);
            lemma_octets_for_bounds(v, k);
            if sub[0] != 0 {
                super::lemmas_tlv::lemma_be_value_leading_nonzero(sub);
            } else {
                super::lemmas_tlv::lemma_be_value_leading_zero(sub);
                if k >= 2 {
                    lemma_octets_for_bounds(v, (k - 1) as nat);
                } else {
                    assert(pow256(0) == 1);
                    assert(v == 0);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// An element.
// ---------------------------------------------------------------------------

/// The Guide's element and the standard's value agree on every input: same
/// identifier, same contents range.
pub proof fn lemma_element_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_tlv(b, i, end) {
            Some(t) => k_element(b, i, end) == Some(
                KElem {
                    ident: KIdent { class_bits: class_bits(t.tag.class), constructed: t.tag.constructed, number: t.tag.number as nat },
                    content_start: t.cstart,
                    content_end: t.cend,
                },
            ),
            None => k_element(b, i, end) is None,
        },
{
    lemma_ident_equiv(b, i, end);
    if let Some((tag, id_len)) = read_identifier(b, i, end) {
        super::lemmas::lemma_read_identifier_bounds(b, i, end);
        lemma_length_equiv(b, i + id_len, end);
    }
}

// ---------------------------------------------------------------------------
// INTEGER contents.
// ---------------------------------------------------------------------------

/// The running value of the fold over the contents, when the last octet is
/// appended, shifts by one digit.
pub proof fn lemma_k_twos_push(d: Seq<u8>, x: u8, j: nat, a: int)
    requires
        j <= d.len(),
    ensures
        k_twos(d.push(x), j, a) == k_twos(d, j, a) * 256 + x as int,
    decreases d.len() - j,
{
    if j < d.len() {
        assert(d.push(x)[j as int] == d[j as int]);
        lemma_k_twos_push(d, x, j + 1, a * 256 + d[j as int] as int);
    } else {
        assert(d.push(x)[j as int] == x);
        assert(k_twos(d, j, a) == a);
        assert(k_twos(d.push(x), j, a) == k_twos(d.push(x), j + 1, a * 256 + x as int));
        assert(k_twos(d.push(x), j + 1, a * 256 + x as int) == a * 256 + x as int);
    }
}

/// The integer value of contents with one more octet appended.
pub proof fn lemma_k_value_push(d: Seq<u8>, x: u8)
    requires
        d.len() >= 1,
    ensures
        k_integer_value(d.push(x)) == k_integer_value(d) * 256 + x as int,
{
    assert(d.push(x)[0] == d[0]);
    lemma_k_twos_push(d, x, 1, if d[0] >= 128 { d[0] as int - 256 } else { d[0] as int });
}

/// Dropping the first octet shifts the fold's index.
pub proof fn lemma_k_twos_shift(c: Seq<u8>, j: nat, acc: int)
    requires
        c.len() >= 1,
    ensures
        k_twos(c.skip(1), j, acc) == k_twos(c, j + 1, acc),
    decreases c.len() - j,
{
    if j + 1 < c.len() {
        assert(c.skip(1)[j as int] == c[j as int + 1]);
        lemma_k_twos_shift(c, j + 1, acc * 256 + c[j as int + 1] as int);
    }
}

/// One octet spells its signed value, and that value is spelled by that
/// one octet alone.
pub proof fn lemma_k_single(c: Seq<u8>)
    requires
        c.len() == 1,
    ensures
        k_integer_value(c) == (if c[0] >= 128 { c[0] as int - 256 } else { c[0] as int }),
        -128 <= k_integer_value(c) < 128,
        c =~= k_int_bytes(k_integer_value(c)),
{
    let v = k_integer_value(c);
    assert(v == (if c[0] >= 128 { c[0] as int - 256 } else { c[0] as int }));
    assert((v % 256) as u8 == c[0]);
}

/// The minimal spelling of a value is never longer than any spelling of it.
pub proof fn lemma_k_int_bytes_len(t: Seq<u8>)
    requires
        t.len() >= 1,
    ensures
        k_int_bytes(k_integer_value(t)).len() <= t.len(),
    decreases t.len(),
{
    if t.len() == 1 {
        lemma_k_single(t);
    } else {
        let d = t.drop_last();
        let last = t.last();
        assert(t =~= d.push(last));
        lemma_k_value_push(d, last);
        lemma_k_int_bytes_len(d);
        let v = k_integer_value(t);
        if !(-128 <= v && v < 128) {
            let vd = k_integer_value(d);
            assert(v / 256 == vd) by (nonlinear_arith)
                requires
                    v == vd * 256 + last as int,
                    0 <= last < 256,
            ;
        }
    }
}

/// A leading octet that only repeats the sign of the next one does not
/// change the value.
pub proof fn lemma_k_leading(c: Seq<u8>)
    requires
        c.len() >= 2,
        (c[0] == 0 && c[1] < 128) || (c[0] == 255 && c[1] >= 128),
    ensures
        k_integer_value(c) == k_integer_value(c.skip(1)),
{
    let tail = c.skip(1);
    assert(tail[0] == c[1]);
    lemma_k_twos_shift(c, 1, if c[1] >= 128 { c[1] as int - 256 } else { c[1] as int });
    assert(k_twos(c, 1, if c[0] >= 128 { c[0] as int - 256 } else { c[0] as int }) == k_twos(
        c,
        2,
        (if c[0] >= 128 { c[0] as int - 256 } else { c[0] as int }) * 256 + c[1] as int,
    ));
}

/// The Guide's INTEGER rule (the contents are the minimal two's complement
/// spelling of their value) and the standard's (X.690 8.3.2: no redundant
/// first octet) accept exactly the same contents.
pub proof fn lemma_integer_equiv(c: Seq<u8>)
    ensures
        k_integer_ok(c) == integer_contents_ok(c),
    decreases c.len(),
{
    if c.len() == 1 {
        lemma_k_single(c);
    } else if c.len() >= 2 {
        let d = c.drop_last();
        let last = c.last();
        assert(c =~= d.push(last));
        lemma_k_value_push(d, last);
        let v = k_integer_value(c);
        let vd = k_integer_value(d);
        let bad = (c[0] == 0 && c[1] < 128) || (c[0] == 255 && c[1] >= 128);
        if bad {
            // Not minimal: the tail alone spells the same value.
            lemma_k_leading(c);
            lemma_k_int_bytes_len(c.skip(1));
            assert(c.skip(1).len() == c.len() - 1);
        } else {
            lemma_integer_equiv(d);
            assert(d.len() >= 1);
            if d.len() >= 2 {
                assert(d[0] == c[0]);
                assert(d[1] == c[1]);
            }
            // d is minimal and so is c.
            assert(integer_contents_ok(d));
            assert(k_integer_ok(d));
            assert(d =~= k_int_bytes(vd));
            if vd == 0 {
                assert(d =~= seq![0u8]);
                assert(c =~= seq![0u8, last]);
                assert(last >= 128);
            }
            if vd == -1 {
                assert(d =~= seq![255u8]);
                assert(c =~= seq![255u8, last]);
                assert(last < 128);
            }
            assert(!(-128 <= v && v < 128));
            assert(v / 256 == vd) by (nonlinear_arith)
                requires
                    v == vd * 256 + last as int,
                    0 <= last < 256,
            ;
            assert(v % 256 == last as int) by (nonlinear_arith)
                requires
                    v == vd * 256 + last as int,
                    0 <= last < 256,
            ;
            assert(c =~= k_int_bytes(vd) + seq![last]);
        }
    }
}

// ---------------------------------------------------------------------------
// BIT STRING and NULL contents.
// ---------------------------------------------------------------------------

/// The Guide's BIT STRING rule and the standard's accept the same contents.
pub proof fn lemma_bitstring_equiv(c: Seq<u8>)
    ensures
        k_bitstring_ok(c) == bit_string_contents_ok(c),
{
    if c.len() >= 1 {
        assert(k_pow2_small(c[0]) == pow2_unused(c[0]));
    }
}

/// The Guide's NULL rule and the standard's accept the same contents: none.
pub proof fn lemma_null_equiv(c: Seq<u8>)
    ensures
        k_null_ok(c) == (c.len() == 0),
{
}

// ---------------------------------------------------------------------------
// OBJECT IDENTIFIER contents.
// ---------------------------------------------------------------------------

/// The Guide's list of values value3 to valuen after `found`, read from
/// octet `i`, is `found` followed by the standard's subidentifiers of the
/// rest.
pub proof fn lemma_k_rest_values(c: Seq<u8>, i: nat, found: Seq<nat>)
    requires
        i <= c.len(),
    ensures
        k_rest_values(c, i, found) == match subidentifiers(c.skip(i as int)) {
            None => None,
            Some(rest) => Some(found + rest),
        },
    decreases c.len() - i,
{
    if i >= c.len() {
        assert(c.skip(i as int) =~= Seq::<u8>::empty());
        assert(found + Seq::<nat>::empty() =~= found);
    } else {
        super::lemmas::lemma_subidentifiers_step(c, i);
        lemma_k_base128_run(c, i, 0, true);
        super::lemmas_oid::lemma_series_end_props(c, i, c.len());
        if let Some(j) = series_end(c, i, c.len()) {
            let v = base128(c.subrange(i as int, j as int + 1));
            assert(0 * k_pow128((j - i + 1) as nat) == 0);
            if c[i as int] != 128 && v < 0x1_0000_0000_0000_0000 {
                lemma_k_rest_values(c, j + 1, found.push(v));
                if let Some(rest) = subidentifiers(c.skip(j as int + 1)) {
                    assert(found.push(v) + rest =~= found + (seq![v] + rest));
                }
            }
        }
    }
}

/// The Guide's object identifier rule (first octet `40 * value1 + value2`,
/// the others base 128) and the standard's (§8.19.2 to §8.19.5) give the same
/// components, for contents whose first octet is below 128: the case the
/// Guide's rule states.
pub proof fn lemma_oid_equiv(c: Seq<u8>)
    requires
        c.len() >= 1,
        c[0] < 128,
    ensures
        k_oid(c) == oid_components(c),
{
    let f = c[0] as nat;
    super::lemmas::lemma_subidentifiers_step(c, 0);
    assert(c.skip(0) =~= c);
    assert(c.subrange(0, 1) =~= seq![c[0]]);
    super::lemmas_tlv::lemma_base128_single(c[0]);
    assert(series_end(c, 0, c.len()) == Some(0nat));
    lemma_k_rest_values(c, 1, seq![if f / 40 >= 2 { 2nat } else { f / 40 }, (f - 40 * (if f / 40 >= 2 { 2nat } else { f / 40 })) as nat]);
    if let Some(rest) = subidentifiers(c.skip(1)) {
        let subs = seq![f] + rest;
        assert(subs.skip(1) =~= rest);
        assert(subs[0] == f);
    }
}

// ---------------------------------------------------------------------------
// The typed readers.
// ---------------------------------------------------------------------------

/// The standard's tag is universal and primitive of number `n` exactly when
/// the Guide's identifier says so.
proof fn lemma_tag_is_universal(tag: Tag, constructed: bool, n: u32)
    ensures
        (tag == Tag { class: Class::Universal, constructed, number: n }) == (class_bits(tag.class) == 0 && tag.constructed
            == constructed && tag.number as nat == n as nat),
{
}

/// An INTEGER read by the Guide's rules is read by the standard's, and the
/// other way round, from every input, with the same extent.
pub proof fn lemma_read_integer_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_integer(b, i, end), k_read_integer(b, i, end)) {
            (Some((_, _, me, next)), Some(e)) => me == e.content_end && next == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_element_equiv(b, i, end);
    if let Some(t) = read_tlv(b, i, end) {
        lemma_tag_is_universal(t.tag, false, 2);
        super::lemmas::lemma_read_tlv_bounds(b, i, end);
        lemma_integer_equiv(b.subrange(t.cstart as int, t.cend as int));
    }
}

/// A BIT STRING read by the Guide's rules is read by the standard's, and
/// the other way round, from every input, with the same extent.
pub proof fn lemma_read_bit_string_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_bit_string(b, i, end), k_read_bit_string(b, i, end)) {
            (Some((_, _, me, next)), Some(e)) => me == e.content_end && next == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_element_equiv(b, i, end);
    if let Some(t) = read_tlv(b, i, end) {
        lemma_tag_is_universal(t.tag, false, 3);
        super::lemmas::lemma_read_tlv_bounds(b, i, end);
        lemma_bitstring_equiv(b.subrange(t.cstart as int, t.cend as int));
    }
}

/// A NULL read by the Guide's rules is read by the standard's, and the
/// other way round, from every input, with the same extent.
pub proof fn lemma_read_null_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_null(b, i, end), k_read_null(b, i, end)) {
            (Some(next), Some(e)) => next == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_element_equiv(b, i, end);
    if let Some(t) = read_tlv(b, i, end) {
        lemma_tag_is_universal(t.tag, false, 5);
        super::lemmas::lemma_read_tlv_bounds(b, i, end);
        lemma_null_equiv(b.subrange(t.cstart as int, t.cend as int));
    }
}

/// An OCTET STRING, PrintableString, IA5String or UTCTime (numbers 4, 19,
/// 22 and 23) read by the Guide's rules is read by the standard's, and the
/// other way round, from every input, with the same contents range.
pub proof fn lemma_read_string_equiv(b: Seq<u8>, i: nat, end: nat, number: u32)
    requires
        end <= b.len(),
        number == 4 || number == 19 || number == 22 || number == 23,
    ensures
        match (read_octets(b, i, end, number), k_read_string(b, i, end, number as nat)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_element_equiv(b, i, end);
    if let Some(t) = read_tlv(b, i, end) {
        lemma_tag_is_universal(t.tag, false, number);
    }
}

/// A SEQUENCE (number 16) or SET (number 17) read by the Guide's rules is
/// read by the standard's, and the other way round, from every input, with
/// the same contents range.
pub proof fn lemma_expect_constructed_equiv(b: Seq<u8>, i: nat, end: nat, number: u32)
    requires
        end <= b.len(),
        number == 16 || number == 17,
    ensures
        match (expect_constructed(b, i, end, number), k_expect_universal(b, i, end, true, number as nat)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_element_equiv(b, i, end);
    if let Some(t) = read_tlv(b, i, end) {
        lemma_tag_is_universal(t.tag, true, number);
    }
}

/// A component with a context-specific tag `[number]`: the Guide finds it
/// exactly when the standard's optional-component reader does, with the
/// same form and contents range. (An absent component is "no element" to
/// the Guide's reader, so only the present case is compared.)
pub proof fn lemma_context_equiv(b: Seq<u8>, i: nat, end: nat, number: u32)
    requires
        end <= b.len(),
    ensures
        match k_expect_context(b, i, end, number as nat) {
            Some(e) => read_optional_context(b, i, end, number) == Some(Some((e.ident.constructed, e.content_start, e.content_end))),
            None => !(read_optional_context(b, i, end, number) matches Some(Some(_))),
        },
{
    lemma_element_equiv(b, i, end);
    lemma_ident_equiv(b, i, end);
    if i < end {
        if let Some((tag, n)) = read_identifier(b, i, end) {
            super::lemmas::lemma_read_identifier_bounds(b, i, end);
            assert(class_bits(tag.class) == 2 <==> tag.class == Class::ContextSpecific);
        }
    }
}


/// An OBJECT IDENTIFIER (§5.9): a primitive universal element of tag number
/// 6 whose contents [`k_oid`] reads.
pub open spec fn k_read_oid(b: Seq<u8>, i: nat, end: nat) -> Option<(Seq<nat>, nat)> {
    match k_expect_universal(b, i, end, false, 6) {
        None => None,
        Some(e) => match k_oid(b.subrange(e.content_start as int, e.content_end as int)) {
            Some(arcs) => Some((arcs, e.content_end)),
            None => None,
        },
    }
}

/// An OBJECT IDENTIFIER read by the Guide's rules is read by the standard's,
/// and the other way round, with the same components and extent, for every
/// input whose contents (if it is an element at all) are empty or begin with
/// an octet below 128: the case where the Guide's first-octet rule applies.
pub proof fn lemma_read_oid_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
        read_tlv(b, i, end) matches Some(t) ==> (t.cstart == t.cend || b[t.cstart as int] < 128),
    ensures
        match (read_oid(b, i, end), k_read_oid(b, i, end)) {
            (Some((arcs, next)), Some((arcs2, next2))) => arcs == arcs2 && next == next2,
            (None, None) => true,
            _ => false,
        },
{
    lemma_element_equiv(b, i, end);
    if let Some(t) = read_tlv(b, i, end) {
        lemma_tag_is_universal(t.tag, false, 6);
        super::lemmas::lemma_read_tlv_bounds(b, i, end);
        let c = b.subrange(t.cstart as int, t.cend as int);
        if t.tag == universal_primitive(OBJECT_IDENTIFIER) {
            if t.cstart < t.cend {
                assert(c[0] == b[t.cstart as int]);
                lemma_oid_equiv(c);
            } else {
                assert(c =~= Seq::<u8>::empty());
            }
        }
    }
}

/// The wrappers that fix a universal tag number agree with the Guide's
/// reader at that number: an OCTET STRING (4).
pub proof fn lemma_read_octet_string_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_octet_string(b, i, end), k_read_string(b, i, end, 4)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_read_string_equiv(b, i, end, 4);
}

/// A PrintableString (19).
pub proof fn lemma_read_printable_string_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_printable_string(b, i, end), k_read_string(b, i, end, 19)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_read_string_equiv(b, i, end, 19);
}

/// An IA5String (22).
pub proof fn lemma_read_ia5_string_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_ia5_string(b, i, end), k_read_string(b, i, end, 22)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_read_string_equiv(b, i, end, 22);
}

/// A UTCTime (23).
pub proof fn lemma_read_utc_time_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (read_utc_time(b, i, end), k_read_string(b, i, end, 23)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_read_string_equiv(b, i, end, 23);
}

/// A SEQUENCE (16).
pub proof fn lemma_expect_sequence_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (expect_sequence(b, i, end), k_expect_universal(b, i, end, true, 16)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_expect_constructed_equiv(b, i, end, 16);
}

/// A SET (17).
pub proof fn lemma_expect_set_equiv(b: Seq<u8>, i: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match (expect_set(b, i, end), k_expect_universal(b, i, end, true, 17)) {
            (Some((cs, ce)), Some(e)) => cs == e.content_start && ce == e.content_end,
            (None, None) => true,
            _ => false,
        },
{
    lemma_expect_constructed_equiv(b, i, end, 17);
}


/// The value the standard gives the contents (§8.3.3, "a two's complement
/// binary number": the octets' number, less 256^n if bit 8 of the first is
/// set) and the value the Guide gives them (§5.7, base 256 two's complement,
/// most significant digit first) are the same number, for every contents.
pub proof fn lemma_integer_value_equiv(c: Seq<u8>)
    ensures
        integer_value(c) == k_integer_value(c),
    decreases c.len(),
{
    if c.len() == 1 {
        lemma_k_single(c);
        assert(c =~= seq![c[0]]);
        super::lemmas_typed::lemma_be_value_single(c[0]);
        assert(pow256(1) == 256 * pow256(0));
        assert(pow256(0) == 1);
    } else if c.len() >= 2 {
        let d = c.drop_last();
        let last = c.last();
        assert(c =~= d.push(last));
        lemma_integer_value_equiv(d);
        lemma_k_value_push(d, last);
        assert(d[0] == c[0]);
        assert(be_value(c) == be_value(d) * 256 + last as nat);
        assert(pow256(c.len()) == 256 * pow256(d.len()));
        if c[0] >= 128 {
            assert(integer_value(c) == (be_value(d) as int - pow256(d.len()) as int) * 256 + last as int) by (nonlinear_arith)
                requires
                    integer_value(c) == be_value(c) as int - pow256(c.len()) as int,
                    be_value(c) == be_value(d) * 256 + last as nat,
                    pow256(c.len()) == 256 * pow256(d.len()),
            ;
        }
    }
}

} // verus!
