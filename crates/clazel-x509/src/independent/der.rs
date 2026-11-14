//! DER, transcribed for the independent decoder from Rec. ITU-T X.690 (02/2021)
//! | ISO/IEC 8825-1:2021, clauses 8, 10 and 11 (PDF SHA-256
//! `6ac799a2d1ebed36abe39c9eac3586185bfb7db679f801e737189d6fdb1bbd6c`), with
//! Rec. ITU-T X.680 (02/2021) | ISO/IEC 8824-1:2021, clauses 22, 41, 46 and 47
//! (PDF SHA-256
//! `b69dc4754f0709a7e344c886f277ed9e37a4336029593ba91bc6df6065f9ee14`).
//!
//! Not read while writing this file: see the list in `independent/mod.rs`.
//! That includes `clazel-der`: this file imports nothing from it, and its
//! author did not open its decoder.
//!
//! Modelling choices:
//! - A refusal is `None`. X.690 says what an encoder "shall" do. A decoder
//!   here accepts exactly the octets that a conforming DER encoder can
//!   produce for the type asked for, and refuses all others.
//! - One encoding is a [`Tlv`]: identifier, length and contents octets of
//!   8.1.1.1 a) to c). End-of-contents octets (8.1.1.1 d)) never occur,
//!   because 10.1 requires the definite form.
//! - A tag's class is the number that bits 8 and 7 of the leading octet form
//!   in Table 1 (0 universal, 1 application, 2 context-specific, 3 private).
//! - Numbers are unbounded (`nat`, `int`). X.690 sets no limit on a tag
//!   number, a length, an INTEGER or a subidentifier, so neither does this.
//! - A sequence of encodings is split once into a `Seq<Tlv>`
//!   ([`parse_tlvs`]). The typed decoders then walk that list, which keeps
//!   each ASN.1 type's order of components visible in its decoder.
//! - An OBJECT IDENTIFIER value is its list of components, the two packed
//!   into the first subidentifier unpacked again (8.19.4).
//! - A time keeps its fields. The fraction of a GeneralizedTime stays a list
//!   of digit octets, since 11.7.3 fixes its form and nothing here needs its
//!   value.
//!
//! Open choices, all listed in the pull request:
//! - X.680 46.3 defines GeneralizedTime by reference to ISO 8601, which is
//!   not freely available and was not read. The bound on seconds is taken
//!   from UTCTime's "ss is seconds (00 to 59)" in 47.3, so a leap second
//!   `60` is refused in both types. The day must exist in the month and year
//!   (Gregorian), read from 47.3's "the day of the month", although 47.3
//!   itself writes only "(01 to 31)".
//! - 11.6 says "ascending order". Two equal encodings in a set-of are
//!   accepted, because a set-of value may repeat a value and the rule still
//!   gives them a place.
//! - Universal tag 0 is refused in every encoding: X.680 Table 1 reserves it
//!   for the encoding rules, so no ASN.1 type has it.
//! - An open type's value is checked as one encoding, without looking
//!   inside: the type that would say how to look is not known here.
//! - TeletexString contents are not checked (their repertoire needs ISO 2022
//!   and the register of 8.23.5). The other string types are.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// 8.1 General rules for encoding
// ---------------------------------------------------------------------------

/// Table 1: the class of a tag.
pub open spec fn class_universal() -> nat {
    0
}

/// Table 1.
pub open spec fn class_context() -> nat {
    2
}

/// One complete encoding (8.1.1.1 a) to c)).
pub struct Tlv {
    /// The class of the tag (Table 1).
    pub class: nat,
    /// 8.1.2.5: bit 6 of the leading identifier octet.
    pub constructed: bool,
    /// The number of the tag.
    pub number: nat,
    /// The contents octets.
    pub contents: Seq<u8>,
    /// All octets of the encoding, identifier octets first.
    pub encoding: Seq<u8>,
}

/// The identifier octets (8.1.2).
pub struct Identifier {
    /// The class of the tag (Table 1).
    pub class: nat,
    /// 8.1.2.5: bit 6 of the leading identifier octet.
    pub constructed: bool,
    /// The number of the tag.
    pub number: nat,
    /// How many octets the identifier took.
    pub size: nat,
}

/// 8.1.2.4.2, the subsequent identifier octets, read from `at` with the
/// number so far in `number`.
pub open spec fn high_tag_number(input: Seq<u8>, at: nat, number: nat) -> Option<(nat, nat)>
    decreases input.len() - at,
{
    if at >= input.len() {
        None
    } else {
        let octet = input[at as int];
        // 8.1.2.4.2 c) "bits 7 to 1 of the first subsequent octet shall not
        // all be zero."
        if at == 1 && octet % 128 == 0 {
            None
        } else {
            // 8.1.2.4.2 b) bits 7 to 1 of each octet, most significant first.
            let next = number * 128 + (octet % 128) as nat;
            // 8.1.2.4.2 a) "bit 8 of each octet shall be set to one unless it
            // is the last octet of the identifier octets".
            if octet >= 128 {
                high_tag_number(input, at + 1, next)
            } else {
                Some((next, at + 1))
            }
        }
    }
}

/// 8.1.2, the identifier octets at the start of `input`.
pub open spec fn parse_identifier(input: Seq<u8>) -> Option<Identifier> {
    if input.len() == 0 {
        None
    } else {
        let leading = input[0];
        // 8.1.2.2 a) bits 8 and 7, Table 1.
        let class = (leading / 64) as nat;
        // 8.1.2.5 bit 6.
        let constructed = (leading / 32) % 2 == 1;
        let low = (leading % 32) as nat;
        if low < 31 {
            // 8.1.2.2 c) "bits 5 to 1 shall encode the number of the tag".
            Some(Identifier { class, constructed, number: low, size: 1 })
        } else {
            // 8.1.2.4.1 c) bits 5 to 1 are 11111.
            match high_tag_number(input, 1, 0) {
                None => None,
                Some((number, size)) => {
                    // 8.1.2.2 and 8.1.2.4: the high form is for "a number
                    // greater than or equal to 31" only.
                    if number < 31 {
                        None
                    } else {
                        Some(Identifier { class, constructed, number, size })
                    }
                },
            }
        }
    }
}

/// The unsigned binary integer in `count` octets from `at`, most significant
/// first (8.1.3.5, last paragraph).
pub open spec fn big_endian(input: Seq<u8>, at: nat, count: nat) -> nat
    decreases count,
{
    if count == 0 || at + count > input.len() {
        0
    } else {
        big_endian(input, at, (count - 1) as nat) * 256 + input[(at + count - 1) as int] as nat
    }
}

/// 8.1.3 with 10.1, the length octets at `at`: the length and the offset of
/// the contents.
pub open spec fn parse_length(input: Seq<u8>, at: nat) -> Option<(nat, nat)> {
    if at >= input.len() {
        None
    } else {
        let first = input[at as int];
        if first < 128 {
            // 8.1.3.4 the short form.
            Some((first as nat, at + 1))
        } else if first == 0x80 {
            // 10.1 "The definite form of length encoding shall be used".
            None
        } else if first == 0xFF {
            // 8.1.3.5 c) "the value 11111111 shall not be used".
            None
        } else {
            // 8.1.3.5 b) the number of subsequent octets.
            let count = (first - 128) as nat;
            if at + 1 + count > input.len() {
                None
            } else if input[(at + 1) as int] == 0 {
                // 10.1 "encoded in the minimum number of octets": a leading
                // zero octet could be left out.
                None
            } else {
                let length = big_endian(input, at + 1, count);
                // 10.1 again: a length of 127 or less has a shorter form.
                if length < 128 {
                    None
                } else {
                    Some((length, at + 1 + count))
                }
            }
        }
    }
}

/// 8.1.1.1, one encoding at the start of `input`. Octets after it stay
/// unread; their number is `input.len() - encoding.len()`.
pub open spec fn parse_tlv(input: Seq<u8>) -> Option<Tlv> {
    match parse_identifier(input) {
        None => None,
        Some(id) => {
            // X.680 Table 1: "UNIVERSAL 0 Reserved for use by the encoding
            // rules".
            if id.class == class_universal() && id.number == 0 {
                None
            } else {
                match parse_length(input, id.size) {
                    None => None,
                    Some((length, start)) => {
                        if start + length > input.len() {
                            None
                        } else {
                            Some(
                                Tlv {
                                    class: id.class,
                                    constructed: id.constructed,
                                    number: id.number,
                                    contents: input.subrange(
                                        start as int,
                                        (start + length) as int,
                                    ),
                                    encoding: input.subrange(0, (start + length) as int),
                                },
                            )
                        }
                    },
                }
            }
        },
    }
}

/// `input` as a list of complete encodings, as in 8.9.2, 8.10.2 and 8.12.2.
/// The size test can only fail for a `parse_tlv` that returned nothing; it is
/// here so that the recursion visibly shrinks.
pub open spec fn parse_tlvs(input: Seq<u8>) -> Option<Seq<Tlv>>
    decreases input.len(),
{
    if input.len() == 0 {
        Some(Seq::<Tlv>::empty())
    } else {
        match parse_tlv(input) {
            None => None,
            Some(t) => {
                let size = t.encoding.len();
                if size == 0 || size > input.len() {
                    None
                } else {
                    match parse_tlvs(input.subrange(size as int, input.len() as int)) {
                        None => None,
                        Some(rest) => Some(seq![t] + rest),
                    }
                }
            },
        }
    }
}

/// `input` as exactly one encoding, nothing after it.
pub open spec fn parse_single(input: Seq<u8>) -> Option<Tlv> {
    match parse_tlv(input) {
        None => None,
        Some(t) => {
            if t.encoding.len() == input.len() {
                Some(t)
            } else {
                None
            }
        },
    }
}

/// `t` has this tag and form.
pub open spec fn has_tag(t: Tlv, class: nat, number: nat, constructed: bool) -> bool {
    t.class == class && t.number == number && t.constructed == constructed
}

/// The encoding at `i` exists and has this tag, in either form. Optional
/// components are found by their tag alone; the form is then checked by the
/// component's own decoder, so a wrong form is a refusal, not an absence.
pub open spec fn tag_at(elements: Seq<Tlv>, i: nat, class: nat, number: nat) -> bool {
    i < elements.len() && elements[i as int].class == class && elements[i as int].number == number
}

/// The encodings from `i` on. An extensible type's unknown additions.
pub open spec fn from_index(elements: Seq<Tlv>, i: nat) -> Seq<Tlv> {
    if i >= elements.len() {
        Seq::<Tlv>::empty()
    } else {
        elements.subrange(i as int, elements.len() as int)
    }
}

// ---------------------------------------------------------------------------
// 8.2 Boolean, with 11.1
// ---------------------------------------------------------------------------

/// 8.2 and 11.1, the contents octets of a boolean.
pub open spec fn boolean_contents(contents: Seq<u8>) -> Option<bool> {
    // 8.2.1 "The contents octets shall consist of a single octet."
    if contents.len() != 1 {
        None
    } else if contents[0] == 0 {
        // 8.2.2 "the octet shall be zero".
        Some(false)
    } else if contents[0] == 0xFF {
        // 11.1 "its single contents octet shall have all eight bits set to
        // one".
        Some(true)
    } else {
        None
    }
}

/// 8.2.1 and X.680 Table 1: BOOLEAN is universal 1, primitive.
pub open spec fn decode_boolean(t: Tlv) -> Option<bool> {
    if !has_tag(t, class_universal(), 1, false) {
        None
    } else {
        boolean_contents(t.contents)
    }
}

// ---------------------------------------------------------------------------
// 8.3 Integer
// ---------------------------------------------------------------------------

/// The value of the first `count` contents octets, unsigned.
pub open spec fn magnitude(contents: Seq<u8>, count: nat) -> nat
    decreases count,
{
    if count == 0 || count > contents.len() {
        0
    } else {
        magnitude(contents, (count - 1) as nat) * 256 + contents[(count - 1) as int] as nat
    }
}

/// 256 to the power `n`.
pub open spec fn power_256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * power_256((n - 1) as nat)
    }
}

/// 8.3, the contents octets of an integer.
pub open spec fn integer_contents(contents: Seq<u8>) -> Option<int> {
    // 8.3.1 "The contents octets shall consist of one or more octets."
    if contents.len() == 0 {
        None
    } else if contents.len() > 1 && contents[0] == 0xFF && contents[1] >= 128 {
        // 8.3.2 a) nine leading ones.
        None
    } else if contents.len() > 1 && contents[0] == 0 && contents[1] < 128 {
        // 8.3.2 b) nine leading zeros.
        None
    } else {
        // 8.3.3 two's complement: bit 8 of the first octet counts negatively.
        let unsigned = magnitude(contents, contents.len());
        if contents[0] >= 128 {
            Some(unsigned as int - power_256(contents.len()) as int)
        } else {
            Some(unsigned as int)
        }
    }
}

/// 8.3.1 and X.680 Table 1: INTEGER is universal 2, primitive.
pub open spec fn decode_integer(t: Tlv) -> Option<int> {
    if !has_tag(t, class_universal(), 2, false) {
        None
    } else {
        integer_contents(t.contents)
    }
}

/// An implicitly tagged `INTEGER(0..MAX)` (8.14.4): primitive, with the
/// contents of the base encoding.
pub open spec fn decode_tagged_non_negative(t: Tlv) -> Option<nat> {
    if t.constructed {
        None
    } else {
        match integer_contents(t.contents) {
            None => None,
            Some(v) => {
                if v < 0 {
                    None
                } else {
                    Some(v as nat)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// 8.6 Bitstring, with 10.2 and 11.2
// ---------------------------------------------------------------------------

/// A bitstring value: `octets` holds the bits from bit 8 of the first octet
/// (8.6.2.1), and the last `unused` bits of the last octet are not part of
/// the value.
pub struct BitString {
    /// The octets after the initial one.
    pub octets: Seq<u8>,
    /// The initial octet (8.6.2.2).
    pub unused: nat,
}

/// 2 to the power `n`, for `n` up to 7.
pub open spec fn bit_weight(n: nat) -> nat {
    if n == 0 {
        1
    } else if n == 1 {
        2
    } else if n == 2 {
        4
    } else if n == 3 {
        8
    } else if n == 4 {
        16
    } else if n == 5 {
        32
    } else if n == 6 {
        64
    } else {
        128
    }
}

/// 8.6.2 with 11.2.1, the contents octets of a primitive bitstring.
pub open spec fn bit_string_contents(contents: Seq<u8>) -> Option<BitString> {
    // 8.6.2 "an initial octet followed by zero, one or more subsequent
    // octets".
    if contents.len() == 0 {
        None
    } else {
        let unused = contents[0] as nat;
        let octets = contents.subrange(1, contents.len() as int);
        // 8.6.2.2 "The number shall be in the range zero to seven."
        if unused > 7 {
            None
        } else if octets.len() == 0 && unused != 0 {
            // 8.6.2.3 "If the bitstring is empty, there shall be no subsequent
            // octets, and the initial octet shall be zero."
            None
        } else if octets.len() > 0 && (octets[(octets.len() - 1) as int] as nat) % bit_weight(unused) != 0 {
            // 11.2.1 "Each unused bit in the final octet ... shall be set to
            // zero."
            None
        } else {
            Some(BitString { octets, unused })
        }
    }
}

/// 8.6 and 10.2 ("the constructed form of encoding shall not be used"), with
/// X.680 Table 1: BIT STRING is universal 3.
pub open spec fn decode_bit_string(t: Tlv) -> Option<BitString> {
    if !has_tag(t, class_universal(), 3, false) {
        None
    } else {
        bit_string_contents(t.contents)
    }
}

/// An implicitly tagged BIT STRING (8.14.4), primitive by 10.2.
pub open spec fn decode_tagged_bit_string(t: Tlv) -> Option<BitString> {
    if t.constructed {
        None
    } else {
        bit_string_contents(t.contents)
    }
}

/// 11.2.2, for a type with a "NamedBitList" (X.680 22.7): "the bitstring shall
/// have all trailing 0 bits removed before it is encoded". So a non-empty
/// value ends in a 1 bit. The last used bit of the final octet has weight
/// 2^unused.
pub open spec fn no_trailing_zero_bits(b: BitString) -> bool {
    b.octets.len() == 0 || ((b.octets[(b.octets.len() - 1) as int] as nat) / bit_weight(b.unused)) % 2 == 1
}

/// Bit `n` of the value, numbered from the leading bit as 0, which is how
/// X.680 22 numbers a NamedBitList. Bits past the end read as zero.
pub open spec fn bit_is_set(b: BitString, n: nat) -> bool {
    let index = n / 8;
    let position = n % 8;
    if index >= b.octets.len() {
        false
    } else if index == b.octets.len() - 1 && position >= 8 - b.unused {
        false
    } else {
        // 8.6.2.1: the leading bit is bit 8 of the octet, weight 128.
        ((b.octets[index as int] as nat) / bit_weight((7 - position) as nat)) % 2 == 1
    }
}

// ---------------------------------------------------------------------------
// 8.7 Octetstring, with 10.2
// ---------------------------------------------------------------------------

/// 8.7.2 and 10.2, with X.680 Table 1: OCTET STRING is universal 4.
pub open spec fn decode_octet_string(t: Tlv) -> Option<Seq<u8>> {
    if !has_tag(t, class_universal(), 4, false) {
        None
    } else {
        Some(t.contents)
    }
}

// ---------------------------------------------------------------------------
// 8.19 Object identifier
// ---------------------------------------------------------------------------

/// 8.19.2, the subidentifiers of `contents` from `at`, with the bits read so
/// far of the current one in `partial`. `started` says one is under way.
pub open spec fn subidentifiers(contents: Seq<u8>, at: nat, partial: nat, started: bool) -> Option<
    Seq<nat>,
>
    decreases contents.len() - at,
{
    if at >= contents.len() {
        // "bit 8 of the last octet is zero": a series still under way never
        // ended.
        if started {
            None
        } else {
            Some(Seq::<nat>::empty())
        }
    } else {
        let octet = contents[at as int];
        // "the leading octet of the subidentifier shall not have the value
        // 80 (hex)".
        if !started && octet == 0x80 {
            None
        } else {
            let value = partial * 128 + (octet % 128) as nat;
            if octet >= 128 {
                subidentifiers(contents, at + 1, value, true)
            } else {
                match subidentifiers(contents, at + 1, 0, false) {
                    None => None,
                    Some(rest) => Some(seq![value] + rest),
                }
            }
        }
    }
}

/// 8.19.4 in reverse: the first two components from the first subidentifier
/// (X*40)+Y, given that its NOTE says "only three values are allocated from
/// the root node, and at most 39 subsequent values from nodes reached by
/// X = 0 and X = 1".
pub open spec fn first_two_components(first: nat) -> Seq<nat> {
    if first < 40 {
        seq![0nat, first]
    } else if first < 80 {
        seq![1nat, (first - 40) as nat]
    } else {
        seq![2nat, (first - 80) as nat]
    }
}

/// 8.19, the contents octets of an object identifier: the value's components.
pub open spec fn object_identifier_contents(contents: Seq<u8>) -> Option<Seq<nat>> {
    match subidentifiers(contents, 0, 0, false) {
        None => None,
        Some(subs) => {
            // 8.19.3: N is one less than the number of components, and a
            // value has at least two (8.19.4 uses both).
            if subs.len() == 0 {
                None
            } else {
                Some(first_two_components(subs[0]) + subs.subrange(1, subs.len() as int))
            }
        },
    }
}

/// 8.19.1 and X.680 Table 1: OBJECT IDENTIFIER is universal 6, primitive.
pub open spec fn decode_object_identifier(t: Tlv) -> Option<Seq<nat>> {
    if !has_tag(t, class_universal(), 6, false) {
        None
    } else {
        object_identifier_contents(t.contents)
    }
}

/// An implicitly tagged OBJECT IDENTIFIER (8.14.4).
pub open spec fn decode_tagged_object_identifier(t: Tlv) -> Option<Seq<nat>> {
    if t.constructed {
        None
    } else {
        object_identifier_contents(t.contents)
    }
}

// ---------------------------------------------------------------------------
// 11.6 Set-of components
// ---------------------------------------------------------------------------

/// The octet at `i`, "padded at their trailing end with 0-octets" (11.6).
pub open spec fn padded_octet(s: Seq<u8>, i: nat) -> u8 {
    if i < s.len() {
        s[i as int]
    } else {
        0
    }
}

/// 11.6's comparison of two encodings from octet `i`: `a` does not come after
/// `b`.
pub open spec fn not_after(a: Seq<u8>, b: Seq<u8>, i: nat) -> bool
    decreases (if a.len() > b.len() { a.len() } else { b.len() }) - i,
{
    if i >= a.len() && i >= b.len() {
        true
    } else if padded_octet(a, i) < padded_octet(b, i) {
        true
    } else if padded_octet(a, i) > padded_octet(b, i) {
        false
    } else {
        not_after(a, b, i + 1)
    }
}

/// 11.6, for the elements from `i`: "shall appear in ascending order".
pub open spec fn set_of_ordered(elements: Seq<Tlv>, i: nat) -> bool
    decreases elements.len() - i,
{
    if i + 1 >= elements.len() {
        true
    } else {
        not_after(elements[i as int].encoding, elements[(i + 1) as int].encoding, 0) && set_of_ordered(
            elements,
            i + 1,
        )
    }
}

// ---------------------------------------------------------------------------
// 8.23 Restricted character strings, and X.680 41
// ---------------------------------------------------------------------------

/// X.680 Table 8: IA5String holds registration numbers 1 and 6 with SPACE and
/// DELETE, the 128 characters of ISO 646, one octet each by X.690 8.23.5.
pub open spec fn all_ia5(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i,
{
    if i >= s.len() {
        true
    } else {
        s[i as int] < 128 && all_ia5(s, i + 1)
    }
}

/// An implicitly tagged IA5String (8.23.3, 8.14.4, 10.2).
pub open spec fn decode_tagged_ia5_string(t: Tlv) -> Option<Seq<u8>> {
    if t.constructed || !all_ia5(t.contents, 0) {
        None
    } else {
        Some(t.contents)
    }
}

/// X.680 41.4, Table 10.
pub open spec fn is_printable(c: u8) -> bool {
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) || (0x30 <= c && c <= 0x39) || c == 0x20
        || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2B || c == 0x2C || c == 0x2D || c == 0x2E
        || c == 0x2F || c == 0x3A || c == 0x3D || c == 0x3F
}

/// Every octet of a PrintableString, from `i` (X.690 8.23.4).
pub open spec fn all_printable(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i,
{
    if i >= s.len() {
        true
    } else {
        is_printable(s[i as int]) && all_printable(s, i + 1)
    }
}

/// `n` octets from `at` exist and are continuation octets of UTF-8.
pub open spec fn continuation(s: Seq<u8>, at: nat, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        at < s.len() && 0x80 <= s[at as int] && s[at as int] <= 0xBF && continuation(
            s,
            at + 1,
            (n - 1) as nat,
        )
    }
}

/// The UTF-8 form X.690 8.23.10 refers to, from `i`: each lead octet starts
/// the shortest form of a scalar value.
pub open spec fn well_formed_utf8(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i,
{
    if i >= s.len() {
        true
    } else {
        let a = s[i as int];
        if a < 0x80 {
            well_formed_utf8(s, i + 1)
        } else if 0xC2 <= a && a <= 0xDF {
            continuation(s, i + 1, 1) && well_formed_utf8(s, i + 2)
        } else if 0xE0 <= a && a <= 0xEF {
            // No overlong forms, and no surrogates.
            i + 3 <= s.len() && continuation(s, i + 1, 2) && (a != 0xE0 || s[(i + 1) as int] >= 0xA0) && (a != 0xED || s[(i + 1) as int]
                <= 0x9F) && well_formed_utf8(s, i + 3)
        } else if 0xF0 <= a && a <= 0xF4 {
            // No overlong forms, nothing past U+10FFFF.
            i + 4 <= s.len() && continuation(s, i + 1, 3) && (a != 0xF0 || s[(i + 1) as int] >= 0x90) && (a != 0xF4 || s[(i + 1) as int]
                <= 0x8F) && well_formed_utf8(s, i + 4)
        } else {
            false
        }
    }
}

// ---------------------------------------------------------------------------
// X.680 46 and 47 with X.690 11.7 and 11.8: times
// ---------------------------------------------------------------------------

/// A date and time of day in UTC. `year` is four digits (X.509 7.2.1 turns a
/// UTCTime's two digits into four). `fraction` is the digits after the
/// decimal point of a GeneralizedTime, usually none.
pub struct Moment {
    /// Four digits, as a number.
    pub year: nat,
    /// The month, January being 1.
    pub month: nat,
    /// The day of the month.
    pub day: nat,
    /// The hour.
    pub hour: nat,
    /// The minute.
    pub minute: nat,
    /// The second.
    pub second: nat,
    /// The digits after the decimal point.
    pub fraction: Seq<u8>,
}

/// One ASCII digit's value.
pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c && c <= 0x39
}

/// `n` digits from `at` are all there.
pub open spec fn digits_at(s: Seq<u8>, at: nat, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        at < s.len() && is_digit(s[at as int]) && digits_at(s, at + 1, (n - 1) as nat)
    }
}

/// The two digits at `at`.
pub open spec fn two_digits(s: Seq<u8>, at: nat) -> nat {
    ((s[at as int] - 0x30) * 10 + (s[(at + 1) as int] - 0x30)) as nat
}

/// Gregorian leap years.
pub open spec fn is_leap_year(year: nat) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

/// How many days `month` has.
pub open spec fn days_in_month(year: nat, month: nat) -> nat {
    if month == 2 {
        if is_leap_year(year) {
            29
        } else {
            28
        }
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        30
    } else {
        31
    }
}

/// The ranges of X.680 47.3: "MM is the month (counting January as 01), and
/// DD is the day of the month (01 to 31)", "hh is hour (00 to 23) and mm is
/// minutes (00 to 59)" and "ss is seconds (00 to 59)". Used for both time
/// types (see the open choices at the top of this file). An hour of 24 is
/// out of range, as 11.7.5 and 11.8.3 ask.
pub open spec fn moment_in_range(m: Moment) -> bool {
    1 <= m.month && m.month <= 12 && 1 <= m.day && m.day <= days_in_month(m.year, m.month) && m.hour
        <= 23 && m.minute <= 59 && m.second <= 59
}

/// X.509 (10/2019) 7.2.1: "If the 2-digit value is 00 through to 49 inclusive,
/// the value shall have 2000 added to it" and "50 through to 99 inclusive ...
/// 1900".
pub open spec fn rationalized_year(two_digit: nat) -> nat {
    if two_digit <= 49 {
        two_digit + 2000
    } else {
        two_digit + 1900
    }
}

/// X.680 47.3 with 11.8: exactly "YYMMDDhhmmssZ". 11.8.1 removes the time
/// differential of 47.3 c) 2) and 11.8.2 the form without seconds.
pub open spec fn utc_time_contents(s: Seq<u8>) -> Option<Moment> {
    if s.len() != 13 || !digits_at(s, 0, 12) || s[12] != 0x5A {
        None
    } else {
        let m = Moment {
            year: rationalized_year(two_digits(s, 0)),
            month: two_digits(s, 2),
            day: two_digits(s, 4),
            hour: two_digits(s, 6),
            minute: two_digits(s, 8),
            second: two_digits(s, 10),
            fraction: Seq::<u8>::empty(),
        };
        if moment_in_range(m) {
            Some(m)
        } else {
            None
        }
    }
}

/// X.680 46.3 with 11.7: "YYYYMMDDhhmmss", then an optional fraction, then Z.
/// 11.7.1 requires the Z, 11.7.2 the seconds and 11.7.4 the point ".", and
/// 11.7.3 forbids a trailing zero in the fraction, which also covers an
/// all-zero one.
pub open spec fn generalized_time_contents(s: Seq<u8>) -> Option<Moment> {
    if s.len() < 15 || !digits_at(s, 0, 14) || s[(s.len() - 1) as int] != 0x5A {
        None
    } else {
        let fraction = if s.len() == 15 {
            Seq::<u8>::empty()
        } else {
            s.subrange(15, s.len() - 1)
        };
        let m = Moment {
            year: two_digits(s, 0) * 100 + two_digits(s, 2),
            month: two_digits(s, 4),
            day: two_digits(s, 6),
            hour: two_digits(s, 8),
            minute: two_digits(s, 10),
            second: two_digits(s, 12),
            fraction,
        };
        if s.len() > 15 && (s[14] != 0x2E || fraction.len() == 0 || !digits_at(
            fraction,
            0,
            fraction.len(),
        ) || fraction[(fraction.len() - 1) as int] == 0x30) {
            None
        } else if moment_in_range(m) {
            Some(m)
        } else {
            None
        }
    }
}

} // verus!
