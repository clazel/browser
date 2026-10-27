//! Executable-style specification of ASN.1 DER, transcribed from ITU-T X.690
//! (08/2015), "Information technology - ASN.1 encoding rules: Specification
//! of Basic Encoding Rules (BER), Canonical Encoding Rules (CER) and
//! Distinguished Encoding Rules (DER)" (also ISO/IEC 8825-1:2015,
//! <https://www.itu.int/rec/T-REC-X.690-201508-I/en>): clause 8 (the basic
//! encoding rules) with clause 10 (the DER restrictions on length forms and
//! string encodings) and clause 11 (the restrictions both CER and DER
//! apply: BOOLEAN, unused bits). An ITU-T Recommendation is a dated edition,
//! so there is no commit to pin; the tag numbers of the universal types are
//! those of ITU-T X.680 (08/2015) Table 1, which X.690 itself uses without
//! listing. Nothing here runs; it defines what "correct" means. Each
//! `// N.` comment is a clause of the standard cited next to it.
//!
//! ## The profile
//!
//! The decoder accepts exactly the DER encodings, never the other BER
//! alternatives (X.690 §7.4: "No alternative encodings are permitted by the
//! Canonical Encoding Rules or Distinguished Encoding Rules"):
//! - definite length only (§10.1; the indefinite form of §8.1.3.6 is
//!   rejected) and in the minimum number of octets (§10.1), so a length that
//!   fits the short form never uses the long form and the long form never
//!   has a leading zero octet;
//! - an identifier in the low-tag-number form for tag numbers 0 to 30
//!   (§8.1.2.2) and the high-tag-number form only from 31 (§8.1.2.4), with no
//!   leading zero digit (§8.1.2.4.2 c);
//! - BOOLEAN as `0x00` or `0xFF` (§8.2, §11.1), INTEGER with no redundant
//!   leading octets (§8.3.2), BIT STRING in the primitive form with an
//!   unused-bits octet of 0 to 7 (§8.6.2.2), zero where the string is empty
//!   (§8.6.2.3), and zero unused bits (§11.2.1), OCTET STRING and the
//!   character string types in the primitive form (§10.2: "the constructed
//!   form of encoding shall not be used"), NULL with no contents (§8.8),
//!   OBJECT IDENTIFIER with no padding digit (§8.19.2), SEQUENCE and SET in
//!   the constructed form (§8.9.1, §8.11.1), and a tagged type either
//!   implicit (§8.14.4) or explicit and constructed (§8.14.3).
//!
//! What this file leaves to its callers, as the roadmap states (item 3.5a):
//! the character and date restrictions of UTF8String, PrintableString,
//! IA5String, UTCTime and GeneralizedTime (RFC 5280 §4.1.2.5, X.509's job),
//! the order of SET OF components (§11.6, checked by X.509 where it
//! matters), and omission of DEFAULT values (§11.5, the schema's job).
//!
//! ## Modelling choices
//!
//! Each is a deviation in form, never in meaning, except where marked as a
//! limit, and the argument is given here once:
//! - **A reader is a cursor.** The standard defines the encoding of a data
//!   value; a decoder is a function from bytes to the value and its extent.
//!   Every reader takes the input `b`, a position `pos` and an `end`, reads
//!   the one value at `pos`, and returns where it stopped. Nothing at or
//!   after `end` exists to it: `end` stands for the end of the enclosing
//!   value's contents, so "descending into a constructed value" is calling
//!   the readers again on `[cstart, cend)`, and "end of contents" is
//!   [`expect_end`].
//! - **"Failure" is `None`.** A byte string that is not the DER encoding of a
//!   value of the requested type gives `None`; the standard has no failure
//!   value, only conformance (§7).
//! - **The next position is the end of the contents.** With the definite
//!   length (§8.1.3.3) there are no end-of-contents octets (§8.1.5), so a
//!   value ends exactly where its contents end: a [`Tlv`] has no field for
//!   it, and `cend` is it.
//! - **"Bits 7 to 1" and "bit 8" are arithmetic.** Bit 8 of an octet `o` is
//!   `o / 128`, bits 7 to 1 are `o % 128`; the class (bits 8 and 7) is
//!   `o / 64` and bit 6 is `(o / 32) % 2` (§8.1.2.2, Table 1).
//! - **Numbers "encoded as an unsigned binary integer" are `nat`s.** A
//!   run of octets spelling a number base 256 is [`be_value`] and a run of
//!   subsequent octets of a tag or subidentifier is [`base128`] (bit 8 of
//!   each octet is the continuation flag and is not part of the number).
//! - **An INTEGER is read as its sign and a range.** §8.3.3 makes the
//!   contents a two's complement number; [`integer_value`] is that number,
//!   and a reader gives its sign and the magnitude octets without the single
//!   `0x00` octet that pads a positive number whose first octet has bit 8
//!   set. The magnitude of a negative number is its two's complement octets
//!   unchanged: they are not negated.
//! - **A BIT STRING is read as its unused-bits count and its octets.**
//! - **An OBJECT IDENTIFIER is read as its components** (`Seq<nat>`), by
//!   §8.19.3 to §8.19.5.
//! - **Limits, which are choices of this project.** Each only rejects
//!   encodings the standard accepts, and none can matter on an input shorter
//!   than 2^64 bytes except the first and the third:
//!   - a tag number of 2^14 or more is rejected (the standard has no bound;
//!     X.509 uses tag numbers 0 to 30, and the high form is parsed up to
//!     16383 so it can be recognised);
//!   - a long-form length of more than 8 octets is rejected, which is what
//!     would reject a length of 2^64 or more; a content that long is not
//!     inside any input of fewer than 2^64 bytes, so the effect is nil
//!     there;
//!   - a subidentifier of 2^64 or more is rejected (no object identifier
//!     in use has one, and an arc is a `u64` in the executable code).
//! - **Tag numbers are `u32`.** The only tag numbers that survive the limit
//!   above are below 2^14.
//! - **Constructed strings.** The standard lets BER senders encode a BIT
//!   STRING or OCTET STRING in the constructed form (§8.6.3, §8.7.3) and DER
//!   forbids it (§10.2). No reader accepts a constructed form of a string
//!   type: the readers require the primitive form of the universal tag, so
//!   the tag with bit 6 set is "another tag" and is rejected.
//!
//! Where the standard is silent but a DER reader must decide, the choice is
//! listed here: a high-tag-number identifier with a number below 31 is
//! rejected (§8.1.2.2 requires the low form for 0 to 30, so the other
//! encoding is not the one DER allows, §7.4); the length octets
//! `0xFF` (reserved, §8.1.3.5 c) and `0x80` (the indefinite form, §8.1.3.6)
//! are rejected; an OBJECT IDENTIFIER has at least one subidentifier
//! (§8.19.3: N is one less than the number of components, and X.680 §32.3
//! gives an object identifier at least two components).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Data model.
// ---------------------------------------------------------------------------

/// The class of a tag (§8.1.2.2, Table 1: "Encoding of class of tag").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// Bits 8 and 7 are `00`.
    Universal,
    /// Bits 8 and 7 are `01`.
    Application,
    /// Bits 8 and 7 are `10`.
    ContextSpecific,
    /// Bits 8 and 7 are `11`.
    Private,
}

/// An ASN.1 tag as the identifier octets carry it (§8.1.2.1: "the identifier
/// octets shall encode the ASN.1 tag (class and number) of the type of the
/// data value"), with the primitive/constructed bit (§8.1.2.5). The number
/// is below 2^14 in everything this crate produces (see the limits above).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tag {
    /// Bits 8 and 7 of the first identifier octet.
    pub class: Class,
    /// Bit 6 of the first identifier octet: 1 if the encoding is
    /// constructed (§8.1.2.5).
    pub constructed: bool,
    /// The tag number.
    pub number: u32,
}

/// A data value's extent: its tag and its contents range `[cstart, cend)`.
/// The value ends at `cend` (no end-of-contents octets, §8.1.5).
pub struct Tlv {
    /// The tag from the identifier octets.
    pub tag: Tag,
    /// Index of the first contents octet.
    pub cstart: nat,
    /// Index after the last contents octet.
    pub cend: nat,
}

/// The largest tag number the decoder accepts (a limit of this project).
pub const MAX_TAG_NUMBER: u32 = 16383;

/// The most octets after the initial one in a long-form length (a limit of
/// this project).
pub const MAX_LENGTH_OCTETS: u32 = 8;

/// Tag numbers of the universal types (ITU-T X.680 Table 1).
pub const BOOLEAN: u32 = 1;

/// INTEGER.
pub const INTEGER: u32 = 2;

/// BIT STRING.
pub const BIT_STRING: u32 = 3;

/// OCTET STRING.
pub const OCTET_STRING: u32 = 4;

/// NULL.
pub const NULL: u32 = 5;

/// OBJECT IDENTIFIER.
pub const OBJECT_IDENTIFIER: u32 = 6;

/// UTF8String.
pub const UTF8_STRING: u32 = 12;

/// SEQUENCE and SEQUENCE OF.
pub const SEQUENCE: u32 = 16;

/// SET and SET OF.
pub const SET: u32 = 17;

/// PrintableString.
pub const PRINTABLE_STRING: u32 = 19;

/// IA5String.
pub const IA5_STRING: u32 = 22;

/// UTCTime.
pub const UTC_TIME: u32 = 23;

/// GeneralizedTime.
pub const GENERALIZED_TIME: u32 = 24;

/// The tag of a universal type with a primitive encoding.
pub open spec fn universal_primitive(number: u32) -> Tag {
    Tag { class: Class::Universal, constructed: false, number }
}

/// The tag of a universal type with a constructed encoding.
pub open spec fn universal_constructed(number: u32) -> Tag {
    Tag { class: Class::Universal, constructed: true, number }
}

/// The tag of a context-specific type (`[number]`).
pub open spec fn context_specific(number: u32, constructed: bool) -> Tag {
    Tag { class: Class::ContextSpecific, constructed, number }
}

// ---------------------------------------------------------------------------
// Numbers.
// ---------------------------------------------------------------------------

/// 256 to the power `n`: the number of values `n` octets can hold.
pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * pow256((n - 1) as nat)
    }
}

/// "An unsigned binary integer ... with bit 8 of the first subsequent octet
/// as the most significant bit" (§8.1.3.5): the number `s` spells base 256,
/// most significant octet first.
pub open spec fn be_value(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        be_value(s.drop_last()) * 256 + s.last() as nat
    }
}

/// The `width` octets spelling `value` base 256, most significant first
/// (the inverse of [`be_value`] for `value < 256^width`).
pub open spec fn be_bytes(value: nat, width: nat) -> Seq<u8>
    decreases width,
{
    if width == 0 {
        seq![]
    } else {
        be_bytes(value / 256, (width - 1) as nat).push((value % 256) as u8)
    }
}

/// "Bits 7 to 1 of the first subsequent octet, followed by bits 7 to 1 of
/// the second ... shall be the encoding of an unsigned binary integer, with
/// bit 7 of the first subsequent octet as the most significant bit"
/// (§8.1.2.4.2 b), and the same for a subidentifier (§8.19.2): the number
/// the low seven bits of each octet of `s` spell, most significant first.
pub open spec fn base128(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        base128(s.drop_last()) * 128 + (s.last() % 128) as nat
    }
}

/// "Bit 8 of each octet shall be set to one unless it is the last octet"
/// (§8.1.2.4.2 a), §8.19.2): the index of the first octet of `b[i..end)`
/// whose bit 8 is zero, which ends the series.
pub open spec fn series_end(b: Seq<u8>, i: nat, end: nat) -> Option<nat>
    decreases end - i,
{
    if i >= end {
        None
    } else if b[i as int] < 128 {
        Some(i)
    } else {
        series_end(b, i + 1, end)
    }
}

// ---------------------------------------------------------------------------
// §8.1.2: identifier octets.
// ---------------------------------------------------------------------------

/// Table 1: the class encoded by bits 8 and 7 (as the number `o / 64`).
pub open spec fn class_from_bits(bits: u8) -> Class {
    if bits == 0 {
        Class::Universal
    } else if bits == 1 {
        Class::Application
    } else if bits == 2 {
        Class::ContextSpecific
    } else {
        Class::Private
    }
}

/// Table 1, the other way: the value of bits 8 and 7.
pub open spec fn class_bits(class: Class) -> u8 {
    match class {
        Class::Universal => 0,
        Class::Application => 1,
        Class::ContextSpecific => 2,
        Class::Private => 3,
    }
}

/// §8.1.2: read the identifier octets at `pos`. Returns the tag and the
/// number of identifier octets.
pub open spec fn read_identifier(b: Seq<u8>, pos: nat, end: nat) -> Option<(Tag, nat)> {
    if pos >= end {
        // The leading octet is missing.
        None
    } else {
        let o = b[pos as int];
        // 8.1.2.2 a), 8.1.2.4.1 a): "bits 8 and 7 shall be encoded to
        // represent the class of the tag as specified in Table 1".
        let class = class_from_bits(o / 64);
        // 8.1.2.2 b), 8.1.2.4.1 b), 8.1.2.5: "Bit 6 shall be set to zero if
        // the encoding is primitive, and shall be set to one if the
        // encoding is constructed."
        let constructed = (o / 32) % 2 == 1;
        if o % 32 != 31 {
            // 1. 8.1.2.2 c): "bits 5 to 1 shall encode the number of the
            //    tag as a binary integer" (tag numbers 0 to 30).
            Some((Tag { class, constructed, number: (o % 32) as u32 }, 1))
        } else {
            // 2. 8.1.2.4: "For tags with a number greater than or equal to
            //    31, the identifier shall comprise a leading octet followed
            //    by one or more subsequent octets." 8.1.2.4.1 c): the
            //    leading octet's bits 5 to 1 are 11111.
            match series_end(b, pos + 1, end) {
                // 8.1.2.4.2 a): the last subsequent octet is missing.
                None => None,
                Some(j) => {
                    // 8.1.2.4.2 b): the tag number.
                    let number = base128(b.subrange(pos as int + 1, j as int + 1));
                    if b[pos as int + 1] % 128 == 0 {
                        // 8.1.2.4.2 c): "bits 7 to 1 of the first
                        // subsequent octet shall not all be zero".
                        None
                    } else if number < 31 {
                        // 8.1.2.2: tag numbers 0 to 30 are encoded in the
                        // low-tag-number form. (DER allows no alternative,
                        // §7.4.)
                        None
                    } else if number > MAX_TAG_NUMBER as nat {
                        // A limit of this project (see the header).
                        None
                    } else {
                        Some((Tag { class, constructed, number: number as u32 }, (j + 1 - pos) as nat))
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §8.1.3: length octets, with §10.1.
// ---------------------------------------------------------------------------

/// §8.1.3: read the length octets at `pos`. Returns the length (the number
/// of contents octets) and the number of length octets.
pub open spec fn read_length(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    if pos >= end {
        // The initial length octet is missing.
        None
    } else {
        let f = b[pos as int];
        if f < 128 {
            // 1. 8.1.3.4: "In the short form, the length octets shall
            //    consist of a single octet in which bit 8 is zero and bits
            //    7 to 1 encode the number of octets in the contents octets."
            Some((f as nat, 1))
        } else if f == 128 {
            // 2. 8.1.3.6: the indefinite form. 10.1: "The definite form of
            //    length encoding shall be used".
            None
        } else if f == 255 {
            // 3. 8.1.3.5 c): "the value 11111111 shall not be used".
            None
        } else {
            // 4. 8.1.3.5: the long form. b): "bits 7 to 1 shall encode the
            //    number of subsequent octets in the length octets".
            let n = (f - 128) as nat;
            if n > MAX_LENGTH_OCTETS as nat {
                // A limit of this project (see the header).
                None
            } else if pos + 1 + n > end {
                // The subsequent octets are missing.
                None
            } else if b[pos as int + 1] == 0 {
                // 10.1: "encoded in the minimum number of octets": a
                // leading zero octet is redundant.
                None
            } else {
                // 8.1.3.5: "the encoding of an unsigned binary integer
                // equal to the number of octets in the contents octets".
                let v = be_value(b.subrange(pos as int + 1, pos as int + 1 + n as int));
                if v < 128 {
                    // 8.1.3.3 NOTE: the short form can be used for 127 or
                    // less, so 10.1 requires it.
                    None
                } else {
                    Some((v, 1 + n))
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §8.1.1: an encoding is identifier, length and contents.
// ---------------------------------------------------------------------------

/// §8.1.1.1: read the identifier octets, the length octets and check that
/// the contents octets lie inside `[pos, end)`. The end-of-contents octets
/// are not present (§8.1.1.2, §8.1.5: the length is definite).
pub open spec fn read_tlv(b: Seq<u8>, pos: nat, end: nat) -> Option<Tlv> {
    match read_identifier(b, pos, end) {
        None => None,
        Some((tag, id_len)) => match read_length(b, pos + id_len, end) {
            None => None,
            Some((len, len_len)) => {
                let cstart = pos + id_len + len_len;
                if cstart + len > end {
                    // 8.1.1.1 c): the contents octets are missing.
                    None
                } else {
                    Some(Tlv { tag, cstart, cend: cstart + len })
                }
            },
        },
    }
}

/// The end of contents: nothing is left in `[pos, end)`. A constructed
/// value's contents are "the complete encoding of one data value from each
/// of the types listed" (§8.9.2) and nothing more.
pub open spec fn expect_end(pos: nat, end: nat) -> bool {
    pos == end
}

// ---------------------------------------------------------------------------
// §8.2, §11.1: BOOLEAN.
// ---------------------------------------------------------------------------

/// The value of a BOOLEAN's contents octets.
pub open spec fn boolean_contents(c: Seq<u8>) -> Option<bool> {
    if c.len() != 1 {
        // 8.2.1: "The contents octets shall consist of a single octet."
        None
    } else if c[0] == 0 {
        // 8.2.2: "If the boolean value is FALSE the octet shall be zero."
        Some(false)
    } else if c[0] == 255 {
        // 11.1: "If the encoding represents the boolean value TRUE, its
        // single contents octet shall have all eight bits set to one."
        Some(true)
    } else {
        None
    }
}

/// Read a BOOLEAN at `pos`. Returns its value and the next position.
pub open spec fn read_boolean(b: Seq<u8>, pos: nat, end: nat) -> Option<(bool, nat)> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            // 8.2.1: "The encoding of a boolean value shall be primitive."
            if t.tag == universal_primitive(BOOLEAN) {
                match boolean_contents(b.subrange(t.cstart as int, t.cend as int)) {
                    Some(v) => Some((v, t.cend)),
                    None => None,
                }
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// §8.3: INTEGER.
// ---------------------------------------------------------------------------

/// §8.3.2: "If the contents octets of an integer value encoding consist of
/// more than one octet, then the bits of the first octet and bit 8 of the
/// second octet: a) shall not all be ones; and b) shall not all be zero."
/// §8.3.1: "The contents octets shall consist of one or more octets."
pub open spec fn integer_contents_ok(c: Seq<u8>) -> bool {
    &&& c.len() >= 1
    &&& c.len() >= 2 ==> !((c[0] == 255 && c[1] >= 128) || (c[0] == 0 && c[1] < 128))
}

/// §8.3.3: "The contents octets shall be a two's complement binary number
/// equal to the integer value": the value of `c` with its bit 8 of the first
/// octet weighing minus 2^(8n-1).
pub open spec fn integer_value(c: Seq<u8>) -> int {
    if c.len() == 0 {
        0
    } else if c[0] >= 128 {
        be_value(c) as int - pow256(c.len()) as int
    } else {
        be_value(c) as int
    }
}

/// Read an INTEGER at `pos`. Returns whether it is negative, the range of
/// its magnitude octets (see the modelling choices) and the next position.
pub open spec fn read_integer(b: Seq<u8>, pos: nat, end: nat) -> Option<(bool, nat, nat, nat)> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            let c = b.subrange(t.cstart as int, t.cend as int);
            // 8.3.1: primitive.
            if t.tag == universal_primitive(INTEGER) && integer_contents_ok(c) {
                // 8.3.3: the value is negative if bit 8 of the first octet
                // is one.
                let negative = c[0] >= 128;
                // A leading 0x00 octet only pads a positive number (8.3.2
                // b) makes it needed exactly when the next octet has bit 8
                // set).
                let start = if c.len() >= 2 && c[0] == 0 { t.cstart + 1 } else { t.cstart };
                Some((negative, start, t.cend, t.cend))
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// §8.6, §11.2: BIT STRING.
// ---------------------------------------------------------------------------

/// 2 to the power of a number of unused bits (0 to 7).
pub open spec fn pow2_unused(u: u8) -> nat {
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

/// §8.6.2: the contents octets of a primitive bit string: "an initial octet
/// followed by zero, one or more subsequent octets".
pub open spec fn bit_string_contents_ok(c: Seq<u8>) -> bool {
    &&& c.len() >= 1
    // 8.6.2.2: "The number [of unused bits in the final subsequent octet]
    // shall be in the range zero to seven."
    &&& c[0] <= 7
    // 8.6.2.3: "If the bitstring is empty, there shall be no subsequent
    // octets, and the initial octet shall be zero."
    &&& (c.len() == 1 ==> c[0] == 0)
    // 11.2.1: "Each unused bit in the final octet of the encoding of a bit
    // string value shall be set to zero." The unused bits are the low bits
    // of the last octet.
    &&& (c.len() >= 2 ==> (c.last() as nat) % pow2_unused(c[0]) == 0)
}

/// Read a BIT STRING at `pos`. Returns the number of unused bits, the range
/// of the octets that hold the bits, and the next position.
pub open spec fn read_bit_string(b: Seq<u8>, pos: nat, end: nat) -> Option<(u8, nat, nat, nat)> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            let c = b.subrange(t.cstart as int, t.cend as int);
            // 8.6.1 and 10.2: primitive (the constructed form is a BER
            // option that DER removes).
            if t.tag == universal_primitive(BIT_STRING) && bit_string_contents_ok(c) {
                Some((c[0], t.cstart + 1, t.cend, t.cend))
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// §8.7, §10.2, §8.8: OCTET STRING, the character string types, NULL.
// ---------------------------------------------------------------------------

/// Read a primitive value of the universal type `number` whose contents are
/// octets taken as they are: OCTET STRING (§8.7.2), UTF8String,
/// PrintableString, IA5String, UTCTime and GeneralizedTime (their contents
/// are octets; the character and date restrictions are X.509's, see the
/// header). Returns the contents range; the next position is its end.
pub open spec fn read_octets(b: Seq<u8>, pos: nat, end: nat, number: u32) -> Option<(nat, nat)> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            // 8.7.1, 10.2: "For bitstring, octetstring and restricted
            // character string types, the constructed form of encoding
            // shall not be used."
            if t.tag == universal_primitive(number) {
                Some((t.cstart, t.cend))
            } else {
                None
            }
        },
    }
}

/// An OCTET STRING (§8.7).
pub open spec fn read_octet_string(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    read_octets(b, pos, end, OCTET_STRING)
}

/// A UTF8String.
pub open spec fn read_utf8_string(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    read_octets(b, pos, end, UTF8_STRING)
}

/// A PrintableString.
pub open spec fn read_printable_string(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    read_octets(b, pos, end, PRINTABLE_STRING)
}

/// An IA5String.
pub open spec fn read_ia5_string(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    read_octets(b, pos, end, IA5_STRING)
}

/// A UTCTime (as octets).
pub open spec fn read_utc_time(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    read_octets(b, pos, end, UTC_TIME)
}

/// A GeneralizedTime (as octets).
pub open spec fn read_generalized_time(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    read_octets(b, pos, end, GENERALIZED_TIME)
}

/// Read a NULL at `pos`. Returns the next position.
pub open spec fn read_null(b: Seq<u8>, pos: nat, end: nat) -> Option<nat> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            // 8.8.1: primitive. 8.8.2: "The contents octets shall not
            // contain any octets."
            if t.tag == universal_primitive(NULL) && t.cstart == t.cend {
                Some(t.cend)
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// §8.19: OBJECT IDENTIFIER.
// ---------------------------------------------------------------------------

/// §8.19.2: the subidentifiers in `c` from index 0 to its end, each "a
/// series of (one or more) octets" whose bit 8 is one except in the last.
/// Termination: `lemma_series_end_bounds`.
pub open spec fn subidentifiers(c: Seq<u8>) -> Option<Seq<nat>>
    decreases c.len(),
    via subidentifiers_decreases
{
    if c.len() == 0 {
        Some(seq![])
    } else {
        match series_end(c, 0, c.len()) {
            // The last octet of the series (bit 8 zero) is missing.
            None => None,
            Some(j) => {
                // Bits 7 to 1 of the octets in the series "collectively
                // encode the subidentifier".
                let v = base128(c.subrange(0, j as int + 1));
                if c[0] == 128 {
                    // 8.19.2: "The subidentifier shall be encoded in the
                    // fewest possible octets, that is, the leading octet of
                    // the subidentifier shall not have the value 80".
                    None
                } else if v >= 0x1_0000_0000_0000_0000 {
                    // A limit of this project (see the header).
                    None
                } else {
                    match subidentifiers(c.skip(j as int + 1)) {
                        None => None,
                        Some(rest) => Some(seq![v] + rest),
                    }
                }
            },
        }
    }
}

/// §8.19.4: "The numerical value of the first subidentifier is derived from
/// the values of the first two object identifier components ... using the
/// formula (X*40) + Y", where X is 0, 1 or 2 (X.660, X.680) and Y is below 40
/// when X is 0 or 1: so the first two components are recovered from `v`.
pub open spec fn first_components(v: nat) -> (nat, nat) {
    if v < 40 {
        (0, v)
    } else if v < 80 {
        (1, (v - 40) as nat)
    } else {
        (2, (v - 80) as nat)
    }
}

/// The components of an OBJECT IDENTIFIER's contents octets (§8.19.2 to
/// §8.19.5): the first subidentifier gives the first two components, the
/// others one each.
pub open spec fn oid_components(c: Seq<u8>) -> Option<Seq<nat>> {
    match subidentifiers(c) {
        None => None,
        Some(subs) => {
            if subs.len() == 0 {
                // 8.19.3: N is one less than the number of components, and
                // X.680 requires at least two components, so N >= 1.
                None
            } else {
                let (x, y) = first_components(subs[0]);
                // 8.19.5: "The numerical value of the ith subidentifier,
                // (2 <= i <= N) is that of the (i + 1)th object identifier
                // component."
                Some(seq![x, y] + subs.skip(1))
            }
        },
    }
}

/// Read an OBJECT IDENTIFIER at `pos`. Returns its components and the next
/// position.
pub open spec fn read_oid(b: Seq<u8>, pos: nat, end: nat) -> Option<(Seq<nat>, nat)> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            // 8.19.1: "The encoding of an object identifier value shall be
            // primitive."
            if t.tag == universal_primitive(OBJECT_IDENTIFIER) {
                match oid_components(b.subrange(t.cstart as int, t.cend as int)) {
                    Some(arcs) => Some((arcs, t.cend)),
                    None => None,
                }
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// §8.9, §8.11, §8.12, §8.14: SEQUENCE, SET, tagged types.
// ---------------------------------------------------------------------------

/// Read a value whose tag is the universal constructed type `number`
/// (SEQUENCE: §8.9.1 "The encoding of a sequence value shall be
/// constructed"; SET: §8.11.1; SEQUENCE OF: §8.10.1; SET OF: §8.12.1). The
/// contents range is the inner range to read with the readers above, and
/// the next position is its end.
pub open spec fn expect_constructed(b: Seq<u8>, pos: nat, end: nat, number: u32) -> Option<(nat, nat)> {
    match read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            if t.tag == universal_constructed(number) {
                Some((t.cstart, t.cend))
            } else {
                None
            }
        },
    }
}

/// A SEQUENCE or SEQUENCE OF (§8.9, §8.10).
pub open spec fn expect_sequence(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    expect_constructed(b, pos, end, SEQUENCE)
}

/// A SET or SET OF (§8.11, §8.12). The order of the components is not
/// checked (§10.3, §11.6 are left to the caller, see the header).
pub open spec fn expect_set(b: Seq<u8>, pos: nat, end: nat) -> Option<(nat, nat)> {
    expect_constructed(b, pos, end, SET)
}

/// An OPTIONAL component with a context-specific tag `[number]` (§8.14, §8.9.3:
/// "The encoding of a data value may, but need not, be present for a type
/// which was referenced with the keyword OPTIONAL"): `Some(None)` when no
/// value is left or the next one has another tag, `Some(Some((constructed,
/// cstart, cend)))` when it is there, and `None` when the bytes are not a
/// well-formed value. For an IMPLICIT tag (§8.14.4) the form is that of the
/// underlying type, so `constructed` is returned for the caller to check.
pub open spec fn read_optional_context(b: Seq<u8>, pos: nat, end: nat, number: u32) -> Option<Option<(bool, nat, nat)>> {
    if pos >= end {
        // Nothing is left: the component is absent.
        Some(None)
    } else {
        match read_identifier(b, pos, end) {
            None => None,
            Some((tag, _)) => {
                if tag.class == Class::ContextSpecific && tag.number == number {
                    match read_tlv(b, pos, end) {
                        None => None,
                        Some(t) => Some(Some((tag.constructed, t.cstart, t.cend))),
                    }
                } else {
                    Some(None)
                }
            },
        }
    }
}

/// As [`read_optional_context`] for an EXPLICIT tag: "If implicit tagging
/// was not used in the definition of the type, the encoding shall be
/// constructed and the contents octets shall be the complete base encoding"
/// (§8.14.3). The inner range holds one value, read by the caller and
/// followed by [`expect_end`].
pub open spec fn read_optional_explicit(b: Seq<u8>, pos: nat, end: nat, number: u32) -> Option<Option<(nat, nat)>> {
    match read_optional_context(b, pos, end, number) {
        None => None,
        Some(None) => Some(None),
        Some(Some((constructed, cstart, cend))) => {
            if constructed {
                Some(Some((cstart, cend)))
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The encoder: the DER encoding of a value (clauses 8, 10 and 11).
// ---------------------------------------------------------------------------

/// §8.1.2: the identifier octets of `tag` (whose number is below 2^14).
pub open spec fn encode_identifier(tag: Tag) -> Seq<u8> {
    // 8.1.2.2 a) and b), 8.1.2.5: the class and the primitive/constructed
    // bits of the leading octet.
    let first = class_bits(tag.class) * 64 + (if tag.constructed { 32u8 } else { 0u8 });
    if tag.number < 31 {
        // 8.1.2.2 c): "the number of the tag as a binary integer".
        seq![(first + tag.number as u8) as u8]
    } else if tag.number < 128 {
        // 8.1.2.4: one subsequent octet whose bit 8 is zero (8.1.2.4.2 a)
        // and whose bits 7 to 1 are the number.
        seq![(first + 31) as u8, tag.number as u8]
    } else {
        // 8.1.2.4: two subsequent octets, bit 8 set on the first
        // (8.1.2.4.2 a), the number base 128 across them (b); the first
        // digit is not zero (c) because the number is at least 128.
        seq![(first + 31) as u8, (128 + tag.number / 128) as u8, (tag.number % 128) as u8]
    }
}

/// The number of octets after the initial one in the long form of the
/// length `len` in the minimum number of octets (§10.1): the least `w` with
/// `len < 256^w`, for `len < 2^64`.
pub open spec fn length_octets(len: nat) -> nat {
    if len < 0x100 {
        1
    } else if len < 0x1_0000 {
        2
    } else if len < 0x100_0000 {
        3
    } else if len < 0x1_0000_0000 {
        4
    } else if len < 0x100_0000_0000 {
        5
    } else if len < 0x1_0000_0000_0000 {
        6
    } else if len < 0x100_0000_0000_0000 {
        7
    } else {
        8
    }
}

/// §8.1.3, §10.1: the length octets of `len` (below 2^64): the short form
/// for 127 or less, otherwise the long form in the fewest octets.
pub open spec fn encode_length(len: nat) -> Seq<u8> {
    if len < 128 {
        // 8.1.3.4.
        seq![len as u8]
    } else {
        // 8.1.3.5: the initial octet has bit 8 set and bits 7 to 1 the
        // number of subsequent octets; the subsequent octets are the length.
        let w = length_octets(len);
        seq![(128 + w) as u8] + be_bytes(len, w)
    }
}

/// §8.1.1.1: the encoding of a data value with the given tag and contents
/// octets: identifier octets, length octets, contents octets.
pub open spec fn encode_tlv(tag: Tag, contents: Seq<u8>) -> Seq<u8> {
    encode_identifier(tag) + encode_length(contents.len()) + contents
}

/// What a tag and contents must satisfy to be encoded: a tag number the
/// decoder accepts, and contents short enough for a length of at most 8
/// octets.
pub open spec fn tlv_ok(tag: Tag, contents: Seq<u8>) -> bool {
    tag.number <= MAX_TAG_NUMBER && contents.len() < pow256(8)
}

/// §8.2.2, §11.1: a BOOLEAN.
pub open spec fn encode_boolean(v: bool) -> Seq<u8> {
    encode_tlv(universal_primitive(BOOLEAN), seq![if v { 0xFFu8 } else { 0x00u8 }])
}

/// `s` without its leading zero octets.
pub open spec fn strip_leading_zeros(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && s[0] == 0 {
        strip_leading_zeros(s.drop_first())
    } else {
        s
    }
}

/// §8.3.2, §8.3.3: the contents octets of the INTEGER whose value is the
/// number the octets `m` spell base 256 (a non-negative number, most
/// significant octet first, leading zeros allowed): the octets without
/// leading zeros, one `0x00` octet for the value zero, and a `0x00` octet in
/// front when the first octet has bit 8 set, so the two's complement number
/// is not negative (§8.3.3).
pub open spec fn integer_unsigned_contents(m: Seq<u8>) -> Seq<u8> {
    let s = strip_leading_zeros(m);
    if s.len() == 0 {
        seq![0u8]
    } else if s[0] >= 128 {
        seq![0u8] + s
    } else {
        s
    }
}

/// An INTEGER of a non-negative value given as its magnitude octets.
pub open spec fn encode_integer_unsigned(m: Seq<u8>) -> Seq<u8> {
    encode_tlv(universal_primitive(INTEGER), integer_unsigned_contents(m))
}

/// §8.6.2: a primitive BIT STRING with `unused` unused bits (0 to 7) in the
/// final octet of `bits`, whose unused bits are zero (§11.2.1), and which is
/// empty only with `unused` zero (§8.6.2.3).
pub open spec fn encode_bit_string(unused: u8, bits: Seq<u8>) -> Seq<u8> {
    encode_tlv(universal_primitive(BIT_STRING), seq![unused] + bits)
}

/// §8.7.2: a primitive OCTET STRING.
pub open spec fn encode_octet_string(s: Seq<u8>) -> Seq<u8> {
    encode_tlv(universal_primitive(OCTET_STRING), s)
}

/// A primitive value of the universal type `number` with contents `s`
/// (UTF8String, PrintableString, IA5String, UTCTime, GeneralizedTime).
pub open spec fn encode_octets(number: u32, s: Seq<u8>) -> Seq<u8> {
    encode_tlv(universal_primitive(number), s)
}

/// §8.8: NULL, `05 00`.
pub open spec fn encode_null() -> Seq<u8> {
    encode_tlv(universal_primitive(NULL), seq![])
}

/// §8.19.2: the octets of a subidentifier prefix: the digits of `w` base
/// 128, most significant first, each with bit 8 set ("bit 8 of each
/// preceding octet is one"). No leading digit is zero.
pub open spec fn subidentifier_prefix(w: nat) -> Seq<u8>
    decreases w,
{
    if w == 0 {
        seq![]
    } else {
        subidentifier_prefix(w / 128) + seq![(128 + w % 128) as u8]
    }
}

/// §8.19.2: the octets of the subidentifier `v` in the fewest possible
/// octets: its digits base 128, with bit 8 of the last octet zero.
pub open spec fn encode_subidentifier(v: nat) -> Seq<u8> {
    subidentifier_prefix(v / 128) + seq![(v % 128) as u8]
}

/// The octets of a list of subidentifiers, concatenated (§8.19.2).
pub open spec fn encode_subidentifiers(subs: Seq<nat>) -> Seq<u8>
    decreases subs.len(),
{
    if subs.len() == 0 {
        seq![]
    } else {
        encode_subidentifier(subs[0]) + encode_subidentifiers(subs.drop_first())
    }
}

/// What the components of an object identifier must satisfy to be encoded:
/// at least two; the first is 0, 1 or 2, and the second is below 40 unless
/// the first is 2 (§8.19.4 and X.660); and every subidentifier fits the
/// limit.
pub open spec fn oid_valid(arcs: Seq<nat>) -> bool {
    &&& arcs.len() >= 2
    &&& arcs[0] <= 2
    &&& arcs[0] < 2 ==> arcs[1] < 40
    &&& 40 * arcs[0] + arcs[1] < 0x1_0000_0000_0000_0000
    &&& forall|i: int| 2 <= i < arcs.len() ==> arcs[i] < 0x1_0000_0000_0000_0000
}

/// §8.19.2 to §8.19.5: the contents octets of an object identifier.
pub open spec fn oid_contents(arcs: Seq<nat>) -> Seq<u8> {
    // 8.19.4: the first subidentifier is (X*40) + Y; 8.19.5: the others are
    // the remaining components.
    encode_subidentifiers(seq![40 * arcs[0] + arcs[1]] + arcs.skip(2))
}

/// An OBJECT IDENTIFIER (§8.19.1: primitive).
pub open spec fn encode_oid(arcs: Seq<nat>) -> Seq<u8> {
    encode_tlv(universal_primitive(OBJECT_IDENTIFIER), oid_contents(arcs))
}

/// §8.9.1: a SEQUENCE, constructed, with the given contents (the
/// concatenated encodings of its components).
pub open spec fn encode_sequence(contents: Seq<u8>) -> Seq<u8> {
    encode_tlv(universal_constructed(SEQUENCE), contents)
}

/// §8.11.1: a SET, constructed.
pub open spec fn encode_set(contents: Seq<u8>) -> Seq<u8> {
    encode_tlv(universal_constructed(SET), contents)
}

/// §8.14: a value with a context-specific tag `[number]` around `contents`:
/// for an EXPLICIT tag the contents are one complete encoding and the form
/// is constructed (§8.14.3); for an IMPLICIT tag they are the base
/// encoding's contents in the base encoding's form (§8.14.4).
pub open spec fn encode_context(number: u32, constructed: bool, contents: Seq<u8>) -> Seq<u8> {
    encode_tlv(context_specific(number, constructed), contents)
}

/// The `DigestInfo` of RFC 8017 §9.2: `SEQUENCE { digestAlgorithm
/// AlgorithmIdentifier { algorithm OID, parameters NULL }, digest OCTET
/// STRING }`, for the components `arcs` of the algorithm identifier and the
/// digest octets.
pub open spec fn encode_digest_info(arcs: Seq<nat>, digest: Seq<u8>) -> Seq<u8> {
    encode_sequence(encode_sequence(encode_oid(arcs) + encode_null()) + encode_octet_string(digest))
}

/// Termination of [`subidentifiers`]: the series that ends at `j` leaves a
/// strictly shorter rest.
#[via_fn]
pub proof fn subidentifiers_decreases(c: Seq<u8>) {
    if c.len() > 0 {
        super::termination::lemma_series_end_bounds(c, 0, c.len());
    }
}

} // verus!
