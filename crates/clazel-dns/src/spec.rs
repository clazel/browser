//! Executable-style specification of the DNS message format, transcribed
//! from RFC 1035 "Domain Names - Implementation and Specification"
//! (November 1987, STD 13, <https://www.rfc-editor.org/rfc/rfc1035>), with
//! the AAAA record of RFC 3596 "DNS Extensions to Support IP Version 6"
//! (October 2003, <https://www.rfc-editor.org/rfc/rfc3596>), the alias
//! rules of RFC 1034 §3.6.2 and §5.3.3 (<https://www.rfc-editor.org/rfc/rfc1034>),
//! and the reply checks of RFC 5452 §4 to §6
//! (<https://www.rfc-editor.org/rfc/rfc5452>). An RFC is immutable, so
//! there is no commit to pin. Nothing here runs; it defines what "correct"
//! means. RFC 1035 has no numbered steps, so a comment `// §4.1.4` cites
//! the section and quotes the sentence it transcribes.
//!
//! ## What is covered
//!
//! - §4.1.1 the header, §4.1.2 the question, §4.1.3 resource records;
//! - §4.1.4 message compression, with the reading of "a prior occurrence"
//!   given below;
//! - §2.3.4 size limits (labels 63 octets or less, names 255 octets or
//!   less, UDP messages 512 octets or less), §2.3.3 case;
//! - §3.2.2 and §3.2.4 TYPE and CLASS values, §3.3.1 CNAME, §3.4.1 A, and
//!   RFC 3596 §2.1 and §2.2 AAAA;
//! - §4.2.2 the two-octet length of a message sent over TCP;
//! - building a standard query, and extracting the addresses of an answer.
//!
//! Not covered: EDNS(0) (RFC 6891, so no OPT record is ever built and one
//! that arrives is opaque), DNSSEC, and every RDATA format other than A,
//! AAAA and CNAME (each is kept as opaque RDATA, never an error).
//!
//! ## Modelling choices
//!
//! Each is a deviation in form, never in meaning, unless it says otherwise;
//! the argument is given here once.
//!
//! - **A domain name is held in its uncompressed wire format** (§3.1: "each
//!   label is represented as a one octet length field followed by that
//!   number of octets ... a domain name is terminated by a length byte of
//!   zero"): the length octets, the label octets and the final zero, as a
//!   `Seq<u8>`. §2.3.4's "names 255 octets or less" is then
//!   `name.len() <= 255`, and §2.3.3's case-insensitive comparison is
//!   [`bytes_eq_ci`] on the octets. Labels are not split into a list of
//!   strings: that would add a bijection to prove and carry nothing the
//!   wire form lacks.
//! - **"A prior occurrence" means a name that lies wholly before the
//!   pointer.** §4.1.4 says a pointer replaces a name "with a pointer to a
//!   prior occurance of the same name". Read as only "an earlier offset"
//!   (the target is below the pointer's own offset) it still permits a
//!   loop: a label at offset 0 followed by a pointer to offset 0. The
//!   evident intent is a name that already occurred, that is, one that ends
//!   before the pointer starts. [`read_name`] therefore carries a `limit`:
//!   the octets of the name read from a pointer's target must end at or
//!   before the pointer's offset, and a pointer in that part is checked
//!   against its own offset in turn. A target at or above the pointer's own
//!   offset is an error too (step "pointer": the target is "prior"). Every
//!   legitimate message satisfies this, since a name is compressed only
//!   against names that ended earlier. See ERRATA.md.
//! - **The message is a record of decoded sections.** A decoded
//!   [`Message`] holds the header, and the question and the three
//!   resource-record sections as sequences, in the order they appear, with
//!   every name expanded (compression removed). RDATA of types the profile
//!   interprets (A, AAAA and CNAME, in class IN) is decoded; every other
//!   RDATA is kept as its octets, including NS, SOA, PTR and MX, whose
//!   names may hold compression pointers: those are left unexpanded and are
//!   never interpreted here.
//! - **Z is three bits and must be zero** (§4.1.1: "Reserved for future
//!   use. Must be zero in all queries and responses"). RFC 2535 and RFC
//!   4035 later assigned two of those bits (AD and CD); a message that sets
//!   either is rejected here. This is deliberately strict, and the resolver
//!   shell fails closed on it.
//! - **The TTL is kept as the unsigned 32-bit value that was sent.** §2.3.4
//!   says "positive values of a signed 32 bit number", and RFC 2181 §8 says
//!   a value with the high bit set is to be treated as zero. Nothing in the
//!   profile uses the TTL, so it is not interpreted.
//! - **Trailing octets are rejected.** The message ends where the last
//!   resource record ends; octets after it make the message invalid. (RFC
//!   1035 does not say; a datagram or a TCP message of the stated length
//!   is exactly one message.)
//! - **A message is at most 65535 octets** (§4.2.2: the TCP length field is
//!   two octets), and at most 512 over UDP (§2.3.4) when decoded with
//!   [`decode_udp`]. No EDNS(0) is used, so a larger datagram is invalid.
//! - **The name of a query is given as a dotted ASCII string** (the form
//!   `clazel-url` produces after IDNA), converted to wire form by
//!   [`dotted_to_wire`]: labels separated by `.`, one trailing `.`
//!   allowed, `.` alone the root; every octet below 128. An empty label,
//!   a label over 63 octets or a name over 255 octets makes the name
//!   invalid (`None`).
//! - **A name read from a reply is turned back into a dotted string by
//!   [`wire_to_dotted`]**, for the shell to ask about again (a CNAME target,
//!   RFC 1034 §5.3.3 step 3a). It is the inverse of [`dotted_to_wire`] on
//!   what the encoder can write: an uncompressed wire name (§3.1) of at
//!   least one label, joined by `.` with no trailing dot. A name that has
//!   no dotted spelling is `None`: the root (it has no labels, and `.`
//!   is not a host to ask about), a label that holds a `.` (the dotted form
//!   would split it in two) or an octet of 128 or more, a compression
//!   pointer or a reserved length octet (§3.1: the high two bits of a length
//!   octet are zero), and a name over 255 octets (§2.3.4). Octets other
//!   than letters, digits and hyphen are kept: §2.3.1's preferred syntax is
//!   advice ("should"), and the encoder does not enforce it either.
//! - **Addresses are numbers.** An A record's address is the `u32` its four
//!   octets spell in network order, an AAAA record's the `u128` its sixteen
//!   octets spell ([`be_value`]).
//! - **Answer extraction follows the chain to its end** (RFC 1034 §3.6.2:
//!   "if a CNAME RR is present at a node, no other data should be present";
//!   §5.3.3 step 3a: "if the data is a CNAME, ... change the QNAME to the
//!   canonical name"). The chain is followed through the answer section
//!   only, from the first CNAME record at each name, at most as many hops
//!   as there are answer records (so a loop is an error). The addresses
//!   are those of the final name only: an alias that also has address data
//!   breaks §3.6.2's rule and its data is not used. If at least one CNAME
//!   was followed and the final name has no address in the answer section,
//!   the final name is reported as `redirect`, for a new query (§5.3.3
//!   step 3a), and no addresses are returned.
//! - **A reply is accepted only if it answers this query** (RFC 5452 §4:
//!   "the query ID ... and the question section must match"; §6: names
//!   compared case-insensitively): QR set, OPCODE 0, TC clear, the ID the
//!   query's, exactly one question equal (case-insensitively) to the
//!   query's, and RCODE 0 or 3. TC is checked by [`answer_addresses`] only
//!   in that it makes the reply unusable; the caller reads the flag with the
//!   message to decide to retry over TCP (RFC 7766 §8).
//! - **Query types are A and AAAA.** `answer_addresses` accepts no other
//!   QTYPE.
//! - **`resolv.conf` is ours.** RFC 1035 has no file format; the grammar of
//!   [`nameservers`] is in `resolv/spec.rs`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §2.3.4 size limits and §3.2 values.
// ---------------------------------------------------------------------------

/// §2.3.4: "labels 63 octets or less".
pub const MAX_LABEL: usize = 63;

/// §2.3.4: "names 255 octets or less".
pub const MAX_NAME: usize = 255;

/// §2.3.4: "UDP messages 512 octets or less".
pub const MAX_UDP: usize = 512;

/// §4.2.2: the length of a TCP message is a two octet field.
pub const MAX_TCP: usize = 65535;

/// §3.2.2: TYPE 1, "a host address".
pub const TYPE_A: u16 = 1;

/// §3.2.2: TYPE 5, "the canonical name for an alias".
pub const TYPE_CNAME: u16 = 5;

/// RFC 3596 §2.1: "A new resource record type is defined to store a host's
/// IPv6 address ... The AAAA resource record type is a record specific to
/// the Internet class ... The value of the type is 28".
pub const TYPE_AAAA: u16 = 28;

/// §3.2.4: CLASS 1, "the Internet".
pub const CLASS_IN: u16 = 1;

// ---------------------------------------------------------------------------
// Data model.
// ---------------------------------------------------------------------------

/// §4.1.1: the header section. The flags are the bits of the second pair
/// of octets: `QR`, `Opcode`, `AA`, `TC`, `RD`, `RA`, `Z`, `RCODE`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    /// "A 16 bit identifier assigned by the program that generates any kind
    /// of query."
    pub id: u16,
    /// "A one bit field that specifies whether this message is a query (0),
    /// or a response (1)." True for a response.
    pub qr: bool,
    /// "A four bit field that specifies kind of query in this message."
    pub opcode: u8,
    /// "Authoritative Answer".
    pub aa: bool,
    /// "TrunCation - specifies that this message was truncated due to
    /// length greater than that permitted on the transmission channel."
    pub tc: bool,
    /// "Recursion Desired".
    pub rd: bool,
    /// "Recursion Available".
    pub ra: bool,
    /// "Reserved for future use. Must be zero in all queries and
    /// responses." Three bits; a decoded message has zero here.
    pub z: u8,
    /// "Response code - this 4 bit field is set as part of responses."
    pub rcode: u8,
    /// "The number of entries in the question section."
    pub qdcount: u16,
    /// "The number of resource records in the answer section."
    pub ancount: u16,
    /// "The number of name server resource records in the authority records
    /// section."
    pub nscount: u16,
    /// "The number of resource records in the additional records section."
    pub arcount: u16,
}

/// §4.1.2: a question: QNAME, QTYPE, QCLASS.
pub struct Question {
    /// QNAME, in uncompressed wire format.
    pub name: Seq<u8>,
    /// QTYPE.
    pub qtype: u16,
    /// QCLASS.
    pub qclass: u16,
}

/// The RDATA of a resource record, decoded where the profile interprets it.
pub enum Rdata {
    /// §3.4.1 A (class IN, TYPE 1): "A 32 bit Internet address". The number
    /// the four octets spell.
    A(u32),
    /// RFC 3596 §2.2 AAAA (class IN, TYPE 28): "A 128 bit IPv6 address is
    /// encoded in the data portion of an AAAA resource record in network
    /// byte order". The number the sixteen octets spell.
    Aaaa(u128),
    /// §3.3.1 CNAME (class IN, TYPE 5): "A <domain-name> which specifies
    /// the canonical or primary name for the owner", in uncompressed wire
    /// format.
    Cname(Seq<u8>),
    /// Every other type or class: the RDATA octets, uninterpreted.
    Opaque(Seq<u8>),
}

/// §4.1.3: a resource record. RDLENGTH is implied by the RDATA.
pub struct Rr {
    /// NAME: "a domain name to which this resource record pertains", in
    /// uncompressed wire format.
    pub name: Seq<u8>,
    /// TYPE.
    pub rtype: u16,
    /// CLASS.
    pub rclass: u16,
    /// TTL, as sent.
    pub ttl: u32,
    /// RDATA.
    pub rdata: Rdata,
}

/// §4.1: a decoded message.
pub struct Message {
    /// The header.
    pub header: Header,
    /// The question section, `header.qdcount` questions.
    pub questions: Seq<Question>,
    /// The answer section, `header.ancount` records.
    pub answers: Seq<Rr>,
    /// The authority section, `header.nscount` records.
    pub authority: Seq<Rr>,
    /// The additional section, `header.arcount` records.
    pub additional: Seq<Rr>,
}

/// An address from an A or AAAA record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Addr {
    /// An IPv4 address, as the number its four octets spell.
    V4(u32),
    /// An IPv6 address, as the number its sixteen octets spell.
    V6(u128),
}

// ---------------------------------------------------------------------------
// Numbers in network byte order (§2.3.2 "bits are numbered from the left,
// most significant first"; §4.1.1 fields are in network order).
// ---------------------------------------------------------------------------

/// The unsigned integer `s` spells in network byte order, most significant
/// octet first.
pub open spec fn be_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        be_value(s.drop_last()) * 256 + s.last() as nat
    }
}

/// The 16-bit field at `pos`.
pub open spec fn u16_at(b: Seq<u8>, pos: nat) -> nat {
    b[pos as int] as nat * 256 + b[pos as int + 1] as nat
}

/// The 32-bit field at `pos`.
pub open spec fn u32_at(b: Seq<u8>, pos: nat) -> nat {
    u16_at(b, pos) * 65536 + u16_at(b, pos + 2)
}

/// The two octets of a 16-bit field, most significant first.
pub open spec fn be16(v: nat) -> Seq<u8> {
    seq![(v / 256 % 256) as u8, (v % 256) as u8]
}

// ---------------------------------------------------------------------------
// §2.3.3 case.
// ---------------------------------------------------------------------------

/// §2.3.3: "For all parts of the DNS that are part of the official
/// protocol, all comparisons between character strings (e.g., labels,
/// domain names, etc.) are done in a case-insensitive manner." Case is
/// folded for the ASCII letters A to Z (and only those).
pub open spec fn lower(x: u8) -> u8 {
    if 65 <= x && x <= 90 {
        (x + 32) as u8
    } else {
        x
    }
}

/// The octets of `a` and `b` from `i` on are equal up to case.
pub open spec fn eq_from(a: Seq<u8>, b: Seq<u8>, i: nat) -> bool
    decreases a.len() - i
{
    if i >= a.len() {
        true
    } else if lower(a[i as int]) != lower(b[i as int]) {
        false
    } else {
        eq_from(a, b, i + 1)
    }
}

/// §2.3.3: two names (or labels) are equal if they are the same length and
/// their octets are equal up to case. The decoder keeps the octets as they
/// were sent; this is how they are compared. (Length octets are at most 63,
/// so folding them changes nothing: two wire names compare label by
/// label.)
pub open spec fn bytes_eq_ci(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() == b.len() && eq_from(a, b, 0)
}

// ---------------------------------------------------------------------------
// §4.1.1 header.
// ---------------------------------------------------------------------------

/// §4.1.1: the header from the first twelve octets of `b`. `None` if there
/// are fewer, or if Z is not zero.
pub open spec fn decode_header(b: Seq<u8>) -> Option<Header> {
    if b.len() < 12 {
        // "The header contains the following fields": twelve octets.
        None
    } else {
        let w = u16_at(b, 2);
        let z = (w / 16) % 8;
        if z != 0 {
            // "Z  Reserved for future use.  Must be zero in all queries and
            //  responses."
            None
        } else {
            Some(Header {
                id: u16_at(b, 0) as u16,
                qr: (w / 32768) % 2 == 1,
                opcode: ((w / 2048) % 16) as u8,
                aa: (w / 1024) % 2 == 1,
                tc: (w / 512) % 2 == 1,
                rd: (w / 256) % 2 == 1,
                ra: (w / 128) % 2 == 1,
                z: z as u8,
                rcode: (w % 16) as u8,
                qdcount: u16_at(b, 4) as u16,
                ancount: u16_at(b, 6) as u16,
                nscount: u16_at(b, 8) as u16,
                arcount: u16_at(b, 10) as u16,
            })
        }
    }
}

// ---------------------------------------------------------------------------
// §3.1 and §4.1.4: domain names.
// ---------------------------------------------------------------------------

/// `s` is a sequence of labels, each a length octet from 1 to 63 followed
/// by that many octets (§3.1, §2.3.4).
pub open spec fn is_labels(s: Seq<u8>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        1 <= s[0] && s[0] <= 63 && s.len() >= 1 + s[0] as nat && is_labels(s.skip(1 + s[0] as int))
    }
}

/// §3.1 and §2.3.4: a domain name in wire format: labels of 1 to 63 octets,
/// ended by a zero length octet, 255 octets or less in all.
pub open spec fn is_wire_name(s: Seq<u8>) -> bool {
    1 <= s.len() && s.len() <= 255 && s.last() == 0 && is_labels(s.drop_last())
}

/// §4.1.4: read the domain name at `pos`, expanding compression pointers.
/// `limit` is the offset the octets of the name must end at or before: the
/// end of the message (or of the RDATA) at first, and after a pointer at
/// offset `p`, `p` itself (see "A prior occurrence" in the header). `acc`
/// is the expanded name so far, without its final zero octet, and `end` the
/// offset after the name where it started: the offset after the first
/// pointer, if one was followed (§4.1.4: "If a domain name is contained in
/// a part of the message subject to a length field ..., and compression is
/// used, the length of the compressed name is used in the length
/// calculation, rather than the length of the expanded name"). Returns the
/// expanded name, with its zero octet, and the offset where the name ended
/// in the message.
pub open spec fn read_name(b: Seq<u8>, pos: nat, limit: nat, acc: Seq<u8>, end: Option<nat>) -> Option<(Seq<u8>, nat)>
    decreases limit, limit - pos
{
    if pos >= limit || limit > b.len() {
        // The name runs past the message (or past where it must end).
        None
    } else {
        let len = b[pos as int];
        if len == 0 {
            // §3.1: "a domain name is terminated by a length byte of zero".
            // The end of the name is after this octet unless a pointer was
            // followed.
            Some((acc.push(0), match end {
                Some(e) => e,
                None => pos + 1,
            }))
        } else if len < 64 {
            // §4.1.4: "the label must begin with two zero bits". A label of
            // `len` octets, 63 or less (§2.3.4).
            if pos + 1 + len as nat > limit {
                None
            } else if acc.len() + 1 + len as nat > 254 {
                // §2.3.4: "names 255 octets or less": with the final zero
                // octet, the labels may take 254.
                None
            } else {
                read_name(b, pos + 1 + len as nat, limit, acc + b.subrange(pos as int, pos as int + 1 + len as int), end)
            }
        } else if len >= 192 {
            // §4.1.4: "The first two bits are ones. This allows a pointer to
            // be distinguished from a label". The pointer takes two octets.
            if pos + 2 > limit {
                None
            } else {
                // "The OFFSET field specifies an offset from the start of
                // the message".
                let target: nat = ((len as nat - 192) * 256 + b[pos as int + 1] as nat) as nat;
                if target >= pos {
                    // "a prior occurance": a target at or after the pointer
                    // is not one.
                    None
                } else {
                    // The name continues at `target` and must end before
                    // this pointer; the name's own end is after the pointer.
                    read_name(b, target, pos, acc, Some(match end {
                        Some(e) => e,
                        None => pos + 2,
                    }))
                }
            }
        } else {
            // §4.1.4: "(The 10 and 01 combinations are reserved for future
            // use.)"
            None
        }
    }
}

/// The domain name at `pos`: it may extend to the end of the message.
pub open spec fn decode_name(b: Seq<u8>, pos: nat) -> Option<(Seq<u8>, nat)> {
    read_name(b, pos, b.len(), seq![], None)
}

// ---------------------------------------------------------------------------
// §4.1.2 question and §4.1.3 resource records.
// ---------------------------------------------------------------------------

/// §4.1.2: the question at `pos`: QNAME, then "QTYPE a two octet code" and
/// "QCLASS a two octet code". Returns it and the offset after it.
pub open spec fn read_question(b: Seq<u8>, pos: nat) -> Option<(Question, nat)> {
    match decode_name(b, pos) {
        None => None,
        Some((name, p)) => {
            if p + 4 > b.len() {
                None
            } else {
                Some((Question { name, qtype: u16_at(b, p) as u16, qclass: u16_at(b, p + 2) as u16 }, p + 4))
            }
        },
    }
}

/// §3.3.1, §3.4.1 and RFC 3596 §2.2: the RDATA in `b` from `rstart` to
/// `rend` of a record with TYPE `rtype` and CLASS `rclass`.
pub open spec fn decode_rdata(b: Seq<u8>, rtype: u16, rclass: u16, rstart: nat, rend: nat) -> Option<Rdata> {
    if rclass == CLASS_IN && rtype == TYPE_A {
        // §3.4.1: "ADDRESS A 32 bit Internet address."
        if rend - rstart == 4 {
            Some(Rdata::A(u32_at(b, rstart) as u32))
        } else {
            None
        }
    } else if rclass == CLASS_IN && rtype == TYPE_AAAA {
        // RFC 3596 §2.2: "A 128 bit IPv6 address".
        if rend - rstart == 16 {
            Some(Rdata::Aaaa(be_value(b.subrange(rstart as int, rend as int)) as u128))
        } else {
            None
        }
    } else if rclass == CLASS_IN && rtype == TYPE_CNAME {
        // §3.3.1: "CNAME A <domain-name>". The name lies in the RDATA
        // (RDLENGTH counts the compressed form) and fills it.
        match read_name(b, rstart, rend, seq![], None) {
            Some((name, e)) => {
                if e == rend {
                    Some(Rdata::Cname(name))
                } else {
                    None
                }
            },
            None => None,
        }
    } else {
        // §3.2.2: types that are not interpreted are kept as opaque RDATA,
        // never an error.
        Some(Rdata::Opaque(b.subrange(rstart as int, rend as int)))
    }
}

/// §4.1.3: the resource record at `pos`: NAME, "TYPE two octets", "CLASS
/// two octets", "TTL a 32 bit unsigned integer", "RDLENGTH an unsigned 16
/// bit integer that specifies the length in octets of the RDATA field",
/// RDATA. Returns it and the offset after it.
pub open spec fn read_rr(b: Seq<u8>, pos: nat) -> Option<(Rr, nat)> {
    match decode_name(b, pos) {
        None => None,
        Some((name, p)) => {
            if p + 10 > b.len() {
                // The fixed fields are cut short.
                None
            } else {
                let rdlength = u16_at(b, p + 8);
                let rstart = p + 10;
                let rend = rstart + rdlength;
                if rend > b.len() {
                    // The RDATA is cut short.
                    None
                } else {
                    let rtype = u16_at(b, p) as u16;
                    let rclass = u16_at(b, p + 2) as u16;
                    match decode_rdata(b, rtype, rclass, rstart, rend) {
                        None => None,
                        Some(rdata) => Some((Rr { name, rtype, rclass, ttl: u32_at(b, p + 4) as u32, rdata }, rend)),
                    }
                }
            }
        },
    }
}

/// §4.1.2: `n` questions from `pos`, appended to `acc`.
pub open spec fn read_questions(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Question>) -> Option<(Seq<Question>, nat)>
    decreases n
{
    if n == 0 {
        Some((acc, pos))
    } else {
        match read_question(b, pos) {
            None => None,
            Some((q, e)) => read_questions(b, e, (n - 1) as nat, acc.push(q)),
        }
    }
}

/// §4.1.3: `n` resource records from `pos`, appended to `acc`.
pub open spec fn read_rrs(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Rr>) -> Option<(Seq<Rr>, nat)>
    decreases n
{
    if n == 0 {
        Some((acc, pos))
    } else {
        match read_rr(b, pos) {
            None => None,
            Some((r, e)) => read_rrs(b, e, (n - 1) as nat, acc.push(r)),
        }
    }
}

// ---------------------------------------------------------------------------
// §4.1 messages.
// ---------------------------------------------------------------------------

/// §4.1: decode a message: the header, then "the question section", "the
/// answer section", "the authority section" and "the additional space
/// section", with as many entries as the header's counts say. `None` is an
/// invalid message.
pub open spec fn decode_message(b: Seq<u8>) -> Option<Message> {
    if b.len() > MAX_TCP {
        // §4.2.2: no message is longer than its two octet length field
        // can state.
        None
    } else {
        match decode_header(b) {
            None => None,
            Some(h) => match read_questions(b, 12, h.qdcount as nat, seq![]) {
                None => None,
                Some((questions, p1)) => match read_rrs(b, p1, h.ancount as nat, seq![]) {
                    None => None,
                    Some((answers, p2)) => match read_rrs(b, p2, h.nscount as nat, seq![]) {
                        None => None,
                        Some((authority, p3)) => match read_rrs(b, p3, h.arcount as nat, seq![]) {
                            None => None,
                            Some((additional, p4)) => {
                                if p4 == b.len() {
                                    Some(Message { header: h, questions, answers, authority, additional })
                                } else {
                                    // Octets after the last record.
                                    None
                                }
                            },
                        },
                    },
                },
            },
        }
    }
}

/// §2.3.4: "UDP messages 512 octets or less": decode a datagram.
pub open spec fn decode_udp(b: Seq<u8>) -> Option<Message> {
    if b.len() > MAX_UDP {
        None
    } else {
        decode_message(b)
    }
}

// ---------------------------------------------------------------------------
// Query names: dotted ASCII to wire format.
// ---------------------------------------------------------------------------

/// Scan the dotted name `s` from `i`; `start` is where the current label
/// began, and `acc` is the wire format of the labels completed so far.
/// Returns the wire format of all the labels, without the final zero octet.
pub open spec fn dotted_scan(s: Seq<u8>, i: nat, start: nat, acc: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len() - i
{
    if i >= s.len() {
        if i > start {
            // The last label has no dot after it.
            if i - start > MAX_LABEL as nat {
                // §2.3.4: "labels 63 octets or less".
                None
            } else {
                Some(acc + seq![(i - start) as u8] + s.subrange(start as int, i as int))
            }
        } else {
            // The name ended with a dot.
            Some(acc)
        }
    } else if s[i as int] == 46 {
        if i == start || i - start > MAX_LABEL as nat {
            // An empty label ("a..b" or ".a"), or one over 63 octets.
            None
        } else {
            dotted_scan(s, i + 1, i + 1, acc + seq![(i - start) as u8] + s.subrange(start as int, i as int))
        }
    } else if s[i as int] >= 128 {
        // The name is ASCII.
        None
    } else {
        dotted_scan(s, i + 1, start, acc)
    }
}

/// A host name as a dotted ASCII string, in wire format (§3.1), or `None`
/// if it is not a valid name: empty, with an empty label, a label over 63
/// octets, a name over 255 octets, or with an octet of 128 or more. `.` is
/// the root.
pub open spec fn dotted_to_wire(s: Seq<u8>) -> Option<Seq<u8>> {
    if s.len() == 0 {
        None
    } else if s == seq![46u8] {
        Some(seq![0u8])
    } else {
        match dotted_scan(s, 0, 0, seq![]) {
            None => None,
            Some(w) => {
                if w.len() + 1 > MAX_NAME as nat {
                    // §2.3.4: "names 255 octets or less", with the zero
                    // octet.
                    None
                } else {
                    Some(w + seq![0u8])
                }
            },
        }
    }
}

/// A label that can stand between dots: no `.` and only ASCII, the octets
/// [`dotted_scan`] accepts inside a label.
pub open spec fn is_dotted_label(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) != 46 && s[i] < 128
}

/// `a` and `b` are dotted names or empty; the dotted name of both, `a`
/// first: they are joined by a `.` unless one is empty.
pub open spec fn join_dotted(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else {
        a + seq![46u8] + b
    }
}

/// §3.1: the labels of the wire name `w` from `pos`, as a dotted string, or
/// `None` if they are not labels ended by the zero octet that is the last
/// octet of `w`. `Some` of the empty string is the root label alone.
pub open spec fn wire_scan(w: Seq<u8>, pos: nat) -> Option<Seq<u8>>
    decreases w.len() - pos
{
    if pos >= w.len() {
        // §3.1: "a domain name is terminated by a length byte of zero": the
        // name ended without it.
        None
    } else if w[pos as int] == 0 {
        if pos + 1 == w.len() {
            Some(seq![])
        } else {
            // Octets after the root label: not one name.
            None
        }
    } else if w[pos as int] > MAX_LABEL as u8 || pos + 1 + w[pos as int] as nat > w.len() {
        // §3.1: "the high order two bits of every length octet must be
        // zero", so a length over 63 (a compression pointer, §4.1.4, or a
        // reserved value) is not a label; nor is one that runs past the end.
        None
    } else {
        let label = w.subrange(pos as int + 1, pos as int + 1 + w[pos as int] as int);
        if !is_dotted_label(label) {
            None
        } else {
            match wire_scan(w, pos + 1 + w[pos as int] as nat) {
                None => None,
                Some(rest) => Some(join_dotted(label, rest)),
            }
        }
    }
}

/// An uncompressed wire name as a dotted ASCII string (the inverse of
/// [`dotted_to_wire`], see the modelling choices): `None` if it is not a
/// wire name of 255 octets or less with at least one label, or if a label
/// has no dotted spelling.
pub open spec fn wire_to_dotted(w: Seq<u8>) -> Option<Seq<u8>> {
    if w.len() > MAX_NAME as nat {
        // §2.3.4: "names 255 octets or less".
        None
    } else {
        match wire_scan(w, 0) {
            None => None,
            // The root has no label to write.
            Some(d) => if d.len() == 0 { None } else { Some(d) },
        }
    }
}

// ---------------------------------------------------------------------------
// Building a query.
// ---------------------------------------------------------------------------

/// A query for the records of type `qtype` at `name`, a dotted ASCII
/// string, sent with message ID `id`.
pub struct Query {
    /// The message ID (§4.1.1 ID).
    pub id: u16,
    /// The name, as a dotted ASCII string.
    pub name: Seq<u8>,
    /// QTYPE.
    pub qtype: u16,
}

/// The header of a standard query (§4.1.1): ID `id`, QR 0 ("a query"),
/// OPCODE 0 ("a standard query"), AA, TC, RA and Z 0, RD 1 ("directs the
/// name server to pursue the query recursively"), RCODE 0, one question
/// and no records.
pub open spec fn query_header(id: u16) -> Header {
    Header {
        id,
        qr: false,
        opcode: 0,
        aa: false,
        tc: false,
        rd: true,
        ra: false,
        z: 0,
        rcode: 0,
        qdcount: 1,
        ancount: 0,
        nscount: 0,
        arcount: 0,
    }
}

/// The twelve octets of [`query_header`]: the ID, the flags word 0x0100
/// (only RD), and the counts 1, 0, 0, 0.
pub open spec fn query_header_bytes(id: u16) -> Seq<u8> {
    be16(id as nat) + seq![1u8, 0u8] + be16(1) + be16(0) + be16(0) + be16(0)
}

/// §4.1: a standard query for `q`: the header, and one question (§4.1.2)
/// with the name in full (no compression), QTYPE `qtype` and QCLASS IN.
/// `None` if the name is not valid.
pub open spec fn encode_query(q: Query) -> Option<Seq<u8>> {
    match dotted_to_wire(q.name) {
        None => None,
        Some(w) => Some(query_header_bytes(q.id) + w + be16(q.qtype as nat) + be16(CLASS_IN as nat)),
    }
}

// ---------------------------------------------------------------------------
// §4.2.2 TCP.
// ---------------------------------------------------------------------------

/// §4.2.2: "The message is prefixed with a two byte length field which
/// gives the message length, excluding the two byte length field." `None`
/// if the message is longer than 65535 octets.
pub open spec fn tcp_frame(msg: Seq<u8>) -> Option<Seq<u8>> {
    if msg.len() > MAX_TCP {
        None
    } else {
        Some(be16(msg.len()) + msg)
    }
}

/// §4.2.2: the length of the message at the start of `b`, if `b` holds the
/// whole of its two octet length field and the message it states ("This
/// length field allows the low-level processing to assemble a complete
/// message before beginning to parse it"). `None` while more is needed.
pub open spec fn tcp_message_len(b: Seq<u8>) -> Option<nat> {
    if b.len() < 2 {
        None
    } else {
        let n = u16_at(b, 0);
        if b.len() < 2 + n {
            None
        } else {
            Some(n)
        }
    }
}

// ---------------------------------------------------------------------------
// Answer extraction: RFC 1034 §3.6.2, §5.3.3; RFC 5452 §4 to §6.
// ---------------------------------------------------------------------------

/// What a reply gives for a query: the addresses to use, or a name to ask
/// about instead.
pub struct Resolution {
    /// The addresses of the answer section's records at the final name.
    pub addresses: Seq<Addr>,
    /// The last CNAME target, when the chain from the query name leaves the
    /// answer section without an address (RFC 1034 §5.3.3 step 3a).
    pub redirect: Option<Seq<u8>>,
}

/// The address a record gives for a query of type `qtype`: an A record for
/// QTYPE A, an AAAA record for QTYPE AAAA, both class IN.
pub open spec fn rr_addr(rr: Rr, qtype: u16) -> Option<Addr> {
    match rr.rdata {
        Rdata::A(a) => if qtype == TYPE_A && rr.rtype == TYPE_A && rr.rclass == CLASS_IN {
            Some(Addr::V4(a))
        } else {
            None
        },
        Rdata::Aaaa(a) => if qtype == TYPE_AAAA && rr.rtype == TYPE_AAAA && rr.rclass == CLASS_IN {
            Some(Addr::V6(a))
        } else {
            None
        },
        _ => None,
    }
}

/// The target of a CNAME record (class IN, TYPE 5).
pub open spec fn rr_cname(rr: Rr) -> Option<Seq<u8>> {
    match rr.rdata {
        Rdata::Cname(t) => if rr.rtype == TYPE_CNAME && rr.rclass == CLASS_IN {
            Some(t)
        } else {
            None
        },
        _ => None,
    }
}

/// RFC 1034 §3.6.2: the target of the first CNAME record in `answers`
/// whose owner is `name` (compared as §2.3.3 says).
pub open spec fn cname_next(answers: Seq<Rr>, name: Seq<u8>) -> Option<Seq<u8>>
    decreases answers.len()
{
    if answers.len() == 0 {
        None
    } else {
        match rr_cname(answers[0]) {
            Some(t) => if bytes_eq_ci(answers[0].name, name) {
                Some(t)
            } else {
                cname_next(answers.drop_first(), name)
            },
            None => cname_next(answers.drop_first(), name),
        }
    }
}

/// RFC 1034 §5.3.3 step 3a: follow CNAME records from `cur` through
/// `answers`, counting `hops`; at most `fuel` more hops (a longer chain
/// has a loop). Returns the final name and the number of hops.
pub open spec fn chain_end(answers: Seq<Rr>, cur: Seq<u8>, hops: nat, fuel: nat) -> Option<(Seq<u8>, nat)>
    decreases fuel
{
    match cname_next(answers, cur) {
        None => Some((cur, hops)),
        Some(t) => if fuel == 0 {
            None
        } else {
            chain_end(answers, t, hops + 1, (fuel - 1) as nat)
        },
    }
}

/// The addresses, in order, of the records of `answers` whose owner is
/// `name` and which give an address for `qtype`.
pub open spec fn collect(answers: Seq<Rr>, name: Seq<u8>, qtype: u16) -> Seq<Addr>
    decreases answers.len()
{
    if answers.len() == 0 {
        seq![]
    } else {
        let rest = collect(answers.drop_first(), name, qtype);
        match rr_addr(answers[0], qtype) {
            Some(a) => if bytes_eq_ci(answers[0].name, name) {
                seq![a] + rest
            } else {
                rest
            },
            None => rest,
        }
    }
}

/// The addresses a reply `m` gives for the query `q`, or `None` if the
/// reply is not an acceptable answer to it.
pub open spec fn answer_addresses(q: Query, m: Message) -> Option<Resolution> {
    match dotted_to_wire(q.name) {
        None => None,
        Some(qname) => {
            if q.qtype != TYPE_A && q.qtype != TYPE_AAAA {
                None
            } else if !m.header.qr || m.header.opcode != 0 || m.header.tc || m.header.id != q.id {
                // RFC 5452 §4: the ID must match, and the message must be a
                // response to a standard query. A truncated reply is not an
                // answer (RFC 7766 §8: retry over TCP).
                None
            } else if !(m.questions.len() == 1 && bytes_eq_ci(m.questions[0].name, qname) && m.questions[0].qtype == q.qtype
                && m.questions[0].qclass == CLASS_IN) {
                // RFC 5452 §4: "the question section ... must match".
                None
            } else if m.header.rcode == 3 {
                // §4.1.1 RCODE 3: "Name Error - Meaningful only for
                // responses from an authoritative name server, this code
                // signifies that the domain name referenced in the query
                // does not exist." No addresses.
                Some(Resolution { addresses: seq![], redirect: None })
            } else if m.header.rcode != 0 {
                None
            } else {
                match chain_end(m.answers, qname, 0, m.answers.len()) {
                    None => None,
                    Some((fin, hops)) => {
                        let addresses = collect(m.answers, fin, q.qtype);
                        if hops > 0 && addresses.len() == 0 {
                            // §5.3.3 step 3a: the chain leaves the answer
                            // section; the caller asks about `fin`.
                            Some(Resolution { addresses: seq![], redirect: Some(fin) })
                        } else {
                            Some(Resolution { addresses, redirect: None })
                        }
                    },
                }
            }
        },
    }
}

} // verus!
