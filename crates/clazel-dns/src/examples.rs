//! The standard's examples, and the rejections the spec's rules demand,
//! evaluated on the spec: RFC 1035 §4.1.4's compression example (F.ISI.ARPA,
//! FOO.F.ISI.ARPA, ARPA and the root), a header with every field different,
//! the pointer errors, the size limits, a query, and replies for the answer
//! rules.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies, even with
//! `--verify-function`. A mutant that breaks an example would otherwise
//! fail every kill certificate placed next to it, not only the one about
//! the example. The lemmas here are theorems about the spec like any other,
//! so kill certificates (`mutations.json`) may name them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `n` octets of `v`.
pub open spec fn fill(v: u8, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        seq![]
    } else {
        fill(v, (n - 1) as nat).push(v)
    }
}

// ---------------------------------------------------------------------------
// RFC 1035 §4.1.4: the compression example.
// ---------------------------------------------------------------------------

/// The message of §4.1.4's figure, ignoring "the other fields of the
/// message": the names F.ISI.ARPA at offset 20, FOO.F.ISI.ARPA at 40 (FOO,
/// then a pointer to 20), ARPA at 64 (a pointer to 26) and the root at 92.
/// Every other octet is zero.
pub open spec fn rfc_figure() -> Seq<u8> {
    fill(0, 20) + seq![1u8, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0] + fill(0, 8) + seq![3u8, 70, 79, 79, 0xC0, 20] + fill(0, 18)
        + seq![0xC0u8, 26] + fill(0, 26) + seq![0u8]
}

/// §4.1.4: "The domain name for F.ISI.ARPA is shown at offset 20. The domain
/// name FOO.F.ISI.ARPA is shown at offset 40; this definition uses a
/// pointer to concatenate a label for FOO to the previously defined
/// F.ISI.ARPA. The domain name ARPA is defined at offset 64 using a pointer
/// to the ARPA component of the name F.ISI.ARPA at 20; note that this
/// pointer relies on ARPA being the last label in the string at 20. The
/// root domain name is defined by a single zero octet at 92." Each name is
/// read back in full, and the offset after it is where the name ended in
/// the message.
pub proof fn lemma_rfc_1035_4_1_4_example()
    ensures
        rfc_figure().len() == 93,
        decode_name(rfc_figure(), 20) == Some((seq![1u8, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 32nat)),
        decode_name(rfc_figure(), 40) == Some((seq![3u8, 70, 79, 79, 1, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 46nat)),
        decode_name(rfc_figure(), 64) == Some((seq![4u8, 65, 82, 80, 65, 0], 66nat)),
        decode_name(rfc_figure(), 92) == Some((seq![0u8], 93nat)),
{
    assert(rfc_figure().len() == 93) by (compute_only);
    assert(decode_name(rfc_figure(), 20) == Some((seq![1u8, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 32nat))) by (compute_only);
    assert(decode_name(rfc_figure(), 40) == Some((seq![3u8, 70, 79, 79, 1, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 46nat))) by (compute_only);
    assert(decode_name(rfc_figure(), 64) == Some((seq![4u8, 65, 82, 80, 65, 0], 66nat))) by (compute_only);
    assert(decode_name(rfc_figure(), 92) == Some((seq![0u8], 93nat))) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.1.4: pointers that are errors.
// ---------------------------------------------------------------------------

/// A pointer to itself, and a pointer forward, are errors: neither is "a
/// prior occurance".
pub proof fn lemma_pointer_not_prior()
    ensures
        decode_name(seq![0xC0u8, 0], 0) is None,
        decode_name(seq![0xC0u8, 2, 0], 0) is None,
        decode_name(seq![0x00u8, 0xC0, 3, 0], 1) is None,
{
    assert(decode_name(seq![0xC0u8, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0xC0u8, 2, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0x00u8, 0xC0, 3, 0], 1) is None) by (compute_only);
}

/// A pointer to a lower offset is not enough: a label at offset 0 and a
/// pointer at offset 2 back to 0 would be read forever. The name read from
/// the pointer's target must end before the pointer, so it is an error.
pub proof fn lemma_pointer_loop_rejected()
    ensures
        decode_name(seq![1u8, 97, 0xC0, 0], 2) is None,
        decode_name(seq![1u8, 97, 0xC0, 0], 0) is None,
        // Two pointers that point at each other's predecessor.
        decode_name(seq![0xC0u8, 2, 0xC0, 0], 2) is None,
{
    assert(decode_name(seq![1u8, 97, 0xC0, 0], 2) is None) by (compute_only);
    assert(decode_name(seq![1u8, 97, 0xC0, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0xC0u8, 2, 0xC0, 0], 2) is None) by (compute_only);
}

/// A pointer whose target name would run over the pointer itself is an
/// error, though it is at a lower offset: the label at offset 0 covers the
/// octets of the pointer at offset 2.
pub proof fn lemma_pointer_overlap_rejected()
    ensures
        decode_name(seq![4u8, 0x41, 0xC0, 0x00, 0x42, 0], 2) is None,
{
    assert(decode_name(seq![4u8, 0x41, 0xC0, 0x00, 0x42, 0], 2) is None) by (compute_only);
}

/// A pointer to an earlier name that itself ends in a pointer is followed
/// to the end (a name at 0, a pointer at 3 to it, a pointer at 5 to that
/// one), and the name ends after the first pointer.
pub proof fn lemma_pointer_chain()
    ensures
        decode_name(seq![1u8, 97, 0, 0xC0, 0, 0xC0, 3], 5) == Some((seq![1u8, 97, 0], 7nat)),
        decode_name(seq![1u8, 97, 0, 2, 98, 99, 0xC0, 0], 3) == Some((seq![2u8, 98, 99, 1, 97, 0], 8nat)),
{
    assert(decode_name(seq![1u8, 97, 0, 0xC0, 0, 0xC0, 3], 5) == Some((seq![1u8, 97, 0], 7nat))) by (compute_only);
    assert(decode_name(seq![1u8, 97, 0, 2, 98, 99, 0xC0, 0], 3) == Some((seq![2u8, 98, 99, 1, 97, 0], 8nat))) by (compute_only);
}

/// §4.1.4: "(The 10 and 01 combinations are reserved for future use.)", a
/// pointer cut short, and a label cut short are errors.
pub proof fn lemma_name_errors()
    ensures
        decode_name(seq![0x40u8, 0], 0) is None,
        decode_name(seq![0x80u8, 0], 0) is None,
        decode_name(seq![0xC0u8], 0) is None,
        decode_name(seq![3u8, 97, 98], 0) is None,
        decode_name(seq![1u8, 97], 0) is None,
        decode_name(seq![0u8], 1) is None,
{
    assert(decode_name(seq![0x40u8, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0x80u8, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0xC0u8], 0) is None) by (compute_only);
    assert(decode_name(seq![3u8, 97, 98], 0) is None) by (compute_only);
    assert(decode_name(seq![1u8, 97], 0) is None) by (compute_only);
    assert(decode_name(seq![0u8], 1) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §2.3.4: size limits.
// ---------------------------------------------------------------------------

/// A label of 63 octets is the longest: the length octet 64 begins with the
/// bits 01, which are reserved.
pub proof fn lemma_label_limit()
    ensures
        decode_name(seq![63u8] + fill(97, 63) + seq![0u8], 0) == Some((seq![63u8] + fill(97, 63) + seq![0u8], 65nat)),
        decode_name(seq![64u8] + fill(97, 64) + seq![0u8], 0) is None,
{
    assert(decode_name(seq![63u8] + fill(97, 63) + seq![0u8], 0) == Some((seq![63u8] + fill(97, 63) + seq![0u8], 65nat)))
        by (compute_only);
    assert(decode_name(seq![64u8] + fill(97, 64) + seq![0u8], 0) is None) by (compute_only);
}

/// A name of 255 octets is the longest: three labels of 63 octets, one of
/// 61, and the zero octet make 255; one more octet in the last label makes
/// 256.
pub proof fn lemma_name_limit()
    ensures
        decode_name(max_name(61), 0) == Some((max_name(61), 255nat)),
        decode_name(max_name(62), 0) is None,
{
    assert(decode_name(max_name(61), 0) == Some((max_name(61), 255nat))) by (compute_only);
    assert(decode_name(max_name(62), 0) is None) by (compute_only);
}

/// Three labels of 63 octets, then one of `n`, and the zero octet.
pub open spec fn max_name(n: nat) -> Seq<u8> {
    seq![63u8] + fill(97, 63) + seq![63u8] + fill(97, 63) + seq![63u8] + fill(97, 63) + seq![n as u8] + fill(97, n) + seq![0u8]
}

/// The same limits for the names of queries, which are dotted: a label of
/// 63 octets and a name of 255 are accepted, and 64 and 256 are not.
pub proof fn lemma_dotted_limits()
    ensures
        dotted_to_wire(fill(97, 63)) == Some(seq![63u8] + fill(97, 63) + seq![0u8]),
        dotted_to_wire(fill(97, 64)) is None,
        dotted_to_wire(fill(97, 64) + seq![46u8, 97]) is None,
        dotted_to_wire(dotted_name(61)) == Some(max_name(61)),
        dotted_to_wire(dotted_name(62)) is None,
{
    assert(dotted_to_wire(fill(97, 63)) == Some(seq![63u8] + fill(97, 63) + seq![0u8])) by (compute_only);
    assert(dotted_to_wire(fill(97, 64)) is None) by (compute_only);
    assert(dotted_to_wire(fill(97, 64) + seq![46u8, 97]) is None) by (compute_only);
    assert(dotted_to_wire(dotted_name(61)) == Some(max_name(61))) by (compute_only);
    assert(dotted_to_wire(dotted_name(62)) is None) by (compute_only);
}

/// Three labels of 63 octets and one of `n`, separated by dots.
pub open spec fn dotted_name(n: nat) -> Seq<u8> {
    fill(97, 63) + seq![46u8] + fill(97, 63) + seq![46u8] + fill(97, 63) + seq![46u8] + fill(97, n)
}

/// Dotted names: the root, a trailing dot, and what is not a name.
pub proof fn lemma_dotted_names()
    ensures
        dotted_to_wire(seq![46u8]) == Some(seq![0u8]),
        dotted_to_wire(seq![97u8]) == Some(seq![1u8, 97, 0]),
        dotted_to_wire(seq![97u8, 46]) == Some(seq![1u8, 97, 0]),
        dotted_to_wire(seq![97u8, 46, 98, 99]) == Some(seq![1u8, 97, 2, 98, 99, 0]),
        dotted_to_wire(seq![]) is None,
        dotted_to_wire(seq![97u8, 46, 46, 98]) is None,
        dotted_to_wire(seq![46u8, 97]) is None,
        dotted_to_wire(seq![46u8, 46]) is None,
        dotted_to_wire(seq![97u8, 128]) is None,
{
    assert(dotted_to_wire(seq![46u8]) == Some(seq![0u8])) by (compute_only);
    assert(dotted_to_wire(seq![97u8]) == Some(seq![1u8, 97, 0])) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 46]) == Some(seq![1u8, 97, 0])) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 46, 98, 99]) == Some(seq![1u8, 97, 2, 98, 99, 0])) by (compute_only);
    assert(dotted_to_wire(seq![]) is None) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 46, 46, 98]) is None) by (compute_only);
    assert(dotted_to_wire(seq![46u8, 97]) is None) by (compute_only);
    assert(dotted_to_wire(seq![46u8, 46]) is None) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 128]) is None) by (compute_only);
}

/// Wire names to dotted names: labels joined by dots, and everything that
/// has no dotted spelling (the root, no zero octet, octets after it, a label
/// with a dot or an octet of 128 or more, a pointer, a label that runs past
/// the end).
pub proof fn lemma_wire_names()
    ensures
        wire_to_dotted(seq![4u8, 114, 101, 97, 108, 4, 116, 101, 115, 116, 0]) == Some(seq![114u8, 101, 97, 108, 46, 116, 101, 115, 116]),
        wire_to_dotted(seq![1u8, 97, 0]) == Some(seq![97u8]),
        wire_to_dotted(seq![1u8, 97, 1, 98, 1, 99, 0]) == Some(seq![97u8, 46, 98, 46, 99]),
        wire_to_dotted(seq![1u8, 65, 0]) == Some(seq![65u8]),
        wire_to_dotted(seq![0u8]) is None,
        wire_to_dotted(seq![]) is None,
        wire_to_dotted(seq![4u8, 114, 101, 97, 108]) is None,
        wire_to_dotted(seq![4u8, 114, 101, 97, 108, 0, 0]) is None,
        wire_to_dotted(seq![3u8, 97, 46, 98, 0]) is None,
        wire_to_dotted(seq![3u8, 97, 128, 98, 0]) is None,
        wire_to_dotted(seq![0xC0u8, 0x0C]) is None,
        wire_to_dotted(seq![5u8, 97, 98, 0]) is None,
{
    assert(wire_to_dotted(seq![4u8, 114, 101, 97, 108, 4, 116, 101, 115, 116, 0]) == Some(seq![114u8, 101, 97, 108, 46, 116, 101, 115, 116])) by (compute_only);
    assert(wire_to_dotted(seq![1u8, 97, 0]) == Some(seq![97u8])) by (compute_only);
    assert(wire_to_dotted(seq![1u8, 97, 1, 98, 1, 99, 0]) == Some(seq![97u8, 46, 98, 46, 99])) by (compute_only);
    assert(wire_to_dotted(seq![1u8, 65, 0]) == Some(seq![65u8])) by (compute_only);
    assert(wire_to_dotted(seq![0u8]) is None) by (compute_only);
    assert(wire_to_dotted(seq![]) is None) by (compute_only);
    assert(wire_to_dotted(seq![4u8, 114, 101, 97, 108]) is None) by (compute_only);
    assert(wire_to_dotted(seq![4u8, 114, 101, 97, 108, 0, 0]) is None) by (compute_only);
    assert(wire_to_dotted(seq![3u8, 97, 46, 98, 0]) is None) by (compute_only);
    assert(wire_to_dotted(seq![3u8, 97, 128, 98, 0]) is None) by (compute_only);
    assert(wire_to_dotted(seq![0xC0u8, 0x0C]) is None) by (compute_only);
    assert(wire_to_dotted(seq![5u8, 97, 98, 0]) is None) by (compute_only);
}

/// The limits, from the wire side: a label of 63 octets and a name of 255
/// are spelled, a label of 64 (a length octet that is not a label's) and a
/// name of 256 are not. The names are the same as in [`lemma_dotted_limits`].
pub proof fn lemma_wire_limits()
    ensures
        wire_to_dotted(seq![63u8] + fill(97, 63) + seq![0u8]) == Some(fill(97, 63)),
        wire_to_dotted(seq![64u8] + fill(97, 64) + seq![0u8]) is None,
        wire_to_dotted(max_name(61)) == Some(dotted_name(61)),
        wire_to_dotted(max_name(62)) is None,
{
    assert(wire_to_dotted(seq![63u8] + fill(97, 63) + seq![0u8]) == Some(fill(97, 63))) by (compute_only);
    assert(wire_to_dotted(seq![64u8] + fill(97, 64) + seq![0u8]) is None) by (compute_only);
    assert(wire_to_dotted(max_name(61)) == Some(dotted_name(61))) by (compute_only);
    assert(wire_to_dotted(max_name(62)) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.1.1: the header.
// ---------------------------------------------------------------------------

/// A header with every field different from its neighbours: ID 0x1234,
/// flags 0xAA8A (QR, OPCODE 5, TC, RA, RCODE 10) and the counts 3, 2, 1, 4.
pub proof fn lemma_header_fields()
    ensures
        decode_header(seq![0x12u8, 0x34, 0xAA, 0x8A, 0, 3, 0, 2, 0, 1, 0, 4]) == Some(
            Header {
                id: 0x1234,
                qr: true,
                opcode: 5,
                aa: false,
                tc: true,
                rd: false,
                ra: true,
                z: 0,
                rcode: 10,
                qdcount: 3,
                ancount: 2,
                nscount: 1,
                arcount: 4,
            },
        ),
{
    assert(decode_header(seq![0x12u8, 0x34, 0xAA, 0x8A, 0, 3, 0, 2, 0, 1, 0, 4]) == Some(
        Header {
            id: 0x1234,
            qr: true,
            opcode: 5,
            aa: false,
            tc: true,
            rd: false,
            ra: true,
            z: 0,
            rcode: 10,
            qdcount: 3,
            ancount: 2,
            nscount: 1,
            arcount: 4,
        },
    )) by (compute_only);
}

/// The other flag bits, one at a time: AA and RD (clear above), and the
/// header is too short, or has Z set (§4.1.1: "Must be zero in all queries
/// and responses").
pub proof fn lemma_header_other_bits()
    ensures
        decode_header(seq![0u8, 0, 0x05, 0x00, 0, 0, 0, 0, 0, 0, 0, 0]) == Some(
            Header {
                id: 0,
                qr: false,
                opcode: 0,
                aa: true,
                tc: false,
                rd: true,
                ra: false,
                z: 0,
                rcode: 0,
                qdcount: 0,
                ancount: 0,
                nscount: 0,
                arcount: 0,
            },
        ),
        decode_header(seq![0u8, 0, 0x00, 0x10, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_header(seq![0u8, 0, 0x00, 0x20, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_header(seq![0u8, 0, 0x00, 0x40, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_header(seq![0u8, 0, 0x00, 0x00, 0, 0, 0, 0, 0, 0, 0]) is None,
{
    assert(decode_header(seq![0u8, 0, 0x05, 0x00, 0, 0, 0, 0, 0, 0, 0, 0]) == Some(
        Header {
            id: 0,
            qr: false,
            opcode: 0,
            aa: true,
            tc: false,
            rd: true,
            ra: false,
            z: 0,
            rcode: 0,
            qdcount: 0,
            ancount: 0,
            nscount: 0,
            arcount: 0,
        },
    )) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x10, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x20, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x40, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x00, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §3.3.1, §3.4.1, RFC 3596, RFC 1034 §3.6.2 and RFC 5452: answers.
// ---------------------------------------------------------------------------

/// The name `a` in wire format.
pub open spec fn na() -> Seq<u8> {
    seq![1u8, 97, 0]
}

/// The name `b` in wire format.
pub open spec fn nb() -> Seq<u8> {
    seq![1u8, 98, 0]
}

/// The name `c` in wire format.
pub open spec fn nc() -> Seq<u8> {
    seq![1u8, 99, 0]
}

/// The name `A` (the same as `a` up to case).
pub open spec fn na_upper() -> Seq<u8> {
    seq![1u8, 65, 0]
}

/// An A record of class IN.
pub open spec fn a_rr(owner: Seq<u8>, address: u32) -> Rr {
    Rr { name: owner, rtype: 1, rclass: 1, ttl: 300, rdata: Rdata::A(address) }
}

/// An AAAA record of class IN.
pub open spec fn aaaa_rr(owner: Seq<u8>, address: u128) -> Rr {
    Rr { name: owner, rtype: 28, rclass: 1, ttl: 300, rdata: Rdata::Aaaa(address) }
}

/// A CNAME record of class IN.
pub open spec fn cname_rr(owner: Seq<u8>, target: Seq<u8>) -> Rr {
    Rr { name: owner, rtype: 5, rclass: 1, ttl: 300, rdata: Rdata::Cname(target) }
}

/// The header of a reply with ID 7, QR set, OPCODE 0, TC `tc`, RCODE
/// `rcode`, RD and RA set, and the given counts.
pub open spec fn reply_header(tc: bool, rcode: u8, qd: u16, an: u16, ns: u16, ar: u16) -> Header {
    Header {
        id: 7,
        qr: true,
        opcode: 0,
        aa: false,
        tc,
        rd: true,
        ra: true,
        z: 0,
        rcode,
        qdcount: qd,
        ancount: an,
        nscount: ns,
        arcount: ar,
    }
}

/// A reply with ID 7, QR set, OPCODE 0, TC `tc`, RCODE `rcode` and the
/// question `qname`, QTYPE `qtype`, class IN.
pub open spec fn reply(
    qname: Seq<u8>,
    qtype: u16,
    tc: bool,
    rcode: u8,
    answers: Seq<Rr>,
    authority: Seq<Rr>,
    additional: Seq<Rr>,
) -> Message {
    Message {
        header: reply_header(tc, rcode, 1, answers.len() as u16, authority.len() as u16, additional.len() as u16),
        questions: seq![Question { name: qname, qtype, qclass: 1 }],
        answers,
        authority,
        additional,
    }
}

/// The query "a", type A, ID 7.
pub open spec fn query_a() -> Query {
    Query { id: 7, name: seq![97u8], qtype: 1 }
}

/// The query "a", type AAAA, ID 7.
pub open spec fn query_aaaa() -> Query {
    Query { id: 7, name: seq![97u8], qtype: 28 }
}

/// A direct answer, and the reply's case: the owner `A` matches the query
/// `a` (§2.3.3), and the question `A` matches too (RFC 5452 §6).
pub proof fn lemma_answer_direct()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304), a_rr(na(), 0x05060708)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(0x01020304), Addr::V4(0x05060708)], redirect: None }),
        answer_addresses(query_a(), reply(na_upper(), 1, false, 0, seq![a_rr(na_upper(), 0x01020304)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(0x01020304)], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(nb(), 0x01020304)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
{
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304), a_rr(na(), 0x05060708)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(0x01020304), Addr::V4(0x05060708)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na_upper(), 1, false, 0, seq![a_rr(na_upper(), 0x01020304)], seq![], seq![]))
        == Some(Resolution { addresses: seq![Addr::V4(0x01020304)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(nb(), 0x01020304)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
}

/// RFC 3596: an AAAA query takes AAAA records and ignores A records, and an
/// A query takes A records and ignores AAAA records; only A and AAAA are
/// queried.
pub proof fn lemma_answer_types()
    ensures
        answer_addresses(query_aaaa(), reply(na(), 28, false, 0, seq![aaaa_rr(na(), 0x0102030405060708090a0b0c0d0e0f10)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V6(0x0102030405060708090a0b0c0d0e0f10)], redirect: None }),
        answer_addresses(query_aaaa(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![aaaa_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(Query { id: 7, name: seq![97u8], qtype: 5 }, reply(na(), 5, false, 0, seq![], seq![], seq![])) is None,
{
    assert(answer_addresses(
        query_aaaa(),
        reply(na(), 28, false, 0, seq![aaaa_rr(na(), 0x0102030405060708090a0b0c0d0e0f10)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V6(0x0102030405060708090a0b0c0d0e0f10)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_aaaa(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![aaaa_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(Query { id: 7, name: seq![97u8], qtype: 5 }, reply(na(), 5, false, 0, seq![], seq![], seq![])) is None)
        by (compute_only);
}

/// RFC 1034 §3.6.2: a CNAME chain inside the answer section is followed,
/// in whatever order the records come, and its owners are compared up to
/// case; only the final name's addresses are returned.
pub proof fn lemma_answer_cname_chain()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc()), a_rr(nc(), 9)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None }),
        answer_addresses(
            query_a(),
            reply(na(), 1, false, 0, seq![a_rr(nc(), 9), cname_rr(seq![1u8, 66, 0], nc()), cname_rr(na_upper(), nb())], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(na(), 5), cname_rr(na(), nb()), a_rr(nb(), 6)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(6)], redirect: None }),
{
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc()), a_rr(nc(), 9)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![a_rr(nc(), 9), cname_rr(seq![1u8, 66, 0], nc()), cname_rr(na_upper(), nb())], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(na(), 5), cname_rr(na(), nb()), a_rr(nb(), 6)], seq![], seq![]))
        == Some(Resolution { addresses: seq![Addr::V4(6)], redirect: None })) by (compute_only);
}

/// RFC 1034 §5.3.3 step 3a: a chain that leaves the answer section gives
/// the last target to ask about and no addresses; a loop is an error.
pub proof fn lemma_answer_cname_redirect()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc())], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: Some(nc()) }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb())], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: Some(nb()) }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), na())], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), na())], seq![], seq![])) is None,
{
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc())], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: Some(nc()) })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb())], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: Some(nb()) })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), na())], seq![], seq![])) is None)
        by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), na())], seq![], seq![])) is None) by (compute_only);
}

/// The authority and additional sections are never used: addresses in them
/// are not returned, and a CNAME there is not followed.
pub proof fn lemma_answer_sections()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![], seq![a_rr(na(), 1)], seq![a_rr(na(), 2)]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![], seq![cname_rr(na(), nb())], seq![cname_rr(na(), nb()), a_rr(nb(), 2)]))
            == Some(Resolution { addresses: seq![], redirect: None }),
{
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![], seq![a_rr(na(), 1)], seq![a_rr(na(), 2)]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![], seq![cname_rr(na(), nb())], seq![cname_rr(na(), nb()), a_rr(nb(), 2)]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
}

/// RCODE 3 (name error) gives no addresses; every other RCODE but 0 is
/// refused (RFC 1035 §4.1.1: 1 format error, 2 server failure, 4 not
/// implemented, 5 refused).
pub proof fn lemma_answer_rcodes()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 3, seq![], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 3, seq![a_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 1, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 2, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 4, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 5, seq![a_rr(na(), 1)], seq![], seq![])) is None,
{
    assert(answer_addresses(query_a(), reply(na(), 1, false, 3, seq![], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 3, seq![a_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 1, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 2, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 4, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 5, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
}

/// RFC 5452 §4 to §6: a reply is refused if its ID or question differ from
/// the query's, if it is not a response to a standard query, or if it is
/// truncated.
pub proof fn lemma_answer_matching()
    ensures
        answer_addresses(Query { id: 8, name: seq![97u8], qtype: 1 }, reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(nb(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(
            query_a(),
            Message {
                questions: seq![Question { name: na(), qtype: 1, qclass: 3 }],
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(
            query_a(),
            Message { questions: seq![], ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![]) },
        ) is None,
        answer_addresses(
            query_a(),
            Message {
                questions: seq![Question { name: na(), qtype: 1, qclass: 1 }, Question { name: na(), qtype: 1, qclass: 1 }],
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(
            query_a(),
            Message {
                header: Header { qr: false, ..reply_header(false, 0, 1, 1, 0, 0) },
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(
            query_a(),
            Message {
                header: Header { opcode: 2, ..reply_header(false, 0, 1, 1, 0, 0) },
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(query_a(), reply(na(), 1, true, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
{
    assert(answer_addresses(Query { id: 8, name: seq![97u8], qtype: 1 }, reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None)
        by (compute_only);
    assert(answer_addresses(query_a(), reply(nb(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            questions: seq![Question { name: na(), qtype: 1, qclass: 3 }],
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message { questions: seq![], ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![]) },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            questions: seq![Question { name: na(), qtype: 1, qclass: 1 }, Question { name: na(), qtype: 1, qclass: 1 }],
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            header: Header { qr: false, ..reply_header(false, 0, 1, 1, 0, 0) },
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            header: Header { opcode: 2, ..reply_header(false, 0, 1, 1, 0, 0) },
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, true, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.1: a whole message, and the query we send.
// ---------------------------------------------------------------------------

/// The query for "example.com", type A, ID 0x1234, built octet by octet from
/// §4.1: the header (ID, flags 0x0100, QDCOUNT 1, no records), QNAME, QTYPE
/// 1 and QCLASS 1; and for AAAA, a trailing dot, the root, and a bad name.
pub proof fn lemma_query_example()
    ensures
        encode_query(Query { id: 0x1234, name: seq![101u8, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109], qtype: 1 }) == Some(
            seq![0x12u8, 0x34, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1],
        ),
        encode_query(Query { id: 0xABCD, name: seq![97u8, 46], qtype: 28 }) == Some(
            seq![0xABu8, 0xCD, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 1, 97, 0, 0, 28, 0, 1],
        ),
        encode_query(Query { id: 1, name: seq![46u8], qtype: 1 }) == Some(seq![0u8, 1, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]),
        encode_query(Query { id: 1, name: seq![97u8, 46, 46, 98], qtype: 1 }) is None,
{
    assert(encode_query(Query { id: 0x1234, name: seq![101u8, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109], qtype: 1 }) == Some(
        seq![0x12u8, 0x34, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1],
    )) by (compute_only);
    assert(encode_query(Query { id: 0xABCD, name: seq![97u8, 46], qtype: 28 }) == Some(
        seq![0xABu8, 0xCD, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 1, 97, 0, 0, 28, 0, 1],
    )) by (compute_only);
    assert(encode_query(Query { id: 1, name: seq![46u8], qtype: 1 }) == Some(seq![0u8, 1, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]))
        by (compute_only);
    assert(encode_query(Query { id: 1, name: seq![97u8, 46, 46, 98], qtype: 1 }) is None) by (compute_only);
}

/// A reply built from §4.1 and §3.4.1: the header (ID 7, flags 0x8180: QR,
/// RD, RA), one question "a" A IN, and one answer whose owner is a pointer
/// to the question's name at offset 12 (§4.1.4), type A, class IN, TTL
/// 300, RDLENGTH 4, address 1.2.3.4. It decodes to the message; with TC set
/// in the flags it decodes with TC set (§4.1.1).
pub proof fn lemma_reply_example()
    ensures
        decode_message(
            seq![0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
        ) == Some(reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![])),
        decode_message(
            seq![0u8, 7, 0x83, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
        ) == Some(reply(na(), 1, true, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![])),
{
    assert(decode_message(
        seq![0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
    ) == Some(reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![]))) by (compute_only);
    assert(decode_message(
        seq![0u8, 7, 0x83, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
    ) == Some(reply(na(), 1, true, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![]))) by (compute_only);
}

/// The record rules: RDLENGTH must be 4 for an A record and 16 for AAAA, a
/// CNAME's name must fill its RDATA, unknown types are kept as opaque
/// RDATA, a class other than IN is not interpreted, octets after the last
/// record are an error, and so is a count larger than what follows.
pub proof fn lemma_record_rules()
    ensures
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 3, 1, 2, 3]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 5, 1, 2, 3, 4, 5]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 28, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 1, 44, 0, 4, 1, 98, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 16, 0, 1, 0, 0, 1, 44, 0, 2, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(seq![1u8, 9]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0]) is None,
{
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 3, 1, 2, 3]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 5, 1, 2, 3, 4, 5]) is None)
        by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 28, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4]) is None)
        by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 1, 44, 0, 4, 1, 98, 0, 0]) is None)
        by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 16, 0, 1, 0, 0, 1, 44, 0, 2, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(seq![1u8, 9]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
}

/// §4.2.2 and §2.3.4: a two octet length, then the message; a UDP message
/// is 512 octets or less.
pub proof fn lemma_tcp_and_udp_limits()
    ensures
        tcp_frame(seq![9u8, 8, 7]) == Some(seq![0u8, 3, 9, 8, 7]),
        tcp_frame(fill(1, 300)) == Some(seq![1u8, 44] + fill(1, 300)),
        tcp_message_len(seq![0u8, 3, 9, 8, 7, 6]) == Some(3nat),
        tcp_message_len(seq![0u8, 3, 9, 8]) is None,
        tcp_message_len(seq![0u8]) is None,
        tcp_message_len(seq![1u8, 44] + fill(1, 300)) == Some(300nat),
        decode_udp(fill(0, 513)) is None,
{
    assert(tcp_frame(seq![9u8, 8, 7]) == Some(seq![0u8, 3, 9, 8, 7])) by (compute_only);
    assert(tcp_frame(fill(1, 300)) == Some(seq![1u8, 44] + fill(1, 300))) by (compute_only);
    assert(tcp_message_len(seq![0u8, 3, 9, 8, 7, 6]) == Some(3nat)) by (compute_only);
    assert(tcp_message_len(seq![0u8, 3, 9, 8]) is None) by (compute_only);
    assert(tcp_message_len(seq![0u8]) is None) by (compute_only);
    assert(tcp_message_len(seq![1u8, 44] + fill(1, 300)) == Some(300nat)) by (compute_only);
    assert(decode_udp(fill(0, 513)) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// More rules, one example each: the cases that tell one rule from its
// neighbours.
// ---------------------------------------------------------------------------

/// §4.1.4: "(The 10 and 01 combinations are reserved for future use.)" A
/// length octet of 0x40 to 0x7F or 0x80 to 0xBF is not a label, even when
/// that many octets follow.
pub proof fn lemma_reserved_prefixes()
    ensures
        decode_name(seq![0x80u8] + fill(97, 128) + seq![0u8], 0) is None,
        decode_name(seq![0x40u8] + fill(97, 64) + seq![0u8], 0) is None,
        decode_name(seq![0x7Fu8] + fill(97, 127) + seq![0u8], 0) is None,
        decode_name(seq![0xBFu8] + fill(97, 191) + seq![0u8], 0) is None,
{
    assert(decode_name(seq![0x80u8] + fill(97, 128) + seq![0u8], 0) is None) by (compute_only);
    assert(decode_name(seq![0x40u8] + fill(97, 64) + seq![0u8], 0) is None) by (compute_only);
    assert(decode_name(seq![0x7Fu8] + fill(97, 127) + seq![0u8], 0) is None) by (compute_only);
    assert(decode_name(seq![0xBFu8] + fill(97, 191) + seq![0u8], 0) is None) by (compute_only);
}

/// §4.1.4: the pointer's OFFSET is 14 bits: a pointer 0xC1 0x00 at offset
/// 270 points to offset 256, where the name "a" is.
pub proof fn lemma_pointer_offset_bits()
    ensures
        decode_name(fill(0, 256) + seq![1u8, 97, 0] + fill(0, 11) + seq![0xC1u8, 0x00], 270) == Some((seq![1u8, 97, 0], 272nat)),
        // 0xC1 0x2C is offset 300, which is not before the pointer.
        decode_name(fill(0, 256) + seq![1u8, 97, 0] + fill(0, 11) + seq![0xC1u8, 0x2C], 270) is None,
{
    assert(decode_name(fill(0, 256) + seq![1u8, 97, 0] + fill(0, 11) + seq![0xC1u8, 0x00], 270) == Some((seq![1u8, 97, 0], 272nat)))
        by (compute_only);
    assert(decode_name(fill(0, 256) + seq![1u8, 97, 0] + fill(0, 11) + seq![0xC1u8, 0x2C], 270) is None) by (compute_only);
}

/// §2.3.3: names compare equal up to the case of ASCII letters, and only
/// of those: `@` and `` ` `` (just outside A to Z and a to z) are not
/// letters, `[` and `{` neither; and lengths must agree.
pub proof fn lemma_case_folding()
    ensures
        bytes_eq_ci(seq![65u8], seq![97u8]),
        bytes_eq_ci(seq![97u8], seq![65u8]),
        bytes_eq_ci(seq![90u8], seq![122u8]),
        bytes_eq_ci(seq![1u8, 69, 88, 97, 77, 112, 76, 69, 0], seq![1u8, 101, 120, 65, 109, 80, 108, 101, 0]),
        !bytes_eq_ci(seq![64u8], seq![96u8]),
        !bytes_eq_ci(seq![91u8], seq![123u8]),
        !bytes_eq_ci(seq![65u8], seq![98u8]),
        !bytes_eq_ci(seq![97u8, 98u8], seq![97u8, 99u8]),
        !bytes_eq_ci(seq![97u8], seq![97u8, 98u8]),
        !bytes_eq_ci(seq![97u8, 98u8], seq![97u8]),
        bytes_eq_ci(seq![], seq![]),
{
    assert(bytes_eq_ci(seq![65u8], seq![97u8])) by (compute_only);
    assert(bytes_eq_ci(seq![97u8], seq![65u8])) by (compute_only);
    assert(bytes_eq_ci(seq![90u8], seq![122u8])) by (compute_only);
    assert(bytes_eq_ci(seq![1u8, 69, 88, 97, 77, 112, 76, 69, 0], seq![1u8, 101, 120, 65, 109, 80, 108, 101, 0])) by (compute_only);
    assert(!bytes_eq_ci(seq![64u8], seq![96u8])) by (compute_only);
    assert(!bytes_eq_ci(seq![91u8], seq![123u8])) by (compute_only);
    assert(!bytes_eq_ci(seq![65u8], seq![98u8])) by (compute_only);
    assert(!bytes_eq_ci(seq![97u8, 98u8], seq![97u8, 99u8])) by (compute_only);
    assert(!bytes_eq_ci(seq![97u8], seq![97u8, 98u8])) by (compute_only);
    assert(!bytes_eq_ci(seq![97u8, 98u8], seq![97u8])) by (compute_only);
    assert(bytes_eq_ci(seq![], seq![])) by (compute_only);
}

/// A reply for the question "a" AAAA IN with one AAAA answer whose owner is
/// a pointer to the question's name (RFC 3596 §2.2: "A 128 bit IPv6 address
/// is encoded in the data portion of an AAAA resource record in network byte
/// order"), and one for the question "a" A IN with a CNAME answer whose
/// RDATA is the label `b` followed by a pointer to "a" (§4.1.4: the length of
/// the compressed name is the RDLENGTH, 4).
pub proof fn lemma_reply_aaaa_and_cname()
    ensures
        decode_message(
            seq![
                0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 28, 0, 1, 0xC0, 12, 0, 28, 0, 1, 0, 0, 1, 44, 0, 16, 1, 2, 3, 4, 5, 6, 7,
                8, 9, 10, 11, 12, 13, 14, 15, 16,
            ],
        ) == Some(reply(na(), 28, false, 0, seq![aaaa_rr(na(), 0x0102030405060708090a0b0c0d0e0f10)], seq![], seq![])),
        decode_message(
            seq![0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 5, 0, 1, 0, 0, 1, 44, 0, 4, 1, 98, 0xC0, 12],
        ) == Some(reply(na(), 1, false, 0, seq![cname_rr(na(), seq![1u8, 98, 1, 97, 0])], seq![], seq![])),
{
    assert(decode_message(
        seq![
            0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 28, 0, 1, 0xC0, 12, 0, 28, 0, 1, 0, 0, 1, 44, 0, 16, 1, 2, 3, 4, 5, 6, 7, 8,
            9, 10, 11, 12, 13, 14, 15, 16,
        ],
    ) == Some(reply(na(), 28, false, 0, seq![aaaa_rr(na(), 0x0102030405060708090a0b0c0d0e0f10)], seq![], seq![]))) by (compute_only);
    assert(decode_message(
        seq![0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 5, 0, 1, 0, 0, 1, 44, 0, 4, 1, 98, 0xC0, 12],
    ) == Some(reply(na(), 1, false, 0, seq![cname_rr(na(), seq![1u8, 98, 1, 97, 0])], seq![], seq![]))) by (compute_only);
}

/// One answer, two authority and three additional records, each an A record
/// with its own address and a TTL of 60: the sections are read in that order
/// with the counts the header gives, and kept apart.
pub proof fn lemma_three_sections()
    ensures
        decode_message(seq![0u8, 7, 129, 128, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 2, 2, 2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 4, 4, 4, 4, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 3, 3, 3, 3, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 5, 5, 5, 5, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 6, 6, 6, 6]) == Some(Message {
                header: reply_header(false, 0, 0, 1, 2, 3),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x01010101) }],
                authority: seq![Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x02020202) }, Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x04040404) }],
                additional: seq![Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x03030303) }, Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x05050505) }, Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x06060606) }],
            }),
{
    assert(decode_message(seq![0u8, 7, 129, 128, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 2, 2, 2, 2, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 4, 4, 4, 4, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 3, 3, 3, 3, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 5, 5, 5, 5, 0, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 6, 6, 6, 6]) == Some(Message {
                header: reply_header(false, 0, 0, 1, 2, 3),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x01010101) }],
                authority: seq![Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x02020202) }, Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x04040404) }],
                additional: seq![Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x03030303) }, Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x05050505) }, Rr { name: seq![0u8], rtype: 1, rclass: 1, ttl: 60, rdata: Rdata::A(0x06060606) }],
            })) by (compute_only);
}

/// A, AAAA and CNAME are interpreted only in class IN: in class 3 (CH) the
/// RDATA is kept as octets, whatever its length.
pub proof fn lemma_other_classes_opaque()
    ensures
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 28, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 28, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 5, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
{
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 28, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 28, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 5, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
}

/// A message whose RDATA is `n` octets of 7, in a record of unknown type 16
/// with the root as owner: 23 octets and `n`.
pub open spec fn big_message(n: nat) -> Seq<u8> {
    seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 16, 0, 1, 0, 0, 1, 44, (n / 256) as u8, (n % 256) as u8] + fill(7, n)
}

/// §2.3.4: "UDP messages 512 octets or less": a datagram of 512 octets is
/// decoded, one of 513 is not, though the same 513 octets are a message
/// over TCP (§4.2.2).
pub proof fn lemma_udp_limit()
    ensures
        big_message(489).len() == 512,
        big_message(490).len() == 513,
        decode_udp(big_message(489)) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(fill(7, 489)) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_udp(big_message(490)) is None,
        decode_message(big_message(490)) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(fill(7, 490)) }],
                authority: seq![],
                additional: seq![],
            },
        ),
{
    assert(big_message(489).len() == 512) by (compute_only);
    assert(big_message(490).len() == 513) by (compute_only);
    assert(decode_udp(big_message(489)) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(fill(7, 489)) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_udp(big_message(490)) is None) by (compute_only);
    assert(decode_message(big_message(490)) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(fill(7, 490)) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
}

/// An address record is an address only if its type and class say so, and
/// a CNAME only likewise: a record of type 1 in class 3, or of type 2 with
/// an A address, or the like, gives nothing, even if its data looks like
/// an address.
pub proof fn lemma_answer_record_kinds()
    ensures
        answer_addresses(
            query_a(),
            reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 1, rclass: 3, ttl: 1, rdata: Rdata::A(5) }], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(
            query_a(),
            reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 2, rclass: 1, ttl: 1, rdata: Rdata::A(5) }], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(
            query_aaaa(),
            reply(na(), 28, false, 0, seq![Rr { name: na(), rtype: 28, rclass: 3, ttl: 1, rdata: Rdata::Aaaa(5) }], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(
            query_aaaa(),
            reply(na(), 28, false, 0, seq![Rr { name: na(), rtype: 1, rclass: 1, ttl: 1, rdata: Rdata::Aaaa(5) }], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(
            query_a(),
            reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 5, rclass: 3, ttl: 1, rdata: Rdata::Cname(nb()) }], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(
            query_a(),
            reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 16, rclass: 1, ttl: 1, rdata: Rdata::Cname(nb()) }], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![], redirect: None }),
        // A CNAME owned by another name is not on the chain.
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(nb(), nc()), a_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(1)], redirect: None }),
        // The first CNAME for a name is the one followed.
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(na(), nc()), a_rr(nb(), 2), a_rr(nc(), 3)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(2)], redirect: None }),
{
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 1, rclass: 3, ttl: 1, rdata: Rdata::A(5) }], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 2, rclass: 1, ttl: 1, rdata: Rdata::A(5) }], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_aaaa(),
        reply(na(), 28, false, 0, seq![Rr { name: na(), rtype: 28, rclass: 3, ttl: 1, rdata: Rdata::Aaaa(5) }], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_aaaa(),
        reply(na(), 28, false, 0, seq![Rr { name: na(), rtype: 1, rclass: 1, ttl: 1, rdata: Rdata::Aaaa(5) }], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 5, rclass: 3, ttl: 1, rdata: Rdata::Cname(nb()) }], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![Rr { name: na(), rtype: 16, rclass: 1, ttl: 1, rdata: Rdata::Cname(nb()) }], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(nb(), nc()), a_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![Addr::V4(1)], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(na(), nc()), a_rr(nb(), 2), a_rr(nc(), 3)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(2)], redirect: None })) by (compute_only);
}

/// §2.3.4 and §4.2.2: the limits and the codes, as numbers: labels 63,
/// names 255, UDP messages 512, TCP messages 65535 (the largest value of the
/// two octet length field: a message that long cannot be built here, which
/// is why this is a statement about the constant), and the TYPE and CLASS
/// values of §3.2.2, §3.2.4 and RFC 3596 §2.1.
pub proof fn lemma_limits_and_codes()
    ensures
        MAX_LABEL == 63,
        MAX_NAME == 255,
        MAX_UDP == 512,
        MAX_TCP == 65535,
        TYPE_A == 1,
        TYPE_CNAME == 5,
        TYPE_AAAA == 28,
        CLASS_IN == 1,
        tcp_frame(fill(1, 535)) is Some,
{
    assert(MAX_LABEL == 63);
    assert(MAX_NAME == 255);
    assert(MAX_UDP == 512);
    assert(MAX_TCP == 65535);
    assert(TYPE_A == 1);
    assert(TYPE_CNAME == 5);
    assert(TYPE_AAAA == 28);
    assert(CLASS_IN == 1);
    assert(tcp_frame(fill(1, 535)) is Some) by (compute_only);
}

} // verus!
