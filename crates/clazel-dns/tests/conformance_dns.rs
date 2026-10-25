//! DNS message conformance (docs/phases/phase-3.md item 3.4).
//!
//! The proofs show the executable functions equal `spec.rs`, and
//! `independent.rs` (RFC 883) that the decoder equals a second reading of the
//! wire format. This file checks the spec against the outside world, in
//! six suites, each printing one `clazel-conformance:` line:
//!
//! 1. `hand-built DNS messages`: messages built octet by octet for every
//!    rule: truncation (TC=1), NXDOMAIN, CNAME chains, AAAA, every
//!    compression error, every size limit, the RFC 1035 §4.1.4 example, the
//!    TCP length prefix, and the replies `answer_addresses` must refuse.
//! 2. `captured DNS responses`: real responses, captured once (see
//!    [`CAPTURED`] for how and when) and checked against what the
//!    standard says they mean.
//! 3. `simple-dns differential: random messages`: random well-formed
//!    messages written by `simple-dns`, with and without name compression,
//!    decoded by us and compared with the message that was written and with
//!    what `simple-dns` reads back.
//! 4. `simple-dns differential: our queries`: queries we encode, read by
//!    `simple-dns`.
//! 5. `simple-dns differential: mutated messages`: those messages with random
//!    damage. Both parsers read every one. Where they agree on the result
//!    the contents must be equal; where they differ each case is explained
//!    by one of the listed reasons (the `xfail` count), and none may be left
//!    unexplained.
//! 6. `resolv.conf nameserver lines`: the grammar on hand-written files.
//!
//! The reference engine is `simple-dns` 0.12.0, which parses and writes whole
//! messages and has one dependency (`bitflags`); `dnsparse` has none but
//! parses only the header, questions and answers, and `dns-parser` writes
//! only queries (docs/DEPENDENCIES.md).

use clazel_dns::answer::answer_addresses;
use clazel_dns::decode::{decode_message, decode_udp};
use clazel_dns::encode::{
    dotted_to_wire, encode_query, tcp_frame, tcp_message_len, wire_to_dotted as dotted_of_wire,
};
use clazel_dns::resolv::parse::nameservers;
use clazel_dns::spec::Addr;
use clazel_dns::types::{Msg, Rd, Rec};
use simple_dns::rdata::{A, AAAA, CNAME, NULL, RData};
use simple_dns::{
    CLASS, Name, OPCODE, Packet, PacketFlag, QCLASS, QTYPE, Question, RCODE, ResourceRecord,
};
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Utilities.
// ---------------------------------------------------------------------------

/// A small deterministic generator (xorshift), so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }
    fn chance(&mut self, one_in: usize) -> bool {
        self.below(one_in) == 0
    }
    fn byte(&mut self) -> u8 {
        u8::try_from(self.below(256)).unwrap_or(0)
    }
    fn u16(&mut self) -> u16 {
        u16::try_from(self.below(65536)).unwrap_or(0)
    }
    fn u32(&mut self) -> u32 {
        u32::try_from(self.next() >> 32).unwrap_or(0)
    }
    fn u128(&mut self) -> u128 {
        (u128::from(self.next()) << 64) | u128::from(self.next())
    }
}

fn at(b: &[u8], i: usize) -> u8 {
    b.get(i).copied().unwrap_or(0)
}

fn hex(s: &str) -> Vec<u8> {
    let digits: Vec<u8> = s
        .bytes()
        .filter_map(|c| match c {
            b'0'..=b'9' => Some(c.saturating_sub(b'0')),
            b'a'..=b'f' => Some(c.saturating_sub(b'a').saturating_add(10)),
            _ => None,
        })
        .collect();
    digits
        .chunks(2)
        .map(|p| at(p, 0).saturating_mul(16).saturating_add(at(p, 1)))
        .collect()
}

/// An expanded wire name as a dotted string (the root is the empty string).
fn wire_to_dotted(w: &[u8]) -> String {
    let mut out = String::new();
    let mut i = 0usize;
    loop {
        let l = usize::from(at(w, i));
        if l == 0 {
            break;
        }
        if !out.is_empty() {
            out.push('.');
        }
        for k in 0..l {
            out.push(char::from(at(w, i.saturating_add(1).saturating_add(k))));
        }
        i = i.saturating_add(1).saturating_add(l);
    }
    out
}

/// The labels of an expanded wire name, as octets.
fn labels_of(w: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut i = 0usize;
    loop {
        let l = usize::from(at(w, i));
        if l == 0 {
            break;
        }
        let start = i.saturating_add(1);
        out.push(
            w.get(start..start.saturating_add(l))
                .unwrap_or(&[])
                .to_vec(),
        );
        i = start.saturating_add(l);
    }
    out
}

/// The labels of a simple-dns name, as octets.
fn their_labels(n: &Name<'_>) -> Vec<Vec<u8>> {
    n.as_bytes().map(<[u8]>::to_vec).collect()
}

fn same_name(a: &str, b: &str) -> bool {
    a.trim_end_matches('.')
        .eq_ignore_ascii_case(b.trim_end_matches('.'))
}

fn be16(v: u16) -> [u8; 2] {
    v.to_be_bytes()
}

/// A wire name from labels.
fn name_wire(labels: &[&str]) -> Vec<u8> {
    let mut w = Vec::new();
    for l in labels {
        w.push(u8::try_from(l.len()).unwrap_or(0));
        w.extend_from_slice(l.as_bytes());
    }
    w.push(0);
    w
}

/// A header: ID, flags and the four counts.
fn header(id: u16, flags: u16, qd: u16, an: u16, ns: u16, ar: u16) -> Vec<u8> {
    let mut h = Vec::new();
    for v in [id, flags, qd, an, ns, ar] {
        h.extend_from_slice(&be16(v));
    }
    h
}

/// A resource record with the owner `name` (wire octets).
fn rr(name: &[u8], rtype: u16, rclass: u16, ttl: u32, rdata: &[u8]) -> Vec<u8> {
    let mut v = name.to_vec();
    v.extend_from_slice(&be16(rtype));
    v.extend_from_slice(&be16(rclass));
    v.extend_from_slice(&ttl.to_be_bytes());
    v.extend_from_slice(&be16(u16::try_from(rdata.len()).unwrap_or(0)));
    v.extend_from_slice(rdata);
    v
}

fn question(name: &[u8], qtype: u16, qclass: u16) -> Vec<u8> {
    let mut v = name.to_vec();
    v.extend_from_slice(&be16(qtype));
    v.extend_from_slice(&be16(qclass));
    v
}

/// Counts passes and failures of one suite and prints its summary line
/// (format: xtask/src/conformance.rs).
struct Suite {
    name: &'static str,
    pass: usize,
    xfail: usize,
    fail: usize,
    total: usize,
    failures: Vec<String>,
}

impl Suite {
    fn new(name: &'static str, total: usize) -> Self {
        Suite {
            name,
            pass: 0,
            xfail: 0,
            fail: 0,
            total,
            failures: Vec::new(),
        }
    }
    fn check(&mut self, what: &str, result: Result<(), String>) {
        match result {
            Ok(()) => self.pass = self.pass.saturating_add(1),
            Err(e) => {
                self.fail = self.fail.saturating_add(1);
                if self.failures.len() < 20 {
                    self.failures.push(format!("{what}: {e}"));
                }
            }
        }
    }
    fn xfail(&mut self) {
        self.xfail = self.xfail.saturating_add(1);
    }
    fn finish(self) {
        println!(
            "clazel-conformance: suite=\"{}\" pass={} xfail={} fail={} total={}",
            self.name, self.pass, self.xfail, self.fail, self.total
        );
        assert_eq!(
            self.pass
                .saturating_add(self.xfail)
                .saturating_add(self.fail),
            self.total,
            "{}: the counts must add up",
            self.name
        );
        assert!(self.failures.is_empty(), "{}", self.failures.join("\n"));
    }
}

fn expect(cond: bool, what: &str) -> Result<(), String> {
    if cond { Ok(()) } else { Err(what.to_owned()) }
}

// ---------------------------------------------------------------------------
// 1. Hand-built messages.
// ---------------------------------------------------------------------------

const QR_RD_RA: u16 = 0x8180;

fn decoded(b: &[u8]) -> Result<Msg, String> {
    decode_message(b).ok_or_else(|| format!("rejected {b:02x?}"))
}

fn rejected(b: &[u8]) -> Result<(), String> {
    match decode_message(b) {
        None => Ok(()),
        Some(m) => Err(format!("accepted {b:02x?} as {m:?}")),
    }
}

fn addrs(id: u16, name: &str, qtype: u16, m: &Msg) -> Option<(Vec<Addr>, Option<String>)> {
    answer_addresses(id, name.as_bytes(), qtype, m)
        .map(|r| (r.addresses, r.redirect.map(|w| wire_to_dotted(&w))))
}

fn v4(a: u8, b: u8, c: u8, d: u8) -> Addr {
    Addr::V4(u32::from_be_bytes([a, b, c, d]))
}

/// The reply for "www.a.test" A with the given answer records (wire).
fn reply_for(name: &[&str], qtype: u16, flags: u16, answers: &[Vec<u8>]) -> Vec<u8> {
    let q = question(&name_wire(name), qtype, 1);
    let mut m = header(7, flags, 1, u16::try_from(answers.len()).unwrap_or(0), 0, 0);
    m.extend_from_slice(&q);
    for a in answers {
        m.extend_from_slice(a);
    }
    m
}

fn hand_built() -> Suite {
    type Case = (&'static str, Box<dyn Fn() -> Result<(), String>>);
    let www = ["www", "a", "test"];
    let owner_ptr: [u8; 2] = [0xC0, 12];
    let mut cases: Vec<Case> = Vec::new();

    // TC=1: a truncated reply is decoded, says so, and gives no answer.
    cases.push((
        "TC=1 (truncated) reply",
        Box::new(move || {
            let b = reply_for(&www, 1, QR_RD_RA | 0x0200, &[]);
            let m = decoded(&b)?;
            expect(
                m.header.tc && m.questions.len() == 1 && m.answers.is_empty(),
                "flags",
            )?;
            expect(
                addrs(7, "www.a.test", 1, &m).is_none(),
                "a truncated reply is not an answer",
            )?;
            // §4.2.2: retry over TCP with the length prefix.
            let framed = tcp_frame(&b).ok_or("frame")?;
            expect(tcp_message_len(&framed) == Some(b.len()), "length prefix")
        }),
    ));
    // NXDOMAIN: rcode 3, authority SOA, no answers.
    cases.push((
        "NXDOMAIN reply",
        Box::new(move || {
            let soa = rr(&name_wire(&["a", "test"]), 6, 1, 60, &[0; 22]);
            let mut b = header(7, QR_RD_RA | 3, 1, 0, 1, 0);
            b.extend_from_slice(&question(&name_wire(&www), 1, 1));
            b.extend_from_slice(&soa);
            let m = decoded(&b)?;
            expect(m.header.rcode == 3 && m.authority.len() == 1, "header")?;
            expect(
                addrs(7, "www.a.test", 1, &m) == Some((vec![], None)),
                "NXDOMAIN gives the empty answer",
            )
        }),
    ));
    // CNAME chain www -> b -> c -> A, inside the answer section.
    cases.push((
        "CNAME chain ending in an A record",
        Box::new(move || {
            let b = reply_for(
                &www,
                1,
                QR_RD_RA,
                &[
                    rr(&owner_ptr, 5, 1, 60, &name_wire(&["b", "test"])),
                    rr(
                        &name_wire(&["b", "test"]),
                        5,
                        1,
                        60,
                        &name_wire(&["C", "test"]),
                    ),
                    rr(&name_wire(&["c", "test"]), 1, 1, 60, &[9, 8, 7, 6]),
                ],
            );
            let m = decoded(&b)?;
            expect(
                addrs(7, "www.a.test", 1, &m) == Some((vec![v4(9, 8, 7, 6)], None)),
                "the chain is followed, case-insensitively",
            )
        }),
    ));
    // A chain that leaves the answer section: the last target is returned.
    cases.push((
        "CNAME chain leaving the answer section",
        Box::new(move || {
            let b = reply_for(
                &www,
                1,
                QR_RD_RA,
                &[rr(
                    &owner_ptr,
                    5,
                    1,
                    60,
                    &name_wire(&["cdn", "other", "test"]),
                )],
            );
            let m = decoded(&b)?;
            expect(
                addrs(7, "www.a.test", 1, &m) == Some((vec![], Some("cdn.other.test".into()))),
                "redirect",
            )
        }),
    ));
    // A CNAME loop, and a CNAME to itself.
    cases.push((
        "CNAME loop",
        Box::new(move || {
            let b = reply_for(
                &www,
                1,
                QR_RD_RA,
                &[
                    rr(&owner_ptr, 5, 1, 60, &name_wire(&["b", "test"])),
                    rr(
                        &name_wire(&["b", "test"]),
                        5,
                        1,
                        60,
                        &name_wire(&["www", "a", "test"]),
                    ),
                ],
            );
            let m = decoded(&b)?;
            expect(addrs(7, "www.a.test", 1, &m).is_none(), "a loop is refused")
        }),
    ));
    // AAAA.
    cases.push((
        "AAAA answer",
        Box::new(move || {
            let mut ip = [0u8; 16];
            ip[0] = 0x26;
            ip[1] = 0x06;
            ip[15] = 1;
            let b = reply_for(&www, 28, QR_RD_RA, &[rr(&owner_ptr, 28, 1, 60, &ip)]);
            let m = decoded(&b)?;
            expect(
                addrs(7, "www.a.test", 28, &m)
                    == Some((vec![Addr::V6(u128::from_be_bytes(ip))], None)),
                "AAAA address",
            )?;
            // An A query does not take it.
            expect(
                addrs(7, "www.a.test", 1, &m).is_none(),
                "the question is for AAAA, not A",
            )
        }),
    ));
    // Authority and additional records are never used.
    cases.push((
        "authority and additional sections are not used",
        Box::new(move || {
            let mut b = header(7, QR_RD_RA, 1, 0, 1, 1);
            b.extend_from_slice(&question(&name_wire(&www), 1, 1));
            b.extend_from_slice(&rr(&owner_ptr, 1, 1, 60, &[1, 1, 1, 1]));
            b.extend_from_slice(&rr(&owner_ptr, 1, 1, 60, &[2, 2, 2, 2]));
            let m = decoded(&b)?;
            expect(
                m.authority.len() == 1 && m.additional.len() == 1,
                "the sections are kept apart",
            )?;
            expect(
                addrs(7, "www.a.test", 1, &m) == Some((vec![], None)),
                "no answer-section address",
            )
        }),
    ));
    // ID, question, QR, opcode, rcode checks.
    cases.push((
        "replies that do not answer the query",
        Box::new(move || {
            let b = reply_for(
                &www,
                1,
                QR_RD_RA,
                &[rr(&owner_ptr, 1, 1, 60, &[1, 2, 3, 4])],
            );
            let m = decoded(&b)?;
            expect(addrs(8, "www.a.test", 1, &m).is_none(), "ID differs")?;
            expect(addrs(7, "www.b.test", 1, &m).is_none(), "name differs")?;
            expect(addrs(7, "www.a.test", 28, &m).is_none(), "type differs")?;
            expect(
                addrs(7, "WWW.A.Test", 1, &m).is_some(),
                "the query name is compared case-insensitively",
            )?;
            let not_response = reply_for(&www, 1, 0x0100, &[]);
            expect(
                addrs(7, "www.a.test", 1, &decoded(&not_response)?).is_none(),
                "QR clear",
            )?;
            let other_opcode = reply_for(&www, 1, QR_RD_RA | 0x1000, &[]);
            expect(
                addrs(7, "www.a.test", 1, &decoded(&other_opcode)?).is_none(),
                "OPCODE 2",
            )?;
            for rcode in [1u16, 2, 4, 5] {
                let bad = reply_for(&www, 1, QR_RD_RA | rcode, &[]);
                expect(
                    addrs(7, "www.a.test", 1, &decoded(&bad)?).is_none(),
                    "RCODE",
                )?;
            }
            Ok(())
        }),
    ));
    // §4.1.1: Z must be zero.
    cases.push((
        "Z bits set",
        Box::new(move || {
            for z in [0x0010u16, 0x0020, 0x0040] {
                rejected(&reply_for(&www, 1, QR_RD_RA | z, &[]))?;
            }
            Ok(())
        }),
    ));
    // Compression errors.
    cases.push((
        "compression: pointer to itself",
        Box::new(move || {
            let mut b = header(7, QR_RD_RA, 1, 0, 0, 0);
            b.extend_from_slice(&[0xC0, 12, 0, 1, 0, 1]);
            rejected(&b)
        }),
    ));
    cases.push((
        "compression: pointer forward",
        Box::new(move || {
            let mut b = header(7, QR_RD_RA, 1, 0, 0, 0);
            b.extend_from_slice(&[0xC0, 20, 0, 1, 0, 1, 0, 0, 0, 0]);
            b.extend_from_slice(&[1, b'a', 0]);
            rejected(&b)
        }),
    ));
    cases.push((
        "compression: loop between a label and a pointer",
        Box::new(move || {
            // A label at 12, then a pointer back to 12: the name would
            // never end.
            let mut b = header(7, QR_RD_RA, 1, 0, 0, 0);
            b.extend_from_slice(&[1, b'a', 0xC0, 12, 0, 1, 0, 1]);
            rejected(&b)
        }),
    ));
    cases.push((
        "compression: a pointer whose target name runs over the pointer",
        Box::new(move || {
            // Record 1's RDATA is the single octet 6 at offset 23; record 2's
            // owner is the pointer C0 17 (to 23) at offset 24. Read from 23,
            // the label of 6 octets covers the pointer and the next four
            // octets, and the zero octet after it is the TTL's first: a name
            // that ends after the pointer that led to it. It is not "a prior
            // occurance" (ERRATA.md).
            let mut b = header(7, QR_RD_RA, 0, 2, 0, 0);
            b.extend_from_slice(&rr(&[0], 16, 1, 0, &[6]));
            expect(b.len() == 24, "layout")?;
            b.extend_from_slice(&rr(&[0xC0, 23], 16, 1, 0, &[]));
            rejected(&b)
        }),
    ));
    cases.push((
        "compression: reserved label types 01 and 10",
        Box::new(move || {
            for first in [0x40u8, 0x80, 0x7F, 0xBF] {
                let mut b = header(7, QR_RD_RA, 1, 0, 0, 0);
                b.push(first);
                b.extend(std::iter::repeat_n(b'a', usize::from(first & 0x3F)));
                b.extend_from_slice(&[0, 0, 1, 0, 1]);
                rejected(&b)?;
            }
            Ok(())
        }),
    ));
    cases.push((
        "compression: truncated pointer and truncated label",
        Box::new(move || {
            let mut b = header(7, QR_RD_RA, 1, 0, 0, 0);
            b.push(0xC0);
            rejected(&b)?;
            let mut c = header(7, QR_RD_RA, 1, 0, 0, 0);
            c.extend_from_slice(&[5, b'a', b'b']);
            rejected(&c)
        }),
    ));
    cases.push((
        "compression: pointers to pointers are followed",
        Box::new(move || {
            // Question "a" at 12; the answer owner is a pointer to a
            // pointer to the question's name.
            let mut b = header(7, QR_RD_RA, 1, 2, 0, 0);
            b.extend_from_slice(&question(&[1, b'a', 0], 1, 1));
            let first = rr(&[0xC0, 12], 1, 1, 60, &[1, 1, 1, 1]);
            let second_owner_at = b.len().saturating_add(first.len());
            b.extend_from_slice(&first);
            // second owner: a pointer to the first answer's owner (a
            // pointer to 12).
            let target = u16::try_from(b.len().saturating_sub(first.len())).unwrap_or(0);
            let _ = second_owner_at;
            b.extend_from_slice(&rr(
                &[0xC0 | (target >> 8) as u8, (target & 0xFF) as u8],
                1,
                1,
                60,
                &[2, 2, 2, 2],
            ));
            let m = decoded(&b)?;
            expect(
                m.answers.iter().all(|r| r.name == [1, b'a', 0]),
                "both owners expand to a",
            )
        }),
    ));
    cases.push((
        "compression: an expanded name over 255 octets",
        Box::new(move || {
            // Three labels of 63 octets (a 193 octet name) and, further on,
            // a label of 63 followed by a pointer to it: 257 expanded.
            let long: Vec<u8> = {
                let mut w = Vec::new();
                for _ in 0..3 {
                    w.push(63);
                    w.extend(std::iter::repeat_n(b'x', 63));
                }
                w.push(0);
                w
            };
            let mut b = header(7, QR_RD_RA, 1, 1, 0, 0);
            b.extend_from_slice(&question(&long, 1, 1));
            let mut owner = vec![63u8];
            owner.extend(std::iter::repeat_n(b'y', 63));
            owner.extend_from_slice(&[0xC0, 12]);
            b.extend_from_slice(&rr(&owner, 1, 1, 60, &[1, 2, 3, 4]));
            rejected(&b)?;
            // With a label of 61 octets it is 255 and is accepted.
            let mut ok = header(7, QR_RD_RA, 1, 1, 0, 0);
            ok.extend_from_slice(&question(&long, 1, 1));
            let mut owner = vec![61u8];
            owner.extend(std::iter::repeat_n(b'y', 61));
            owner.extend_from_slice(&[0xC0, 12]);
            ok.extend_from_slice(&rr(&owner, 1, 1, 60, &[1, 2, 3, 4]));
            let m = decoded(&ok)?;
            expect(
                m.answers.first().map(|r| r.name.len()) == Some(255),
                "a name of 255 octets",
            )
        }),
    ));
    // Size limits.
    cases.push((
        "limits: label of 63 and 64 octets",
        Box::new(move || {
            let l63 = name_wire(&[&"a".repeat(63)]);
            let mut ok = header(7, QR_RD_RA, 1, 0, 0, 0);
            ok.extend_from_slice(&question(&l63, 1, 1));
            let m = decoded(&ok)?;
            expect(
                m.questions.first().map(|q| q.name.len()) == Some(65),
                "63-octet label",
            )?;
            let mut bad = header(7, QR_RD_RA, 1, 0, 0, 0);
            bad.push(64);
            bad.extend(std::iter::repeat_n(b'a', 64));
            bad.extend_from_slice(&[0, 0, 1, 0, 1]);
            rejected(&bad)?;
            // And the same limits for the names of queries.
            expect(
                dotted_to_wire("a".repeat(63).as_bytes()).is_some(),
                "63-octet dotted label",
            )?;
            expect(
                dotted_to_wire("a".repeat(64).as_bytes()).is_none(),
                "64-octet dotted label",
            )
        }),
    ));
    cases.push((
        "limits: name of 255 and 256 octets",
        Box::new(move || {
            let l63 = "a".repeat(63);
            let l61 = "b".repeat(61);
            let l62 = "b".repeat(62);
            let ok = name_wire(&[&l63, &l63, &l63, &l61]);
            let bad = name_wire(&[&l63, &l63, &l63, &l62]);
            expect(ok.len() == 255 && bad.len() == 256, "construction")?;
            let mut a = header(7, QR_RD_RA, 1, 0, 0, 0);
            a.extend_from_slice(&question(&ok, 1, 1));
            decoded(&a)?;
            let mut b = header(7, QR_RD_RA, 1, 0, 0, 0);
            b.extend_from_slice(&question(&bad, 1, 1));
            rejected(&b)?;
            let d_ok = format!("{l63}.{l63}.{l63}.{l61}");
            let d_bad = format!("{l63}.{l63}.{l63}.{l62}");
            expect(
                dotted_to_wire(d_ok.as_bytes()).is_some(),
                "255-octet dotted name",
            )?;
            expect(
                dotted_to_wire(d_bad.as_bytes()).is_none(),
                "256-octet dotted name",
            )?;
            // And from the wire side: 255 octets are spelled, 256 are not,
            // and a name that holds a dot in a label, or is a pointer, has
            // no dotted spelling.
            expect(
                dotted_of_wire(&ok).as_deref() == Some(d_ok.as_bytes()),
                "255-octet wire name",
            )?;
            expect(dotted_of_wire(&bad).is_none(), "256-octet wire name")?;
            expect(
                dotted_of_wire(b"\x03a.b\x00").is_none() && dotted_of_wire(&[0xC0, 12]).is_none(),
                "no dotted spelling",
            )
        }),
    ));
    cases.push((
        "limits: UDP message of 512 and 513 octets, TCP message of 65535 and 65536",
        Box::new(move || {
            // A record of unknown type with RDATA of n octets.
            let big = |n: usize| {
                let mut b = header(7, QR_RD_RA, 0, 1, 0, 0);
                b.extend_from_slice(&rr(&[0], 16, 1, 60, &vec![7u8; n]));
                b
            };
            expect(
                big(489).len() == 512 && decode_udp(&big(489)).is_some(),
                "512",
            )?;
            expect(
                big(490).len() == 513 && decode_udp(&big(490)).is_none(),
                "513 over UDP",
            )?;
            expect(decode_message(&big(490)).is_some(), "513 over TCP")?;
            // RDLENGTH is 16 bits: the largest message is 12 + 11 + 65535.
            let largest = {
                let mut b = header(7, QR_RD_RA, 0, 1, 0, 0);
                b.extend_from_slice(&rr(&[0], 16, 1, 60, &vec![7u8; 65535]));
                b
            };
            expect(largest.len() > 65535, "construction")?;
            expect(decode_message(&largest).is_none(), "over 65535 octets")?;
            let frame_ok = tcp_frame(&vec![0u8; 65535]);
            expect(
                frame_ok.as_ref().map(Vec::len) == Some(65537),
                "65535-octet frame",
            )?;
            expect(
                tcp_frame(&vec![0u8; 65536]).is_none(),
                "65536-octet message cannot be framed",
            )
        }),
    ));
    // TCP length prefix.
    cases.push((
        "TCP length prefix",
        Box::new(move || {
            let m = reply_for(
                &www,
                1,
                QR_RD_RA,
                &[rr(&owner_ptr, 1, 1, 60, &[1, 2, 3, 4])],
            );
            let framed = tcp_frame(&m).ok_or("frame")?;
            expect(
                framed.get(..2) == Some(&be16(u16::try_from(m.len()).unwrap_or(0))[..]),
                "prefix",
            )?;
            expect(tcp_message_len(&framed) == Some(m.len()), "complete")?;
            for cut in [0usize, 1, 2, framed.len().saturating_sub(1)] {
                expect(
                    tcp_message_len(framed.get(..cut).unwrap_or(&[])).is_none(),
                    "incomplete",
                )?;
            }
            let mut two = framed.clone();
            two.extend_from_slice(&framed);
            expect(tcp_message_len(&two) == Some(m.len()), "the first of two")
        }),
    ));
    // Record rules.
    cases.push((
        "record rules: RDLENGTH, unknown types and classes, trailing octets",
        Box::new(move || {
            let msg = |r: Vec<u8>| {
                let mut b = header(7, QR_RD_RA, 0, 1, 0, 0);
                b.extend_from_slice(&r);
                b
            };
            rejected(&msg(rr(&[0], 1, 1, 60, &[1, 2, 3])))?;
            rejected(&msg(rr(&[0], 1, 1, 60, &[1, 2, 3, 4, 5])))?;
            rejected(&msg(rr(&[0], 28, 1, 60, &[0; 4])))?;
            rejected(&msg(rr(&[0], 5, 1, 60, &[1, b'b', 0, 0])))?;
            let txt = decoded(&msg(rr(&[0], 16, 1, 60, &[3, b'a', b'b', b'c'])))?;
            expect(
                matches!(txt.answers.first().map(|r| &r.rdata), Some(Rd::Opaque(d)) if d == &[3, b'a', b'b', b'c']),
                "TXT is kept as octets",
            )?;
            let ch = decoded(&msg(rr(&[0], 1, 3, 60, &[9])))?;
            expect(
                matches!(ch.answers.first().map(|r| &r.rdata), Some(Rd::Opaque(d)) if d == &[9]),
                "class CH is not interpreted",
            )?;
            let mut trailing = msg(rr(&[0], 16, 1, 60, &[1, 2]));
            trailing.push(0);
            rejected(&trailing)?;
            // Counts that promise more than there is.
            rejected(&header(7, QR_RD_RA, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF))?;
            rejected(&header(7, QR_RD_RA, 0, 1, 0, 0))
        }),
    ));
    // RFC 1035 §4.1.4's example.
    cases.push((
        "RFC 1035 §4.1.4 example (F.ISI.ARPA, FOO.F.ISI.ARPA, ARPA, the root)",
        Box::new(move || {
            // The figure's offsets, shifted by -8 to follow a 12-octet
            // header: F.ISI.ARPA at 12, FOO and a pointer to 12 at 32, a
            // pointer to the ARPA label at 18 for ARPA, the root.
            let mut b = header(7, QR_RD_RA, 0, 4, 0, 0);
            let f_isi_arpa = [1u8, b'F', 3, b'I', b'S', b'I', 4, b'A', b'R', b'P', b'A', 0];
            let start = b.len();
            b.extend_from_slice(&rr(&f_isi_arpa, 16, 1, 0, &[]));
            let foo_at = b.len();
            b.extend_from_slice(&rr(&[3, b'F', b'O', b'O', 0xC0, 12], 16, 1, 0, &[]));
            let arpa_at = b.len();
            b.extend_from_slice(&rr(&[0xC0, 18], 16, 1, 0, &[]));
            let root_at = b.len();
            b.extend_from_slice(&rr(&[0], 16, 1, 0, &[]));
            expect(
                start == 12 && foo_at > start && arpa_at > foo_at && root_at > arpa_at,
                "layout",
            )?;
            let m = decoded(&b)?;
            let owners: Vec<String> = m.answers.iter().map(|r| wire_to_dotted(&r.name)).collect();
            expect(
                owners == ["F.ISI.ARPA", "FOO.F.ISI.ARPA", "ARPA", ""],
                &format!("owners {owners:?}"),
            )?;
            // Case is kept as sent (§2.3.3).
            expect(
                m.answers.first().map(|r| r.name.clone()) == Some(f_isi_arpa.to_vec()),
                "case kept",
            )
        }),
    ));
    // Queries.
    cases.push((
        "queries: ID, flags, one question, class IN, no compression",
        Box::new(move || {
            let q = encode_query(0x1234, b"example.com", 1).ok_or("encode")?;
            expect(
                q == hex("123401000001000000000000076578616d706c6503636f6d0000010001"),
                "the bytes a stub resolver sends for example.com A",
            )?;
            let m = decoded(&q)?;
            expect(
                !m.header.qr
                    && m.header.rd
                    && !m.header.tc
                    && m.header.opcode == 0
                    && m.header.qdcount == 1,
                "header",
            )?;
            let q6 = encode_query(0xBEEF, b"EXAMPLE.org.", 28).ok_or("encode")?;
            expect(
                q6 == hex("beef01000001000000000000074558414d504c45036f72670000 1c0001"),
                "AAAA, trailing dot, case kept",
            )?;
            expect(encode_query(1, b"a..b", 1).is_none(), "empty label")?;
            expect(encode_query(1, b"", 1).is_none(), "empty name")?;
            expect(
                encode_query(1, "é.com".as_bytes(), 1).is_none(),
                "non-ASCII",
            )?;
            expect(
                encode_query(1, b".", 1) == Some(hex("0001010000010000000000000000010001")),
                "root",
            )
        }),
    ));
    let total = cases.len();
    let mut suite = Suite::new("hand-built DNS messages", total);
    for (name, case) in &cases {
        suite.check(name, case());
    }
    suite
}

// ---------------------------------------------------------------------------
// 2. Captured responses.
// ---------------------------------------------------------------------------

/// A real exchange, captured once on 2026-10-23 from this machine with a
/// short Python 3 script (`python3 -I`, standard library `socket` only).
/// `kind` says where it came from: `udp` is a UDP query (ID 0x1234, RD set,
/// no EDNS) of the type shown to the public resolver 8.8.8.8, `tcp` is the
/// same over TCP to 8.8.8.8 (the two-octet length prefix is removed), and
/// `auth` is a UDP query with RD clear to `a.iana-servers.net`
/// (199.43.135.53). `query` and `response` are the octets that were sent and
/// came back, as hex; nothing was edited. `outcome` is what
/// `answer_addresses` must say: `ans` (addresses, as simple-dns reads them),
/// `nx` (NXDOMAIN: none), `tc` (truncated: no answer), `refused` (RCODE 5:
/// no answer), `redirect` (a CNAME chain that leaves the answer section: no
/// addresses and the last target), `none` (the question is not for A or AAAA).
struct Captured {
    label: &'static str,
    host: &'static str,
    qtype: u16,
    kind: &'static str,
    outcome: &'static str,
    query: &'static str,
    response: &'static str,
}

const CAPTURED: &[Captured] = &[
    Captured {
        label: "example.com A",
        host: "example.com",
        qtype: 1,
        kind: "udp",
        outcome: "ans",
        query: "123401000001000000000000076578616d706c6503636f6d0000010001",
        response: "123481800001000200000000076578616d706c6503636f6d0000010001c00c000100010000012c00046814179ac00c000100010000012c0004ac4293f3",
    },
    Captured {
        label: "example.com AAAA",
        host: "example.com",
        qtype: 28,
        kind: "udp",
        outcome: "ans",
        query: "123401000001000000000000076578616d706c6503636f6d00001c0001",
        response: "123481800001000200000000076578616d706c6503636f6d00001c0001c00c001c00010000012c0010260647000010000000000000ac4293f3c00c001c00010000012c00102606470000100000000000006814179a",
    },
    Captured {
        label: "clazel-test-name.invalid A (NXDOMAIN, SOA in the authority section)",
        host: "clazel-test-name.invalid",
        qtype: 1,
        kind: "udp",
        outcome: "nx",
        query: "12340100000100000000000010636c617a656c2d746573742d6e616d6507696e76616c69640000010001",
        response: "12348183000100000001000010636c617a656c2d746573742d6e616d6507696e76616c696400000100010000060001000150d8004001610c726f6f742d73657276657273036e657400056e73746c640c766572697369676e2d67727303636f6d0078c3de1f000007080000038400093a8000015180",
    },
    Captured {
        label: "www.wikipedia.org A (a CNAME, then an A record)",
        host: "www.wikipedia.org",
        qtype: 1,
        kind: "udp",
        outcome: "ans",
        query: "123401000001000000000000037777770977696b697065646961036f72670000010001",
        response: "123481800001000200000000037777770977696b697065646961036f72670000010001c00c00050001000051e800110464796e610977696b696d65646961c01ac02f00010001000000b40004b90f3be0",
    },
    Captured {
        label: "www.wikipedia.org AAAA (a CNAME, then an AAAA record)",
        host: "www.wikipedia.org",
        qtype: 28,
        kind: "udp",
        outcome: "ans",
        query: "123401000001000000000000037777770977696b697065646961036f726700001c0001",
        response: "123481800001000200000000037777770977696b697065646961036f726700001c0001c00c0005000100004d4800110464796e610977696b696d65646961c01ac02f001c0001000000b400102a02ec800300ed1a0000000000000001",
    },
    Captured {
        label: "www.microsoft.com A (a chain of CNAME records)",
        host: "www.microsoft.com",
        qtype: 1,
        kind: "udp",
        outcome: "ans",
        query: "12340100000100000000000003777777096d6963726f736f667403636f6d0000010001",
        response: "12348180000100030000000003777777096d6963726f736f667403636f6d0000010001c00c0005000100000908002303777777096d6963726f736f667407636f6d2d632d3307656467656b6579036e657400c02f000500010000037100190665313336373804647363620a616b616d616965646765c04dc05e000100010000001400040210b24b",
    },
    Captured {
        label: "google.com TXT (TC=1: truncated over UDP)",
        host: "google.com",
        qtype: 16,
        kind: "udp",
        outcome: "tc",
        query: "12340100000100000000000006676f6f676c6503636f6d0000100001",
        response: "12348380000100000000000006676f6f676c6503636f6d0000100001",
    },
    Captured {
        label: "google.com TXT over TCP (1176 octets)",
        host: "google.com",
        qtype: 16,
        kind: "tcp",
        outcome: "none",
        query: "12340100000100000000000006676f6f676c6503636f6d0000100001",
        response: "12348180000100110000000006676f6f676c6503636f6d0000100001c00c00100001000001260021205f723472643170767779727069377377346133687a6d77386535317968397464c00c0010000100000126005e5d636973636f2d63692d646f6d61696e2d766572696669636174696f6e3d34376333386263386334623734623732333365393035333232306331626265373662636331636433336337616366376163643336636436613533333230303462c00c0010000100000126004544676f6f676c652d736974652d766572696669636174696f6e3d346962465567422d77584c515f5337767358566f6d535456616d754f58426956417a705235495a38374430c00c0010000100000126002c2b4d533d45344136384239414232424239363730424345313534313246363239313631363443304232304242c00c0010000100000126004140776f726b2d6163636f756e74732d646f6d61696e2d766572696669636174696f6e3d54636a364a6a494d5a4f77324b73534577324e7432724c61653839744e36c00c0010000100000126004544676f6f676c652d736974652d766572696669636174696f6e3d7744384e3769314a544e546b657a4a34397377765757343866385f39787665524556346f422d304866356fc00c0010000100000126004847617263756c65732d646f6d61696e2d766572696669636174696f6e3d325234743547376e49367452436f36316c707878624c6b73505973747868476d745637356370723878394bc00c00100001000001260009085a3239765a32786cc00c0010000100000126002b2a6170706c652d646f6d61696e2d766572696669636174696f6e3d33306166494263765375445632504c58c00c0010000100000126002e2d646f63757369676e3d30353935383438382d343735322d346566322d393565622d616137626138613362643065c00c0010000100000126004544676f6f676c652d736974652d766572696669636174696f6e3d5456392d44426534523830583476304d34555f62645f4a3963704f4a4d306e696b6674306a41676a6d7351c00c0010000100000126003e3d6f6e6574727573742d646f6d61696e2d766572696669636174696f6e3d3664363835663164343161393436393661643765663737316636383939336530c00c0010000100000126003c3b66616365626f6f6b2d646f6d61696e2d766572696669636174696f6e3d3232726d3535316375346b3061623062787377353336746c647334683935c00c0010000100000126002423763d7370663120696e636c7564653a5f7370662e676f6f676c652e636f6d207e616c6cc00c0010000100000126004140676c6f62616c7369676e2d736d696d652d64763d434459582b584648557732776d6c362f4762382b353942734833314b7a55723663316c32425076714b58383dc00c0010000100000126002e2d646f63757369676e3d31623061363735342d343962312d346462352d383534302d643263313236363462323839c00c0010000100000126003e3d6f6e6574727573742d646f6d61696e2d766572696669636174696f6e3d3064343737666536303830373465366639633132626361373832363033356363",
    },
    Captured {
        label: "gmail.com MX (five records, names compressed in RDATA)",
        host: "gmail.com",
        qtype: 15,
        kind: "udp",
        outcome: "none",
        query: "12340100000100000000000005676d61696c03636f6d00000f0001",
        response: "12348180000100050000000005676d61696c03636f6d00000f0001c00c000f0001000007e7001b00050d676d61696c2d736d74702d696e016c06676f6f676c65c012c00c000f0001000007e70009002804616c7434c029c00c000f0001000007e70009001e04616c7433c029c00c000f0001000007e70009000a04616c7431c029c00c000f0001000007e70009001404616c7432c029",
    },
    Captured {
        label: "example.com NS (an authoritative reply, AA set)",
        host: "example.com",
        qtype: 2,
        kind: "auth",
        outcome: "none",
        query: "123400000001000000000000076578616d706c6503636f6d0000020001",
        response: "123484000001000200000000076578616d706c6503636f6d0000020001c00c0002000100015180001401610c69616e612d73657276657273036e657400c00c000200010001518000040162c02b",
    },
    Captured {
        label: "www.example.com A from the authoritative server (AA set)",
        host: "www.example.com",
        qtype: 1,
        kind: "auth",
        outcome: "redirect",
        query: "12340000000100000000000003777777076578616d706c6503636f6d0000010001",
        response: "12348400000100010000000003777777076578616d706c6503636f6d0000010001c00c000500010000012c002403777777076578616d706c6503636f6d0363646e0a636c6f7564666c617265036e657400",
    },
    Captured {
        label: "nothere.invalid A from the authoritative server (REFUSED)",
        host: "nothere.invalid",
        qtype: 1,
        kind: "auth",
        outcome: "refused",
        query: "123400000001000000000000076e6f746865726507696e76616c69640000010001",
        response: "123480050001000000000000076e6f746865726507696e76616c69640000010001",
    },
];

fn check_captured(c: &Captured) -> Result<(), String> {
    let query = hex(c.query);
    let response = hex(c.response);
    // The query we would send is the one that was sent (the authoritative
    // server was asked without RD, which we never send).
    if c.kind != "auth" {
        expect(
            encode_query(0x1234, c.host.as_bytes(), c.qtype).as_deref() == Some(query.as_slice()),
            "our query equals the captured query",
        )?;
    }
    let m = decoded(&response)?;
    // simple-dns reads the same message the same way.
    let theirs = Packet::parse(&response).map_err(|e| format!("simple-dns: {e}"))?;
    compare_packet(&m, &theirs)?;
    expect(
        usize::from(m.header.qdcount) == m.questions.len()
            && usize::from(m.header.ancount) == m.answers.len()
            && usize::from(m.header.nscount) == m.authority.len()
            && usize::from(m.header.arcount) == m.additional.len(),
        "counts",
    )?;
    expect(
        m.answers
            .iter()
            .chain(&m.authority)
            .all(|r| r.name.len() <= 255)
            && m.questions.iter().all(|q| q.name.len() <= 255),
        "name limits",
    )?;
    // UDP responses are datagrams; the TCP one is longer than one.
    expect(
        decode_udp(&response).is_some() == (response.len() <= 512),
        "UDP size limit",
    )?;
    let answer = answer_addresses(0x1234, c.host.as_bytes(), c.qtype, &m);
    match c.outcome {
        "tc" => expect(
            m.header.tc && answer.is_none(),
            "truncated: decoded, flagged, no answer",
        ),
        "nx" => expect(
            m.header.rcode == 3
                && answer
                    .as_ref()
                    .is_some_and(|a| a.addresses.is_empty() && a.redirect.is_none()),
            "NXDOMAIN gives the empty answer",
        ),
        "refused" => expect(
            m.header.rcode == 5 && answer.is_none(),
            "REFUSED is no answer",
        ),
        "none" => expect(answer.is_none(), "not an A or AAAA question"),
        "redirect" => {
            let a = answer.ok_or("an answer")?;
            let last = theirs.answers.iter().rev().find_map(|r| match &r.rdata {
                RData::CNAME(c) => Some(c.0.to_string()),
                _ => None,
            });
            expect(
                a.addresses.is_empty() && a.redirect.as_deref().map(wire_to_dotted) == last,
                "the chain leaves the answer section: the last CNAME target, no addresses",
            )
        }
        _ => {
            let a = answer.ok_or("an answer")?;
            let expected: Vec<Addr> = theirs
                .answers
                .iter()
                .filter_map(|r| match &r.rdata {
                    RData::A(x) if c.qtype == 1 => Some(Addr::V4(x.address)),
                    RData::AAAA(x) if c.qtype == 28 => Some(Addr::V6(x.address)),
                    _ => None,
                })
                .collect();
            expect(
                !a.addresses.is_empty() && a.redirect.is_none(),
                "addresses, no redirect",
            )?;
            expect(a.addresses == expected, "the addresses simple-dns reads")
        }
    }
}

fn captured() -> Suite {
    let mut suite = Suite::new("captured DNS responses", CAPTURED.len());
    for c in CAPTURED {
        suite.check(c.label, check_captured(c));
    }
    suite
}

// ---------------------------------------------------------------------------
// simple-dns.
// ---------------------------------------------------------------------------

fn rcode_number(r: RCODE) -> Option<u8> {
    (0u8..=10).find(|n| RCODE::from(u16::from(*n)) == r)
}

fn opcode_number(o: OPCODE) -> Option<u8> {
    [0u8, 1, 2, 4, 5]
        .into_iter()
        .find(|n| OPCODE::from(u16::from(*n)) == o)
}

/// Compare what we decoded with what simple-dns read from the same octets:
/// the header, the questions, and every record's owner, type, class, TTL and
/// (for A, AAAA and CNAME) data.
fn compare_packet(ours: &Msg, theirs: &Packet<'_>) -> Result<(), String> {
    let h = &ours.header;
    expect(h.id == theirs.id(), "id")?;
    expect(h.qr == theirs.has_flags(PacketFlag::RESPONSE), "qr")?;
    expect(
        h.aa == theirs.has_flags(PacketFlag::AUTHORITATIVE_ANSWER),
        "aa",
    )?;
    expect(h.tc == theirs.has_flags(PacketFlag::TRUNCATION), "tc")?;
    expect(
        h.rd == theirs.has_flags(PacketFlag::RECURSION_DESIRED),
        "rd",
    )?;
    expect(
        h.ra == theirs.has_flags(PacketFlag::RECURSION_AVAILABLE),
        "ra",
    )?;
    if let Some(n) = opcode_number(theirs.opcode()) {
        expect(h.opcode == n, "opcode")?;
    }
    if let Some(n) = rcode_number(theirs.rcode()) {
        expect(h.rcode == n, "rcode")?;
    }
    expect(
        ours.questions.len() == theirs.questions.len(),
        "question count",
    )?;
    for (o, t) in ours.questions.iter().zip(&theirs.questions) {
        expect(
            labels_of(&o.name) == their_labels(&t.qname),
            "question name",
        )?;
        expect(o.qtype == u16::from(t.qtype), "qtype")?;
        let class = u16::from(t.qclass) | if t.unicast_response { 0x8000 } else { 0 };
        expect(o.qclass == class, "qclass")?;
    }
    for (os, ts, what) in [
        (&ours.answers, &theirs.answers, "answer"),
        (&ours.authority, &theirs.name_servers, "authority"),
        (&ours.additional, &theirs.additional_records, "additional"),
    ] {
        expect(os.len() == ts.len(), &format!("{what} count"))?;
        for (o, t) in os.iter().zip(ts.iter()) {
            compare_record(o, t).map_err(|e| format!("{what}: {e}"))?;
        }
    }
    Ok(())
}

fn compare_record(o: &Rec, t: &ResourceRecord<'_>) -> Result<(), String> {
    expect(labels_of(&o.name) == their_labels(&t.name), "owner")?;
    expect(o.rtype == u16::from(t.rdata.type_code()), "type")?;
    let class = (t.class as u16) | if t.cache_flush { 0x8000 } else { 0 };
    expect(o.rclass == class, "class")?;
    expect(o.ttl == t.ttl, "ttl")?;
    match (&o.rdata, &t.rdata) {
        (Rd::A(a), RData::A(b)) => expect(*a == b.address, "A address"),
        (Rd::Aaaa(a), RData::AAAA(b)) => expect(*a == b.address, "AAAA address"),
        (Rd::Cname(a), RData::CNAME(b)) => {
            expect(labels_of(a) == their_labels(&b.0), "CNAME target")
        }
        (Rd::Opaque(_), _) => Ok(()),
        (a, b) => Err(format!("rdata kinds differ: {a:?} and {b:?}")),
    }
}

// ---------------------------------------------------------------------------
// 3. Random well-formed messages.
// ---------------------------------------------------------------------------

const LABEL_CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-";

fn random_label(r: &mut Rng) -> String {
    let n = if r.chance(40) {
        63
    } else {
        r.below(10).saturating_add(1)
    };
    (0..n)
        .map(|_| char::from(at(LABEL_CHARS, r.below(LABEL_CHARS.len()))))
        .collect()
}

fn random_name(r: &mut Rng, pool: &[String]) -> String {
    if !pool.is_empty() && r.chance(2) {
        let base = pool.get(r.below(pool.len())).cloned().unwrap_or_default();
        if r.chance(2) {
            return base;
        }
        // A new first label on an old name: compressible.
        return format!("{}.{base}", random_label(r));
    }
    let mut labels = Vec::new();
    let mut total = 1usize;
    for _ in 0..r.below(4).saturating_add(1) {
        let l = random_label(r);
        total = total.saturating_add(l.len()).saturating_add(1);
        if total > 200 {
            break;
        }
        labels.push(l);
    }
    labels.join(".")
}

#[derive(Debug, Clone)]
enum Data {
    A(u32),
    Aaaa(u128),
    Cname(String),
    /// A type simple-dns keeps as raw data, and the octets.
    Opaque(u16, Vec<u8>),
}

#[derive(Debug, Clone)]
struct RecDesc {
    owner: String,
    class: u16,
    ttl: u32,
    data: Data,
}

#[derive(Debug, Clone)]
struct Desc {
    id: u16,
    response: bool,
    opcode: u8,
    rcode: u8,
    aa: bool,
    tc: bool,
    rd: bool,
    ra: bool,
    questions: Vec<(String, u16)>,
    sections: [Vec<RecDesc>; 3],
}

fn random_record(r: &mut Rng, pool: &mut Vec<String>) -> RecDesc {
    let owner = random_name(r, pool);
    pool.push(owner.clone());
    let data = match r.below(5) {
        0 | 1 => Data::A(r.u32()),
        2 => Data::Aaaa(r.u128()),
        3 => Data::Cname(random_name(r, pool)),
        _ => {
            let kinds = [99u16, 300, 65280, 10];
            let t = kinds.get(r.below(kinds.len())).copied().unwrap_or(99);
            Data::Opaque(t, (0..r.below(20)).map(|_| r.byte()).collect())
        }
    };
    RecDesc {
        owner,
        class: 1,
        ttl: r.u32() & 0x7FFF_FFFF,
        data,
    }
}

fn random_desc(r: &mut Rng) -> Desc {
    let mut pool: Vec<String> = Vec::new();
    let opcodes = [0u8, 1, 2, 4, 5];
    let mut d = Desc {
        id: r.u16(),
        response: !r.chance(5),
        opcode: opcodes.get(r.below(opcodes.len())).copied().unwrap_or(0),
        rcode: u8::try_from(r.below(6)).unwrap_or(0),
        aa: r.chance(2),
        tc: r.chance(8),
        rd: r.chance(2),
        ra: r.chance(2),
        questions: Vec::new(),
        sections: [Vec::new(), Vec::new(), Vec::new()],
    };
    for _ in 0..r.below(3) {
        let name = random_name(r, &pool);
        pool.push(name.clone());
        let qtypes = [1u16, 28, 5, 16];
        let qt = qtypes.get(r.below(qtypes.len())).copied().unwrap_or(1);
        d.questions.push((name, qt));
    }
    for s in 0..3 {
        for _ in 0..r.below(5) {
            let rec = random_record(r, &mut pool);
            if let Some(sec) = d.sections.get_mut(s) {
                sec.push(rec);
            }
        }
    }
    d
}

fn build_rr(rd: &RecDesc) -> Option<ResourceRecord<'static>> {
    let data = match &rd.data {
        Data::A(a) => RData::A(A { address: *a }),
        Data::Aaaa(a) => RData::AAAA(AAAA { address: *a }),
        Data::Cname(n) => RData::CNAME(CNAME(Name::new_unchecked(n).into_owned())),
        Data::Opaque(t, bytes) => RData::NULL(*t, NULL::new(bytes.as_slice()).ok()?.into_owned()),
    };
    Some(ResourceRecord::new(
        Name::new_unchecked(&rd.owner).into_owned(),
        CLASS::try_from(rd.class).ok()?,
        rd.ttl,
        data,
    ))
}

/// The message simple-dns writes for `d`, with or without compression.
fn encode_desc(d: &Desc, compressed: bool) -> Option<Vec<u8>> {
    let mut p = if d.response {
        Packet::new_reply(d.id)
    } else {
        Packet::new_query(d.id)
    };
    for (flag, on) in [
        (PacketFlag::AUTHORITATIVE_ANSWER, d.aa),
        (PacketFlag::TRUNCATION, d.tc),
        (PacketFlag::RECURSION_DESIRED, d.rd),
        (PacketFlag::RECURSION_AVAILABLE, d.ra),
    ] {
        if on {
            p.set_flags(flag);
        } else {
            p.remove_flags(flag);
        }
    }
    *p.opcode_mut() = OPCODE::from(u16::from(d.opcode));
    *p.rcode_mut() = RCODE::from(u16::from(d.rcode));
    for (name, qt) in &d.questions {
        p.questions.push(Question::new(
            Name::new_unchecked(name).into_owned(),
            QTYPE::try_from(*qt).ok()?,
            QCLASS::CLASS(CLASS::IN),
            false,
        ));
    }
    for rec in d.sections.first()? {
        p.answers.push(build_rr(rec)?);
    }
    for rec in d.sections.get(1)? {
        p.name_servers.push(build_rr(rec)?);
    }
    for rec in d.sections.get(2)? {
        p.additional_records.push(build_rr(rec)?);
    }
    if compressed {
        p.build_bytes_vec_compressed().ok()
    } else {
        p.build_bytes_vec().ok()
    }
}

/// What we decoded against what was written.
fn compare_desc(ours: &Msg, d: &Desc, exact_case: bool) -> Result<(), String> {
    let h = &ours.header;
    expect(h.id == d.id && h.qr == d.response, "id, qr")?;
    expect(h.opcode == d.opcode && h.rcode == d.rcode, "opcode, rcode")?;
    expect(
        h.aa == d.aa && h.tc == d.tc && h.rd == d.rd && h.ra == d.ra,
        "flags",
    )?;
    expect(h.z == 0, "z")?;
    let eq = |a: &str, b: &str| {
        if exact_case { a == b } else { same_name(a, b) }
    };
    expect(ours.questions.len() == d.questions.len(), "question count")?;
    for (o, (name, qt)) in ours.questions.iter().zip(&d.questions) {
        expect(
            eq(&wire_to_dotted(&o.name), name) && o.qtype == *qt && o.qclass == 1,
            "question",
        )?;
    }
    for (s, (os, what)) in [
        (&ours.answers, "answer"),
        (&ours.authority, "authority"),
        (&ours.additional, "additional"),
    ]
    .into_iter()
    .enumerate()
    {
        let ds = d.sections.get(s).ok_or("sections")?;
        expect(os.len() == ds.len(), &format!("{what} count"))?;
        for (o, rec) in os.iter().zip(ds) {
            expect(
                eq(&wire_to_dotted(&o.name), &rec.owner),
                &format!("{what} owner"),
            )?;
            expect(
                o.rclass == rec.class && o.ttl == rec.ttl,
                &format!("{what} class, ttl"),
            )?;
            match (&o.rdata, &rec.data) {
                (Rd::A(a), Data::A(b)) if o.rtype == 1 => expect(a == b, "A")?,
                (Rd::Aaaa(a), Data::Aaaa(b)) if o.rtype == 28 => expect(a == b, "AAAA")?,
                (Rd::Cname(a), Data::Cname(b)) if o.rtype == 5 => {
                    expect(eq(&wire_to_dotted(a), b), "CNAME")?;
                }
                (Rd::Opaque(a), Data::Opaque(t, b)) if o.rtype == *t => expect(a == b, "opaque")?,
                _ => {
                    return Err(format!(
                        "{what}: rdata {:?} against {:?}",
                        o.rdata, rec.data
                    ));
                }
            }
        }
    }
    Ok(())
}

fn random_messages() -> Suite {
    let mut r = Rng(0x1B87_3593_CC9E_2D51);
    let cases = if cfg!(miri) { 30 } else { 4000usize };
    let mut suite = Suite::new(
        "simple-dns differential: random messages",
        cases.saturating_mul(2),
    );
    for n in 0..cases {
        let d = random_desc(&mut r);
        for compressed in [false, true] {
            let what = format!("message {n} (compressed: {compressed})");
            let result = (|| -> Result<(), String> {
                let bytes = encode_desc(&d, compressed).ok_or("simple-dns could not write it")?;
                let ours = decode_message(&bytes)
                    .ok_or_else(|| format!("rejected {bytes:02x?} for {d:?}"))?;
                // What was written: names exactly as given where nothing
                // is compressed, up to case where simple-dns compressed.
                compare_desc(&ours, &d, !compressed)?;
                // What simple-dns reads back.
                let theirs = Packet::parse(&bytes).map_err(|e| format!("simple-dns: {e}"))?;
                compare_packet(&ours, &theirs)?;
                // The counts of the header are the lengths.
                expect(
                    usize::from(ours.header.ancount) == ours.answers.len(),
                    "ancount is the number of answers",
                )?;
                // UDP and TCP framing of the same message.
                if bytes.len() <= 512 {
                    expect(decode_udp(&bytes).is_some(), "UDP")?;
                } else {
                    expect(
                        decode_udp(&bytes).is_none(),
                        "over 512 octets is not a datagram",
                    )?;
                }
                let framed = tcp_frame(&bytes).ok_or("frame")?;
                expect(tcp_message_len(&framed) == Some(bytes.len()), "TCP length")
            })();
            suite.check(&what, result);
        }
    }
    suite
}

// ---------------------------------------------------------------------------
// 4. Our queries, read by simple-dns.
// ---------------------------------------------------------------------------

fn our_queries() -> Suite {
    let mut r = Rng(0x85EB_CA6B_C2B2_AE35);
    let cases = if cfg!(miri) { 30 } else { 4000usize };
    let mut suite = Suite::new("simple-dns differential: our queries", cases);
    for n in 0..cases {
        let mut pool: Vec<String> = Vec::new();
        let mut name = random_name(&mut r, &pool);
        pool.push(name.clone());
        if r.chance(4) {
            name.push('.');
        }
        let qtypes = [1u16, 28, 5, 16, 255];
        let qtype = qtypes.get(r.below(qtypes.len())).copied().unwrap_or(1);
        let id = r.u16();
        let result = (|| -> Result<(), String> {
            let bytes = encode_query(id, name.as_bytes(), qtype)
                .ok_or("our encoder refused a valid name")?;
            let theirs = Packet::parse(&bytes).map_err(|e| format!("simple-dns: {e}"))?;
            expect(theirs.id() == id, "id")?;
            expect(!theirs.has_flags(PacketFlag::RESPONSE), "a query")?;
            expect(theirs.has_flags(PacketFlag::RECURSION_DESIRED), "RD")?;
            expect(
                !theirs.has_flags(PacketFlag::AUTHORITATIVE_ANSWER | PacketFlag::TRUNCATION),
                "AA, TC clear",
            )?;
            expect(
                theirs.opcode() == OPCODE::StandardQuery && theirs.rcode() == RCODE::NoError,
                "opcode, rcode",
            )?;
            expect(theirs.questions.len() == 1, "one question")?;
            expect(
                theirs.answers.is_empty()
                    && theirs.name_servers.is_empty()
                    && theirs.additional_records.is_empty(),
                "no records",
            )?;
            let q = theirs.questions.first().ok_or("question")?;
            expect(
                q.qname.to_string() == name.trim_end_matches('.'),
                "name, as given",
            )?;
            expect(
                u16::from(q.qtype) == qtype && q.qclass == QCLASS::CLASS(CLASS::IN),
                "type, class",
            )?;
            // And we read it ourselves, as a datagram.
            let m = decode_udp(&bytes).ok_or("decode_udp")?;
            // The name, from the wire back to a dotted string: ours must
            // give the name that was asked, and the labels simple-dns read.
            let wire = m
                .questions
                .first()
                .map(|q| q.name.as_slice())
                .ok_or("question")?;
            let dotted = dotted_of_wire(wire).ok_or("wire_to_dotted refused a name we sent")?;
            expect(
                dotted == name.trim_end_matches('.').as_bytes(),
                "wire_to_dotted gives the name back",
            )?;
            let their_dotted: Vec<u8> = their_labels(&q.qname).join(&b'.');
            expect(
                dotted == their_dotted,
                "wire_to_dotted agrees with simple-dns",
            )?;
            expect(
                m.questions.len() == 1 && m.header.rd && !m.header.qr,
                "decoded",
            )
        })();
        suite.check(&format!("query {n} {name}"), result);
    }
    suite
}

// ---------------------------------------------------------------------------
// 5. Mutated messages.
// ---------------------------------------------------------------------------

/// Damage an encoding: overwrite, drop, insert or duplicate octets, plant
/// compression pointers and extreme lengths, or truncate.
fn mutate(r: &mut Rng, mut b: Vec<u8>) -> Vec<u8> {
    for _ in 0..=r.below(3) {
        match r.below(8) {
            0 if !b.is_empty() => {
                let i = r.below(b.len());
                if let Some(x) = b.get_mut(i) {
                    *x = r.byte();
                }
            }
            1 if !b.is_empty() => {
                let i = r.below(b.len());
                b.remove(i);
            }
            2 => {
                let i = r.below(b.len().saturating_add(1));
                b.insert(i, r.byte());
            }
            3 if b.len() > 13 => {
                // A pointer, anywhere, to anywhere.
                let i = r.below(b.len().saturating_sub(1));
                let target = u16::try_from(r.below(b.len())).unwrap_or(0);
                if let Some(x) = b.get_mut(i) {
                    *x = 0xC0 | u8::try_from(target >> 8).unwrap_or(0);
                }
                if let Some(x) = b.get_mut(i.saturating_add(1)) {
                    *x = u8::try_from(target & 0xFF).unwrap_or(0);
                }
            }
            4 if b.len() > 12 => {
                // An extreme length octet or count.
                let i = r.below(b.len());
                let v = [0u8, 1, 62, 63, 64, 127, 128, 191, 192, 255];
                if let Some(x) = b.get_mut(i) {
                    *x = v.get(r.below(v.len())).copied().unwrap_or(0);
                }
            }
            5 if b.len() > 5 => {
                // A huge count in the header.
                let i = r.below(4).saturating_add(4);
                if let Some(x) = b.get_mut(i) {
                    *x = 0xFF;
                }
            }
            6 if !b.is_empty() => {
                let i = r.below(b.len());
                let v = at(&b, i);
                b.insert(i, v);
            }
            _ => b.truncate(r.below(b.len().saturating_add(1))),
        }
    }
    b
}

/// The rules that are varied to say why we reject what simple-dns accepts.
#[derive(Clone, Copy)]
struct Rules {
    /// A pointer's target name must end before the pointer ("a prior
    /// occurrence", spec.rs); without it any offset below the message's
    /// length is followed (the expanded name is still limited to 255
    /// octets, which stops loops, as in simple-dns).
    prior: bool,
    /// The data of an A, AAAA or CNAME record may be shorter than its
    /// RDLENGTH (the rest is skipped).
    rdata_slack: bool,
    /// A record of a type we interpret may have RDLENGTH 0.
    empty_rdata: bool,
    /// Octets may follow the last record.
    trailing: bool,
    /// The Z bits that RFC 4035 assigned (AD and CD) may be set.
    ad_cd: bool,
}

/// Where a name at `pos` ends in the message, with its labels within
/// `limit`.
fn rules_name_end(b: &[u8], pos: usize, limit: usize, rules: Rules) -> Option<usize> {
    let mut p = pos;
    let mut lim = limit.min(b.len());
    let mut end: Option<usize> = None;
    let mut total = 0usize;
    let mut steps = 0usize;
    loop {
        steps = steps.saturating_add(1);
        if p >= lim || steps > 4000 {
            return None;
        }
        let l = usize::from(at(b, p));
        if l == 0 {
            return Some(end.unwrap_or_else(|| p.saturating_add(1)));
        }
        if l >= 192 {
            if p.saturating_add(2) > lim {
                return None;
            }
            let target = (l & 63)
                .saturating_mul(256)
                .saturating_add(usize::from(at(b, p.saturating_add(1))));
            if end.is_none() {
                end = Some(p.saturating_add(2));
            }
            if rules.prior {
                if target >= p {
                    return None;
                }
                lim = p;
            } else {
                lim = b.len();
            }
            p = target;
        } else if l >= 64 {
            return None;
        } else {
            let next = p.saturating_add(1).saturating_add(l);
            if next > lim {
                return None;
            }
            total = total.saturating_add(1).saturating_add(l);
            if total > 254 {
                return None;
            }
            p = next;
        }
    }
}

/// Whether the message is accepted under `rules` (with all of spec.rs's
/// rules when `rules` is [`SPEC_RULES`]).
fn rules_accept(b: &[u8], rules: Rules) -> bool {
    let z = (u16::from_be_bytes([at(b, 2), at(b, 3)]) >> 4) & 7;
    let z_ok = if rules.ad_cd { z & 4 == 0 } else { z == 0 };
    if b.len() < 12 || b.len() > 65535 || !z_ok {
        return false;
    }
    let count = |i: usize| usize::from(u16::from_be_bytes([at(b, i), at(b, i.saturating_add(1))]));
    let mut pos = 12usize;
    for _ in 0..count(4) {
        let Some(e) = rules_name_end(b, pos, b.len(), rules) else {
            return false;
        };
        pos = e.saturating_add(4);
        if pos > b.len() {
            return false;
        }
    }
    for i in [6usize, 8, 10] {
        for _ in 0..count(i) {
            let Some(e) = rules_name_end(b, pos, b.len(), rules) else {
                return false;
            };
            let fixed = e.saturating_add(10);
            if fixed > b.len() {
                return false;
            }
            let rtype = u16::from_be_bytes([at(b, e), at(b, e.saturating_add(1))]);
            let rclass =
                u16::from_be_bytes([at(b, e.saturating_add(2)), at(b, e.saturating_add(3))]);
            let rdlen = usize::from(u16::from_be_bytes([
                at(b, e.saturating_add(8)),
                at(b, e.saturating_add(9)),
            ]));
            let rend = fixed.saturating_add(rdlen);
            if rend > b.len() {
                return false;
            }
            let interpreted = rclass == 1 && matches!(rtype, 1 | 5 | 28);
            let ok = if interpreted && rdlen == 0 && rules.empty_rdata {
                true
            } else {
                match (rclass == 1, rtype) {
                    (true, 1) => rdlen == 4 || (rules.rdata_slack && rdlen > 4),
                    (true, 28) => rdlen == 16 || (rules.rdata_slack && rdlen > 16),
                    (true, 5) => match rules_name_end(b, fixed, rend, rules) {
                        Some(e) => e == rend || (rules.rdata_slack && e <= rend),
                        None => false,
                    },
                    _ => true,
                }
            };
            if !ok {
                return false;
            }
            pos = rend;
        }
    }
    pos == b.len() || (rules.trailing && pos < b.len())
}

const SPEC_RULES: Rules = Rules {
    prior: true,
    rdata_slack: false,
    empty_rdata: false,
    trailing: false,
    ad_cd: false,
};

/// Why simple-dns accepts what we reject, from the octets alone.
fn why_we_reject(bytes: &[u8], theirs: &Packet<'_>) -> Option<String> {
    if theirs.opt().is_some()
        || theirs
            .additional_records
            .iter()
            .any(|r| u16::from(r.rdata.type_code()) == 41)
    {
        return Some("OPT record (EDNS): read by simple-dns as header data".to_owned());
    }
    // Which of our rules, relaxed, would accept it? Each is a rule of spec.rs
    // that simple-dns does not have; the fewest relaxations that do are the
    // reason.
    let names = [
        "a pointer to a name that does not end before it (spec.rs requires \"a prior occurrence\", ERRATA.md)",
        "an A, AAAA or CNAME record whose RDLENGTH is longer than its data (simple-dns skips the rest)",
        "RDLENGTH 0 on a type we interpret (simple-dns reads an empty record, RFC 2136)",
        "octets after the last record",
        "the AD or CD bit (RFC 4035) in what RFC 1035 calls Z",
    ];
    let mut subsets: Vec<u8> = (1u8..32).collect();
    subsets.sort_by_key(|s| s.count_ones());
    for s in subsets {
        let on = |bit: u8| s & (1 << bit) != 0;
        let rules = Rules {
            prior: !on(0),
            rdata_slack: on(1),
            empty_rdata: on(2),
            trailing: on(3),
            ad_cd: on(4),
        };
        if rules_accept(bytes, rules) {
            let why: Vec<&str> = (0u8..5)
                .filter(|b| on(*b))
                .filter_map(|b| names.get(usize::from(b)).copied())
                .collect();
            return Some(why.join("; and "));
        }
    }
    None
}

/// Why we accept what simple-dns rejects.
fn why_they_reject(ours: &Msg) -> Option<String> {
    let all = ours
        .answers
        .iter()
        .chain(&ours.authority)
        .chain(&ours.additional);
    for rec in all {
        if matches!(rec.rdata, Rd::Opaque(_)) && ![1u16, 5, 28].contains(&rec.rtype) {
            return Some(
                "a type we keep as opaque RDATA that simple-dns reads structurally (or a class it does not know)".to_owned(),
            );
        }
        if CLASS::try_from(rec.rclass & 0x7FFF).is_err() {
            return Some("a class simple-dns does not know".to_owned());
        }
    }
    if ours
        .questions
        .iter()
        .any(|q| QTYPE::try_from(q.qtype).is_err() || QCLASS::try_from(q.qclass & 0x7FFF).is_err())
    {
        return Some("a QTYPE or QCLASS simple-dns does not know".to_owned());
    }
    if ours.header.opcode == 3 || ours.header.opcode > 5 {
        return Some("a reserved OPCODE".to_owned());
    }
    None
}

fn bump(kinds: &mut BTreeMap<String, usize>, key: String) {
    let slot = kinds.entry(key).or_insert(0);
    *slot = slot.saturating_add(1);
}

fn mutated_messages() -> Suite {
    let mut r = Rng(0xC2B2_AE3D_27D4_EB4F);
    let cases = if cfg!(miri) { 60 } else { 60_000usize };
    let mut suite = Suite::new("simple-dns differential: mutated messages", cases);
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for n in 0..cases {
        let bytes = if r.chance(8) {
            (0..r.below(40)).map(|_| r.byte()).collect()
        } else {
            let d = random_desc(&mut r);
            let compressed = r.chance(2);
            let base = encode_desc(&d, compressed).unwrap_or_default();
            mutate(&mut r, base)
        };
        let ours = decode_message(&bytes);
        let theirs = Packet::parse(&bytes);
        // The test's own reading of spec.rs's structure must agree with the
        // decoder on every input (it is what explains the differences).
        if ours.is_some() != rules_accept(&bytes, SPEC_RULES) {
            suite.check(
                &format!("mutated {n}"),
                Err(format!(
                    "decode_message and the test's own reading disagree on {bytes:02x?}"
                )),
            );
            continue;
        }
        let (outcome, kind): (Result<(), String>, String) = match (&ours, &theirs) {
            (Some(o), Ok(t)) => match compare_packet(o, t) {
                Ok(()) => (Ok(()), "both accept, equal contents".into()),
                Err(e) => (
                    Err(format!("both accept {bytes:02x?} but differ: {e}")),
                    format!("both accept, differ: {e}"),
                ),
            },
            (None, Err(_)) => (Ok(()), "both reject".into()),
            (None, Ok(t)) => match why_we_reject(&bytes, t) {
                Some(why) => {
                    suite.xfail();
                    bump(&mut kinds, format!("we reject, simple-dns accepts: {why}"));
                    continue;
                }
                None => (
                    Err(format!(
                        "we reject {bytes:02x?}, simple-dns accepts it as {t:?}"
                    )),
                    "unexplained".into(),
                ),
            },
            (Some(o), Err(e)) => match why_they_reject(o) {
                Some(why) => {
                    suite.xfail();
                    bump(&mut kinds, format!("we accept, simple-dns rejects: {why}"));
                    continue;
                }
                None => (
                    Err(format!(
                        "we accept {bytes:02x?} as {o:?}, simple-dns rejects it: {e}"
                    )),
                    "unexplained".into(),
                ),
            },
        };
        bump(&mut kinds, kind);
        suite.check(&format!("mutated {n}"), outcome);
    }
    for (k, v) in &kinds {
        println!("clazel-dns mutated messages: {v:>6} {k}");
    }
    suite
}

// ---------------------------------------------------------------------------
// 6. resolv.conf.
// ---------------------------------------------------------------------------

fn resolv_conf() -> Suite {
    let cases: &[(&str, &str, Vec<Addr>)] = &[
        (
            "macOS style",
            "#\n# macOS Notice\n#\nnameserver 192.168.1.1\nnameserver fe80::1\nsearch lan\n",
            vec![
                v4(192, 168, 1, 1),
                Addr::V6(0xfe80_0000_0000_0000_0000_0000_0000_0001),
            ],
        ),
        (
            "glibc style",
            "# Generated\nnameserver 127.0.0.53\noptions edns0 trust-ad\nsearch example.com\n",
            vec![v4(127, 0, 0, 53)],
        ),
        (
            "two IPv6 servers",
            "nameserver 2001:4860:4860::8888\nnameserver 2001:4860:4860::8844\n",
            vec![
                Addr::V6(0x2001_4860_4860_0000_0000_0000_0000_8888),
                Addr::V6(0x2001_4860_4860_0000_0000_0000_0000_8844),
            ],
        ),
        (
            "no nameserver",
            "search example.com\noptions ndots:1\n",
            vec![],
        ),
        ("empty", "", vec![]),
        (
            "CR LF",
            "nameserver 1.2.3.4\r\nnameserver 5.6.7.8\r\n",
            vec![v4(1, 2, 3, 4), v4(5, 6, 7, 8)],
        ),
        (
            "comment after address",
            "nameserver 9.9.9.9 # quad nine\n",
            vec![v4(9, 9, 9, 9)],
        ),
        (
            "not addresses",
            "nameserver example.com\nnameserver 1.2.3\nnameserver 999.1.1.1\nnameserver ::g\n",
            vec![],
        ),
        (
            "zone id and brackets",
            "nameserver fe80::1%en0\nnameserver [::1]\n",
            vec![],
        ),
        ("tabs", "\tnameserver\t10.1.1.1\n", vec![v4(10, 1, 1, 1)]),
    ];
    let mut suite = Suite::new("resolv.conf nameserver lines", cases.len());
    for (name, text, expected) in cases {
        let got = nameservers(text.as_bytes());
        suite.check(
            name,
            expect(
                &got == expected,
                &format!("got {got:?}, expected {expected:?}"),
            ),
        );
    }
    suite
}

// ---------------------------------------------------------------------------
// The tests.
// ---------------------------------------------------------------------------

#[test]
fn hand_built_messages() {
    hand_built().finish();
}

#[test]
fn captured_responses() {
    captured().finish();
}

#[test]
fn differential_random_messages() {
    random_messages().finish();
}

#[test]
fn differential_our_queries() {
    our_queries().finish();
}

#[test]
fn differential_mutated_messages() {
    mutated_messages().finish();
}

#[test]
fn resolv_conf_nameserver_lines() {
    resolv_conf().finish();
}
