//! Store conformance (docs/phases/phase-3.md item 3.10a).
//!
//! The proofs show the code equal to `spec.rs`. The log format is this
//! project's own (the 3.10a.0 design note), so no official suite exists for
//! it; this file checks the parts that have outside definitions against the
//! outside world:
//!
//! 1. CRC-32C's published vectors: RFC 7143 §A.4's four 32-octet messages
//!    and the catalogue check value of "123456789" (CRC-32C/ISCSI, `0xe3069283`).
//! 2. A differential against an independent CRC engine, `crc` 3.4.0's
//!    catalogue entry `CRC_32_ISCSI`, on random messages of every length up
//!    to 300 octets and a few long ones.
//! 3. Headers and records decoded by an independent DER engine, RustCrypto's
//!    `der` 0.8.2: every header and record we write must be one complete DER
//!    value that `der` reads back field by field as what was written, with
//!    each record's check equal to `crc`'s CRC-32C of its commit and
//!    operations. The inputs are random identities and transactions (keys
//!    and values up to 70 000 octets, so long-form lengths occur), with
//!    commit numbers across the whole range.
//!
//! Each case is one unit of its suite. Under Miri, which is there to find
//! undefined behaviour and not to repeat these comparisons, the suites run
//! fewer cases and no long inputs: a bit-at-a-time CRC of a megabyte takes
//! hours there.

use clazel_store::crc32c::exec::crc32c;
use clazel_store::log::exec::{OpRef, encode_header, encode_record};
use der::asn1::{AnyRef, OctetString};
use der::{Decode, Reader, SliceReader, Tag, TagNumber, Tagged};

const ISCSI: crc::Crc<u32> = crc::Crc::<u32>::new(&crc::CRC_32_ISCSI);

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
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next().to_le_bytes()[0]).collect()
    }
}

fn report(suite: &str, pass: usize, fail: usize, total: usize) {
    println!("clazel-conformance: suite=\"{suite}\" pass={pass} xfail=0 fail={fail} total={total}");
}

#[test]
fn crc32c_published_vectors() {
    let mut incrementing = [0u8; 32];
    let mut decrementing = [0u8; 32];
    for (i, (up, down)) in incrementing
        .iter_mut()
        .zip(decrementing.iter_mut())
        .enumerate()
    {
        let i = u8::try_from(i).unwrap_or(0);
        *up = i;
        *down = 31u8.saturating_sub(i);
    }
    let cases: [(&[u8], [u8; 4]); 5] = [
        (&[0u8; 32], [0xaa, 0x36, 0x91, 0x8a]),
        (&[0xffu8; 32], [0x43, 0xab, 0xa8, 0x62]),
        (&incrementing, [0x4e, 0x79, 0xdd, 0x46]),
        (&decrementing, [0x5c, 0xdb, 0x3f, 0x11]),
        (b"123456789", 0xe306_9283u32.to_le_bytes()),
    ];
    let fail = cases.iter().filter(|(m, want)| crc32c(m) != *want).count();
    report(
        "CRC-32C RFC 7143 A.4 and catalogue check value",
        cases.len().saturating_sub(fail),
        fail,
        cases.len(),
    );
    assert_eq!(fail, 0);
}

#[test]
fn crc32c_against_crc_engine() {
    let mut rng = Rng(0x5eed_c0de_1234_5678);
    let lengths = if cfg!(miri) { 0..=20 } else { 0..=300 };
    let mut messages: Vec<Vec<u8>> = lengths.map(|n| rng.bytes(n)).collect();
    if !cfg!(miri) {
        for n in [1000usize, 4096, 65_537, 1_000_003] {
            messages.push(rng.bytes(n));
        }
    }
    let fail = messages
        .iter()
        .filter(|m| crc32c(m) != ISCSI.checksum(m).to_le_bytes())
        .count();
    report(
        "CRC-32C differential vs crc 3.4.0 CRC_32_ISCSI",
        messages.len().saturating_sub(fail),
        fail,
        messages.len(),
    );
    assert_eq!(fail, 0);
}

/// The fields of one decoded value: a complete DER encoding, nothing after.
fn whole(bytes: &[u8]) -> Option<AnyRef<'_>> {
    AnyRef::from_der(bytes).ok()
}

/// Read the components of a SEQUENCE's contents as raw values.
fn components(contents: &[u8]) -> Option<Vec<AnyRef<'_>>> {
    let mut r = SliceReader::new(contents).ok()?;
    let mut out = Vec::new();
    while !r.is_finished() {
        out.push(AnyRef::decode(&mut r).ok()?);
    }
    Some(out)
}

fn octets(any: &AnyRef<'_>) -> Option<Vec<u8>> {
    let v: OctetString = any.decode_as().ok()?;
    Some(v.as_bytes().to_vec())
}

/// What `der` reads from a header: magic, version and identity.
fn der_header(bytes: &[u8]) -> Option<(Vec<u8>, u64, Vec<u8>)> {
    let seq = whole(bytes)?;
    if seq.tag() != Tag::Sequence {
        return None;
    }
    let parts = components(seq.value())?;
    let [magic, version, identity] = parts.as_slice() else {
        return None;
    };
    Some((octets(magic)?, version.decode_as().ok()?, octets(identity)?))
}

#[test]
fn headers_against_der() {
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    let lengths = if cfg!(miri) { 0..10 } else { 0..200 };
    let mut identities: Vec<Vec<u8>> = lengths.map(|n| rng.bytes(n)).collect();
    if !cfg!(miri) {
        identities.push(rng.bytes(4096));
    }
    let fail = identities
        .iter()
        .filter(|id| {
            der_header(&encode_header(id)) != Some((b"clazel-store".to_vec(), 1, id.to_vec()))
        })
        .count();
    report(
        "Store headers decoded by der 0.8.2",
        identities.len().saturating_sub(fail),
        fail,
        identities.len(),
    );
    assert_eq!(fail, 0);
}

/// An operation as `der` reads it back.
#[derive(Debug, PartialEq)]
enum Owned {
    Put(u32, Vec<u8>, Vec<u8>),
    Delete(u32, Vec<u8>),
    Clear(u32),
}

fn owned(op: &OpRef) -> Owned {
    match op {
        OpRef::Put { bottle, key, value } => Owned::Put(*bottle, key.to_vec(), value.to_vec()),
        OpRef::Delete { bottle, key } => Owned::Delete(*bottle, key.to_vec()),
        OpRef::Clear { bottle } => Owned::Clear(*bottle),
    }
}

fn der_op(any: &AnyRef<'_>) -> Option<Owned> {
    let Tag::ContextSpecific {
        constructed: true,
        number,
    } = any.tag()
    else {
        return None;
    };
    let parts = components(any.value())?;
    match (number, parts.as_slice()) {
        (TagNumber(0), [b, k, v]) => Some(Owned::Put(b.decode_as().ok()?, octets(k)?, octets(v)?)),
        (TagNumber(1), [b, k]) => Some(Owned::Delete(b.decode_as().ok()?, octets(k)?)),
        (TagNumber(2), [b]) => Some(Owned::Clear(b.decode_as().ok()?)),
        _ => None,
    }
}

/// What `der` reads from a record: commit, operations, and whether the
/// check is `crc`'s CRC-32C of the octets before it.
fn der_record(bytes: &[u8]) -> Option<(u64, Vec<Owned>, bool)> {
    let seq = whole(bytes)?;
    if seq.tag() != Tag::Sequence {
        return None;
    }
    let contents = seq.value();
    let parts = components(contents)?;
    let [commit, ops, check] = parts.as_slice() else {
        return None;
    };
    if ops.tag() != Tag::Sequence {
        return None;
    }
    let ops = components(ops.value())?
        .iter()
        .map(der_op)
        .collect::<Option<Vec<_>>>()?;
    let check = octets(check)?;
    // The check is the last six octets of the contents (04 04 and the CRC).
    let body = contents.get(..contents.len().checked_sub(6)?)?;
    let ok = check == ISCSI.checksum(body).to_le_bytes();
    Some((commit.decode_as().ok()?, ops, ok))
}

#[test]
fn records_against_der() {
    let mut rng = Rng(0x0dd_ba11_cafe_f00d);
    let commits = [1u64, 2, 127, 128, 255, 256, 65_535, 1 << 31, u64::MAX];
    let mut cases = 0usize;
    let mut fail = 0usize;
    for round in 0..(if cfg!(miri) { 6usize } else { 300 }) {
        let n = rng.below(8);
        let mut keys = Vec::new();
        let mut values = Vec::new();
        for _ in 0..n {
            let long = !cfg!(miri) && round % 50 == 0;
            let most = if cfg!(miri) { 8 } else { 200 };
            let kl = if long { 70_000 } else { rng.below(most) };
            let vl = if long { 1000 } else { rng.below(most) };
            keys.push(rng.bytes(kl));
            values.push(rng.bytes(vl));
        }
        let mut ops = Vec::new();
        for i in 0..n {
            let bottle = match rng.below(4) {
                0 => 0,
                1 => 127,
                2 => u32::MAX,
                _ => u32::try_from(rng.next() >> 32).unwrap_or(0),
            };
            let (Some(key), Some(value)) = (keys.get(i), values.get(i)) else {
                continue;
            };
            ops.push(match rng.below(3) {
                0 => OpRef::Put { bottle, key, value },
                1 => OpRef::Delete { bottle, key },
                _ => OpRef::Clear { bottle },
            });
        }
        let commit = match commits.get(rng.below(commits.len().saturating_add(1))) {
            Some(&c) => c,
            None => rng.next().max(1),
        };
        cases = cases.saturating_add(1);
        let want = (commit, ops.iter().map(owned).collect::<Vec<_>>(), true);
        let got = encode_record(commit, &ops).and_then(|r| der_record(&r));
        if got.as_ref() != Some(&want) {
            fail = fail.saturating_add(1);
        }
    }
    report(
        "Store records decoded by der 0.8.2",
        cases.saturating_sub(fail),
        fail,
        cases,
    );
    assert_eq!(fail, 0);
}
