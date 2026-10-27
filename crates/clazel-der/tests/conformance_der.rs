//! DER conformance (docs/phases/phase-3.md item 3.5a).
//!
//! The proofs show the decoder and encoder equal `spec.rs`, and
//! `independent.rs` shows the spec equal to Kaliski's Layman's Guide on its
//! subset. This file checks the spec against the outside world:
//!
//! 1. Hand-built cases, as Rust literals (no official DER test suite is
//!    vendored here: `x509-limbo` is item 3.5b's): valid encodings from X.690
//!    and the Guide that must decode and re-encode to the same bytes, and one
//!    case for every rejection rule (indefinite length, a long-form length
//!    that fits the short form, a leading zero in a length, INTEGER
//!    `00 7F`, BOOLEAN `01`, a BIT STRING with 8 unused bits, an OID with `80`
//!    padding, a constructed OCTET STRING, truncated contents, trailing
//!    bytes, and others) that must be rejected.
//! 2. A differential test against RustCrypto's `der` crate (0.8.2, default
//!    features off): random valid values encoded by `der` must decode to the
//!    same value with our readers, our encoders must write the same bytes,
//!    and `der` must decode what we wrote.
//! 3. The same on random and mutated bytes. Where we reject and `der`
//!    accepts, or the other way round, the difference must be one of the
//!    listed categories, each with its reason; any other difference fails
//!    the test. The counts of each category are printed.

use clazel_der::decode::{
    expect_end, read_bit_string, read_boolean, read_generalized_time, read_ia5_string,
    read_integer, read_null, read_octet_string, read_oid, read_printable_string, read_tlv,
    read_utc_time, read_utf8_string,
};
use clazel_der::encode::{
    encode_bit_string, encode_boolean, encode_digest_info, encode_integer_unsigned, encode_null,
    encode_octet_string, encode_octets, encode_oid, encode_tlv,
};
use clazel_der::spec::{
    BIT_STRING, BOOLEAN, Class, GENERALIZED_TIME, IA5_STRING, INTEGER, NULL, OBJECT_IDENTIFIER,
    OCTET_STRING, PRINTABLE_STRING, Tag, UTC_TIME, UTF8_STRING,
};

use der::asn1::{
    AnyRef, BitString, Ia5StringRef, Int, Null, ObjectIdentifier, OctetString, PrintableStringRef,
    UtcTime, Utf8StringRef,
};
use der::{Class as DerClass, Decode, Encode, Tag as DerTag, TagNumber, Tagged};

// ---------------------------------------------------------------------------
// Helpers without indexing or unchecked arithmetic.
// ---------------------------------------------------------------------------

fn at(b: &[u8], i: usize) -> u8 {
    b.get(i).copied().unwrap_or(0)
}

fn sub(b: &[u8], from: usize, to: usize) -> Vec<u8> {
    b.get(from..to).map(<[u8]>::to_vec).unwrap_or_default()
}

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
    fn byte(&mut self) -> u8 {
        u8::try_from(self.next() & 0xFF).unwrap_or(0)
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.byte()).collect()
    }
    fn coin(&mut self) -> bool {
        self.below(2) == 1
    }
}

// ---------------------------------------------------------------------------
// The values compared, and the two sides' readers and writers.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Bool,
    Int,
    Bits,
    Octets,
    Null,
    Oid,
    Utf8,
    Printable,
    Ia5,
    Utc,
    Any,
}

const KINDS: [Kind; 11] = [
    Kind::Bool,
    Kind::Int,
    Kind::Bits,
    Kind::Octets,
    Kind::Null,
    Kind::Oid,
    Kind::Utf8,
    Kind::Printable,
    Kind::Ia5,
    Kind::Utc,
    Kind::Any,
];

/// A decoded value in a form both sides can produce.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    Bool(bool),
    /// The contents octets of an INTEGER.
    Int(Vec<u8>),
    Bits(u8, Vec<u8>),
    Octets(Vec<u8>),
    Null,
    Oid(Vec<u64>),
    Str(Vec<u8>),
    /// class bits, constructed, number, contents
    Any(u8, bool, u32, Vec<u8>),
}

fn our_tag_bits(tag: Tag) -> u8 {
    match tag.class {
        Class::Universal => 0,
        Class::Application => 1,
        Class::ContextSpecific => 2,
        Class::Private => 3,
    }
}

/// The whole input must be one value: nothing may follow it.
fn whole(next: usize, b: &[u8]) -> bool {
    expect_end(next, b.len())
}

fn ours_decode(kind: Kind, b: &[u8]) -> Option<Val> {
    let len = b.len();
    match kind {
        Kind::Bool => {
            let (v, next) = read_boolean(b, 0, len)?;
            whole(next, b).then_some(Val::Bool(v))
        }
        Kind::Int => {
            let (_, _, _, next) = read_integer(b, 0, len)?;
            let t = read_tlv(b, 0, len)?;
            whole(next, b).then(|| Val::Int(sub(b, t.cstart, t.cend)))
        }
        Kind::Bits => {
            let (unused, s, e, next) = read_bit_string(b, 0, len)?;
            whole(next, b).then(|| Val::Bits(unused, sub(b, s, e)))
        }
        Kind::Octets => {
            let (s, e) = read_octet_string(b, 0, len)?;
            whole(e, b).then(|| Val::Octets(sub(b, s, e)))
        }
        Kind::Null => {
            let next = read_null(b, 0, len)?;
            whole(next, b).then_some(Val::Null)
        }
        Kind::Oid => {
            let (arcs, next) = read_oid(b, 0, len)?;
            whole(next, b).then_some(Val::Oid(arcs))
        }
        Kind::Utf8 | Kind::Printable | Kind::Ia5 | Kind::Utc => {
            let (s, e) = match kind {
                Kind::Utf8 => read_utf8_string(b, 0, len)?,
                Kind::Printable => read_printable_string(b, 0, len)?,
                Kind::Ia5 => read_ia5_string(b, 0, len)?,
                _ => read_utc_time(b, 0, len)?,
            };
            whole(e, b).then(|| Val::Str(sub(b, s, e)))
        }
        Kind::Any => {
            let t = read_tlv(b, 0, len)?;
            whole(t.cend, b).then(|| {
                Val::Any(
                    our_tag_bits(t.tag),
                    t.tag.constructed,
                    t.tag.number,
                    sub(b, t.cstart, t.cend),
                )
            })
        }
    }
}

fn ours_encode(val: &Val, kind: Kind) -> Vec<u8> {
    match (val, kind) {
        (Val::Bool(v), _) => encode_boolean(*v),
        (Val::Int(c), _) => {
            if at(c, 0) < 128 {
                encode_integer_unsigned(c)
            } else {
                encode_tlv(
                    Tag {
                        class: Class::Universal,
                        constructed: false,
                        number: INTEGER,
                    },
                    c,
                )
            }
        }
        (Val::Bits(u, b), _) => encode_bit_string(*u, b),
        (Val::Octets(s), _) => encode_octet_string(s),
        (Val::Null, _) => encode_null(),
        (Val::Oid(arcs), _) => encode_oid(arcs),
        (Val::Str(s), Kind::Utf8) => encode_octets(UTF8_STRING, s),
        (Val::Str(s), Kind::Printable) => encode_octets(PRINTABLE_STRING, s),
        (Val::Str(s), Kind::Ia5) => encode_octets(IA5_STRING, s),
        (Val::Str(s), _) => encode_octets(UTC_TIME, s),
        (Val::Any(class, constructed, number, c), _) => {
            let class = match class {
                1 => Class::Application,
                2 => Class::ContextSpecific,
                3 => Class::Private,
                _ => Class::Universal,
            };
            encode_tlv(
                Tag {
                    class,
                    constructed: *constructed,
                    number: *number,
                },
                c,
            )
        }
    }
}

fn theirs_decode(kind: Kind, b: &[u8]) -> Option<Val> {
    match kind {
        Kind::Bool => bool::from_der(b).ok().map(Val::Bool),
        Kind::Int => Int::from_der(b)
            .ok()
            .map(|i| Val::Int(i.as_bytes().to_vec())),
        Kind::Bits => {
            let bs = BitString::from_der(b).ok()?;
            Some(Val::Bits(bs.unused_bits(), bs.raw_bytes().to_vec()))
        }
        Kind::Octets => OctetString::from_der(b)
            .ok()
            .map(|o| Val::Octets(o.as_bytes().to_vec())),
        Kind::Null => Null::from_der(b).ok().map(|_| Val::Null),
        Kind::Oid => {
            let oid = ObjectIdentifier::<39>::from_der(b).ok()?;
            Some(Val::Oid(oid.arcs().map(u64::from).collect()))
        }
        Kind::Utf8 => Utf8StringRef::from_der(b)
            .ok()
            .map(|s| Val::Str(s.as_str().as_bytes().to_vec())),
        Kind::Printable => PrintableStringRef::from_der(b)
            .ok()
            .map(|s| Val::Str(s.as_str().as_bytes().to_vec())),
        Kind::Ia5 => Ia5StringRef::from_der(b)
            .ok()
            .map(|s| Val::Str(s.as_str().as_bytes().to_vec())),
        Kind::Utc => {
            // `der` parses a UTCTime into a date and writes it back canonically.
            let t = UtcTime::from_der(b).ok()?;
            let again = t.to_der().ok()?;
            Some(Val::Str(
                again.get(2..).map(<[u8]>::to_vec).unwrap_or_default(),
            ))
        }
        Kind::Any => {
            let any = AnyRef::from_der(b).ok()?;
            let tag = any.tag();
            let class = match tag.class() {
                DerClass::Universal => 0,
                DerClass::Application => 1,
                DerClass::ContextSpecific => 2,
                DerClass::Private => 3,
            };
            Some(Val::Any(
                class,
                tag.is_constructed(),
                tag.number().value(),
                any.value().to_vec(),
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// Random valid values, written by `der`.
// ---------------------------------------------------------------------------

const PRINTABLE: &[u8] =
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 '()+,-./:=?";

fn edge_len(r: &mut Rng) -> usize {
    let edges = [0usize, 1, 2, 126, 127, 128, 129, 255, 256, 257, 1000];
    if r.below(3) == 0 {
        edges.get(r.below(edges.len())).copied().unwrap_or(0)
    } else {
        r.below(300)
    }
}

fn random_arc(r: &mut Rng) -> u32 {
    let edges = [
        0u32,
        1,
        39,
        40,
        127,
        128,
        16383,
        16384,
        2_097_151,
        2_097_152,
        u32::MAX,
    ];
    if r.coin() {
        edges.get(r.below(edges.len())).copied().unwrap_or(0)
    } else {
        u32::try_from(r.next() & 0xFFFF_FFFF).unwrap_or(0) >> r.below(32)
    }
}

/// A random value of `kind` and its encoding by `der`. `None` where `der`
/// declines to build one (then the case is skipped).
fn generate(kind: Kind, r: &mut Rng) -> Option<(Vec<u8>, Val)> {
    match kind {
        Kind::Bool => {
            let v = r.coin();
            Some((v.to_der().ok()?, Val::Bool(v)))
        }
        Kind::Int => {
            let n = r.below(20).saturating_add(1);
            let mut bytes = r.bytes(n);
            if r.below(3) == 0 {
                // Redundant leading octets, which `der` canonicalises away.
                let pad = if r.coin() { 0x00 } else { 0xFF };
                let n = r.below(3);
                bytes.splice(0..0, std::iter::repeat_n(pad, n));
            }
            // `Int::new` keeps redundant octets, which DER forbids: strip them.
            while bytes.len() >= 2
                && ((at(&bytes, 0) == 0x00 && at(&bytes, 1) < 0x80)
                    || (at(&bytes, 0) == 0xFF && at(&bytes, 1) >= 0x80))
            {
                bytes.remove(0);
            }
            let i = Int::new(&bytes).ok()?;
            Some((i.to_der().ok()?, Val::Int(i.as_bytes().to_vec())))
        }
        Kind::Bits => {
            let n = r.below(40);
            let mut bytes = r.bytes(n);
            let unused = if n == 0 {
                0
            } else {
                u8::try_from(r.below(8)).unwrap_or(0)
            };
            if let Some(last) = bytes.last_mut() {
                *last &= 0xFFu8 << unused;
            }
            let bs = BitString::new(unused, bytes.clone()).ok()?;
            Some((bs.to_der().ok()?, Val::Bits(unused, bytes)))
        }
        Kind::Octets => {
            let n = edge_len(r);
            let bytes = r.bytes(n);
            let o = OctetString::new(bytes.clone()).ok()?;
            Some((o.to_der().ok()?, Val::Octets(bytes)))
        }
        Kind::Null => Some((Null.to_der().ok()?, Val::Null)),
        Kind::Oid => {
            let first = u32::try_from(r.below(3)).unwrap_or(0);
            let second = if first < 2 {
                u32::try_from(r.below(40)).unwrap_or(0)
            } else {
                random_arc(r) >> 2
            };
            let mut arcs = vec![first, second];
            for _ in 0..r.below(9) {
                arcs.push(random_arc(r));
            }
            let oid = ObjectIdentifier::<39>::from_arcs(arcs.iter().copied()).ok()?;
            Some((
                oid.to_der().ok()?,
                Val::Oid(arcs.iter().map(|a| u64::from(*a)).collect()),
            ))
        }
        Kind::Utf8 => {
            let pool = [
                'a',
                'Z',
                '0',
                ' ',
                '\u{e9}',
                '\u{20ac}',
                '\u{1f600}',
                '\u{7ff}',
                '\u{800}',
            ];
            let s: String = (0..edge_len(r).min(120))
                .map(|_| pool.get(r.below(pool.len())).copied().unwrap_or('a'))
                .collect();
            let u = Utf8StringRef::new(&s).ok()?;
            Some((u.to_der().ok()?, Val::Str(s.into_bytes())))
        }
        Kind::Printable => {
            let s: Vec<u8> = (0..edge_len(r).min(120))
                .map(|_| {
                    PRINTABLE
                        .get(r.below(PRINTABLE.len()))
                        .copied()
                        .unwrap_or(b'a')
                })
                .collect();
            let p = PrintableStringRef::new(&s).ok()?;
            Some((p.to_der().ok()?, Val::Str(s)))
        }
        Kind::Ia5 => {
            let s: Vec<u8> = (0..edge_len(r).min(120)).map(|_| r.byte() & 0x7F).collect();
            let p = Ia5StringRef::new(&s).ok()?;
            Some((p.to_der().ok()?, Val::Str(s)))
        }
        Kind::Utc => {
            let two = |v: usize| format!("{v:02}");
            let s = format!(
                "{}{}{}{}{}{}Z",
                two(r.below(100)),
                two(r.below(12).saturating_add(1)),
                two(r.below(28).saturating_add(1)),
                two(r.below(24)),
                two(r.below(60)),
                two(r.below(60))
            );
            let mut enc = vec![0x17, 0x0D];
            enc.extend_from_slice(s.as_bytes());
            let t = UtcTime::from_der(&enc).ok()?;
            Some((t.to_der().ok()?, Val::Str(s.into_bytes())))
        }
        Kind::Any => {
            let number = {
                let edges = [0u32, 1, 30, 31, 32, 127, 128, 255, 16383];
                if r.coin() {
                    edges.get(r.below(edges.len())).copied().unwrap_or(0)
                } else {
                    u32::try_from(r.below(16384)).unwrap_or(0)
                }
            };
            let constructed = r.coin();
            let (tag, class) = match r.below(3) {
                0 => (TagNumber(number).application(constructed), 1u8),
                1 => (TagNumber(number).context_specific(constructed), 2),
                _ => (TagNumber(number).private(constructed), 3),
            };
            let n = edge_len(r);
            let contents = r.bytes(n);
            let any = AnyRef::new(tag, &contents).ok()?;
            Some((
                any.to_der().ok()?,
                Val::Any(class, constructed, number, contents),
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// Mutations.
// ---------------------------------------------------------------------------

fn mutate(b: &[u8], r: &mut Rng) -> Vec<u8> {
    let mut v = b.to_vec();
    match r.below(9) {
        0 => {
            let i = r.below(v.len().max(1));
            if let Some(x) = v.get_mut(i) {
                *x = r.byte();
            }
        }
        1 => {
            let i = r.below(v.len().max(1));
            let bit = 1u8 << r.below(8);
            if let Some(x) = v.get_mut(i) {
                *x ^= bit;
            }
        }
        2 => v.truncate(r.below(v.len().saturating_add(1))),
        3 => {
            let n = r.below(4).saturating_add(1);
            let extra = r.bytes(n);
            v.extend(extra);
        }
        4 => {
            let i = r.below(v.len().saturating_add(1));
            v.insert(i, r.byte());
        }
        5 => {
            if !v.is_empty() {
                let i = r.below(v.len());
                v.remove(i);
            }
        }
        6 => {
            // A tricky length octet in place of the second octet.
            let tricky = [0x80u8, 0xFF, 0x81, 0x82, 0x84, 0x7F, 0x00];
            let t = tricky.get(r.below(tricky.len())).copied().unwrap_or(0);
            if let Some(x) = v.get_mut(1) {
                *x = t;
            }
        }
        7 => {
            // A tricky first octet.
            let tricky = [0x1Fu8, 0x00, 0x3F, 0x5F, 0xFF, 0x20, 0x24, 0xA0];
            let t = tricky.get(r.below(tricky.len())).copied().unwrap_or(0);
            if let Some(x) = v.get_mut(0) {
                *x = t;
            }
        }
        _ => {
            let i = r.below(v.len().max(1));
            let j = r.below(v.len().max(1));
            let (a, c) = (at(&v, i), at(&v, j));
            if let Some(x) = v.get_mut(i) {
                *x = c;
            }
            if let Some(x) = v.get_mut(j) {
                *x = a;
            }
        }
    }
    v
}

/// Why we accept a value that `der` rejects, if the difference is explained.
fn we_accept_they_reject(kind: Kind, val: &Val, encoded: &[u8]) -> Option<&'static str> {
    match (kind, val) {
        (Kind::Utf8, Val::Str(s)) if std::str::from_utf8(s).is_err() => {
            Some("UTF8String contents are not checked here (X.509's, item 3.5b)")
        }
        (Kind::Printable, Val::Str(s)) if s.iter().any(|c| !PRINTABLE.contains(c)) => {
            Some("PrintableString characters are not checked here (X.509's, item 3.5b)")
        }
        (Kind::Ia5, Val::Str(s)) if s.iter().any(|c| *c >= 0x80) => {
            Some("IA5String characters are not checked here (X.509's, item 3.5b)")
        }
        (Kind::Utc, Val::Str(_)) => {
            Some("UTCTime date format is not checked here (RFC 5280 §4.1.2.5, item 3.5b)")
        }
        (Kind::Oid, Val::Oid(arcs)) if arcs.iter().any(|a| *a > u64::from(u32::MAX)) => {
            Some("an arc above 2^32 (ours are u64, `const-oid`'s are u32)")
        }
        (Kind::Oid, Val::Oid(_)) if encoded.len() > 41 => {
            Some("an OID of more than 39 contents octets (`const-oid`'s buffer)")
        }
        (Kind::Oid, Val::Oid(arcs)) if arcs.get(1).is_some_and(|a| *a > 39) => {
            Some("a second arc above 39 (`const-oid` refuses it, X.660 allows it under the root 2)")
        }
        (Kind::Any, Val::Any(0, _, _, _)) => Some("a universal tag `der` has no variant for"),
        _ => None,
    }
}

/// Whether any subidentifier of an OID's contents begins with the padding
/// octet 0x80 (X.690 8.19.2).
fn oid_padded(encoded: &[u8]) -> bool {
    let header = if at(encoded, 1) < 0x80 {
        2
    } else {
        2usize.saturating_add(usize::from(at(encoded, 1) & 0x7F))
    };
    let mut start = true;
    for c in encoded.iter().skip(header) {
        if start && *c == 0x80 {
            return true;
        }
        start = *c < 0x80;
    }
    false
}

/// Why we reject something `der` accepts, if the difference is explained.
fn we_reject_they_accept(kind: Kind, val: &Val, encoded: &[u8]) -> Option<&'static str> {
    match (kind, val) {
        (Kind::Any, Val::Any(_, _, number, _)) if *number > 16383 => {
            Some("a tag number of 2^14 or more (our stated limit)")
        }
        (Kind::Bits, Val::Bits(unused, bytes))
            if *unused > 0
                && bytes
                    .last()
                    .is_some_and(|b| *b & ((1u8 << *unused).wrapping_sub(1)) != 0) =>
        {
            Some("BIT STRING padding bits that are not zero (X.690 11.2.1; `der` does not check)")
        }
        (Kind::Oid, Val::Oid(_)) if oid_padded(encoded) => {
            Some("an OID subidentifier padded with 80 (X.690 8.19.2; `der` does not check)")
        }
        _ => None,
    }
}

/// Why both accept but read different values, if explained.
fn both_accept_differ(kind: Kind, ours: &Val) -> Option<&'static str> {
    match (kind, ours) {
        (Kind::Oid, Val::Oid(arcs)) if arcs.iter().any(|a| *a > u64::from(u32::MAX)) => {
            Some("an arc above 2^32: `const-oid` truncates it silently, we read it as a u64")
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Suite 1: hand-built cases.
// ---------------------------------------------------------------------------

/// 04 81 C9 followed by 201 zero octets.
static LONG_201: std::sync::LazyLock<Vec<u8>> = std::sync::LazyLock::new(|| {
    let mut v = vec![0x04, 0x81, 0xC9];
    v.extend(std::iter::repeat_n(0u8, 201));
    v
});

struct Hand<'a> {
    name: &'static str,
    kind: Kind,
    bytes: &'a [u8],
    /// The value it must decode to, or `None` if it must be rejected.
    expected: Option<Val>,
}

fn hand_cases() -> Vec<Hand<'static>> {
    let v = |name, kind, bytes, expected| Hand {
        name,
        kind,
        bytes,
        expected,
    };
    vec![
        // --- valid: X.690 and Kaliski's examples.
        v(
            "X.690 8.2.2 BOOLEAN TRUE 01 01 FF",
            Kind::Bool,
            &[0x01, 0x01, 0xFF],
            Some(Val::Bool(true)),
        ),
        v(
            "BOOLEAN FALSE 01 01 00",
            Kind::Bool,
            &[0x01, 0x01, 0x00],
            Some(Val::Bool(false)),
        ),
        v(
            "X.690 8.8 NULL 05 00",
            Kind::Null,
            &[0x05, 0x00],
            Some(Val::Null),
        ),
        v(
            "Guide 5.7 INTEGER 0",
            Kind::Int,
            &[0x02, 0x01, 0x00],
            Some(Val::Int(vec![0x00])),
        ),
        v(
            "Guide 5.7 INTEGER 127",
            Kind::Int,
            &[0x02, 0x01, 0x7F],
            Some(Val::Int(vec![0x7F])),
        ),
        v(
            "Guide 5.7 INTEGER 128",
            Kind::Int,
            &[0x02, 0x02, 0x00, 0x80],
            Some(Val::Int(vec![0x00, 0x80])),
        ),
        v(
            "Guide 5.7 INTEGER 256",
            Kind::Int,
            &[0x02, 0x02, 0x01, 0x00],
            Some(Val::Int(vec![0x01, 0x00])),
        ),
        v(
            "Guide 5.7 INTEGER -128",
            Kind::Int,
            &[0x02, 0x01, 0x80],
            Some(Val::Int(vec![0x80])),
        ),
        v(
            "Guide 5.7 INTEGER -129",
            Kind::Int,
            &[0x02, 0x02, 0xFF, 0x7F],
            Some(Val::Int(vec![0xFF, 0x7F])),
        ),
        v(
            "X.690 8.6.4.2 BIT STRING '0A3B5F291CD'H",
            Kind::Bits,
            &[0x03, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0],
            Some(Val::Bits(4, vec![0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0])),
        ),
        v(
            "Guide 5.4 BIT STRING 011011100101110111",
            Kind::Bits,
            &[0x03, 0x04, 0x06, 0x6E, 0x5D, 0xC0],
            Some(Val::Bits(6, vec![0x6E, 0x5D, 0xC0])),
        ),
        v(
            "empty BIT STRING 03 01 00",
            Kind::Bits,
            &[0x03, 0x01, 0x00],
            Some(Val::Bits(0, vec![])),
        ),
        v(
            "Guide 5.10 OCTET STRING",
            Kind::Octets,
            &[0x04, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF],
            Some(Val::Octets(vec![
                0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
            ])),
        ),
        v(
            "X.690 8.19.5 OID {2 999 3}",
            Kind::Oid,
            &[0x06, 0x03, 0x88, 0x37, 0x03],
            Some(Val::Oid(vec![2, 999, 3])),
        ),
        v(
            "Guide 5.9 OID {1 2 840 113549}",
            Kind::Oid,
            &[0x06, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D],
            Some(Val::Oid(vec![1, 2, 840, 113_549])),
        ),
        v(
            "X.690 8.1.3.5 length 201 in the long form",
            Kind::Octets,
            LONG_201.as_slice(),
            Some(Val::Octets(vec![0; 201])),
        ),
        v(
            "Guide 5.6 IA5String",
            Kind::Ia5,
            &[0x16, 0x03, 0x61, 0x62, 0x63],
            Some(Val::Str(b"abc".to_vec())),
        ),
        v(
            "PrintableString",
            Kind::Printable,
            &[0x13, 0x02, 0x55, 0x53],
            Some(Val::Str(b"US".to_vec())),
        ),
        v(
            "UTF8String",
            Kind::Utf8,
            &[0x0C, 0x03, 0xE2, 0x82, 0xAC],
            Some(Val::Str("\u{20ac}".as_bytes().to_vec())),
        ),
        v(
            "Guide 5.17 UTCTime 910506234540Z",
            Kind::Utc,
            &[
                0x17, 0x0D, 0x39, 0x31, 0x30, 0x35, 0x30, 0x36, 0x32, 0x33, 0x34, 0x35, 0x34, 0x30,
                0x5A,
            ],
            Some(Val::Str(b"910506234540Z".to_vec())),
        ),
        v(
            "context [2] constructed A2 00",
            Kind::Any,
            &[0xA2, 0x00],
            Some(Val::Any(2, true, 2, vec![])),
        ),
        v(
            "high tag number 31 (1F 1F 00)",
            Kind::Any,
            &[0x5F, 0x1F, 0x00],
            Some(Val::Any(1, false, 31, vec![])),
        ),
        v(
            "high tag number 16383 (BF FF 7F 00)",
            Kind::Any,
            &[0xBF, 0xFF, 0x7F, 0x00],
            Some(Val::Any(2, true, 16383, vec![])),
        ),
        // --- rejected: every rule.
        v(
            "X.690 8.1.3.6 indefinite length (30 80 .. 00 00)",
            Kind::Any,
            &[0x30, 0x80, 0x02, 0x01, 0x00, 0x00, 0x00],
            None,
        ),
        v(
            "indefinite length of an OCTET STRING",
            Kind::Octets,
            &[0x24, 0x80, 0x04, 0x01, 0x00, 0x00, 0x00],
            None,
        ),
        v(
            "X.690 8.1.3.5 c) reserved length octet FF",
            Kind::Octets,
            &[0x04, 0xFF, 0x00],
            None,
        ),
        v(
            "10.1 length 38 in the long form (81 26)",
            Kind::Octets,
            &[0x04, 0x81, 0x26],
            None,
        ),
        v(
            "10.1 long form that fits the short form, 0 (81 00)",
            Kind::Null,
            &[0x05, 0x81, 0x00],
            None,
        ),
        v(
            "10.1 length with a leading zero octet (82 00 C9)",
            Kind::Octets,
            &[0x04, 0x82, 0x00, 0xC9],
            None,
        ),
        v(
            "10.1 length 201 in three octets (82 00 C9)",
            Kind::Any,
            &[0x04, 0x82, 0x00, 0xC9],
            None,
        ),
        v(
            "8.3.2 INTEGER 00 7F",
            Kind::Int,
            &[0x02, 0x02, 0x00, 0x7F],
            None,
        ),
        v(
            "8.3.2 INTEGER 00 00",
            Kind::Int,
            &[0x02, 0x02, 0x00, 0x00],
            None,
        ),
        v(
            "8.3.2 INTEGER FF 80",
            Kind::Int,
            &[0x02, 0x02, 0xFF, 0x80],
            None,
        ),
        v(
            "8.3.2 INTEGER FF FF",
            Kind::Int,
            &[0x02, 0x02, 0xFF, 0xFF],
            None,
        ),
        v(
            "8.3.1 INTEGER with no contents",
            Kind::Int,
            &[0x02, 0x00],
            None,
        ),
        v(
            "11.1 BOOLEAN TRUE as 01",
            Kind::Bool,
            &[0x01, 0x01, 0x01],
            None,
        ),
        v(
            "11.1 BOOLEAN TRUE as 7F",
            Kind::Bool,
            &[0x01, 0x01, 0x7F],
            None,
        ),
        v(
            "8.2.1 BOOLEAN with two octets",
            Kind::Bool,
            &[0x01, 0x02, 0xFF, 0xFF],
            None,
        ),
        v(
            "8.2.1 BOOLEAN with no contents",
            Kind::Bool,
            &[0x01, 0x00],
            None,
        ),
        v(
            "8.6.2.2 BIT STRING with 8 unused bits",
            Kind::Bits,
            &[0x03, 0x02, 0x08, 0x00],
            None,
        ),
        v(
            "8.6.2.3 empty BIT STRING with 1 unused bit",
            Kind::Bits,
            &[0x03, 0x01, 0x01],
            None,
        ),
        v(
            "8.6.2.1 BIT STRING with no contents",
            Kind::Bits,
            &[0x03, 0x00],
            None,
        ),
        v(
            "11.2.1 BIT STRING padding bits not zero",
            Kind::Bits,
            &[0x03, 0x04, 0x06, 0x6E, 0x5D, 0xE0],
            None,
        ),
        v(
            "10.2 constructed BIT STRING",
            Kind::Bits,
            &[
                0x23, 0x09, 0x03, 0x03, 0x00, 0x6E, 0x5D, 0x03, 0x02, 0x06, 0xC0,
            ],
            None,
        ),
        v(
            "8.8.2 NULL with contents",
            Kind::Null,
            &[0x05, 0x01, 0x00],
            None,
        ),
        v(
            "8.19.2 OID subidentifier padded with 80",
            Kind::Oid,
            &[0x06, 0x04, 0x2A, 0x80, 0x81, 0x01],
            None,
        ),
        v(
            "8.19.2 OID whose last octet has bit 8 set",
            Kind::Oid,
            &[0x06, 0x02, 0x2A, 0x86],
            None,
        ),
        v(
            "8.19.3 OID with no subidentifier",
            Kind::Oid,
            &[0x06, 0x00],
            None,
        ),
        v(
            "8.19.1 constructed OBJECT IDENTIFIER",
            Kind::Oid,
            &[0x26, 0x01, 0x2A],
            None,
        ),
        v(
            "10.2 constructed OCTET STRING",
            Kind::Octets,
            &[0x24, 0x06, 0x04, 0x01, 0x01, 0x04, 0x01, 0x02],
            None,
        ),
        v(
            "10.2 constructed UTF8String",
            Kind::Utf8,
            &[0x2C, 0x03, 0x0C, 0x01, 0x61],
            None,
        ),
        v(
            "8.1.1.1 truncated contents",
            Kind::Octets,
            &[0x04, 0x05, 0x01, 0x02],
            None,
        ),
        v(
            "8.1.1.1 truncated length octets",
            Kind::Octets,
            &[0x04, 0x82, 0x01],
            None,
        ),
        v("8.1.1.1 identifier only", Kind::Any, &[0x04], None),
        v("8.1.1.1 empty input", Kind::Any, &[], None),
        v(
            "trailing bytes after a value",
            Kind::Null,
            &[0x05, 0x00, 0x00],
            None,
        ),
        v(
            "trailing bytes after an OCTET STRING",
            Kind::Octets,
            &[0x04, 0x01, 0x00, 0xFF],
            None,
        ),
        v(
            "8.1.2.2 high form for tag 30 (5F 1E)",
            Kind::Any,
            &[0x5F, 0x1E, 0x00],
            None,
        ),
        v(
            "8.1.2.4.2 c) high tag number with a leading 80 digit",
            Kind::Any,
            &[0x5F, 0x80, 0x1F, 0x00],
            None,
        ),
        v(
            "8.1.2.4.2 a) high tag number never ends",
            Kind::Any,
            &[0x5F, 0x81],
            None,
        ),
        v(
            "tag number 16384, past this crate's limit (stated)",
            Kind::Any,
            &[0x5F, 0x81, 0x80, 0x00, 0x00],
            None,
        ),
        v(
            "wrong tag: INTEGER read as OCTET STRING",
            Kind::Octets,
            &[0x02, 0x01, 0x00],
            None,
        ),
        v(
            "wrong class: [0] primitive read as OCTET STRING",
            Kind::Octets,
            &[0x84, 0x00],
            None,
        ),
    ]
}

#[test]
fn hand_built_cases() {
    let cases = hand_cases();
    let mut failures = Vec::new();
    let mut failed = 0usize;
    let mut valid = 0usize;
    let mut theirs_differs = Vec::new();
    for c in &cases {
        let before = failures.len();
        let got = ours_decode(c.kind, c.bytes);
        match (&c.expected, &got) {
            (None, None) => {}
            (Some(e), Some(g)) if e == g => {
                valid = valid.saturating_add(1);
                // It must re-encode to the same bytes (DER canonicity).
                if ours_encode(g, c.kind) != c.bytes {
                    failures.push(format!("{}: does not re-encode to the same bytes", c.name));
                }
            }
            (None, Some(g)) => {
                failures.push(format!("{}: must be rejected but decoded to {g:?}", c.name))
            }
            (Some(e), got) => failures.push(format!("{}: expected {e:?}, got {got:?}", c.name)),
        }
        // Note what `der` does with the same bytes.
        if theirs_decode(c.kind, c.bytes) != c.expected {
            theirs_differs.push(c.name);
        }
        if failures.len() != before {
            failed = failed.saturating_add(1);
        }
    }
    println!(
        "clazel-conformance: suite=\"DER hand-built cases (X.690, Kaliski, one per rule)\" pass={} xfail=0 fail={failed} total={}",
        cases.len().saturating_sub(failed),
        cases.len()
    );
    println!(
        "{valid} valid cases; `der` 0.8.2 differs on {} of {}: {theirs_differs:?}",
        theirs_differs.len(),
        cases.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // `der` is itself a DER decoder: the only cases it treats differently
    // are `der`'s own limits and unchecked rules, which are, in order: an
    // OID whose second arc is above 39 under the root 2 (`const-oid`), BIT
    // STRING padding bits that are not zero (11.2.1), an OID subidentifier
    // padded with 80 (8.19.2), and a tag number above our stated limit.
    assert_eq!(
        theirs_differs,
        [
            "X.690 8.19.5 OID {2 999 3}",
            "11.2.1 BIT STRING padding bits not zero",
            "8.19.2 OID subidentifier padded with 80",
            "tag number 16384, past this crate's limit (stated)"
        ]
    );
}

/// RFC 8017 §9.2 Note 1, the `DigestInfo` prefixes, through the encoder, for
/// the three digests item 3.5c needs.
#[test]
fn digest_info_prefixes() {
    let oids: [(&[u64], usize, &[u8]); 3] = [
        (
            &[2, 16, 840, 1, 101, 3, 4, 2, 1],
            32,
            &[
                0x30, 0x31, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
                0x01, 0x05, 0x00, 0x04, 0x20,
            ],
        ),
        (
            &[2, 16, 840, 1, 101, 3, 4, 2, 2],
            48,
            &[
                0x30, 0x41, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
                0x02, 0x05, 0x00, 0x04, 0x30,
            ],
        ),
        (
            &[2, 16, 840, 1, 101, 3, 4, 2, 3],
            64,
            &[
                0x30, 0x51, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
                0x03, 0x05, 0x00, 0x04, 0x40,
            ],
        ),
    ];
    let mut failed = 0usize;
    for (arcs, n, prefix) in oids {
        let digest: Vec<u8> = (0..n)
            .map(|i| u8::try_from(i & 0xFF).unwrap_or(0))
            .collect();
        let mut expected = prefix.to_vec();
        expected.extend_from_slice(&digest);
        if encode_digest_info(arcs, &digest) != expected {
            failed = failed.saturating_add(1);
        }
    }
    println!(
        "clazel-conformance: suite=\"RFC 8017 9.2 DigestInfo prefixes (SHA-256, SHA-384, SHA-512)\" pass={} xfail=0 fail={failed} total=3",
        3usize.saturating_sub(failed)
    );
    assert_eq!(failed, 0);
}

/// Rounds of the two random suites; Miri (an interpreter, about a thousand
/// times slower) runs a hundredth of them.
const VALID_ROUNDS: usize = if cfg!(miri) { 60 } else { 6000 };
const MUTATED_ROUNDS: usize = if cfg!(miri) { 600 } else { 60_000 };

// ---------------------------------------------------------------------------
// Suites 2 and 3: the differential against `der`.
// ---------------------------------------------------------------------------

#[test]
fn differential_valid_values() {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let mut failures = Vec::new();
    let mut cases = 0usize;
    let mut failed = 0usize;
    let mut per_kind = [0usize; 11];
    for round in 0..VALID_ROUNDS {
        let kind = KINDS
            .get(round % KINDS.len())
            .copied()
            .unwrap_or(Kind::Null);
        let Some((their_bytes, val)) = generate(kind, &mut r) else {
            continue;
        };
        cases = cases.saturating_add(1);
        if let Some(n) = per_kind.get_mut(round % KINDS.len()) {
            *n = n.saturating_add(1);
        }
        let before = failures.len();
        // 1. `der` writes, we read.
        let ours = ours_decode(kind, &their_bytes);
        if ours.as_ref() != Some(&val) {
            failures.push(format!(
                "{kind:?}: we read {ours:?} from {their_bytes:02x?}, expected {val:?}"
            ));
        }
        // 2. We write: the same bytes (DER has one encoding).
        let mine = ours_encode(&val, kind);
        if mine != their_bytes {
            failures.push(format!(
                "{kind:?}: we write {mine:02x?}, `der` writes {their_bytes:02x?} for {val:?}"
            ));
        }
        // 3. `der` reads what we wrote.
        let back = theirs_decode(kind, &mine);
        if back.as_ref() != Some(&val) {
            failures.push(format!(
                "{kind:?}: `der` reads {back:?} from {mine:02x?}, expected {val:?}"
            ));
        }
        if failures.len() != before {
            failed = failed.saturating_add(1);
        }
    }
    println!(
        "clazel-conformance: suite=\"der 0.8.2 differential, random valid values (der writes, we read; we write, der reads)\" pass={} xfail=0 fail={failed} total={cases}",
        cases.saturating_sub(failed)
    );
    println!("valid values per kind: {per_kind:?}");
    assert!(
        cases > VALID_ROUNDS / 6 * 5,
        "only {cases} values were generated"
    );
    assert!(
        failures.is_empty(),
        "{}",
        failures
            .iter()
            .take(10)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn differential_mutated_bytes() {
    let mut r = Rng(0xD1B5_4A32_D192_ED03);
    let mut failures = Vec::new();
    let mut total = 0usize;
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut fail = 0usize;
    let mut both_accept = 0usize;
    let mut both_reject = 0usize;
    let mut notes: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for round in 0..MUTATED_ROUNDS {
        let kind = KINDS
            .get(round % KINDS.len())
            .copied()
            .unwrap_or(Kind::Null);
        let Some((bytes, _)) = generate(kind, &mut r) else {
            continue;
        };
        // Short values keep the run fast; the long ones are in the valid test.
        if bytes.len() > 400 {
            continue;
        }
        let mut m = mutate(&bytes, &mut r);
        if r.below(4) == 0 {
            m = mutate(&m, &mut r);
        }
        total = total.saturating_add(1);
        let ours = ours_decode(kind, &m);
        let theirs = theirs_decode(kind, &m);
        match (&ours, &theirs) {
            (None, None) => {
                both_reject = both_reject.saturating_add(1);
                pass = pass.saturating_add(1);
            }
            (Some(a), Some(b)) => {
                both_accept = both_accept.saturating_add(1);
                if a == b {
                    pass = pass.saturating_add(1);
                } else if let Some(why) = both_accept_differ(kind, a) {
                    xfail = xfail.saturating_add(1);
                    *notes
                        .entry(format!("both accept, values differ: {why}"))
                        .or_insert(0) += 1;
                } else {
                    fail = fail.saturating_add(1);
                    failures.push(format!(
                        "{kind:?}: both accept {m:02x?} but read {a:?} and {b:?}"
                    ));
                }
            }
            (Some(a), None) => match we_accept_they_reject(kind, a, &m) {
                Some(why) => {
                    xfail = xfail.saturating_add(1);
                    *notes
                        .entry(format!("we accept, `der` rejects: {why}"))
                        .or_insert(0) += 1;
                }
                None => {
                    fail = fail.saturating_add(1);
                    failures.push(format!(
                        "{kind:?}: we accept {m:02x?} as {a:?}, `der` rejects it"
                    ));
                }
            },
            (None, Some(b)) => match we_reject_they_accept(kind, b, &m) {
                Some(why) => {
                    xfail = xfail.saturating_add(1);
                    *notes
                        .entry(format!("we reject, `der` accepts: {why}"))
                        .or_insert(0) += 1;
                }
                None => {
                    fail = fail.saturating_add(1);
                    failures.push(format!(
                        "{kind:?}: we reject {m:02x?}, `der` accepts it as {b:?}"
                    ));
                }
            },
        }
    }
    println!(
        "clazel-conformance: suite=\"der 0.8.2 differential, mutated bytes\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
    println!(
        "both accept {both_accept} (same value), both reject {both_reject}; explained differences:"
    );
    for (why, n) in &notes {
        println!("  {n:6}  {why}");
    }
    assert!(
        both_accept > MUTATED_ROUNDS / 60 && both_reject > MUTATED_ROUNDS / 60,
        "the mutations did not exercise both outcomes"
    );
    assert!(
        failures.is_empty(),
        "{}",
        failures
            .iter()
            .take(15)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Silence the unused-constant warning for the types the table above leaves
/// to `x509`: they are read by the decoder and covered by the proofs.
#[test]
fn tag_numbers_are_the_universal_ones() {
    assert_eq!(
        [
            BOOLEAN,
            INTEGER,
            BIT_STRING,
            OCTET_STRING,
            NULL,
            OBJECT_IDENTIFIER,
            UTF8_STRING,
            PRINTABLE_STRING,
            IA5_STRING,
            UTC_TIME,
            GENERALIZED_TIME
        ],
        [1, 2, 3, 4, 5, 6, 12, 19, 22, 23, 24]
    );
    // GeneralizedTime is read as octets like the other strings.
    let t = b"20240101000000Z";
    let enc = encode_octets(GENERALIZED_TIME, t);
    let got = read_generalized_time(&enc, 0, enc.len());
    assert_eq!(got, Some((2, enc.len())));
    assert_eq!(DerTag::GeneralizedTime.number().value(), GENERALIZED_TIME);
}

/// The example in the crate's README.
#[test]
fn readme_example() {
    use clazel_der::decode::expect_sequence;
    use clazel_der::encode::encode_sequence;
    let mut body = encode_oid(&[1, 2, 840, 113_549]);
    body.extend_from_slice(&[0x02, 0x01, 0x05]);
    let bytes = encode_sequence(&body);
    let parsed = (|| {
        let (start, end) = expect_sequence(&bytes, 0, bytes.len())?;
        let (arcs, next) = read_oid(&bytes, start, end)?;
        let (negative, ms, me, next) = read_integer(&bytes, next, end)?;
        Some((
            arcs,
            negative,
            bytes.get(ms..me)? == [5],
            expect_end(next, end),
        ))
    })();
    assert_eq!(parsed, Some((vec![1, 2, 840, 113_549], false, true, true)));
    assert!(read_tlv(&[0x04, 0x81, 0x26], 0, 3).is_none());
}
