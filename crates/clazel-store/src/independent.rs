//! A second transcription of what this crate specifies, from different
//! texts. The definitions (everything before the equivalence section at the
//! end) were written from these texts alone, in a session that had not read
//! `crc32c/spec.rs`, `log/spec.rs`, `log/lemmas.rs`, `log/theorems.rs`,
//! `log/read.rs` or `log/exec.rs`:
//!
//! - **CRC-32C**: Ross N. Williams, "A Painless Guide to CRC Error Detection
//!   Algorithms" (version 3, 1993): the Rocksoft parameter model, the
//!   reflected table-driven loop, and the `cm_tab` routine of its reference
//!   implementation for a table entry. The parameters are the CRC catalogue's
//!   entry CRC-32C/ISCSI (Greg Cook, "Catalogue of parametrised CRC
//!   algorithms"): width 32, poly 0x1EDC6F41, init 0xFFFFFFFF, refin true,
//!   refout true, xorout 0xFFFFFFFF, check 0xE3069283. The parameters came
//!   from the brief for this file, which quoted the entry, and the Guide's algorithm from
//!   memory: no copy of either was opened in the session.
//! - **Recovery**: the 3.10a.0 design note in `docs/phases/phase-3.md`, its
//!   paragraph "Records: DER through `clazel-der`" (the layout), and its
//!   sentence "Recovery takes the longest run of records, from the header on,
//!   that decode, check correctly, and number their commits in sequence. It
//!   stops at the first record that fails any of these."
//!
//! The session also read `clazel-der`'s `spec.rs` (another crate's spec, whose
//! readers are used here), `clazel-der`'s `independent.rs` for this file's
//! shape, and this crate's `lib.rs` and `Cargo.toml`. A `grep` for
//! `decreases_by` over the workspace printed one line of `log/spec.rs`, the
//! attribute itself and nothing else. After every definition was written, and
//! before they were committed, a Verus run's warnings printed `log/spec.rs`
//! lines 98 to 118, part of `enum Op` (a `Put` with a bottle, and field types);
//! no definition here changed for that. Nothing else of this crate was opened
//! until the definitions were committed on their own. Only then were the
//! files above read, to write the equivalence lemmas at the end, which
//! necessarily name the spec's functions; only they do. An attempt to fetch
//! the Guide at that point was refused by its server, so its algorithm is
//! still from memory; what supports it is the catalogue's check value
//! ([`i_crc32c_check`]) and the proof against RFC 7143's process
//! ([`theorem_crc32c_equiv`]).
//!
//! ## The one change after reading the spec
//!
//! As first committed, the first record after the header could carry any
//! commit below 2^64, because the design note says only that "`commit`
//! increases by exactly 1 from record to record". The spec numbers commits 1,
//! 2, 3, ... (`encode_log`, and `transaction_ok`'s `1 <= commit`), so a file
//! whose first record has any other commit recovers that record under the
//! first reading and not under the spec. The equivalence is false for that
//! reading. The parser now starts from 1 ([`i_recover`] passes `previous` 0, and
//! `previous` is no longer an `Option`). The first number comes from the spec,
//! not from the note: this is the one place where this file follows the spec
//! rather than a text of its own. Nothing else differed.
//!
//! ## What the texts say and this file models
//!
//! - The CRC is computed the way the Guide's reflected table-driven loop does:
//!   `r = t[(r ^ byte) & 0xFF] ^ (r >> 8)`. A table entry is `cm_tab`'s: the
//!   index reflected in 8 bits, moved to the top of the register, eight
//!   left-shifting steps with the catalogue's poly 0x1EDC6F41 as written, and
//!   the register reflected in 32 bits. The table is a function here, not an
//!   array.
//! - The Guide reflects `init` for a reflected register; `init` is all ones,
//!   so its reflection is itself and the reflecting step is folded.
//! - The digest's four octets are least significant first, which neither the
//!   Guide nor the catalogue says: the brief for this file gives it.
//! - Recovery is a parser, front to back. A record is read with `clazel-der`'s
//!   readers, its check compared, its commit compared with the one before.
//!   Nothing here mentions encoding a record or a prefix of the file.
//!
//! ## How the design note was read, where it leaves something open
//!
//! - "The `check` field covers the record's other contents": the check is over
//!   the octets of the `commit` and `ops` encodings, the record's contents
//!   before the `check` encoding.
//! - "`commit` increases by exactly 1 from record to record": each record's commit is
//!   the one before plus 1. The note states no first number; it is 1 (see the
//!   change above).
//! - `put [0] { bottle, key, value }`: an `Op` is a constructed context-tagged
//!   value holding exactly its fields, with `bottle` an INTEGER (limit: below
//!   2^32) and `key` and `value` OCTET STRINGs ("Keys and values are octet
//!   strings"). Neither commit nor bottle may be negative.
//! - "at most 64 MiB per record": the whole encoding of a record, from its
//!   identifier to the end of its contents, is at most 64 MiB. A record over
//!   that is one that fails to decode.
//! - A SEQUENCE OF may be empty: a record with no ops decodes.
//! - A header that does not decode, or names another identity, is refused
//!   (`None`); from a good header on, recovery always gives a list, perhaps
//!   empty, whatever follows it.
//! - An identity over 4096 octets cannot be the header's: refused.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// CRC-32C: the Rocksoft model's parameters, from the catalogue.
// ---------------------------------------------------------------------------

/// Poly: the catalogue's, top bit (x^32) implied.
pub const I_POLY: u32 = 0x1EDC_6F41;

/// Init: the register's starting value.
pub const I_INIT: u32 = 0xFFFF_FFFF;

/// XorOut: XORed into the final register.
pub const I_XOROUT: u32 = 0xFFFF_FFFF;

/// Width 32's top bit: `topbit` in `cm_tab`.
pub const I_TOPBIT: u32 = 0x8000_0000;

/// The bottom `n` bits of `v` in reverse order, after the bits already in
/// `acc`: `reflect(v, n)` is `i_reflect(v, n, 0)`.
pub open spec fn i_reflect(v: u32, n: nat, acc: u32) -> u32
    decreases n,
{
    if n == 0 {
        acc
    } else {
        i_reflect(v >> 1u32, (n - 1) as nat, (acc << 1u32) | (v & 1u32))
    }
}

/// `cm_tab`'s loop, `n` times: "if (r & topbit) r = (r << 1) ^ poly; else
/// r <<= 1;".
pub open spec fn i_shifts(r: u32, n: nat) -> u32
    decreases n,
{
    if n == 0 {
        r
    } else if r & I_TOPBIT != 0 {
        i_shifts((r << 1u32) ^ I_POLY, (n - 1) as nat)
    } else {
        i_shifts(r << 1u32, (n - 1) as nat)
    }
}

/// `cm_tab`: the table entry for `index`, refin true.
pub open spec fn i_table(index: u32) -> u32 {
    let inbyte = i_reflect(index, 8, 0);
    let r = inbyte << 24u32;
    let r = i_shifts(r, 8);
    i_reflect(r, 32, 0)
}

/// The reflected table-driven loop over `data[i..]`:
/// "r = t[(r ^ *p++) & 0xFF] ^ (r >> 8)".
pub open spec fn i_register(data: Seq<u8>, i: nat, r: u32) -> u32
    decreases data.len() - i,
{
    if i >= data.len() {
        r
    } else {
        i_register(data, i + 1, i_table((r ^ (data[i as int] as u32)) & 0xFFu32) ^ (r >> 8u32))
    }
}

/// The value the model gives `data`: the loop from Init, then XorOut. RefOut
/// is true and the register is already reflected, so nothing else is done.
pub open spec fn i_crc_value(data: Seq<u8>) -> u32 {
    i_register(data, 0, I_INIT) ^ I_XOROUT
}

/// CRC-32C's four digest octets, least significant first.
pub open spec fn i_crc32c(data: Seq<u8>) -> Seq<u8> {
    let v = i_crc_value(data);
    seq![v as u8, (v >> 8u32) as u8, (v >> 16u32) as u8, (v >> 24u32) as u8]
}

/// The catalogue's check: the octets of "123456789" give 0xE3069283.
pub proof fn i_crc32c_check()
    ensures
        i_crc_value(seq![0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x35u8, 0x36u8, 0x37u8, 0x38u8, 0x39u8]) == 0xE306_9283u32,
{
    assert(i_crc_value(seq![0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x35u8, 0x36u8, 0x37u8, 0x38u8, 0x39u8]) == 0xE306_9283u32) by (compute_only);
}

// ---------------------------------------------------------------------------
// Records: what recovery gives.
// ---------------------------------------------------------------------------

/// "`Op` is one of three context-tagged choices".
pub enum IOp {
    /// `put [0] { bottle, key, value }`.
    Put {
        /// The bottle.
        bottle: nat,
        /// The key.
        key: Seq<u8>,
        /// The value.
        value: Seq<u8>,
    },
    /// `delete [1] { bottle, key }`.
    Delete {
        /// The bottle.
        bottle: nat,
        /// The key.
        key: Seq<u8>,
    },
    /// `clear [2] { bottle }`.
    Clear {
        /// The bottle.
        bottle: nat,
    },
}

/// `SEQUENCE { commit INTEGER, ops SEQUENCE OF Op, check OCTET STRING (4) }`,
/// the check having been compared.
pub struct IRecord {
    /// `commit`.
    pub commit: nat,
    /// `ops`.
    pub ops: Seq<IOp>,
}

/// The design note's limit: 64 MiB per record.
pub open spec fn i_max_record() -> nat {
    67108864
}

/// The limit on a bottle number: below 2^32.
pub open spec fn i_bottle_limit() -> nat {
    0x1_0000_0000
}

/// The limit on a commit number: below 2^64.
pub open spec fn i_commit_limit() -> nat {
    0x1_0000_0000_0000_0000
}

/// The limit on an identity's length.
pub open spec fn i_max_identity() -> nat {
    4096
}

/// The header's magic: the octets of "clazel-store".
pub open spec fn i_magic() -> Seq<u8> {
    seq![0x63u8, 0x6Cu8, 0x61u8, 0x7Au8, 0x65u8, 0x6Cu8, 0x2Du8, 0x73u8, 0x74u8, 0x6Fu8, 0x72u8, 0x65u8]
}

// ---------------------------------------------------------------------------
// Reading, front to back.
// ---------------------------------------------------------------------------

/// An INTEGER at `pos`, not negative and below `limit`: its value and the
/// next position.
pub open spec fn i_number(b: Seq<u8>, pos: nat, end: nat, limit: nat) -> Option<(nat, nat)> {
    match clazel_der::spec::read_integer(b, pos, end) {
        None => None,
        Some((negative, start, stop, next)) => {
            if negative {
                None
            } else {
                let v = clazel_der::spec::be_value(b.subrange(start as int, stop as int));
                if v < limit {
                    Some((v, next))
                } else {
                    None
                }
            }
        },
    }
}

/// An OCTET STRING at `pos`: its octets and the next position.
pub open spec fn i_octets(b: Seq<u8>, pos: nat, end: nat) -> Option<(Seq<u8>, nat)> {
    match clazel_der::spec::read_octet_string(b, pos, end) {
        None => None,
        Some((start, stop)) => Some((b.subrange(start as int, stop as int), stop)),
    }
}

/// The contents `[pos, end)` of a `put [0]`: `bottle, key, value` and nothing
/// more.
pub open spec fn i_put(b: Seq<u8>, pos: nat, end: nat) -> Option<IOp> {
    match i_number(b, pos, end, i_bottle_limit()) {
        None => None,
        Some((bottle, p1)) => match i_octets(b, p1, end) {
            None => None,
            Some((key, p2)) => match i_octets(b, p2, end) {
                None => None,
                Some((value, p3)) => {
                    if p3 == end {
                        Some(IOp::Put { bottle, key, value })
                    } else {
                        None
                    }
                },
            },
        },
    }
}

/// The contents `[pos, end)` of a `delete [1]`: `bottle, key` and nothing
/// more.
pub open spec fn i_delete(b: Seq<u8>, pos: nat, end: nat) -> Option<IOp> {
    match i_number(b, pos, end, i_bottle_limit()) {
        None => None,
        Some((bottle, p1)) => match i_octets(b, p1, end) {
            None => None,
            Some((key, p2)) => {
                if p2 == end {
                    Some(IOp::Delete { bottle, key })
                } else {
                    None
                }
            },
        },
    }
}

/// The contents `[pos, end)` of a `clear [2]`: `bottle` and nothing more.
pub open spec fn i_clear(b: Seq<u8>, pos: nat, end: nat) -> Option<IOp> {
    match i_number(b, pos, end, i_bottle_limit()) {
        None => None,
        Some((bottle, p1)) => {
            if p1 == end {
                Some(IOp::Clear { bottle })
            } else {
                None
            }
        },
    }
}

/// One `Op` at `pos`: the choice its tag names, and the next position.
pub open spec fn i_op(b: Seq<u8>, pos: nat, end: nat) -> Option<(IOp, nat)> {
    match clazel_der::spec::read_tlv(b, pos, end) {
        None => None,
        Some(t) => {
            let parsed = if t.tag == clazel_der::spec::context_specific(0, true) {
                i_put(b, t.cstart, t.cend)
            } else if t.tag == clazel_der::spec::context_specific(1, true) {
                i_delete(b, t.cstart, t.cend)
            } else if t.tag == clazel_der::spec::context_specific(2, true) {
                i_clear(b, t.cstart, t.cend)
            } else {
                None
            };
            match parsed {
                None => None,
                Some(op) => Some((op, t.cend)),
            }
        },
    }
}

/// An `Op` read ends after `pos` and by `end`.
#[verifier::decreases_by]
proof fn i_ops_terminates(b: Seq<u8>, pos: nat, end: nat) {
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
}

/// `SEQUENCE OF Op`: the `Op`s filling `[pos, end)` exactly.
pub open spec fn i_ops(b: Seq<u8>, pos: nat, end: nat) -> Option<Seq<IOp>>
    decreases end - pos,
        via i_ops_terminates
{
    if pos >= end {
        Some(Seq::empty())
    } else {
        match i_op(b, pos, end) {
            None => None,
            Some((op, next)) => match i_ops(b, next, end) {
                None => None,
                Some(rest) => Some(seq![op] + rest),
            },
        }
    }
}

/// One record at `pos`: it decodes, "check[s] correctly" and numbers its
/// commit in sequence after `previous`, the commit of the record before it.
/// Returns the record and the next position.
pub open spec fn i_record(file: Seq<u8>, pos: nat, previous: nat) -> Option<(IRecord, nat)> {
    match clazel_der::spec::read_tlv(file, pos, file.len()) {
        None => None,
        Some(t) => {
            if t.tag != clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE) || t.cend - pos > i_max_record() {
                None
            } else {
                match i_number(file, t.cstart, t.cend, i_commit_limit()) {
                    None => None,
                    Some((commit, p1)) => match clazel_der::spec::expect_sequence(file, p1, t.cend) {
                        None => None,
                        Some((ops_start, ops_end)) => match i_ops(file, ops_start, ops_end) {
                            None => None,
                            Some(ops) => match i_octets(file, ops_end, t.cend) {
                                None => None,
                                Some((check, p2)) => {
                                    // "check OCTET STRING (4)", and the last
                                    // thing in the record.
                                    if check.len() != 4 || p2 != t.cend {
                                        None
                                    } else if i_crc32c(file.subrange(t.cstart as int, ops_end as int)) != check {
                                        None
                                    } else if commit != previous + 1 {
                                        // "`commit` increases by exactly 1".
                                        None
                                    } else {
                                        Some((IRecord { commit, ops }, t.cend))
                                    }
                                },
                            },
                        },
                    },
                }
            }
        },
    }
}

/// A record read ends after `pos` and by the end of the file.
#[verifier::decreases_by]
proof fn i_records_terminates(file: Seq<u8>, pos: nat, previous: nat) {
    clazel_der::lemmas::lemma_read_tlv_bounds(file, pos, file.len());
}

/// "The longest run of records ... It stops at the first record that fails
/// any of these." `pos` is where the next record would start.
pub open spec fn i_records(file: Seq<u8>, pos: nat, previous: nat) -> Seq<IRecord>
    decreases file.len() - pos,
        via i_records_terminates
{
    if pos >= file.len() {
        Seq::empty()
    } else {
        match i_record(file, pos, previous) {
            None => Seq::empty(),
            Some((record, next)) => seq![record] + i_records(file, next, record.commit),
        }
    }
}

/// The header at the start of the file,
/// `SEQUENCE { magic OCTET STRING "clazel-store", version INTEGER 1, identity OCTET STRING }`,
/// naming `identity`. Returns where the records start.
pub open spec fn i_header(identity: Seq<u8>, file: Seq<u8>) -> Option<nat> {
    match clazel_der::spec::expect_sequence(file, 0, file.len()) {
        None => None,
        Some((start, stop)) => match i_octets(file, start, stop) {
            None => None,
            Some((magic, p1)) => match i_number(file, p1, stop, 2) {
                None => None,
                Some((version, p2)) => match i_octets(file, p2, stop) {
                    None => None,
                    Some((named, p3)) => {
                        if magic != i_magic() || version != 1 || p3 != stop {
                            None
                        } else if named.len() > i_max_identity() || named != identity {
                            // "a file whose header doesn't match its name is
                            // refused".
                            None
                        } else {
                            Some(stop)
                        }
                    },
                },
            },
        },
    }
}

/// Recovery: the header, then the longest run of records from it on.
pub open spec fn i_recover(identity: Seq<u8>, file: Seq<u8>) -> Option<Seq<IRecord>> {
    match i_header(identity, file) {
        None => None,
        // The first commit is 1: the spec's, not the note's (see the header).
        Some(start) => Some(i_records(file, start, 0)),
    }
}


// ---------------------------------------------------------------------------
// Equivalence with the spec: the CRC. Only this section and the next name the
// spec's functions.
// ---------------------------------------------------------------------------

/// The catalogue's poly reflected: each coefficient of the spec's register
/// (x^31 first) is the bit of `r` with the same index.
pub open spec fn e_g() -> u32 {
    0x82F6_3B78
}

/// One step of division with no coefficient brought down, on the reflected
/// register: the register is multiplied by x modulo G(x).
pub open spec fn e_s(x: u32) -> u32 {
    (x >> 1u32) ^ (if x & 1u32 == 1u32 { 0x82F6_3B78u32 } else { 0u32 })
}

/// [`e_s`], `k` times.
pub open spec fn e_iter(x: u32, k: nat) -> u32
    decreases k,
{
    if k == 0 {
        x
    } else {
        e_iter(e_s(x), (k - 1) as nat)
    }
}

/// The coefficient `b`, brought down at x^0 of the reflected register.
pub open spec fn e_top(b: bool) -> u32 {
    if b {
        0x8000_0000u32
    } else {
        0u32
    }
}

/// The coefficient `b`, at x^31 of the reflected register.
pub open spec fn e_low(b: bool) -> u32 {
    if b {
        1u32
    } else {
        0u32
    }
}

/// The remainder of `d`, as the reflected register.
pub open spec fn e_rem(d: Seq<bool>) -> u32
    decreases d.len(),
{
    if d.len() == 0 {
        0
    } else {
        e_s(e_rem(d.drop_last())) ^ e_top(d.last())
    }
}

/// The "direct" register over the coefficients `m`, from `w`: each coefficient
/// enters at x^31 and the register is multiplied by x.
pub open spec fn e_direct(w: u32, m: Seq<bool>) -> u32
    decreases m.len(),
{
    if m.len() == 0 {
        w
    } else {
        e_s(e_direct(w, m.drop_last()) ^ e_low(m.last()))
    }
}

/// The spec's 32 coefficients held in the reflected register.
pub open spec fn e_bits(r: u32) -> Seq<bool> {
    Seq::new(32, |j: int| crate::crc32c::spec::bit_of_value(r as nat, j as nat))
}

/// `k` zero coefficients.
pub open spec fn e_zeros(k: nat) -> Seq<bool> {
    Seq::new(k, |j: int| false)
}

/// Coefficient-wise sum of two polynomials of one length.
pub open spec fn e_xor(a: Seq<bool>, b: Seq<bool>) -> Seq<bool> {
    Seq::new(a.len(), |j: int| a[j] != b[j])
}

/// 32 one coefficients.
pub open spec fn e_ones() -> Seq<bool> {
    Seq::new(32, |j: int| true)
}

/// `(r >> i)` is `r` divided by 2^i.
proof fn lemma_shr_div(r: u32, i: nat)
    requires
        i <= 31,
    ensures
        (r >> (i as u32)) as nat == r as nat / vstd::arithmetic::power2::pow2(i),
    decreases i,
{
    vstd::arithmetic::power2::lemma2_to64();
    if i == 0 {
        assert(r >> 0u32 == r) by (bit_vector);
    } else {
        let j = (i - 1) as nat;
        lemma_shr_div(r, j);
        let ju = j as u32;
        assert(r >> ((ju + 1) as u32) == (r >> ju) / 2) by (bit_vector)
            requires
                ju < 31u32,
        ;
        assert((j + 1) as u32 == (ju + 1) as u32);
        vstd::arithmetic::power2::lemma_pow2_unfold(i);
        assert(j == i - 1);
        vstd::arithmetic::power2::lemma_pow2_pos(j);
        vstd::arithmetic::div_mod::lemma_div_denominator(r as int, vstd::arithmetic::power2::pow2(j) as int, 2);
        assert(vstd::arithmetic::power2::pow2(i) == vstd::arithmetic::power2::pow2(j) * 2) by (nonlinear_arith)
            requires
                vstd::arithmetic::power2::pow2(i) == 2 * vstd::arithmetic::power2::pow2(j),
        ;
    }
}

/// The spec's `bit_of_value` on a 32-bit number is that bit.
proof fn lemma_bit_of(r: u32, i: nat)
    requires
        i <= 31,
    ensures
        crate::crc32c::spec::bit_of_value(r as nat, i) == ((r >> (i as u32)) & 1u32 == 1u32),
{
    lemma_shr_div(r, i);
    let x = r >> (i as u32);
    assert((x & 1u32 == 1u32) == (x % 2 == 1)) by (bit_vector);
}

/// Multiplying by x is linear.
proof fn lemma_s_xor(x: u32, y: u32)
    ensures
        e_s(x ^ y) == e_s(x) ^ e_s(y),
{
    let g = 0x82F6_3B78u32;
    assert(((x ^ y) >> 1u32) ^ (if (x ^ y) & 1u32 == 1u32 { g } else { 0u32 }) == ((x >> 1u32) ^ (if x & 1u32 == 1u32 { g } else { 0u32 })) ^ ((y >> 1u32) ^ (if y & 1u32 == 1u32 { g } else { 0u32 }))) by (bit_vector)
        requires
            g == 0x82F6_3B78u32,
    ;
}

/// So is doing it `k` times.
proof fn lemma_iter_xor(x: u32, y: u32, k: nat)
    ensures
        e_iter(x ^ y, k) == e_iter(x, k) ^ e_iter(y, k),
    decreases k,
{
    if k > 0 {
        lemma_s_xor(x, y);
        lemma_iter_xor(e_s(x), e_s(y), (k - 1) as nat);
    }
}

/// [`e_iter`] one more time, from the other end.
proof fn lemma_iter_last(x: u32, k: nat)
    ensures
        e_iter(e_s(x), k) == e_s(e_iter(x, k)),
    decreases k,
{
    if k > 0 {
        lemma_iter_last(e_s(x), (k - 1) as nat);
    }
}

/// A division step of the spec is one of [`e_rem`], bit by bit.
proof fn lemma_division_step(r: u32, next: bool)
    ensures
        e_bits(e_s(r) ^ e_top(next)) =~= crate::crc32c::spec::division_step(e_bits(r), next),
{
    let new = e_s(r) ^ e_top(next);
    let old = e_bits(r);
    let shifted = old.drop_first().push(next);
    let g = crate::crc32c::spec::generator_below_x32();
    let top = e_top(next);
    assert forall|j: int| 0 <= j < 32 implies #[trigger] e_bits(new)[j] == crate::crc32c::spec::division_step(old, next)[j] by {
        let ju = j as u32;
        lemma_bit_of(new, j as nat);
        lemma_bit_of(r, 0);
        lemma_bit_of(0x1EDC_6F41u32, (31 - j) as nat);
        assert(old[0] == crate::crc32c::spec::bit_of_value(r as nat, 0));
        assert(r >> 0u32 == r) by (bit_vector);
        assert(g[j] == crate::crc32c::spec::bit_of_value(0x1EDC_6F41, (31 - j) as nat));
        let gen_bit = (0x1EDC_6F41u32 >> ((31 - ju) as u32)) & 1u32 == 1u32;
        assert(((31 - j) as nat) as u32 == (31 - ju) as u32);
        assert(gen_bit == ((0x82F6_3B78u32 >> ju) & 1u32 == 1u32)) by (bit_vector)
            requires
                ju < 32u32,
                gen_bit == ((0x1EDC_6F41u32 >> ((31 - ju) as u32)) & 1u32 == 1u32),
        ;
        assert(new == ((r >> 1u32) ^ (if r & 1u32 == 1u32 { 0x82F6_3B78u32 } else { 0u32 })) ^ top);
        if j < 31 {
            lemma_bit_of(r, (j + 1) as nat);
            assert(shifted[j] == old[j + 1]);
            assert(((j + 1) as nat) as u32 == (ju + 1) as u32);
            assert(top == 0u32 || top == 0x8000_0000u32);
            let sh = (r >> ((ju + 1) as u32)) & 1u32 == 1u32;
            let gb = (0x82F6_3B78u32 >> ju) & 1u32 == 1u32;
            assert(((new >> ju) & 1u32 == 1u32) == (if r & 1u32 == 1u32 { sh != gb } else { sh })) by (bit_vector)
                requires
                    ju < 31u32,
                    top == 0u32 || top == 0x8000_0000u32,
                    new == ((r >> 1u32) ^ (if r & 1u32 == 1u32 { 0x82F6_3B78u32 } else { 0u32 })) ^ top,
                    sh == ((r >> ((ju + 1) as u32)) & 1u32 == 1u32),
                    gb == ((0x82F6_3B78u32 >> ju) & 1u32 == 1u32),
            ;
        } else {
            assert(j == 31);
            assert(ju == 31u32);
            assert(shifted[j] == next);
            assert(next == (top == 0x8000_0000u32));
            let n = top == 0x8000_0000u32;
            assert(((new >> 31u32) & 1u32 == 1u32) == (if r & 1u32 == 1u32 { !n } else { n })) by (bit_vector)
                requires
                    top == 0u32 || top == 0x8000_0000u32,
                    new == ((r >> 1u32) ^ (if r & 1u32 == 1u32 { 0x82F6_3B78u32 } else { 0u32 })) ^ top,
                    n == (top == 0x8000_0000u32),
            ;
            assert((0x82F6_3B78u32 >> 31u32) & 1u32 == 1u32) by (bit_vector);
        }
        assert((r & 1u32 == 1u32) == ((r & 1u32) == 1u32));
    }
}

/// The spec's remainder is [`e_rem`].
proof fn lemma_remainder(d: Seq<bool>)
    ensures
        crate::crc32c::spec::remainder(d) =~= e_bits(e_rem(d)),
    decreases d.len(),
{
    if d.len() == 0 {
        assert forall|j: int| 0 <= j < 32 implies !#[trigger] e_bits(0u32)[j] by {
            vstd::arithmetic::power2::lemma_pow2_pos(j as nat);
            vstd::arithmetic::div_mod::lemma_basic_div(0, vstd::arithmetic::power2::pow2(j as nat) as int);
        }
    } else {
        lemma_remainder(d.drop_last());
        lemma_division_step(e_rem(d.drop_last()), d.last());
    }
}

/// Bringing down zeros is multiplying by x that many times.
proof fn lemma_rem_zeros(x: Seq<bool>, k: nat)
    ensures
        e_rem(x + e_zeros(k)) == e_iter(e_rem(x), k),
    decreases k,
{
    if k == 0 {
        assert(x + e_zeros(0) =~= x);
    } else {
        let j = (k - 1) as nat;
        lemma_rem_zeros(x, j);
        let d = x + e_zeros(k);
        assert(d.drop_last() =~= x + e_zeros(j));
        assert(d.last() == false);
        let s = e_s(e_iter(e_rem(x), j));
        assert(s ^ 0u32 == s) by (bit_vector);
        lemma_iter_last(e_rem(x), j);
    }
}

/// The remainder of a sum is the sum of the remainders.
proof fn lemma_rem_xor(a: Seq<bool>, b: Seq<bool>)
    requires
        a.len() == b.len(),
    ensures
        e_rem(e_xor(a, b)) == e_rem(a) ^ e_rem(b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(e_xor(a, b) =~= a);
        assert(0u32 ^ 0u32 == 0u32) by (bit_vector);
    } else {
        let c = e_xor(a, b);
        assert(c.drop_last() =~= e_xor(a.drop_last(), b.drop_last()));
        lemma_rem_xor(a.drop_last(), b.drop_last());
        let (x, y) = (e_rem(a.drop_last()), e_rem(b.drop_last()));
        lemma_s_xor(x, y);
        let (sx, sy, ta, tb, tc) = (e_s(x), e_s(y), e_top(a.last()), e_top(b.last()), e_top(c.last()));
        assert(tc == ta ^ tb) by {
            assert(c.last() == (a.last() != b.last()));
            assert(0u32 ^ 0u32 == 0u32 && 0u32 ^ 0x8000_0000u32 == 0x8000_0000u32 && 0x8000_0000u32 ^ 0u32 == 0x8000_0000u32 && 0x8000_0000u32 ^ 0x8000_0000u32 == 0u32) by (bit_vector);
        }
        assert((sx ^ sy) ^ (ta ^ tb) == (sx ^ ta) ^ (sy ^ tb)) by (bit_vector);
    }
}

/// [`e_direct`] from 0 is the remainder of `m` followed by 32 zeros.
proof fn lemma_direct_zero(m: Seq<bool>)
    ensures
        e_direct(0, m) == e_rem(m + e_zeros(32)),
    decreases m.len(),
{
    lemma_rem_zeros(m, 32);
    if m.len() == 0 {
        assert(e_iter(0u32, 32) == 0u32) by (compute_only);
    } else {
        let d = m.drop_last();
        let b = m.last();
        lemma_direct_zero(d);
        lemma_rem_zeros(d, 32);
        let q = e_rem(d);
        let f = e_iter(q, 32);
        lemma_iter_xor(e_s(q), e_top(b), 32);
        lemma_iter_last(q, 32);
        lemma_s_xor(f, e_low(b));
        assert(e_iter(e_top(b), 32) == e_s(e_low(b))) by {
            assert(e_iter(0u32, 32) == e_s(0u32)) by (compute_only);
            assert(e_iter(0x8000_0000u32, 32) == e_s(1u32)) by (compute_only);
        }
    }
}

/// [`e_direct`] from `w` adds what `w` alone becomes.
proof fn lemma_direct_start(w: u32, m: Seq<bool>)
    ensures
        e_direct(w, m) == e_direct(0, m) ^ e_iter(w, m.len()),
    decreases m.len(),
{
    if m.len() == 0 {
        assert(0u32 ^ w == w) by (bit_vector);
    } else {
        let d = m.drop_last();
        lemma_direct_start(w, d);
        let (f, i, l) = (e_direct(0, d), e_iter(w, d.len()), e_low(m.last()));
        assert((f ^ i) ^ l == (f ^ l) ^ i) by (bit_vector);
        lemma_s_xor(f ^ l, i);
        lemma_iter_last(w, d.len());
    }
}

/// 32 ones divided give all ones: nothing reached x^32 yet.
proof fn lemma_rem_ones(k: nat)
    requires
        k <= 32,
    ensures
        e_rem(Seq::new(k, |j: int| true)) == e_ones_value(k),
    decreases k,
{
    if k > 0 {
        let d = Seq::new(k, |j: int| true);
        assert(d.drop_last() =~= Seq::new((k - 1) as nat, |j: int| true));
        lemma_rem_ones((k - 1) as nat);
        let v = e_ones_value((k - 1) as nat);
        assert(e_ones_value(k) == e_s(v) ^ 0x8000_0000u32) by {
            lemma_ones_value((k - 1) as nat);
            let g = 0x82F6_3B78u32;
            assert(((v >> 1u32) ^ (if v & 1u32 == 1u32 { g } else { 0u32 })) == v >> 1u32) by (bit_vector)
                requires
                    v & 1u32 == 0u32,
            ;
        }
    }
}

/// The register after `k` ones, with no reduction yet.
pub open spec fn e_ones_value(k: nat) -> u32
    decreases k,
{
    if k == 0 {
        0u32
    } else {
        (e_ones_value((k - 1) as nat) >> 1u32) ^ 0x8000_0000u32
    }
}

/// The low bit of [`e_ones_value`] is clear until 32 ones are in, so [`e_s`]
/// is just the shift.
proof fn lemma_ones_value(k: nat)
    requires
        k < 32,
    ensures
        e_ones_value(k) & 1u32 == 0u32,
{
    assert(e_check_ones(32)) by (compute_only);
    lemma_check_ones(32, k);
}

/// Every [`e_ones_value`] below `n` has its low bit clear.
pub open spec fn e_check_ones(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        e_check_ones((n - 1) as nat) && e_ones_value((n - 1) as nat) & 1u32 == 0u32
    }
}

/// What [`e_check_ones`] says.
proof fn lemma_check_ones(n: nat, k: nat)
    requires
        e_check_ones(n),
        k < n,
    ensures
        e_ones_value(k) & 1u32 == 0u32,
    decreases n,
{
    if k < n - 1 {
        lemma_check_ones((n - 1) as nat, k);
    }
}

/// The 32 highest coefficients complemented: the sum with 32 ones.
proof fn lemma_complemented(m: Seq<bool>)
    ensures
        e_rem(crate::crc32c::spec::complement_first_32(m + e_zeros(32))) == e_direct(0xFFFF_FFFF, m),
{
    let d = m + e_zeros(32);
    let mask = e_ones() + e_zeros(m.len());
    assert(crate::crc32c::spec::complement_first_32(d) =~= e_xor(d, mask));
    lemma_rem_xor(d, mask);
    lemma_rem_zeros(e_ones(), m.len());
    lemma_direct_zero(m);
    lemma_direct_start(0xFFFF_FFFF, m);
    lemma_rem_ones(32);
    assert(Seq::new(32, |j: int| true) =~= e_ones());
    assert(e_ones_value(32) == 0xFFFF_FFFFu32) by (compute_only);
}

/// The direct register over two polynomials in turn.
proof fn lemma_direct_append(w: u32, a: Seq<bool>, b: Seq<bool>)
    ensures
        e_direct(w, a + b) == e_direct(e_direct(w, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_direct_append(w, a, b.drop_last());
    }
}

/// `v ^ y` stepped: the low bit of `y` goes in, the rest is just shifted.
proof fn lemma_s_peel(v: u32, y: u32)
    ensures
        e_s(v ^ y) == e_s(v ^ (y & 1u32)) ^ (y >> 1u32),
{
    let g = 0x82F6_3B78u32;
    assert(((v ^ y) >> 1u32) ^ (if (v ^ y) & 1u32 == 1u32 { g } else { 0u32 }) == (((v ^ (y & 1u32)) >> 1u32) ^ (if (v ^ (y & 1u32)) & 1u32 == 1u32 { g } else { 0u32 })) ^ (y >> 1u32)) by (bit_vector);
}

/// The first `t` coefficients of the octet `x`, against the whole octet
/// added to the register at once.
proof fn lemma_byte_take(w: u32, x: u8, t: nat)
    requires
        t <= 8,
    ensures
        e_direct(w, crate::crc32c::spec::byte_bits(x).take(t as int)) ^ ((x as u32) >> (t as u32)) == e_iter(w ^ (x as u32), t),
    decreases t,
{
    let y = x as u32;
    let bits = crate::crc32c::spec::byte_bits(x);
    if t == 0 {
        assert(bits.take(0) =~= Seq::<bool>::empty());
        assert(y >> 0u32 == y) by (bit_vector);
    } else {
        let j = (t - 1) as nat;
        let ju = j as u32;
        lemma_byte_take(w, x, j);
        let now = bits.take(t as int);
        assert(now.drop_last() =~= bits.take(j as int));
        assert(now.last() == bits[j as int]);
        let v = e_direct(w, bits.take(j as int));
        let z = y >> ju;
        lemma_s_peel(v, z);
        lemma_iter_last(w ^ y, j);
        lemma_bit_of(y, j);
        assert(bits[j as int] == crate::crc32c::spec::bit_of_value(y as nat, j));
        assert(z & 1u32 == e_low(bits[j as int])) by {
            assert((z & 1u32) == 1u32 || (z & 1u32) == 0u32) by (bit_vector);
        }
        assert(z >> 1u32 == y >> ((ju + 1) as u32)) by (bit_vector)
            requires
                ju < 8u32,
                z == y >> ju,
        ;
        assert((t as u32) == (ju + 1) as u32);
    }
}

/// The octet's coefficients in turn are the octet added at once and eight
/// multiplications by x.
proof fn lemma_byte_direct(w: u32, x: u8)
    ensures
        e_direct(w, crate::crc32c::spec::byte_bits(x)) == e_iter(w ^ (x as u32), 8),
{
    lemma_byte_take(w, x, 8);
    let bits = crate::crc32c::spec::byte_bits(x);
    assert(bits.take(8) =~= bits);
    let y = x as u32;
    let v = e_direct(w, bits);
    assert((y >> 8u32) == 0u32 && (v ^ 0u32) == v) by (bit_vector)
        requires
            y < 256u32,
    ;
}

/// Every table entry below `n` is eight multiplications by x.
pub open spec fn e_check_table(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        e_check_table((n - 1) as nat) && i_table((n - 1) as u32) == e_iter((n - 1) as u32, 8)
    }
}

/// What [`e_check_table`] says.
proof fn lemma_check_table(n: nat, i: nat)
    requires
        e_check_table(n),
        i < n,
        n <= 256,
    ensures
        i_table(i as u32) == e_iter(i as u32, 8),
    decreases n,
{
    if i < n - 1 {
        lemma_check_table((n - 1) as nat, i);
    }
}

/// `t` multiplications by x of a register whose low `t` bits are clear only
/// shift it.
proof fn lemma_iter_clear(z: u32, t: u32)
    requires
        t <= 8u32,
        z & (((1u32 << t) - 1) as u32) == 0u32,
    ensures
        e_iter(z, t as nat) == z >> t,
    decreases t,
{
    if t == 0u32 {
        assert(z >> 0u32 == z) by (bit_vector);
    } else {
        let u = (t - 1) as u32;
        assert(z & 1u32 == 0u32 && (z >> 1u32) & (((1u32 << u) - 1) as u32) == 0u32 && (z >> 1u32) >> u == z >> t) by (bit_vector)
            requires
                t <= 8u32,
                t >= 1u32,
                u == t - 1,
                z & (((1u32 << t) - 1) as u32) == 0u32,
        ;
        let s = z >> 1u32;
        assert(s ^ 0u32 == s) by (bit_vector);
        assert(e_s(z) == s);
        lemma_iter_clear(s, u);
        assert((t as nat - 1) as nat == u as nat);
    }
}

/// The Guide's loop body is the octet's eight steps.
proof fn lemma_table_step(w: u32, x: u8)
    ensures
        e_direct(w, crate::crc32c::spec::byte_bits(x)) == i_table((w ^ (x as u32)) & 0xFFu32) ^ (w >> 8u32),
{
    lemma_byte_direct(w, x);
    let y = w ^ (x as u32);
    let lo = y & 0xFFu32;
    let hi = y & 0xFFFF_FF00u32;
    let xx = x as u32;
    assert(y == lo ^ hi && hi & (((1u32 << 8u32) - 1) as u32) == 0u32 && hi >> 8u32 == w >> 8u32 && lo < 256u32) by (bit_vector)
        requires
            y == w ^ xx,
            xx < 256u32,
            lo == y & 0xFFu32,
            hi == y & 0xFFFF_FF00u32,
    ;
    lemma_iter_xor(lo, hi, 8);
    lemma_iter_clear(hi, 8u32);
    assert(e_check_table(256)) by (compute_only);
    lemma_check_table(256, lo as nat);
}

/// The Guide's loop over `data[i..]` is the direct register over its
/// coefficients.
proof fn lemma_register(data: Seq<u8>, i: nat, r: u32)
    requires
        i <= data.len(),
    ensures
        i_register(data, i, r) == e_direct(r, crate::crc32c::spec::message_bits(data.skip(i as int))),
    decreases data.len() - i,
{
    let rest = data.skip(i as int);
    if i == data.len() {
        assert(rest.len() == 0);
    } else {
        assert(rest[0] == data[i as int]);
        assert(rest.drop_first() =~= data.skip((i + 1) as int));
        lemma_direct_append(r, crate::crc32c::spec::byte_bits(rest[0]), crate::crc32c::spec::message_bits(rest.drop_first()));
        lemma_table_step(r, rest[0]);
        lemma_register(data, i + 1, i_table((r ^ (data[i as int] as u32)) & 0xFFu32) ^ (r >> 8u32));
    }
}

/// Eight coefficients as a digest octet.
proof fn lemma_octet_value(s: Seq<bool>, y: nat)
    requires
        forall|t: int| 0 <= t < s.len() ==> s[t] == ((y / vstd::arithmetic::power2::pow2(t as nat)) % 2 == 1),
    ensures
        crate::crc32c::spec::octet_value(s) == y % vstd::arithmetic::power2::pow2(s.len()),
    decreases s.len(),
{
    vstd::arithmetic::power2::lemma2_to64();
    if s.len() == 0 {
        assert(y % 1 == 0);
    } else {
        let n = (s.len() - 1) as nat;
        let d = s.drop_first();
        assert forall|t: int| 0 <= t < d.len() implies d[t] == (((y / 2) / vstd::arithmetic::power2::pow2(t as nat)) % 2 == 1) by {
            assert(d[t] == s[t + 1]);
            vstd::arithmetic::power2::lemma_pow2_unfold((t + 1) as nat);
            vstd::arithmetic::power2::lemma_pow2_pos(t as nat);
            vstd::arithmetic::div_mod::lemma_div_denominator(y as int, 2, vstd::arithmetic::power2::pow2(t as nat) as int);
            assert(((t + 1) as nat - 1) as nat == t as nat);
        }
        lemma_octet_value(d, y / 2);
        assert(s[0] == ((y / vstd::arithmetic::power2::pow2(0)) % 2 == 1));
        vstd::arithmetic::power2::lemma_pow2_unfold(s.len());
        vstd::arithmetic::power2::lemma_pow2_pos(n);
        vstd::arithmetic::div_mod::lemma_mod_breakdown(y as int, 2, vstd::arithmetic::power2::pow2(n) as int);
        assert((s.len() - 1) as nat == n);
    }
}

/// One digest octet of the register `u`.
proof fn lemma_digest_octet(u: u32, k: u32)
    requires
        k < 4u32,
    ensures
        crate::crc32c::spec::octet_value(e_bits(u).subrange(8 * k as int, 8 * k as int + 8)) as u8 == (u >> ((8 * k) as u32)) as u8,
{
    let shift = (8 * k) as u32;
    let y = u >> shift;
    let s = e_bits(u).subrange(8 * k as int, 8 * k as int + 8);
    vstd::arithmetic::power2::lemma2_to64();
    assert forall|t: int| 0 <= t < s.len() implies s[t] == (((y as nat) / vstd::arithmetic::power2::pow2(t as nat)) % 2 == 1) by {
        let tu = t as u32;
        lemma_bit_of(u, (8 * k + t) as nat);
        lemma_bit_of(y, t as nat);
        assert(((8 * k + t) as nat) as u32 == (shift + tu) as u32);
        assert((u >> ((shift + tu) as u32)) == y >> tu) by (bit_vector)
            requires
                shift <= 24u32,
                tu < 8u32,
                y == u >> shift,
        ;
        assert(s[t] == e_bits(u)[8 * k + t]);
    }
    lemma_octet_value(s, y as nat);
    let v = crate::crc32c::spec::octet_value(s);
    assert(v == y as nat % 256);
    assert(((y as u8) as u32) == y & 0xFFu32 && y & 0xFFu32 == y % 256) by (bit_vector);
    assert(v as u8 == y as u8);
}

/// The Guide's CRC is the spec's, for every input.
pub proof fn theorem_crc32c_equiv(data: Seq<u8>)
    ensures
        i_crc32c(data) == crate::crc32c::spec::crc32c(data),
{
    let m = crate::crc32c::spec::message_bits(data);
    let zeros = Seq::new(32, |j: int| false);
    assert(zeros =~= e_zeros(32));
    let dividend = crate::crc32c::spec::complement_first_32(m + zeros);
    let v = e_rem(dividend);
    lemma_remainder(dividend);
    lemma_complemented(m);
    assert(data.skip(0) =~= data);
    lemma_register(data, 0, I_INIT);
    let u = v ^ 0xFFFF_FFFFu32;
    assert(i_crc_value(data) == u);
    assert forall|j: int| 0 <= j < 32 implies #[trigger] e_bits(u)[j] == !e_bits(v)[j] by {
        let ju = j as u32;
        lemma_bit_of(u, j as nat);
        lemma_bit_of(v, j as nat);
        assert(((u >> ju) & 1u32 == 1u32) == !((v >> ju) & 1u32 == 1u32)) by (bit_vector)
            requires
                ju < 32u32,
                u == v ^ 0xFFFF_FFFFu32,
        ;
    }
    let crc = crate::crc32c::spec::complement(crate::crc32c::spec::remainder(dividend));
    assert(crc =~= e_bits(u));
    lemma_digest_octet(u, 0);
    lemma_digest_octet(u, 1);
    lemma_digest_octet(u, 2);
    lemma_digest_octet(u, 3);
    assert(u >> 0u32 == u) by (bit_vector);
    assert(i_crc32c(data) =~= crate::crc32c::spec::digest_word(crc));
}

// ---------------------------------------------------------------------------
// Equivalence with the spec: recovery.
// ---------------------------------------------------------------------------

/// The spec's operation for one this file read.
pub open spec fn e_op(o: IOp) -> crate::log::spec::Op {
    match o {
        IOp::Put { bottle, key, value } => crate::log::spec::Op::Put { bottle, key, value },
        IOp::Delete { bottle, key } => crate::log::spec::Op::Delete { bottle, key },
        IOp::Clear { bottle } => crate::log::spec::Op::Clear { bottle },
    }
}

/// The spec's transaction for the `ops` of a record this file read.
pub open spec fn e_ops(s: Seq<IOp>) -> Seq<crate::log::spec::Op> {
    s.map_values(|o: IOp| e_op(o))
}

/// The spec's transaction list for the records this file read.
pub open spec fn e_log(v: Seq<IRecord>) -> Seq<Seq<crate::log::spec::Op>> {
    v.map_values(|r: IRecord| e_ops(r.ops))
}

/// The spec's result for what this file recovered.
pub open spec fn e_recovery(r: Option<Seq<IRecord>>) -> Option<Seq<Seq<crate::log::spec::Op>>> {
    match r {
        Some(v) => Some(e_log(v)),
        None => None,
    }
}

/// Octets of `x + y` at `pos` are `x` at `pos` and `y` after it.
proof fn lemma_e_split(b: Seq<u8>, pos: nat, x: Seq<u8>, y: Seq<u8>)
    requires
        pos + x.len() + y.len() <= b.len(),
        b.subrange(pos as int, (pos + x.len() + y.len()) as int) == x + y,
    ensures
        b.subrange(pos as int, (pos + x.len()) as int) == x,
        b.subrange((pos + x.len()) as int, (pos + x.len() + y.len()) as int) == y,
{
    let s = b.subrange(pos as int, (pos + x.len() + y.len()) as int);
    assert(b.subrange(pos as int, (pos + x.len()) as int) =~= s.subrange(0, x.len() as int));
    assert(s.subrange(0, x.len() as int) =~= x);
    assert(b.subrange((pos + x.len()) as int, (pos + x.len() + y.len()) as int) =~= s.subrange(x.len() as int, s.len() as int));
    assert(s.subrange(x.len() as int, s.len() as int) =~= y);
}

/// Adjacent ranges of octets, as one.
proof fn lemma_e_join(b: Seq<u8>, p: nat, q: nat, r: nat)
    requires
        p <= q,
        q <= r,
        r <= b.len(),
    ensures
        b.subrange(p as int, r as int) =~= b.subrange(p as int, q as int) + b.subrange(q as int, r as int),
{
}

/// Numbers spelled equally have equal octets but for leading zeros.
proof fn lemma_strip_same(a: Seq<u8>, b: Seq<u8>)
    requires
        clazel_der::spec::be_value(a) == clazel_der::spec::be_value(b),
    ensures
        clazel_der::spec::strip_leading_zeros(a) == clazel_der::spec::strip_leading_zeros(b),
{
    let (sa, sb) = (clazel_der::spec::strip_leading_zeros(a), clazel_der::spec::strip_leading_zeros(b));
    clazel_der::lemmas_typed::lemma_strip_leading_zeros_value(a);
    clazel_der::lemmas_typed::lemma_strip_leading_zeros_value(b);
    if sa.len() < sb.len() {
        clazel_der::lemmas::lemma_be_value_bound(sa);
        clazel_der::lemmas_tlv::lemma_be_value_leading_nonzero(sb);
        clazel_der::lemmas_tlv::lemma_pow256_monotone(sa.len(), (sb.len() - 1) as nat);
    } else if sb.len() < sa.len() {
        clazel_der::lemmas::lemma_be_value_bound(sb);
        clazel_der::lemmas_tlv::lemma_be_value_leading_nonzero(sa);
        clazel_der::lemmas_tlv::lemma_pow256_monotone(sb.len(), (sa.len() - 1) as nat);
    } else {
        clazel_der::lemmas::lemma_be_bytes_of_be_value(sa);
        clazel_der::lemmas::lemma_be_bytes_of_be_value(sb);
    }
}

/// A number this file read is the spec's encoding of it.
proof fn lemma_number_encode(b: Seq<u8>, pos: nat, end: nat, limit: nat)
    requires
        end <= b.len(),
        limit <= 0x1_0000_0000_0000_0000,
    ensures
        match i_number(b, pos, end, limit) {
            Some((v, next)) => {
                &&& v < limit
                &&& pos < next
                &&& next <= end
                &&& b.subrange(pos as int, next as int) == crate::log::spec::encode_number(v)
            },
            None => true,
        },
{
    clazel_der::lemmas_typed::lemma_encode_integer_read_integer(b, pos, end);
    if let Some((v, next)) = i_number(b, pos, end, limit) {
        let (negative, ms, me, nx) = clazel_der::spec::read_integer(b, pos, end).unwrap();
        let mag = b.subrange(ms as int, me as int);
        clazel_der::lemmas::lemma_pow256_8();
        clazel_der::lemmas::lemma_be_value_of_be_bytes(v, 8);
        lemma_strip_same(mag, clazel_der::spec::be_bytes(v, 8));
        assert(clazel_der::spec::integer_unsigned_contents(mag) == clazel_der::spec::integer_unsigned_contents(clazel_der::spec::be_bytes(v, 8)));
    }
}

/// The spec's encoding of a number below the limit reads as that number.
proof fn lemma_number_read(v: nat, b: Seq<u8>, pos: nat, end: nat, limit: nat)
    requires
        v < limit,
        limit <= 0x1_0000_0000_0000_0000,
        pos + crate::log::spec::encode_number(v).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + crate::log::spec::encode_number(v).len()) as int) == crate::log::spec::encode_number(v),
    ensures
        i_number(b, pos, end, limit) == Some((v, pos + crate::log::spec::encode_number(v).len())),
{
    let m = clazel_der::spec::be_bytes(v, 8);
    clazel_der::lemmas::lemma_pow256_8();
    clazel_der::lemmas::lemma_be_bytes_len(v, 8);
    clazel_der::lemmas_typed::lemma_integer_unsigned_contents(m);
    clazel_der::lemmas_typed::lemma_read_integer_encode_integer_unsigned(m, b, pos, end);
    clazel_der::lemmas::lemma_be_value_of_be_bytes(v, 8);
}

/// An OCTET STRING this file read is the spec's encoding of it.
proof fn lemma_octets_encode(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match i_octets(b, pos, end) {
            Some((s, next)) => {
                &&& pos < next
                &&& next <= end
                &&& b.subrange(pos as int, next as int) == clazel_der::spec::encode_octet_string(s)
            },
            None => true,
        },
{
    clazel_der::lemmas_typed::lemma_encode_octets_read_octets(b, pos, end, clazel_der::spec::OCTET_STRING);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
}

/// The spec's encoding of octets reads as those octets.
proof fn lemma_octets_read(s: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        s.len() < clazel_der::spec::pow256(8),
        pos + clazel_der::spec::encode_octet_string(s).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + clazel_der::spec::encode_octet_string(s).len()) as int) == clazel_der::spec::encode_octet_string(s),
    ensures
        i_octets(b, pos, end) == Some((s, pos + clazel_der::spec::encode_octet_string(s).len())),
{
    clazel_der::lemmas_typed::lemma_read_octets_encode_octets(clazel_der::spec::OCTET_STRING, s, b, pos, end);
    let (cs, ce) = clazel_der::spec::read_octet_string(b, pos, end).unwrap();
    assert(b.subrange(cs as int, ce as int) == s);
}

/// An `Op` this file read is the spec's encoding of it.
proof fn lemma_op_encode(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match i_op(b, pos, end) {
            Some((o, next)) => {
                &&& pos < next
                &&& next <= end
                &&& b.subrange(pos as int, next as int) == crate::log::spec::encode_op(e_op(o))
                &&& crate::log::spec::op_bottle(e_op(o)) < clazel_der::spec::pow256(4)
            },
            None => true,
        },
{
    clazel_der::lemmas::lemma_pow256_8();
    clazel_der::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some((o, next)) = i_op(b, pos, end) {
        let t = clazel_der::spec::read_tlv(b, pos, end).unwrap();
        let (cs, ce) = (t.cstart, t.cend);
        let c = b.subrange(cs as int, ce as int);
        assert(next == ce);
        lemma_number_encode(b, cs, ce, i_bottle_limit());
        let (bottle, p1) = i_number(b, cs, ce, i_bottle_limit()).unwrap();
        lemma_octets_encode(b, p1, ce);
        if t.tag == clazel_der::spec::context_specific(0, true) {
            let (key, p2) = i_octets(b, p1, ce).unwrap();
            lemma_octets_encode(b, p2, ce);
            let (value, p3) = i_octets(b, p2, ce).unwrap();
            lemma_e_join(b, cs, p1, ce);
            lemma_e_join(b, p1, p2, ce);
            assert(c =~= crate::log::spec::encode_number(bottle) + clazel_der::spec::encode_octet_string(key) + clazel_der::spec::encode_octet_string(value));
        } else if t.tag == clazel_der::spec::context_specific(1, true) {
            let (key, p2) = i_octets(b, p1, ce).unwrap();
            lemma_e_join(b, cs, p1, ce);
        } else {
            assert(t.tag == clazel_der::spec::context_specific(2, true));
        }
    }
}

/// The spec's encoding of an operation reads as that operation.
proof fn lemma_op_read(e: crate::log::spec::Op, b: Seq<u8>, pos: nat, end: nat)
    requires
        crate::log::spec::op_bottle(e) < clazel_der::spec::pow256(4),
        crate::log::spec::encode_op(e).len() < clazel_der::spec::pow256(8),
        pos + crate::log::spec::encode_op(e).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + crate::log::spec::encode_op(e).len()) as int) == crate::log::spec::encode_op(e),
    ensures
        i_op(b, pos, end) matches Some((o, next)) && e_op(o) == e && next == pos + crate::log::spec::encode_op(e).len(),
{
    clazel_der::lemmas::lemma_pow256_8();
    crate::log::lemmas::lemma_encode_op(e);
    let c = crate::log::lemmas::op_contents(e);
    let tag = clazel_der::spec::context_specific(crate::log::lemmas::op_tag(e), true);
    clazel_der::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, c, b, pos, end);
    let t = clazel_der::spec::read_tlv(b, pos, end).unwrap();
    let (cs, ce) = (t.cstart, t.cend);
    assert(ce == pos + crate::log::spec::encode_op(e).len()) by {
        assert(crate::log::spec::encode_op(e).len() == clazel_der::spec::encode_identifier(tag).len() + clazel_der::spec::encode_length(c.len()).len() + c.len());
    }
    assert(b.subrange(cs as int, ce as int) == c);
    assert(ce <= b.len());
    let n = crate::log::spec::encode_number(crate::log::spec::op_bottle(e));
    match e {
        crate::log::spec::Op::Put { bottle, key, value } => {
            let (ok, ov) = (clazel_der::spec::encode_octet_string(key), clazel_der::spec::encode_octet_string(value));
            assert(c =~= n + (ok + ov));
            lemma_e_split(b, cs, n, ok + ov);
            lemma_e_split(b, cs + n.len(), ok, ov);
            lemma_number_read(bottle, b, cs, ce, i_bottle_limit());
            lemma_octets_read(key, b, cs + n.len(), ce);
            lemma_octets_read(value, b, cs + n.len() + ok.len(), ce);
            assert(cs + n.len() + ok.len() + ov.len() == ce);
            assert(i_put(b, cs, ce) == Some(IOp::Put { bottle, key, value }));
        },
        crate::log::spec::Op::Delete { bottle, key } => {
            let ok = clazel_der::spec::encode_octet_string(key);
            lemma_e_split(b, cs, n, ok);
            lemma_number_read(bottle, b, cs, ce, i_bottle_limit());
            lemma_octets_read(key, b, cs + n.len(), ce);
            assert(i_delete(b, cs, ce) == Some(IOp::Delete { bottle, key }));
        },
        crate::log::spec::Op::Clear { bottle } => {
            lemma_number_read(bottle, b, cs, ce, i_bottle_limit());
            assert(i_clear(b, cs, ce) == Some(IOp::Clear { bottle }));
        },
    }
}

/// Every bottle of `ops` below 2^32.
pub open spec fn e_bottles_ok(ops: Seq<crate::log::spec::Op>) -> bool {
    forall|i: int| 0 <= i < ops.len() ==> crate::log::spec::op_bottle(#[trigger] ops[i]) < clazel_der::spec::pow256(4)
}

/// The `Op`s this file read are the spec's encoding of them.
proof fn lemma_ops_encode(b: Seq<u8>, pos: nat, end: nat)
    requires
        pos <= end,
        end <= b.len(),
    ensures
        i_ops(b, pos, end) matches Some(v) ==> b.subrange(pos as int, end as int) == crate::log::spec::encode_ops(e_ops(v)) && e_bottles_ok(e_ops(v)),
    decreases end - pos,
{
    if pos >= end {
        assert(b.subrange(pos as int, end as int) =~= Seq::<u8>::empty());
        assert(e_ops(Seq::<IOp>::empty()) =~= Seq::<crate::log::spec::Op>::empty());
    } else {
        lemma_op_encode(b, pos, end);
        if let Some((o, next)) = i_op(b, pos, end) {
            lemma_ops_encode(b, next, end);
            if let Some(rest) = i_ops(b, next, end) {
                let v = seq![o] + rest;
                assert(i_ops(b, pos, end) == Some(v));
                let ev = e_ops(v);
                assert(ev[0] == e_op(o));
                assert(ev.drop_first() =~= e_ops(rest));
                crate::log::lemmas::lemma_encode_ops_front(ev);
                lemma_e_join(b, pos, next, end);
                assert forall|i: int| 0 <= i < ev.len() implies crate::log::spec::op_bottle(#[trigger] ev[i]) < clazel_der::spec::pow256(4) by {
                    if i > 0 {
                        assert(ev[i] == e_ops(rest)[i - 1]);
                    }
                }
            }
        }
    }
}

/// The spec's encoding of operations reads as those operations.
proof fn lemma_ops_read(e: Seq<crate::log::spec::Op>, b: Seq<u8>, pos: nat, end: nat)
    requires
        e_bottles_ok(e),
        crate::log::spec::encode_ops(e).len() < clazel_der::spec::pow256(8),
        pos <= end,
        end <= b.len(),
        b.subrange(pos as int, end as int) == crate::log::spec::encode_ops(e),
    ensures
        i_ops(b, pos, end) matches Some(v) && e_ops(v) == e,
    decreases e.len(),
{
    if e.len() == 0 {
        assert(crate::log::spec::encode_ops(e).len() == 0);
        assert(pos == end);
        assert(e_ops(Seq::<IOp>::empty()) =~= e);
    } else {
        crate::log::lemmas::lemma_encode_ops_front(e);
        let (first, rest) = (e[0], e.drop_first());
        let (x, y) = (crate::log::spec::encode_op(first), crate::log::spec::encode_ops(rest));
        crate::log::lemmas::lemma_encode_op(first);
        lemma_e_split(b, pos, x, y);
        lemma_op_read(first, b, pos, end);
        let (o, next) = i_op(b, pos, end).unwrap();
        assert forall|i: int| 0 <= i < rest.len() implies crate::log::spec::op_bottle(#[trigger] rest[i]) < clazel_der::spec::pow256(4) by {
            assert(rest[i] == e[i + 1]);
        }
        assert(next + y.len() == end);
        lemma_ops_read(rest, b, next, end);
        let tail = i_ops(b, next, end).unwrap();
        assert(i_ops(b, pos, end) == Some(seq![o] + tail));
        assert(e_ops(seq![o] + tail) =~= e) by {
            assert forall|i: int| 0 <= i < e.len() implies #[trigger] e_ops(seq![o] + tail)[i] == e[i] by {
                if i > 0 {
                    assert((seq![o] + tail)[i] == tail[i - 1]);
                    assert(e_ops(tail)[i - 1] == rest[i - 1]);
                }
            }
        }
    }
}

/// A record this file read is the spec's record of a valid transaction, with
/// the next commit number.
proof fn lemma_record_encode(file: Seq<u8>, pos: nat, c: nat)
    ensures
        match i_record(file, pos, c) {
            Some((r, next)) => {
                &&& r.commit == c + 1
                &&& pos < next
                &&& next <= file.len()
                &&& file.subrange(pos as int, next as int) == crate::log::spec::encode_record(c + 1, e_ops(r.ops))
                &&& crate::log::spec::transaction_ok(c + 1, e_ops(r.ops))
            },
            None => true,
        },
{
    clazel_der::lemmas::lemma_pow256_8();
    clazel_der::lemmas_tlv::lemma_encode_tlv_read_tlv(file, pos, file.len());
    clazel_der::lemmas::lemma_read_tlv_bounds(file, pos, file.len());
    if let Some((r, next)) = i_record(file, pos, c) {
        let t = clazel_der::spec::read_tlv(file, pos, file.len()).unwrap();
        let (cs, ce) = (t.cstart, t.cend);
        lemma_number_encode(file, cs, ce, i_commit_limit());
        let (commit, p1) = i_number(file, cs, ce, i_commit_limit()).unwrap();
        clazel_der::lemmas_typed::lemma_encode_sequence_expect_sequence(file, p1, ce);
        clazel_der::lemmas::lemma_read_tlv_bounds(file, p1, ce);
        let (os, oe) = clazel_der::spec::expect_sequence(file, p1, ce).unwrap();
        lemma_ops_encode(file, os, oe);
        let ops = i_ops(file, os, oe).unwrap();
        lemma_octets_encode(file, oe, ce);
        let (check, p2) = i_octets(file, oe, ce).unwrap();
        let e = e_ops(ops);
        assert(r.ops == ops);
        assert(commit == c + 1);
        lemma_e_join(file, cs, p1, oe);
        let body = file.subrange(cs as int, oe as int);
        assert(body == crate::log::spec::record_body(commit, e));
        theorem_crc32c_equiv(body);
        lemma_e_join(file, cs, oe, ce);
        assert(file.subrange(cs as int, ce as int) == crate::log::spec::record_body(commit, e) + clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(crate::log::spec::record_body(commit, e))));
        assert(next == ce);
        assert(file.subrange(pos as int, next as int) == crate::log::spec::encode_record(commit, e));
        assert(crate::log::spec::transaction_ok(commit, e)) by {
            assert(commit >= 1);
            assert(crate::log::spec::encode_record(commit, e).len() == ce - pos);
        }
    }
}

/// The spec's record of a valid transaction reads as that transaction.
proof fn lemma_record_read(file: Seq<u8>, pos: nat, c: nat, e: Seq<crate::log::spec::Op>)
    requires
        crate::log::spec::transaction_ok(c + 1, e),
        pos + crate::log::spec::encode_record(c + 1, e).len() <= file.len(),
        file.subrange(pos as int, (pos + crate::log::spec::encode_record(c + 1, e).len()) as int) == crate::log::spec::encode_record(c + 1, e),
    ensures
        i_record(file, pos, c) matches Some((r, next)) && r.commit == c + 1 && e_ops(r.ops) == e && next == pos + crate::log::spec::encode_record(c + 1, e).len(),
{
    clazel_der::lemmas::lemma_pow256_8();
    let commit = c + 1;
    let body = crate::log::spec::record_body(commit, e);
    let crc = crate::crc32c::spec::crc32c(body);
    let check = clazel_der::spec::encode_octet_string(crc);
    let n = crate::log::spec::encode_number(commit);
    let oss = clazel_der::spec::encode_sequence(crate::log::spec::encode_ops(e));
    let rec = crate::log::spec::encode_record(commit, e);
    let contents = body + check;
    let seq_tag = clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE);
    crate::log::lemmas::lemma_transaction_ok_bounds(commit, e);
    crate::log::lemmas::lemma_tlv_len(seq_tag, contents);
    clazel_der::lemmas_tlv::lemma_read_tlv_encode_tlv(seq_tag, contents, file, pos, file.len());
    let t = clazel_der::spec::read_tlv(file, pos, file.len()).unwrap();
    let (cs, ce) = (t.cstart, t.cend);
    assert(rec.len() == clazel_der::spec::encode_identifier(seq_tag).len() + clazel_der::spec::encode_length(contents.len()).len() + contents.len());
    assert(ce == pos + rec.len());
    assert(file.subrange(cs as int, ce as int) == contents);
    assert(contents =~= n + (oss + check));
    lemma_e_split(file, cs, n, oss + check);
    let p1 = cs + n.len();
    lemma_e_split(file, p1, oss, check);
    lemma_number_read(commit, file, cs, ce, i_commit_limit());
    clazel_der::lemmas_typed::lemma_expect_sequence_encode_sequence(crate::log::spec::encode_ops(e), file, p1, ce);
    clazel_der::lemmas::lemma_read_tlv_bounds(file, p1, ce);
    let (os, oe) = clazel_der::spec::expect_sequence(file, p1, ce).unwrap();
    assert(oe == p1 + oss.len());
    lemma_ops_read(e, file, os, oe);
    let ops = i_ops(file, os, oe).unwrap();
    lemma_octets_read(crc, file, oe, ce);
    lemma_e_join(file, cs, p1, oe);
    assert(file.subrange(cs as int, oe as int) == body);
    theorem_crc32c_equiv(body);
    assert(crc.len() == 4);
    assert(oe + check.len() == ce);
}

/// When a longer list fits, its next transaction is valid and its record
/// follows the log so far.
proof fn lemma_e_next_record(identity: Seq<u8>, file: Seq<u8>, done: Seq<Seq<crate::log::spec::Op>>, w: Seq<Seq<crate::log::spec::Op>>)
    requires
        crate::log::spec::fits(identity, file, done),
        crate::log::spec::fits(identity, file, w),
        w.len() > done.len(),
    ensures
        crate::log::spec::transaction_ok(done.len() + 1, w[done.len() as int]),
        crate::log::spec::encode_log(identity, done).len() + crate::log::spec::encode_record(done.len() + 1, w[done.len() as int]).len() <= file.len(),
        file.subrange(crate::log::spec::encode_log(identity, done).len() as int, (crate::log::spec::encode_log(identity, done).len() + crate::log::spec::encode_record(done.len() + 1, w[done.len() as int]).len()) as int) == crate::log::spec::encode_record(done.len() + 1, w[done.len() as int]),
{
    let k = done.len();
    crate::log::lemmas::lemma_fits_agree(identity, file, w, done);
    crate::log::lemmas::lemma_fits_take(identity, file, w, k + 1);
    let wk = w.take((k + 1) as int);
    assert(wk.drop_last() =~= w.take(k as int));
    let e = w[k as int];
    assert(wk.last() == e);
    let head = crate::log::spec::encode_log(identity, done);
    let rec = crate::log::spec::encode_record(k + 1, e);
    assert(wk.len() == k + 1);
    assert(crate::log::spec::encode_log(identity, wk) == head + rec);
    assert(crate::log::spec::transaction_ok(k + 1, wk[k as int]));
    assert(file.subrange(0, (head + rec).len() as int) =~= head + rec);
    assert(file.subrange(0, (0 + head.len() + rec.len()) as int) == head + rec);
    lemma_e_split(file, 0, head, rec);
}

/// A valid next transaction whose record follows the log extends what fits.
proof fn lemma_e_extend(identity: Seq<u8>, file: Seq<u8>, done: Seq<Seq<crate::log::spec::Op>>, x: Seq<crate::log::spec::Op>, next: nat)
    requires
        crate::log::spec::fits(identity, file, done),
        crate::log::spec::transaction_ok(done.len() + 1, x),
        crate::log::spec::encode_log(identity, done).len() <= next,
        next <= file.len(),
        file.subrange(crate::log::spec::encode_log(identity, done).len() as int, next as int) == crate::log::spec::encode_record(done.len() + 1, x),
    ensures
        crate::log::spec::fits(identity, file, done.push(x)),
        next == crate::log::spec::encode_log(identity, done.push(x)).len(),
{
    let now = done.push(x);
    let head = crate::log::spec::encode_log(identity, done);
    let rec = crate::log::spec::encode_record(done.len() + 1, x);
    assert(now.drop_last() =~= done);
    assert(crate::log::spec::encode_log(identity, now) == head + rec);
    assert(file.subrange(0, head.len() as int) =~= head);
    assert(file.subrange(0, next as int) =~= head + rec);
    assert forall|i: int| 0 <= i < now.len() implies crate::log::spec::transaction_ok((i + 1) as nat, #[trigger] now[i]) by {
        if i < done.len() {
            assert(now[i] == done[i]);
        }
    }
}

/// From a list that fits, the parser finds the rest of the longest one, and
/// numbers its commits on from where it is.
proof fn lemma_records(identity: Seq<u8>, file: Seq<u8>, done: Seq<Seq<crate::log::spec::Op>>)
    requires
        crate::log::spec::fits(identity, file, done),
    ensures
        ({
            let v = i_records(file, crate::log::spec::encode_log(identity, done).len(), done.len());
            &&& crate::log::spec::longest_fit(identity, file, done + e_log(v))
            &&& forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).commit == done.len() + 1 + i
        }),
    decreases file.len() - crate::log::spec::encode_log(identity, done).len(),
{
    let pos = crate::log::spec::encode_log(identity, done).len();
    let c = done.len();
    let v = i_records(file, pos, c);
    lemma_record_encode(file, pos, c);
    let stops = pos >= file.len() || i_record(file, pos, c) is None;
    if stops {
        assert(v =~= Seq::<IRecord>::empty());
        assert(done + e_log(v) =~= done);
        assert forall|u: Seq<Seq<crate::log::spec::Op>>| #[trigger] crate::log::spec::fits(identity, file, u) implies u.len() <= done.len() by {
            if u.len() > done.len() {
                lemma_e_next_record(identity, file, done, u);
                let e = u[c as int];
                let body = crate::log::spec::record_body(c + 1, e);
                crate::log::lemmas::lemma_tlv_len(
                    clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE),
                    body + clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(body)),
                );
                lemma_record_read(file, pos, c, e);
            }
        }
    } else {
        let (r, next) = i_record(file, pos, c).unwrap();
        let x = e_ops(r.ops);
        lemma_e_extend(identity, file, done, x, next);
        let now = done.push(x);
        assert(now.len() == c + 1);
        lemma_records(identity, file, now);
        let rest = i_records(file, next, r.commit);
        assert(v == seq![r] + rest);
        assert(e_log(v) =~= seq![x] + e_log(rest)) by {
            assert forall|i: int| 0 <= i < v.len() implies #[trigger] e_log(v)[i] == (seq![x] + e_log(rest))[i] by {
                if i > 0 {
                    assert(v[i] == rest[i - 1]);
                }
            }
        }
        assert(done + e_log(v) =~= now + e_log(rest));
        assert forall|i: int| 0 <= i < v.len() implies (#[trigger] v[i]).commit == c + 1 + i by {
            if i > 0 {
                assert(v[i] == rest[i - 1]);
            }
        }
    }
}

/// A header this file read is the spec's header of the identity.
proof fn lemma_header_encode(identity: Seq<u8>, file: Seq<u8>)
    ensures
        i_header(identity, file) matches Some(start) ==> crate::log::spec::identity_ok(identity) && crate::log::spec::encode_header(identity).is_prefix_of(file) && start == crate::log::spec::encode_header(identity).len(),
{
    clazel_der::lemmas::lemma_pow256_8();
    let len = file.len();
    clazel_der::lemmas_typed::lemma_encode_sequence_expect_sequence(file, 0, len);
    clazel_der::lemmas::lemma_read_tlv_bounds(file, 0, len);
    if let Some(start) = i_header(identity, file) {
        let (cs, ce) = clazel_der::spec::expect_sequence(file, 0, len).unwrap();
        lemma_octets_encode(file, cs, ce);
        let (magic, p1) = i_octets(file, cs, ce).unwrap();
        lemma_number_encode(file, p1, ce, 2);
        let (version, p2) = i_number(file, p1, ce, 2).unwrap();
        lemma_octets_encode(file, p2, ce);
        let (named, p3) = i_octets(file, p2, ce).unwrap();
        assert(magic == crate::log::spec::magic()) by {
            assert(i_magic() =~= crate::log::spec::magic());
        }
        lemma_e_join(file, cs, p1, ce);
        lemma_e_join(file, p1, p2, ce);
        let (a, b, d) = (clazel_der::spec::encode_octet_string(crate::log::spec::magic()), crate::log::spec::encode_number(crate::log::spec::version()), clazel_der::spec::encode_octet_string(identity));
        assert(file.subrange(cs as int, ce as int) =~= a + b + d);
        assert(file.subrange(0, ce as int) == crate::log::spec::encode_header(identity));
        assert(crate::log::spec::encode_header(identity).is_prefix_of(file));
    }
}

/// A header's contents are short, for a valid identity.
proof fn lemma_header_contents_len(identity: Seq<u8>)
    requires
        crate::log::spec::identity_ok(identity),
    ensures
        (clazel_der::spec::encode_octet_string(crate::log::spec::magic()) + crate::log::spec::encode_number(crate::log::spec::version()) + clazel_der::spec::encode_octet_string(identity)).len() < clazel_der::spec::pow256(8),
        crate::log::spec::encode_header(identity) == clazel_der::spec::encode_sequence(clazel_der::spec::encode_octet_string(crate::log::spec::magic()) + crate::log::spec::encode_number(crate::log::spec::version()) + clazel_der::spec::encode_octet_string(identity)),
{
    clazel_der::lemmas::lemma_pow256_8();
    let (um, uo) = (clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), clazel_der::spec::universal_primitive(clazel_der::spec::INTEGER));
    let m = clazel_der::spec::be_bytes(crate::log::spec::version(), 8);
    assert(crate::log::spec::magic().len() == 12);
    clazel_der::lemmas::lemma_encode_tlv_len(um, crate::log::spec::magic());
    clazel_der::lemmas::lemma_encode_tlv_len(um, identity);
    clazel_der::lemmas::lemma_be_bytes_len(crate::log::spec::version(), 8);
    clazel_der::lemmas_typed::lemma_integer_unsigned_contents(m);
    clazel_der::lemmas::lemma_encode_tlv_len(uo, clazel_der::spec::integer_unsigned_contents(m));
}

/// The contents of the spec's header, read field by field.
proof fn lemma_header_fields(identity: Seq<u8>, file: Seq<u8>, cs: nat, ce: nat)
    requires
        crate::log::spec::identity_ok(identity),
        ce <= file.len(),
        cs + (clazel_der::spec::encode_octet_string(crate::log::spec::magic()) + crate::log::spec::encode_number(crate::log::spec::version()) + clazel_der::spec::encode_octet_string(identity)).len() == ce,
        file.subrange(cs as int, ce as int) == clazel_der::spec::encode_octet_string(crate::log::spec::magic()) + crate::log::spec::encode_number(crate::log::spec::version()) + clazel_der::spec::encode_octet_string(identity),
    ensures
        i_octets(file, cs, ce) == Some((crate::log::spec::magic(), cs + clazel_der::spec::encode_octet_string(crate::log::spec::magic()).len())),
        i_number(file, cs + clazel_der::spec::encode_octet_string(crate::log::spec::magic()).len(), ce, 2) == Some((1nat, cs + clazel_der::spec::encode_octet_string(crate::log::spec::magic()).len() + crate::log::spec::encode_number(crate::log::spec::version()).len())),
        i_octets(file, cs + clazel_der::spec::encode_octet_string(crate::log::spec::magic()).len() + crate::log::spec::encode_number(crate::log::spec::version()).len(), ce) == Some((identity, ce)),
{
    clazel_der::lemmas::lemma_pow256_8();
    let (a, b, d) = (clazel_der::spec::encode_octet_string(crate::log::spec::magic()), crate::log::spec::encode_number(crate::log::spec::version()), clazel_der::spec::encode_octet_string(identity));
    assert(crate::log::spec::magic().len() == 12);
    assert(a + b + d =~= a + (b + d));
    lemma_e_split(file, cs, a, b + d);
    lemma_e_split(file, cs + a.len(), b, d);
    lemma_octets_read(crate::log::spec::magic(), file, cs, ce);
    lemma_number_read(crate::log::spec::version(), file, cs + a.len(), ce, 2);
    lemma_octets_read(identity, file, cs + a.len() + b.len(), ce);
}

/// The spec's header of a valid identity reads as that identity.
proof fn lemma_header_read(identity: Seq<u8>, file: Seq<u8>)
    requires
        crate::log::spec::identity_ok(identity),
        crate::log::spec::encode_header(identity).is_prefix_of(file),
    ensures
        i_header(identity, file) == Some(crate::log::spec::encode_header(identity).len()),
{
    let contents = clazel_der::spec::encode_octet_string(crate::log::spec::magic()) + crate::log::spec::encode_number(crate::log::spec::version()) + clazel_der::spec::encode_octet_string(identity);
    let hdr = crate::log::spec::encode_header(identity);
    lemma_header_contents_len(identity);
    assert(file.subrange(0, hdr.len() as int) =~= hdr);
    clazel_der::lemmas_typed::lemma_expect_sequence_encode_sequence(contents, file, 0, file.len());
    let (cs, ce) = clazel_der::spec::expect_sequence(file, 0, file.len()).unwrap();
    clazel_der::lemmas::lemma_read_tlv_bounds(file, 0, file.len());
    assert(ce == hdr.len());
    assert(cs + contents.len() == ce);
    lemma_header_fields(identity, file, cs, ce);
    assert(i_magic() =~= crate::log::spec::magic());
}

/// The parser's recovery is the spec's, for every identity and file: it
/// refuses what the spec refuses, otherwise gives the spec's transactions, and
/// the records it read number their commits 1, 2, 3, ...
pub proof fn theorem_recovery_equiv(identity: Seq<u8>, file: Seq<u8>)
    ensures
        e_recovery(i_recover(identity, file)) == crate::log::spec::recovered(identity, file),
        i_recover(identity, file) matches Some(v) ==> forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).commit == i + 1,
{
    lemma_header_encode(identity, file);
    if crate::log::spec::identity_ok(identity) && crate::log::spec::encode_header(identity).is_prefix_of(file) {
        lemma_header_read(identity, file);
        let e = Seq::<Seq<crate::log::spec::Op>>::empty();
        assert(crate::log::spec::encode_log(identity, e) == crate::log::spec::encode_header(identity));
        assert(crate::log::spec::fits(identity, file, e));
        lemma_records(identity, file, e);
        let v = i_records(file, crate::log::spec::encode_header(identity).len(), 0);
        assert(e + e_log(v) =~= e_log(v));
        crate::log::lemmas::lemma_longest_fit_unique(identity, file, e_log(v));
    }
}

} // verus!
