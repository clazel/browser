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
//!   from this task's statement of the entry, and the Guide's algorithm from
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
//! no definition here changed after that. Nothing else of this crate was
//! opened until the definitions were committed on their own. The equivalence
//! lemmas at the end necessarily name the spec's functions, and only they do.
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
//!   Guide nor the catalogue says: this task's statement of `crc32c` gives it.
//! - Recovery is a parser, front to back. A record is read with `clazel-der`'s
//!   readers, its check compared, its commit compared with the one before.
//!   Nothing here mentions encoding a record or a prefix of the file.
//!
//! ## How the design note was read, where it leaves something open
//!
//! - "The `check` field covers the record's other contents": the check is over
//!   the octets of the `commit` and `ops` encodings, the record's contents
//!   before the `check` encoding.
//! - "`commit` increases by exactly 1 from record to record": the first record
//!   after the header may carry any commit below 2^64. The note states no
//!   first number.
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
pub open spec fn i_record(file: Seq<u8>, pos: nat, previous: Option<nat>) -> Option<(IRecord, nat)> {
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
                                    } else if previous.is_some() && commit != previous.unwrap() + 1 {
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
proof fn i_records_terminates(file: Seq<u8>, pos: nat, previous: Option<nat>) {
    clazel_der::lemmas::lemma_read_tlv_bounds(file, pos, file.len());
}

/// "The longest run of records ... It stops at the first record that fails
/// any of these." `pos` is where the next record would start.
pub open spec fn i_records(file: Seq<u8>, pos: nat, previous: Option<nat>) -> Seq<IRecord>
    decreases file.len() - pos,
        via i_records_terminates
{
    if pos >= file.len() {
        Seq::empty()
    } else {
        match i_record(file, pos, previous) {
            None => Seq::empty(),
            Some((record, next)) => seq![record] + i_records(file, next, Some(record.commit)),
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
        Some(start) => Some(i_records(file, start, None)),
    }
}

} // verus!
