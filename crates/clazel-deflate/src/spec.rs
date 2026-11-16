//! Executable-style specification of DEFLATE and zlib decoding, transcribed
//! from RFC 1951 "DEFLATE Compressed Data Format Specification version 1.3"
//! (<https://www.rfc-editor.org/rfc/rfc1951>) and RFC 1950 "ZLIB Compressed
//! Data Format Specification version 3.3"
//! (<https://www.rfc-editor.org/rfc/rfc1950>), both May 1996. RFCs do not
//! change, so the pin is the number; the plain-text files this was read from
//! have the SHA-256 sums in `lib.rs`. Nothing here runs; it defines what
//! "correct" means. Each `// N.` or section comment cites the RFC section
//! (and the list item or line of pseudo-code) it transcribes.
//!
//! RFC 1952 (gzip) is not here: phase-6.md decision 6.0(h) takes it later.
//!
//! Modelling choices (each a deliberate, reviewable deviation in form; the
//! ones marked **choice** are places where the RFC is silent or ambiguous and
//! this spec decides):
//!
//! - The input is `Seq<u8>`, the whole compressed stream, and the output is
//!   a `Seq<u8>`. A decoder that is given the input in pieces is not part of
//!   this spec: it is correct if, for every way of cutting the input into
//!   chunks, its output and its final error equal this function's on the
//!   concatenation (`contract::chunked_ensures`).
//! - **Bit positions.** RFC 1951 §3.1.1: "Data elements are packed into bytes
//!   in order of increasing bit number within the byte, i.e., starting with
//!   the least-significant bit of the byte." The bit stream is therefore
//!   [`bit_at`]`(input, pos)` for `pos = 0, 1, ...`, bit `pos % 8` of byte
//!   `pos / 8`, counted from the least significant bit. "Data elements other
//!   than Huffman codes are packed starting with the least-significant bit of
//!   the data element": [`bits_value`] makes the first bit read the least
//!   significant. "Huffman codes are packed starting with the most-
//!   significant bit of the code": [`decode_symbol`] makes the first bit read
//!   the most significant of the code.
//! - **Extra bits** (§3.2.5: "The extra bits should be interpreted as a
//!   machine integer stored with the most-significant bit first, e.g., bits
//!   1110 represent the value 14"): read as every other non-Huffman data
//!   element, least significant bit first (§3.1.1), which is what zlib and
//!   every other decoder do. The sentence read literally contradicts §3.1.1;
//!   `docs/ERRATA.md` has the entry.
//! - **Errors.** The RFC says "(error)" for a reserved block type and is
//!   silent about the rest of what a decoder must refuse. [`Error`] lists
//!   every way this spec fails. A stream that ends early is [`Error::Truncated`],
//!   whichever element it ends in. A Huffman code is "Truncated" if the input
//!   ends before a code matched and fewer than 15 bits were read (so a stream
//!   cut inside an invalid code is Truncated, not InvalidCode: whether a code
//!   is invalid is only known after 15 bits).
//! - **Which error comes first** is the order of the RFC's own algorithm
//!   (the order a one-pass decoder meets them), then, where the RFC says
//!   nothing, the order of the checks in zlib's `inflate.c` (version 1.3.1).
//!   Only the order, never whether a stream is accepted, depends on that.
//! - **Prefix codes that are not complete (choice).** §3.2.2 defines the
//!   code of every symbol from the code lengths, and §3.2.7 says "If only one
//!   distance code is used, it is encoded using one bit, not zero bits; in
//!   this case there is a single code length of one, with one unused code.
//!   One distance code of zero bits means that there are no distance codes
//!   used at all". The RFC does not say what to do with a set of lengths that
//!   over-subscribes the code space or leaves part of it unused. This spec
//!   follows zlib: [`code_usable`] accepts a set of lengths only if it is
//!   complete (the code space of 15 bits is exactly filled: Kraft's sum is
//!   1), or, for the literal/length and distance codes only, it has no code
//!   at all, or exactly one code of length 1. Anything else is
//!   [`Error::BadCodeLengths`]. The code-length code (§3.2.7's 19-symbol
//!   alphabet) must be complete.
//! - **HLIT and HDIST (choice).** §3.2.7 gives "HLIT ... (257 - 286)" and
//!   "HDIST ... (1 - 32)". The 5-bit field can say 287 or 288 for HLIT;
//!   those are [`Error::TooManyLengthCodes`] (the field's range is the RFC's
//!   own). HDIST up to 32 is accepted, as the RFC says; distance symbols 30
//!   and 31 can be given a length, and decoding one is
//!   [`Error::InvalidDistanceSymbol`] (§3.2.6: "distance codes 30-31 will never
//!   actually occur in the compressed data"). zlib refuses HDIST above 30
//!   up front; the difference is a stream that names such symbols but never
//!   uses them.
//! - **The end-of-block code (choice).** §3.2.7 says the block holds "The
//!   literal/length symbol 256 (end of data), encoded using the literal/
//!   length Huffman code"; a dynamic block whose code gives symbol 256 no
//!   length can never end, so it is [`Error::NoEndOfBlock`] at its header
//!   (zlib's "invalid code -- missing end-of-block").
//! - **The output limit** is the parameter `limit`: a decoder that would make
//!   the output longer than `limit` fails with [`Error::OutputLimit`] instead.
//!   It is a stated error, not a deviation: with `limit` at least the true
//!   output length the result is the RFC's. A stored block's `LEN` is checked
//!   against the limit as soon as `LEN` and `NLEN` agree, before the data is
//!   read; a literal or a match is checked when it is decoded.
//! - **The window.** §3.2.3 says a distance "cannot refer past the beginning
//!   of the output stream", and §3.2.5's largest distance is 32,768. There is
//!   no separate window in the spec: [`Error::DistanceTooFar`] is a distance
//!   greater than the whole output so far. An implementation keeps only the
//!   last 32,768 bytes, which is enough because no distance is larger.
//! - **A preset dictionary (choice).** RFC 1950 §2.2 allows `FDICT`; §2.3
//!   says a decompressor "must give an error indication if FDICT is set and
//!   DICTID is not the identifier of a known dictionary". This decoder knows
//!   none, so `FDICT` is [`Error::PresetDictionary`] (phase-6.md: "FDICT
//!   refused").
//! - **Termination by fuel.** A block consumes at least 3 bits and a Huffman
//!   symbol at least 1, so every loop below ends when the input does. Verus
//!   needs a measure it can see, so the loops carry `fuel`, started at the
//!   number of bits in the input and decreased by one at each iteration.
//!   When `fuel` is 0 no input bit is left, and the step that would follow
//!   fails with `Truncated` anyway, so the `fuel == 0` branches return that.
//!   `lemmas::lemma_fuel_sufficient` is the statement that fuel never changes
//!   a result; see the README for whether it is proven.
//! - **Stored blocks (§3.2.4).** "Any bits of input up to the next byte
//!   boundary are ignored" is `(pos + 7) / 8`, the index of the next byte.
//!   "NLEN is the one's complement of LEN" is `LEN + NLEN == 65535` (two
//!   16-bit numbers).
//! - **The canonical code (§3.2.2).** The algorithm's three steps are
//!   [`bl_count`], [`next_code`] and [`code_of`]. Step 3's loop assigns
//!   `next_code[len]` and increments it once per symbol with that length, in
//!   symbol order; the code of symbol `n` is therefore `next_code[len]` plus
//!   the number of symbols before `n` with the same length, which is what
//!   [`code_of`] states (`count_eq` over the first `n` symbols). The
//!   decoder reads a code one bit at a time, most significant first, and
//!   stops at the first length for which some symbol has exactly that code.
//!   The spec does not need a tree: for a usable code the first match is the
//!   only one (`lemmas` proves it where it does).
//! - RFC 1950 §2.1: "All multi-byte numbers in the format described here are
//!   stored with the MOST-significant byte first". Adler-32 (§2.2, §8.2) is
//!   [`adler_sums`], the sums of §2.2's "ADLER32" paragraph, one byte at a
//!   time.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `2^n` (vstd's, so its lemmas apply).
pub open spec fn pow2(n: nat) -> nat {
    vstd::arithmetic::power2::pow2(n)
}

// ---------------------------------------------------------------------------
// Errors.
// ---------------------------------------------------------------------------

/// Everything the decoder can refuse. The order of the variants is not
/// meaningful.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Error {
    /// The input ended inside an element (any element).
    Truncated,
    /// §3.2.3: "11 - reserved (error)".
    ReservedBlockType,
    /// §3.2.4: `NLEN` is not the one's complement of `LEN`.
    LengthComplementMismatch,
    /// §3.2.7: HLIT (the field plus 257) is above 286.
    TooManyLengthCodes,
    /// A set of code lengths that [`code_usable`] refuses (see the header).
    BadCodeLengths,
    /// §3.2.7: a dynamic block gives symbol 256 no code.
    NoEndOfBlock,
    /// §3.2.7: code 16 ("copy the previous code length") with no code
    /// length before it.
    RepeatWithoutPrevious,
    /// §3.2.7: a repeat that runs past HLIT + HDIST code lengths.
    RepeatTooLong,
    /// No symbol has the code read (15 bits that match no code).
    InvalidCode,
    /// §3.2.6: literal/length symbols 286 and 287 "will never actually occur".
    InvalidSymbol,
    /// §3.2.6: distance symbols 30 and 31 "will never actually occur".
    InvalidDistanceSymbol,
    /// §3.2.3: "a distance cannot refer past the beginning of the output
    /// stream".
    DistanceTooFar,
    /// The output would be longer than the limit (header).
    OutputLimit,
    /// RFC 1950 §2.2: CMF and FLG are not a multiple of 31 (FCHECK).
    BadZlibCheck,
    /// RFC 1950 §2.3: CM is not 8.
    BadZlibMethod,
    /// RFC 1950 §2.2: "Values of CINFO above 7 are not allowed".
    BadZlibWindow,
    /// RFC 1950 §2.2 and §2.3: FDICT is set (header).
    PresetDictionary,
    /// RFC 1950 §2.2: the Adler-32 trailer is not that of the output.
    AdlerMismatch,
}

// ---------------------------------------------------------------------------
// §3.1.1 Packing into bytes: reading bits.
// ---------------------------------------------------------------------------

/// The number of bits in the input.
pub open spec fn bit_len(input: Seq<u8>) -> nat {
    input.len() * 8
}

/// Bit number `pos` of the stream: byte `pos / 8`, bit `pos % 8` counted
/// from the least significant (§3.1.1, "in order of increasing bit number
/// within the byte, i.e., starting with the least-significant bit").
pub open spec fn bit_at(input: Seq<u8>, pos: nat) -> nat
    recommends
        pos < bit_len(input),
{
    ((input[(pos / 8) as int] as nat) / pow2(pos % 8)) % 2
}

/// The number the `n` bits from `pos` spell when the first bit is the least
/// significant (§3.1.1, "Data elements other than Huffman codes are packed
/// starting with the least-significant bit of the data element").
pub open spec fn bits_value(input: Seq<u8>, pos: nat, n: nat) -> nat
    recommends
        pos + n <= bit_len(input),
    decreases n,
{
    if n == 0 {
        0
    } else {
        bit_at(input, pos) + 2 * bits_value(input, pos + 1, (n - 1) as nat)
    }
}

/// Read a data element of `n` bits at `pos`: its value and the next
/// position, or `None` if the input ends first.
pub open spec fn read_bits(input: Seq<u8>, pos: nat, n: nat) -> Option<(nat, nat)> {
    if pos + n > bit_len(input) {
        None
    } else {
        Some((bits_value(input, pos, n), pos + n))
    }
}

// ---------------------------------------------------------------------------
// §3.2.2 Use of Huffman coding in the "deflate" format.
// ---------------------------------------------------------------------------

/// The longest code length: `MAX_BITS` in §3.2.2's pseudo-code.
pub open spec fn max_bits() -> nat {
    15
}

/// The number of the first `n` symbols whose code length is `v`.
pub open spec fn count_eq(lens: Seq<nat>, v: nat, n: nat) -> nat
    recommends
        n <= lens.len(),
    decreases n,
{
    if n == 0 {
        0
    } else {
        count_eq(lens, v, (n - 1) as nat) + if lens[(n - 1) as int] == v {
            1nat
        } else {
            0nat
        }
    }
}

/// §3.2.2, step 1: "Count the number of codes for each code length. Let
/// bl_count[N] be the number of codes of length N, N >= 1." Step 2 also
/// says "bl_count[0] = 0", which the first branch is.
pub open spec fn bl_count(lens: Seq<nat>, bits: nat) -> nat {
    if bits == 0 {
        0
    } else {
        count_eq(lens, bits, lens.len())
    }
}

/// §3.2.2, step 2: "Find the numerical value of the smallest code for each
/// code length": `code = 0; bl_count[0] = 0; for (bits = 1; bits <=
/// MAX_BITS; bits++) { code = (code + bl_count[bits-1]) << 1;
/// next_code[bits] = code; }`. `code` before the loop is the value for
/// `bits == 0`; each iteration is one recursion step.
pub open spec fn next_code(lens: Seq<nat>, bits: nat) -> nat
    decreases bits,
{
    if bits == 0 {
        0
    } else {
        (next_code(lens, (bits - 1) as nat) + bl_count(lens, (bits - 1) as nat)) * 2
    }
}

/// §3.2.2, step 3: "Assign numerical values to all codes, using consecutive
/// values for all codes of the same length with the base values determined
/// at step 2. Codes that are never used (which have a bit length of zero)
/// must not be assigned a value." (`tree[n].Code = next_code[len];
/// next_code[len]++;`). The value `next_code[len]` has when the loop reaches
/// `n` is the step-2 value plus the symbols before `n` of the same length.
pub open spec fn code_of(lens: Seq<nat>, n: nat) -> nat
    recommends
        n < lens.len(),
        lens[n as int] != 0,
{
    next_code(lens, lens[n as int]) + count_eq(lens, lens[n as int], n)
}

/// The first symbol (from index `i`) of length `len` whose code is `code`.
pub open spec fn find_code(lens: Seq<nat>, len: nat, code: nat, i: nat) -> Option<nat>
    decreases lens.len() - i,
{
    if i >= lens.len() {
        None
    } else if lens[i as int] == len && code_of(lens, i) == code {
        Some(i)
    } else {
        find_code(lens, len, code, i + 1)
    }
}

/// The outcome of decoding one Huffman code.
pub enum Sym {
    /// The symbol, and the position after its code.
    Found(nat, nat),
    /// The input ended before a code matched, with fewer than 15 bits read.
    Truncated,
    /// 15 bits matched no code.
    Invalid,
}

/// Decode a symbol at `pos`: "Huffman codes are packed starting with the
/// most-significant bit of the code" (§3.1.1), so each bit read is appended
/// to the low end of `code`, and the symbol is the first (shortest) length at
/// which some symbol has that code (§3.2.2: "Shorter codes lexicographically
/// precede longer codes"). `len` bits have been read so far and spell
/// `code`. Called with `len == 0` and `code == 0`.
pub open spec fn decode_symbol(lens: Seq<nat>, input: Seq<u8>, pos: nat, len: nat, code: nat) -> Sym
    decreases 15 - (len as int),
{
    if len >= max_bits() {
        Sym::Invalid
    } else if pos >= bit_len(input) {
        Sym::Truncated
    } else {
        let c = code * 2 + bit_at(input, pos);
        match find_code(lens, len + 1, c, 0) {
            Some(s) => Sym::Found(s, pos + 1),
            None => decode_symbol(lens, input, pos + 1, len + 1, c),
        }
    }
}

/// Kraft's sum over lengths `1..=k`, scaled by `2^15`: a code of length `b`
/// takes `2^(15 - b)` of the `2^15` leaves of the code tree.
pub open spec fn kraft(lens: Seq<nat>, k: nat) -> nat
    recommends
        k <= 15,
    decreases k,
{
    if k == 0 {
        0
    } else {
        kraft(lens, (k - 1) as nat) + bl_count(lens, k) * pow2((15 - k) as nat)
    }
}

/// Every length is at most `MAX_BITS`.
pub open spec fn lengths_ok(lens: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < lens.len() ==> #[trigger] lens[i] <= max_bits()
}

/// The number of symbols that have a code.
pub open spec fn used(lens: Seq<nat>) -> nat {
    (lens.len() - count_eq(lens, 0, lens.len())) as nat
}

/// The set of lengths fills the code space exactly (a complete code).
pub open spec fn is_complete(lens: Seq<nat>) -> bool {
    kraft(lens, 15) == pow2(15)
}

/// The set of lengths is a usable code (see "Prefix codes that are not
/// complete" in the header): lengths at most 15, and complete, or, if
/// `allow_incomplete`, empty or a single code of length 1.
pub open spec fn code_usable(lens: Seq<nat>, allow_incomplete: bool) -> bool {
    lengths_ok(lens) && (is_complete(lens) || (allow_incomplete && (used(lens) == 0 || (used(lens)
        == 1 && bl_count(lens, 1) == 1))))
}

// ---------------------------------------------------------------------------
// §3.2.5 Compressed blocks (length and distance codes): the two tables.
// ---------------------------------------------------------------------------

/// The number of extra bits after literal/length code `code` (257 to 285),
/// from the first table of §3.2.5 ("Extra Bits"). 0 for anything else.
pub open spec fn len_extra(code: nat) -> nat {
    if 257 <= code && code <= 264 {
        0
    } else if 265 <= code && code <= 268 {
        1
    } else if 269 <= code && code <= 272 {
        2
    } else if 273 <= code && code <= 276 {
        3
    } else if 277 <= code && code <= 280 {
        4
    } else if 281 <= code && code <= 284 {
        5
    } else {
        0
    }
}

/// The smallest length of literal/length code `code` (257 to 285), the first
/// number in §3.2.5's "Length(s)" column. 0 for anything else.
pub open spec fn len_base(code: nat) -> nat {
    if code == 257 {
        3
    } else if code == 258 {
        4
    } else if code == 259 {
        5
    } else if code == 260 {
        6
    } else if code == 261 {
        7
    } else if code == 262 {
        8
    } else if code == 263 {
        9
    } else if code == 264 {
        10
    } else if code == 265 {
        11
    } else if code == 266 {
        13
    } else if code == 267 {
        15
    } else if code == 268 {
        17
    } else if code == 269 {
        19
    } else if code == 270 {
        23
    } else if code == 271 {
        27
    } else if code == 272 {
        31
    } else if code == 273 {
        35
    } else if code == 274 {
        43
    } else if code == 275 {
        51
    } else if code == 276 {
        59
    } else if code == 277 {
        67
    } else if code == 278 {
        83
    } else if code == 279 {
        99
    } else if code == 280 {
        115
    } else if code == 281 {
        131
    } else if code == 282 {
        163
    } else if code == 283 {
        195
    } else if code == 284 {
        227
    } else if code == 285 {
        258
    } else {
        0
    }
}

/// The number of extra bits after distance code `code` (0 to 29), from the
/// second table of §3.2.5. 0 for anything else.
pub open spec fn dist_extra(code: nat) -> nat {
    if code <= 3 {
        0
    } else if code <= 5 {
        1
    } else if code <= 7 {
        2
    } else if code <= 9 {
        3
    } else if code <= 11 {
        4
    } else if code <= 13 {
        5
    } else if code <= 15 {
        6
    } else if code <= 17 {
        7
    } else if code <= 19 {
        8
    } else if code <= 21 {
        9
    } else if code <= 23 {
        10
    } else if code <= 25 {
        11
    } else if code <= 27 {
        12
    } else if code <= 29 {
        13
    } else {
        0
    }
}

/// The smallest distance of distance code `code` (0 to 29), the first
/// number in §3.2.5's "Dist" column. 0 for anything else.
pub open spec fn dist_base(code: nat) -> nat {
    if code == 0 {
        1
    } else if code == 1 {
        2
    } else if code == 2 {
        3
    } else if code == 3 {
        4
    } else if code == 4 {
        5
    } else if code == 5 {
        7
    } else if code == 6 {
        9
    } else if code == 7 {
        13
    } else if code == 8 {
        17
    } else if code == 9 {
        25
    } else if code == 10 {
        33
    } else if code == 11 {
        49
    } else if code == 12 {
        65
    } else if code == 13 {
        97
    } else if code == 14 {
        129
    } else if code == 15 {
        193
    } else if code == 16 {
        257
    } else if code == 17 {
        385
    } else if code == 18 {
        513
    } else if code == 19 {
        769
    } else if code == 20 {
        1025
    } else if code == 21 {
        1537
    } else if code == 22 {
        2049
    } else if code == 23 {
        3073
    } else if code == 24 {
        4097
    } else if code == 25 {
        6145
    } else if code == 26 {
        8193
    } else if code == 27 {
        12289
    } else if code == 28 {
        16385
    } else if code == 29 {
        24577
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// §3.2.6 Compression with fixed Huffman codes (BTYPE=01).
// ---------------------------------------------------------------------------

/// The code length of literal/length symbol `sym` (0 to 287) in the fixed
/// code, §3.2.6's table: 0-143 8 bits, 144-255 9, 256-279 7, 280-287 8.
pub open spec fn fixed_lit_len(sym: nat) -> nat {
    if sym <= 143 {
        8
    } else if sym <= 255 {
        9
    } else if sym <= 279 {
        7
    } else {
        8
    }
}

/// The fixed literal/length code's 288 lengths ("Literal/length values
/// 286-287 will never actually occur in the compressed data, but participate
/// in the code construction").
pub open spec fn fixed_lit_lengths() -> Seq<nat> {
    Seq::new(288, |i: int| fixed_lit_len(i as nat))
}

/// §3.2.6: "Distance codes 0-31 are represented by (fixed-length) 5-bit
/// codes".
pub open spec fn fixed_dist_lengths() -> Seq<nat> {
    Seq::new(32, |i: int| 5nat)
}

// ---------------------------------------------------------------------------
// §3.2.3 Details of block format, the compressed-data loop.
// ---------------------------------------------------------------------------

/// "move backwards distance bytes in the output stream, and copy length
/// bytes from this position to the output stream" (§3.2.3), one byte at a
/// time so that "the referenced string may overlap the current position".
pub open spec fn lz_copy(out: Seq<u8>, distance: nat, length: nat) -> Seq<u8>
    recommends
        1 <= distance <= out.len(),
    decreases length,
{
    if length == 0 {
        out
    } else {
        lz_copy(out.push(out[out.len() - distance]), distance, (length - 1) as nat)
    }
}

/// The loop of §3.2.3 over the symbols of one compressed block ("loop (until
/// end of block code recognized) decode literal/length value from input
/// stream ..."), with the literal/length code `lit` and the distance code
/// `dist`. Returns the position after the end-of-block code and the output.
pub open spec fn data_loop(
    input: Seq<u8>,
    pos: nat,
    out: Seq<u8>,
    limit: nat,
    lit: Seq<nat>,
    dist: Seq<nat>,
    fuel: nat,
) -> Result<(nat, Seq<u8>), Error>
    decreases fuel,
{
    if fuel == 0 {
        Err(Error::Truncated)
    } else {
        match decode_symbol(lit, input, pos, 0, 0) {
            Sym::Truncated => Err(Error::Truncated),
            Sym::Invalid => Err(Error::InvalidCode),
            Sym::Found(sym, p1) => {
                if sym < 256 {
                    // "if value < 256 copy value (literal byte) to output stream"
                    if out.len() + 1 > limit {
                        Err(Error::OutputLimit)
                    } else {
                        data_loop(input, p1, out.push(sym as u8), limit, lit, dist, (fuel - 1) as nat)
                    }
                } else if sym == 256 {
                    // "if value = end of block (256) break from loop"
                    Ok((p1, out))
                } else if sym > 285 {
                    // 286 and 287 (§3.2.6).
                    Err(Error::InvalidSymbol)
                } else {
                    // "otherwise (value = 257..285) decode distance from input stream"
                    match read_bits(input, p1, len_extra(sym)) {
                        None => Err(Error::Truncated),
                        Some((e, p2)) => {
                            let length = len_base(sym) + e;
                            match decode_symbol(dist, input, p2, 0, 0) {
                                Sym::Truncated => Err(Error::Truncated),
                                Sym::Invalid => Err(Error::InvalidCode),
                                Sym::Found(d, p3) => {
                                    if d > 29 {
                                        Err(Error::InvalidDistanceSymbol)
                                    } else {
                                        match read_bits(input, p3, dist_extra(d)) {
                                            None => Err(Error::Truncated),
                                            Some((e2, p4)) => {
                                                let distance = dist_base(d) + e2;
                                                if distance > out.len() {
                                                    Err(Error::DistanceTooFar)
                                                } else if out.len() + length > limit {
                                                    Err(Error::OutputLimit)
                                                } else {
                                                    data_loop(
                                                        input,
                                                        p4,
                                                        lz_copy(out, distance, length),
                                                        limit,
                                                        lit,
                                                        dist,
                                                        (fuel - 1) as nat,
                                                    )
                                                }
                                            },
                                        }
                                    }
                                },
                            }
                        },
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// §3.2.4 Non-compressed blocks (BTYPE=00).
// ---------------------------------------------------------------------------

/// A stored block whose header ended at bit `pos`: "Any bits of input up to
/// the next byte boundary are ignored. The rest of the block consists of ...
/// LEN ... NLEN ... LEN bytes of literal data", with `LEN` and `NLEN` two
/// bytes each, least significant byte first (§3.1).
pub open spec fn stored_block(input: Seq<u8>, pos: nat, out: Seq<u8>, limit: nat) -> Result<
    (nat, Seq<u8>),
    Error,
> {
    let start = (pos + 7) / 8;
    if start + 4 > input.len() {
        Err(Error::Truncated)
    } else {
        let len = (input[start as int] as nat) + 256 * (input[(start + 1) as int] as nat);
        let nlen = (input[(start + 2) as int] as nat) + 256 * (input[(start + 3) as int] as nat);
        if len + nlen != 65535 {
            // "NLEN is the one's complement of LEN."
            Err(Error::LengthComplementMismatch)
        } else if out.len() + len > limit {
            Err(Error::OutputLimit)
        } else if start + 4 + len > input.len() {
            Err(Error::Truncated)
        } else {
            Ok(((start + 4 + len) * 8, out + input.subrange((start + 4) as int, (start + 4 + len) as int)))
        }
    }
}

// ---------------------------------------------------------------------------
// §3.2.7 Compression with dynamic Huffman codes (BTYPE=10).
// ---------------------------------------------------------------------------

/// "(HCLEN + 4) x 3 bits: code lengths for the code length alphabet given
/// just above, in the order: 16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3,
/// 13, 2, 14, 1, 15": the code-length symbol that the `i`-th of those
/// numbers is the length of.
pub open spec fn cl_order(i: nat) -> nat {
    if i == 0 {
        16
    } else if i == 1 {
        17
    } else if i == 2 {
        18
    } else if i == 3 {
        0
    } else if i == 4 {
        8
    } else if i == 5 {
        7
    } else if i == 6 {
        9
    } else if i == 7 {
        6
    } else if i == 8 {
        10
    } else if i == 9 {
        5
    } else if i == 10 {
        11
    } else if i == 11 {
        4
    } else if i == 12 {
        12
    } else if i == 13 {
        3
    } else if i == 14 {
        13
    } else if i == 15 {
        2
    } else if i == 16 {
        14
    } else if i == 17 {
        1
    } else {
        15
    }
}

/// Read `hclen` 3-bit code lengths (each "interpreted as 3-bit integers
/// (0-7)") into the 19-symbol code-length alphabet, the `i`-th for symbol
/// `cl_order(i)`; the others are 0 ("a code length of 0 means the
/// corresponding symbol ... is not used"). `i` of them are in `acc`.
pub open spec fn read_cl_lengths(input: Seq<u8>, pos: nat, hclen: nat, i: nat, acc: Seq<nat>) -> Option<
    (Seq<nat>, nat),
>
    decreases hclen - i,
{
    if i >= hclen {
        Some((acc, pos))
    } else {
        match read_bits(input, pos, 3) {
            None => None,
            Some((v, p)) => read_cl_lengths(input, p, hclen, i + 1, acc.update(cl_order(i) as int, v)),
        }
    }
}

/// `r` copies of `v`.
pub open spec fn repeat_len(v: nat, r: nat) -> Seq<nat> {
    Seq::new(r, |i: int| v)
}

/// "HLIT + 257 code lengths for the literal/length alphabet, encoded using
/// the code length Huffman code, HDIST + 1 code lengths for the distance
/// alphabet": all of them, `total` in number, as one sequence (§3.2.7: "all
/// code lengths form a single sequence of HLIT + HDIST + 258 values"; "The
/// code length repeat codes can cross from HLIT + 257 to the HDIST + 1 code
/// lengths"). `acc` is those read so far.
pub open spec fn read_lengths(
    cl: Seq<nat>,
    input: Seq<u8>,
    pos: nat,
    total: nat,
    acc: Seq<nat>,
    fuel: nat,
) -> Result<(Seq<nat>, nat), Error>
    decreases fuel,
{
    if acc.len() >= total {
        Ok((acc, pos))
    } else if fuel == 0 {
        Err(Error::Truncated)
    } else {
        match decode_symbol(cl, input, pos, 0, 0) {
            Sym::Truncated => Err(Error::Truncated),
            Sym::Invalid => Err(Error::InvalidCode),
            Sym::Found(sym, p1) => {
                if sym < 16 {
                    // "0 - 15: Represent code lengths of 0 - 15"
                    read_lengths(cl, input, p1, total, acc.push(sym), (fuel - 1) as nat)
                } else if sym == 16 {
                    // "16: Copy the previous code length 3 - 6 times. The next 2 bits
                    // indicate repeat length (0 = 3, ... , 3 = 6)"
                    if acc.len() == 0 {
                        Err(Error::RepeatWithoutPrevious)
                    } else {
                        match read_bits(input, p1, 2) {
                            None => Err(Error::Truncated),
                            Some((e, p2)) => {
                                if acc.len() + 3 + e > total {
                                    Err(Error::RepeatTooLong)
                                } else {
                                    read_lengths(
                                        cl,
                                        input,
                                        p2,
                                        total,
                                        acc + repeat_len(acc.last(), 3 + e),
                                        (fuel - 1) as nat,
                                    )
                                }
                            },
                        }
                    }
                } else if sym == 17 {
                    // "17: Repeat a code length of 0 for 3 - 10 times. (3 bits of length)"
                    match read_bits(input, p1, 3) {
                        None => Err(Error::Truncated),
                        Some((e, p2)) => {
                            if acc.len() + 3 + e > total {
                                Err(Error::RepeatTooLong)
                            } else {
                                read_lengths(cl, input, p2, total, acc + repeat_len(0, 3 + e), (fuel - 1) as nat)
                            }
                        },
                    }
                } else {
                    // "18: Repeat a code length of 0 for 11 - 138 times (7 bits of length)"
                    match read_bits(input, p1, 7) {
                        None => Err(Error::Truncated),
                        Some((e, p2)) => {
                            if acc.len() + 11 + e > total {
                                Err(Error::RepeatTooLong)
                            } else {
                                read_lengths(cl, input, p2, total, acc + repeat_len(0, 11 + e), (fuel - 1) as nat)
                            }
                        },
                    }
                }
            },
        }
    }
}

/// The header of a dynamic block, after BFINAL and BTYPE: HLIT, HDIST, HCLEN,
/// the code-length code, and the literal/length and distance code lengths.
/// Returns the two sets of lengths and the position after them.
pub open spec fn read_dynamic_tables(input: Seq<u8>, pos: nat) -> Result<(Seq<nat>, Seq<nat>, nat), Error> {
    match read_bits(input, pos, 5) {
        None => Err(Error::Truncated),
        Some((hlit_field, p1)) => match read_bits(input, p1, 5) {
            None => Err(Error::Truncated),
            Some((hdist_field, p2)) => match read_bits(input, p2, 4) {
                None => Err(Error::Truncated),
                Some((hclen_field, p3)) => {
                    // "5 Bits: HLIT, # of Literal/Length codes - 257 (257 - 286)", "5 Bits:
                    // HDIST, # of Distance codes - 1 (1 - 32)", "4 Bits: HCLEN, # of Code
                    // Length codes - 4 (4 - 19)".
                    let hlit = hlit_field + 257;
                    let hdist = hdist_field + 1;
                    let hclen = hclen_field + 4;
                    if hlit > 286 {
                        Err(Error::TooManyLengthCodes)
                    } else {
                        match read_cl_lengths(input, p3, hclen, 0, Seq::new(19, |i: int| 0nat)) {
                            None => Err(Error::Truncated),
                            Some((cl, p4)) => {
                                if !code_usable(cl, false) {
                                    Err(Error::BadCodeLengths)
                                } else {
                                    match read_lengths(cl, input, p4, hlit + hdist, Seq::empty(), bit_len(input)) {
                                        Err(e) => Err(e),
                                        Ok((all, p5)) => {
                                            let lit = all.subrange(0, hlit as int);
                                            let dist = all.subrange(hlit as int, (hlit + hdist) as int);
                                            if lit[256] == 0 {
                                                Err(Error::NoEndOfBlock)
                                            } else if !code_usable(lit, true) || !code_usable(dist, true) {
                                                Err(Error::BadCodeLengths)
                                            } else {
                                                Ok((lit, dist, p5))
                                            }
                                        },
                                    }
                                }
                            },
                        }
                    }
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// §3.2.3: the blocks, RFC 1951's top level.
// ---------------------------------------------------------------------------

/// The decoding algorithm of §3.2.3: "do read block header from input
/// stream. if stored with no compression ... otherwise if compressed with
/// dynamic Huffman codes read representation of code trees ... loop ...
/// while not last block", from bit `pos` with `out` already produced.
/// Returns the position after the last block and the whole output.
pub open spec fn inflate_blocks(input: Seq<u8>, pos: nat, out: Seq<u8>, limit: nat, fuel: nat) -> Result<
    (nat, Seq<u8>),
    Error,
>
    decreases fuel,
{
    if fuel == 0 {
        Err(Error::Truncated)
    } else {
        // "Each block of compressed data begins with 3 header bits: first bit
        // BFINAL, next 2 bits BTYPE".
        match read_bits(input, pos, 3) {
            None => Err(Error::Truncated),
            Some((header, p)) => {
                let bfinal = header % 2;
                let btype = header / 2;
                let block = if btype == 0 {
                    stored_block(input, p, out, limit)
                } else if btype == 1 {
                    data_loop(input, p, out, limit, fixed_lit_lengths(), fixed_dist_lengths(), bit_len(input))
                } else if btype == 2 {
                    match read_dynamic_tables(input, p) {
                        Err(e) => Err(e),
                        Ok((lit, dist, p2)) => data_loop(input, p2, out, limit, lit, dist, bit_len(input)),
                    }
                } else {
                    Err(Error::ReservedBlockType)
                };
                match block {
                    Err(e) => Err(e),
                    Ok((p2, out2)) => {
                        // "BFINAL is set if and only if this is the last block of the data set."
                        if bfinal == 1 {
                            Ok((p2, out2))
                        } else {
                            inflate_blocks(input, p2, out2, limit, (fuel - 1) as nat)
                        }
                    },
                }
            },
        }
    }
}

/// Decode a raw DEFLATE stream (RFC 1951): the output, and the number of
/// input bytes the stream occupies (the last byte may be only partly used:
/// bits after the last block's end are ignored).
pub open spec fn inflate(input: Seq<u8>, limit: nat) -> Result<(Seq<u8>, nat), Error> {
    match inflate_blocks(input, 0, Seq::empty(), limit, bit_len(input)) {
        Err(e) => Err(e),
        Ok((pos, out)) => Ok((out, (pos + 7) / 8)),
    }
}

// ---------------------------------------------------------------------------
// RFC 1950: zlib.
// ---------------------------------------------------------------------------

/// RFC 1950 §8.2, "The Adler-32 algorithm", and §2.2's "ADLER32" paragraph:
/// "Adler-32 is composed of two sums accumulated per byte: s1 is the sum of
/// all bytes, s2 is the sum of all s1 values. Both sums are done modulo
/// 65521. s1 is initialized to 1, s2 to zero." Returns `(s1, s2)`.
pub open spec fn adler_sums(data: Seq<u8>) -> (nat, nat)
    decreases data.len(),
{
    if data.len() == 0 {
        (1, 0)
    } else {
        let (s1, s2) = adler_sums(data.drop_last());
        let t1 = (s1 + data.last() as nat) % 65521;
        (t1, (s2 + t1) % 65521)
    }
}

/// "The Adler-32 checksum is stored as s2*65536 + s1".
pub open spec fn adler32(data: Seq<u8>) -> nat {
    adler_sums(data).1 * 65536 + adler_sums(data).0
}

/// A zlib stream (RFC 1950 §2.2): CMF, FLG, the DEFLATE data, ADLER32.
/// Returns the output and the number of input bytes the stream occupies
/// ("Any data which may appear after ADLER32 are not part of the zlib
/// stream").
pub open spec fn zlib_decompress(input: Seq<u8>, limit: nat) -> Result<(Seq<u8>, nat), Error> {
    if input.len() < 2 {
        Err(Error::Truncated)
    } else {
        let cmf = input[0] as nat;
        let flg = input[1] as nat;
        if (cmf * 256 + flg) % 31 != 0 {
            // "The FCHECK value must be such that CMF and FLG, when viewed as a
            // 16-bit unsigned integer stored in MSB order (CMF*256 + FLG), is a
            // multiple of 31."
            Err(Error::BadZlibCheck)
        } else if cmf % 16 != 8 {
            // "bits 0 to 3 CM": "CM = 8 denotes the "deflate" compression method".
            Err(Error::BadZlibMethod)
        } else if cmf / 16 > 7 {
            // "bits 4 to 7 CINFO": "Values of CINFO above 7 are not allowed".
            Err(Error::BadZlibWindow)
        } else if (flg / 32) % 2 == 1 {
            // "bit 5 FDICT"
            Err(Error::PresetDictionary)
        } else {
            match inflate(input.subrange(2, input.len() as int), limit) {
                Err(e) => Err(e),
                Ok((out, used_bytes)) => {
                    let end = 2 + used_bytes;
                    if end + 4 > input.len() {
                        Err(Error::Truncated)
                    } else {
                        // Most significant byte first (§2.1).
                        let stored = (input[end as int] as nat) * 16777216 + (input[(end + 1) as int] as nat)
                            * 65536 + (input[(end + 2) as int] as nat) * 256 + (input[(end + 3) as int] as nat);
                        if stored != adler32(out) {
                            Err(Error::AdlerMismatch)
                        } else {
                            Ok((out, end + 4))
                        }
                    }
                },
            }
        }
    }
}

} // verus!
