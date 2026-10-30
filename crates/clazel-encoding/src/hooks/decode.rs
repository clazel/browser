//! The executable "BOM sniff" and "decode" hooks, proven to meet
//! [`super::contract`]. Step comments live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::labels::spec::Encoding;

verus! {

/// "BOM sniff" (Encoding §6): the encoding of a leading byte order mark,
/// or `None`.
pub fn bom_sniff(input: &[u8]) -> (r: Option<Encoding>)
    ensures
        super::contract::bom_sniff_ensures(input@, r),
{
    let ghost bom = input@.subrange(0, if input@.len() < 3 { input@.len() as int } else { 3 });
    let b0 = match input.first() {
        Some(b) => *b as u32,
        None => 0x100,
    };
    let b1 = match input.get(1) {
        Some(b) => *b as u32,
        None => 0x100,
    };
    let b2 = match input.get(2) {
        Some(b) => *b as u32,
        None => 0x100,
    };
    proof {
        if input@.len() >= 3 {
            assert(bom.subrange(0, 3) =~= seq![input@[0], input@[1], input@[2]]);
        }
        if input@.len() >= 2 {
            assert(bom.subrange(0, 2) =~= seq![input@[0], input@[1]]);
        }
        if b0 == 0xEF && b1 == 0xBB && b2 == 0xBF {
            assert(starts_with(bom, seq![0xEFu8, 0xBBu8, 0xBFu8]));
        } else if input@.len() >= 3 {
            assert(!starts_with(bom, seq![0xEFu8, 0xBBu8, 0xBFu8]) || bom.subrange(0, 3)[0] == 0xEF);
        }
    }
    if b0 == 0xEF && b1 == 0xBB && b2 == 0xBF {
        Some(Encoding::Utf8)
    } else if b0 == 0xFE && b1 == 0xFF {
        Some(Encoding::Utf16Be)
    } else if b0 == 0xFF && b1 == 0xFE {
        Some(Encoding::Utf16Le)
    } else {
        None
    }
}

/// Whether this crate ships `e`'s decoder.
pub fn has_decoder_exec(e: Encoding) -> (r: bool)
    ensures
        r == has_decoder(e),
{
    !matches!(
        e,
        Encoding::Gbk | Encoding::Gb18030 | Encoding::Big5 | Encoding::EucJp | Encoding::Iso2022Jp
            | Encoding::ShiftJis | Encoding::EucKr
    )
}

/// "Process a queue with an instance of encoding's decoder" in
/// "replacement" mode, for an encoding with a decoder here.
fn run_decoder_exec(e: Encoding, input: &[u8]) -> (out: Vec<u32>)
    requires
        has_decoder(e),
    ensures
        out@ == run_decoder(e, input@),
{
    match e {
        Encoding::Utf8 => crate::utf8::decode::decode_without_bom(input),
        Encoding::Replacement => crate::replacement::decode::decode(input),
        Encoding::Utf16Be => crate::utf16::decode::decode(true, input),
        Encoding::Utf16Le => crate::utf16::decode::decode(false, input),
        Encoding::XUserDefined => crate::x_user_defined::decode::decode(input),
        _ => crate::single_byte::decode::decode(e, input),
    }
}

/// "Decode" (Encoding §6) `input` with the fallback encoding `encoding`: a
/// byte order mark wins, then the encoding's decoder runs in "replacement"
/// mode. `None` when that encoding's decoder is not in this crate (the
/// multi-byte encodings, Phase 4 item 4.4).
pub fn decode(input: &[u8], encoding: Encoding) -> (out: Option<Vec<u32>>)
    ensures
        super::contract::decode_ensures(
            input@,
            encoding,
            match out {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    let (encoding, rest) = match bom_sniff(input) {
        Some(bom) => {
            let skip: usize = match bom {
                Encoding::Utf8 => 3,
                _ => 2,
            };
            match input.split_at_checked(skip) {
                Some((_, rest)) => {
                    assert(rest@ =~= input@.subrange(skip as int, input@.len() as int));
                    (bom, rest)
                },
                // Unreachable: a byte order mark is that long.
                None => (bom, input),
            }
        },
        None => (encoding, input),
    };
    if has_decoder_exec(encoding) {
        Some(run_decoder_exec(encoding, rest))
    } else {
        None
    }
}

} // verus!
