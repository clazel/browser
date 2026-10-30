//! The executable UTF-16BE/LE decoder, proven to meet
//! [`super::contract`].
//!
//! [`run_handler`] is the shared UTF-16 decoder's handler (§14.2.1) and
//! [`process_queue_exec`] "process a queue" (§4.1), each proven equal to
//! its spec function, so the step comments live in [`super::spec`]. The
//! decoder state is the spec's own [`Utf16Decoder`] (its fields are
//! machine types).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::utf8::spec::{HandlerResult, Item};

verus! {

/// (leading << 8) + byte, for two bytes.
fn combine(high: u8, low: u8) -> (r: u32)
    ensures
        r == (((high as u32) << 8u32) + low as u32) as u32,
{
    let r = ((high as u32) << 8u32) | (low as u32);
    proof {
        let h = high as u32;
        let l = low as u32;
        assert(h < 256 && l < 256 ==> (h << 8u32) | l == ((h << 8u32) + l) as u32) by (bit_vector);
    }
    r
}

/// Scalar value from surrogates, for a leading and a trailing surrogate.
fn from_surrogates(leading: u32, trailing: u32) -> (r: u32)
    requires
        is_leading_surrogate(leading),
        is_trailing_surrogate(trailing),
    ensures
        r == scalar_value_from_surrogates(leading, trailing),
{
    // Neither subtraction saturates (the ranges above), and the sum is at
    // most 0x10FFFF.
    let high = leading.saturating_sub(0xD800);
    let low = trailing.saturating_sub(0xDC00);
    proof {
        assert(high <= 0x3FF ==> high << 10u32 <= 0xFFC00) by (bit_vector);
    }
    0x10000u32.saturating_add(high << 10u32).saturating_add(low)
}

/// The shared UTF-16 decoder's handler. Returns the result and whether it
/// restored the two bytes it read.
fn run_handler(d: &mut Utf16Decoder, item: Item) -> (r: (HandlerResult, bool))
    requires
        super::lemmas::wf(*old(d)),
    ensures
        super::lemmas::wf(*final(d)),
        *final(d) == handler(*old(d), item).decoder,
        r.0 == handler(*old(d), item).result,
        r.1 == handler(*old(d), item).restored,
{
    let byte = match item {
        Item::EndOfQueue => {
            if d.leading_byte.is_some() || d.leading_surrogate.is_some() {
                d.leading_byte = None;
                d.leading_surrogate = None;
                return (HandlerResult::Error, false);
            } else {
                return (HandlerResult::Finished, false);
            }
        },
        Item::Byte(byte) => byte,
    };
    match d.leading_byte {
        None => {
            d.leading_byte = Some(byte);
            (HandlerResult::Continue, false)
        },
        Some(leading_byte) => {
            let code_unit = if d.is_utf16be {
                combine(leading_byte, byte)
            } else {
                combine(byte, leading_byte)
            };
            d.leading_byte = None;
            match d.leading_surrogate {
                Some(leading_surrogate) => {
                    d.leading_surrogate = None;
                    if (0xDC00..=0xDFFF).contains(&code_unit) {
                        (HandlerResult::CodePoint(from_surrogates(leading_surrogate, code_unit)), false)
                    } else {
                        (HandlerResult::Error, true)
                    }
                },
                None => {
                    if (0xD800..=0xDBFF).contains(&code_unit) {
                        d.leading_surrogate = Some(code_unit);
                        (HandlerResult::Continue, false)
                    } else if (0xDC00..=0xDFFF).contains(&code_unit) {
                        (HandlerResult::Error, false)
                    } else {
                        (HandlerResult::CodePoint(code_unit), false)
                    }
                },
            }
        },
    }
}

/// `prefix` followed by a successful output; failure stays failure.
spec fn prepend(prefix: Seq<u32>, rest: Option<Seq<u32>>) -> Option<Seq<u32>> {
    match rest {
        Some(out) => Some(prefix + out),
        None => None,
    }
}

proof fn lemma_prepend_cons(prefix: Seq<u32>, c: u32, rest: Option<Seq<u32>>)
    ensures
        prepend(prefix, crate::utf8::spec::cons(c, rest)) == prepend(prefix.push(c), rest),
{
    if let Some(out) = rest {
        assert(prefix + (seq![c] + out) =~= prefix.push(c) + out);
    }
}

/// The error mode as a flag.
spec fn mode_of(fatal: bool) -> crate::utf8::spec::ErrorMode {
    if fatal {
        crate::utf8::spec::ErrorMode::Fatal
    } else {
        crate::utf8::spec::ErrorMode::Replacement
    }
}

/// "Process a queue" with a new UTF-16BE (`is_utf16be`) or UTF-16LE decoder
/// over all of `input`.
fn process_queue_exec(fatal: bool, is_utf16be: bool, input: &[u8]) -> (r: Option<Vec<u32>>)
    ensures
        match (r, process_queue(mode_of(fatal), initial_decoder(is_utf16be), input@, 0)) {
            (Some(out), Some(expected)) => out@ == expected,
            (None, None) => true,
            _ => false,
        },
{
    let ghost mode = mode_of(fatal);
    let ghost expected = process_queue(mode, initial_decoder(is_utf16be), input@, 0);
    let mut d = Utf16Decoder { leading_byte: None, leading_surrogate: None, is_utf16be };
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        if let Some(x) = expected {
            assert(Seq::<u32>::empty() + x =~= x);
        }
    }
    loop
        invariant
            mode == mode_of(fatal),
            expected == process_queue(mode, initial_decoder(is_utf16be), input@, 0),
            i <= input.len(),
            super::lemmas::wf(d),
            expected == prepend(out@, process_queue(mode, d, input@, i as nat)),
        decreases measure(d, input@, i as nat),
    {
        let ghost d0 = d;
        let ghost i0 = i as nat;
        let item = match input.get(i) {
            Some(byte) => Item::Byte(*byte),
            None => Item::EndOfQueue,
        };
        assert(item == crate::utf8::spec::item_at(input@, i0));
        let (result, restored) = run_handler(&mut d, item);
        if restored && i >= 1 {
            i = i.saturating_sub(1);
        } else if i < input.len() {
            // Never saturates: i < input.len().
            i = i.saturating_add(1);
        }
        assert(i as nat == next_position(input@, i0, handler(d0, item)));
        match result {
            HandlerResult::Finished => {
                proof {
                    assert(out@ + seq![] =~= out@);
                }
                return Some(out);
            },
            HandlerResult::CodePoint(c) => {
                proof {
                    lemma_prepend_cons(out@, c, process_queue(mode, d, input@, i as nat));
                }
                out.push(c);
            },
            HandlerResult::Error => {
                if fatal {
                    return None;
                }
                proof {
                    lemma_prepend_cons(out@, 0xFFFD, process_queue(mode, d, input@, i as nat));
                }
                out.push(0xFFFD);
            },
            HandlerResult::Continue => {},
        }
    }
}

/// "Process a queue" with UTF-16BE's (`is_utf16be`) or UTF-16LE's decoder
/// over all of `input`, in "replacement" mode.
pub fn decode(is_utf16be: bool, input: &[u8]) -> (out: Vec<u32>)
    ensures
        super::contract::decode_ensures(is_utf16be, input@, out@),
{
    proof {
        super::lemmas::lemma_replacement_total(initial_decoder(is_utf16be), input@, 0);
    }
    process_queue_exec(false, is_utf16be, input).unwrap_or_default()
}

/// The same in "fatal" mode: `None` exactly when it returns error.
pub fn decode_or_fail(is_utf16be: bool, input: &[u8]) -> (out: Option<Vec<u32>>)
    ensures
        match out {
            Some(v) => super::contract::decode_or_fail_ensures(is_utf16be, input@, Some(v@)),
            None => super::contract::decode_or_fail_ensures(is_utf16be, input@, None),
        },
{
    process_queue_exec(true, is_utf16be, input)
}

} // verus!
