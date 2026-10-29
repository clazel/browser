//! The executable single-byte decoder, proven to meet [`super::contract`].
//!
//! The code mirrors the spec: [`index_code_point`] reads index
//! single-byte, [`run_handler`] is the decoder's handler (§9) and
//! [`process_queue_exec`] is "process a queue" (§4.1). Each is proven
//! equal to its spec function, so the step comments live in
//! [`super::spec`] and are not repeated here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::data::*;
use crate::labels::spec::Encoding;
use crate::utf8::spec::HandlerResult;

verus! {

/// Entry `pointer` of `e`'s index (the generated table's value, `NULL`
/// included).
pub fn index_entry_exec(e: Encoding, pointer: usize) -> (r: u32)
    ensures
        r == index_entry(e, pointer as int),
{
    match e {
        Encoding::Ibm866 => index_ibm866_at_exec(pointer),
        Encoding::Iso8859_2 => index_iso_8859_2_at_exec(pointer),
        Encoding::Iso8859_3 => index_iso_8859_3_at_exec(pointer),
        Encoding::Iso8859_4 => index_iso_8859_4_at_exec(pointer),
        Encoding::Iso8859_5 => index_iso_8859_5_at_exec(pointer),
        Encoding::Iso8859_6 => index_iso_8859_6_at_exec(pointer),
        Encoding::Iso8859_7 => index_iso_8859_7_at_exec(pointer),
        Encoding::Iso8859_8 => index_iso_8859_8_at_exec(pointer),
        Encoding::Iso8859_8I => index_iso_8859_8_at_exec(pointer),
        Encoding::Iso8859_10 => index_iso_8859_10_at_exec(pointer),
        Encoding::Iso8859_13 => index_iso_8859_13_at_exec(pointer),
        Encoding::Iso8859_14 => index_iso_8859_14_at_exec(pointer),
        Encoding::Iso8859_15 => index_iso_8859_15_at_exec(pointer),
        Encoding::Iso8859_16 => index_iso_8859_16_at_exec(pointer),
        Encoding::Koi8R => index_koi8_r_at_exec(pointer),
        Encoding::Koi8U => index_koi8_u_at_exec(pointer),
        Encoding::Macintosh => index_macintosh_at_exec(pointer),
        Encoding::Windows874 => index_windows_874_at_exec(pointer),
        Encoding::Windows1250 => index_windows_1250_at_exec(pointer),
        Encoding::Windows1251 => index_windows_1251_at_exec(pointer),
        Encoding::Windows1252 => index_windows_1252_at_exec(pointer),
        Encoding::Windows1253 => index_windows_1253_at_exec(pointer),
        Encoding::Windows1254 => index_windows_1254_at_exec(pointer),
        Encoding::Windows1255 => index_windows_1255_at_exec(pointer),
        Encoding::Windows1256 => index_windows_1256_at_exec(pointer),
        Encoding::Windows1257 => index_windows_1257_at_exec(pointer),
        Encoding::Windows1258 => index_windows_1258_at_exec(pointer),
        Encoding::XMacCyrillic => index_x_mac_cyrillic_at_exec(pointer),
        _ => 0xFFFF_FFFF,
    }
}

/// "Index code point" for `pointer` in `e`'s index.
pub fn index_code_point_exec(e: Encoding, pointer: usize) -> (r: Option<u32>)
    ensures
        r == index_code_point(e, pointer as int),
{
    if pointer >= 128 {
        return None;
    }
    let v = index_entry_exec(e, pointer);
    if v == 0xFFFF_FFFF {
        None
    } else {
        Some(v)
    }
}

/// The single-byte decoder's handler, for a byte.
fn run_handler(e: Encoding, byte: u8) -> (r: HandlerResult)
    ensures
        r == handler(e, crate::utf8::spec::Item::Byte(byte)),
{
    if byte <= 0x7F {
        HandlerResult::CodePoint(byte as u32)
    } else {
        proof {
            assert(byte >= 0x80 ==> byte & 0x7F == byte - 0x80) by (bit_vector);
        }
        match index_code_point_exec(e, (byte & 0x7F) as usize) {
            None => HandlerResult::Error,
            Some(c) => HandlerResult::CodePoint(c),
        }
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

/// "Process a queue" with `e`'s decoder over all of `input`.
fn process_queue_exec(fatal: bool, e: Encoding, input: &[u8]) -> (r: Option<Vec<u32>>)
    ensures
        match (r, process_queue(mode_of(fatal), e, input@, 0)) {
            (Some(out), Some(expected)) => out@ == expected,
            (None, None) => true,
            _ => false,
        },
{
    let ghost mode = mode_of(fatal);
    let ghost expected = process_queue(mode, e, input@, 0);
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        if let Some(x) = expected {
            assert(Seq::<u32>::empty() + x =~= x);
        }
    }
    while i < input.len()
        invariant
            mode == mode_of(fatal),
            expected == process_queue(mode, e, input@, 0),
            i <= input.len(),
            expected == prepend(out@, process_queue(mode, e, input@, i as nat)),
        decreases input.len() - i,
    {
        // `get` cannot fail: i < input.len().
        let byte = match input.get(i) {
            Some(b) => *b,
            None => 0,
        };
        let r = run_handler(e, byte);
        proof {
            assert(crate::utf8::spec::item_at(input@, i as nat) == crate::utf8::spec::Item::Byte(byte));
        }
        match r {
            HandlerResult::CodePoint(c) => {
                proof {
                    lemma_prepend_cons(out@, c, process_queue(mode, e, input@, (i + 1) as nat));
                }
                out.push(c);
            },
            HandlerResult::Error => {
                if fatal {
                    return None;
                }
                proof {
                    lemma_prepend_cons(out@, 0xFFFD, process_queue(mode, e, input@, (i + 1) as nat));
                }
                out.push(0xFFFD);
            },
            _ => {},
        }
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(crate::utf8::spec::item_at(input@, i as nat) == crate::utf8::spec::Item::EndOfQueue);
        assert(out@ + Seq::<u32>::empty() =~= out@);
    }
    Some(out)
}

/// "Process a queue" with an instance of `e`'s single-byte decoder over
/// all of `input`, in "replacement" mode.
pub fn decode(e: Encoding, input: &[u8]) -> (out: Vec<u32>)
    requires
        super::contract::decode_requires(e),
    ensures
        super::contract::decode_ensures(e, input@, out@),
{
    proof {
        super::lemmas::lemma_replacement_total(e, input@, 0);
    }
    process_queue_exec(false, e, input).unwrap_or_default()
}

/// The same in "fatal" mode: `None` exactly when it returns error.
pub fn decode_or_fail(e: Encoding, input: &[u8]) -> (out: Option<Vec<u32>>)
    requires
        super::contract::decode_requires(e),
    ensures
        match out {
            Some(v) => super::contract::decode_or_fail_ensures(e, input@, Some(v@)),
            None => super::contract::decode_or_fail_ensures(e, input@, None),
        },
{
    process_queue_exec(true, e, input)
}

} // verus!
