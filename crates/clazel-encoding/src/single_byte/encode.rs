//! The executable single-byte encoder, proven to meet [`super::contract`].
//!
//! [`index_pointer_exec`] is "index pointer" (§5), [`run_encoder_handler`]
//! the encoder's handler (§9), [`push_decimal`] the "html" error mode's
//! decimal digits (§4.1 process an item, step 7) and [`encode`] "encode"
//! (§6). Each is proven equal to its spec function, so the step comments
//! live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::labels::spec::Encoding;

verus! {

/// "Index pointer" for `code_point` in `e`'s index: the first pointer whose
/// code point it is.
fn index_pointer_exec(e: Encoding, code_point: u32) -> (r: Option<u8>)
    ensures
        match r {
            Some(p) => p < 128 && index_pointer(e, code_point) == Some(p as nat),
            None => index_pointer(e, code_point) is None,
        },
{
    let mut p: u8 = 0;
    while p < 128
        invariant
            p <= 128,
            index_pointer(e, code_point) == index_pointer_from(e, code_point, p as nat),
        decreases 128 - p,
    {
        if super::decode::index_code_point_exec(e, p as usize) == Some(code_point) {
            return Some(p);
        }
        // Never saturates: p < 128.
        p = p.saturating_add(1);
    }
    None
}

/// The encoder handler's result for a scalar value.
fn run_encoder_handler(e: Encoding, code_point: u32) -> (r: EncoderResult)
    ensures
        r == encoder_handler(e, crate::utf8::spec::ScalarItem::ScalarValue(code_point)),
{
    if code_point <= 0x7F {
        EncoderResult::Byte(code_point as u8)
    } else {
        match index_pointer_exec(e, code_point) {
            None => EncoderResult::Error(code_point),
            Some(p) => {
                // p < 128, so the OR adds 0x80.
                proof {
                    assert(p < 128 ==> p | 0x80 == p + 0x80) by (bit_vector);
                }
                EncoderResult::Byte(p | 0x80)
            },
        }
    }
}

/// Append the decimal digits of `n` ([`decimal`]) to `out`.
fn push_decimal(n: u32, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + decimal(n as nat),
    decreases n,
{
    if n >= 10 {
        push_decimal(n / 10, out);
    }
    let digit = (n % 10) as u8;
    proof {
        assert(digit as nat == n as nat % 10);
    }
    // digit < 10, so the OR adds 0x30.
    proof {
        assert(digit < 10 ==> digit | 0x30 == digit + 0x30) by (bit_vector);
    }
    out.push(digit | 0x30);
    proof {
        if n >= 10 {
            assert((n / 10) as nat == n as nat / 10);
        }
        assert(final(out)@ =~= old(out)@ + decimal(n as nat));
    }
}

/// "Encode" (§6) with single-byte encoding `e`: "html" mode, an
/// unencodable scalar value becoming `&#` its decimal value `;`.
pub fn encode(e: Encoding, input: &[u32]) -> (out: Vec<u8>)
    requires
        super::contract::encode_requires(e, input@),
    ensures
        super::contract::encode_ensures(e, input@, out@),
{
    let ghost expected = super::spec::encode(e, input@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(Seq::<u8>::empty() + expected =~= expected);
    }
    while i < input.len()
        invariant
            expected == super::spec::encode(e, input@),
            i <= input.len(),
            expected == out@ + encoder_process_queue(e, input@, i as nat),
        decreases input.len() - i,
    {
        // `get` cannot fail: i < input.len().
        let c = match input.get(i) {
            Some(c) => *c,
            None => 0,
        };
        let ghost before = out@;
        let ghost rest = encoder_process_queue(e, input@, (i + 1) as nat);
        assert(crate::utf8::spec::scalar_item_at(input@, i as nat) == crate::utf8::spec::ScalarItem::ScalarValue(
            c,
        ));
        match run_encoder_handler(e, c) {
            EncoderResult::Byte(b) => {
                out.push(b);
                proof {
                    assert(before + (seq![b] + rest) =~= out@ + rest);
                }
            },
            EncoderResult::Error(cp) => {
                out.push(0x26);
                out.push(0x23);
                let ghost mid = out@;
                push_decimal(cp, &mut out);
                out.push(0x3B);
                proof {
                    assert(before + (seq![0x26u8, 0x23u8] + decimal(cp as nat) + seq![0x3Bu8] + rest) =~= out@
                        + rest);
                }
            },
            EncoderResult::Finished => {},
        }
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(crate::utf8::spec::scalar_item_at(input@, i as nat) == crate::utf8::spec::ScalarItem::EndOfQueue);
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

} // verus!
