//! A second, independent transcription of the shared UTF-16 decoder
//! (Encoding §14.2.1) and "process a queue" (§4.1), proven equal to
//! [`super::spec`].
//!
//! The only text is the Encoding Standard's, so this is a same-text
//! transcription (Phase 4 item 4.3). It differs from the spec where the
//! spec made a modelling choice:
//!
//! - The I/O queue is the sequence of bytes not yet read, and "restore
//!   bytes to ioQueue" is done literally: the handler computes byte1 and
//!   byte2 from the code unit (steps 6.4 to 6.6) and prepends them. The
//!   spec instead moves its read position back; [`lemma_equals_spec`]
//!   proves the two agree on every input, which checks the spec's
//!   argument that the restored bytes are the two last read.
//! - Arithmetic is on integers: a code unit is `high × 256 + low`, a
//!   surrogate pair `0x10000 + (leading − 0xD800) × 1024 + (trailing −
//!   0xDC00)`, and byte1 and byte2 are the quotient and remainder by 256.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The decoder's state: "UTF-16 leading byte", "UTF-16 leading surrogate"
/// and "is UTF-16BE decoder".
pub struct State {
    /// The leading byte, if one is held.
    pub lead_byte: Option<u8>,
    /// The leading surrogate, if one is held.
    pub lead_surrogate: Option<u32>,
    /// True for UTF-16BE.
    pub big_endian: bool,
}

/// What a handler step returns.
pub enum Out {
    /// finished
    Finished,
    /// a code point
    Point(u32),
    /// error
    Error,
    /// continue
    Continue,
}

/// One handler run, given the state, the item read (`None` for
/// end-of-queue) and the queue after reading it. Returns the new state,
/// the result and the queue.
pub open spec fn step(st: State, byte: Option<u8>, rest: Seq<u8>) -> (State, Out, Seq<u8>) {
    match byte {
        None => if st.lead_byte is Some || st.lead_surrogate is Some {
            (State { lead_byte: None, lead_surrogate: None, big_endian: st.big_endian }, Out::Error, rest)
        } else {
            (st, Out::Finished, rest)
        },
        Some(b) => match st.lead_byte {
            None => (State { lead_byte: Some(b), ..st }, Out::Continue, rest),
            Some(lb) => {
                let unit: int = if st.big_endian {
                    lb * 256 + b
                } else {
                    b * 256 + lb
                };
                match st.lead_surrogate {
                    Some(ls) => {
                        let st = State { lead_byte: None, lead_surrogate: None, big_endian: st.big_endian };
                        if 0xDC00 <= unit <= 0xDFFF {
                            (st, Out::Point((0x10000 + (ls - 0xD800) * 1024 + (unit - 0xDC00)) as u32), rest)
                        } else {
                            let byte1 = (unit / 256) as u8;
                            let byte2 = (unit % 256) as u8;
                            let bytes = if st.big_endian {
                                seq![byte1, byte2]
                            } else {
                                seq![byte2, byte1]
                            };
                            (st, Out::Error, bytes + rest)
                        }
                    },
                    None => {
                        let st = State { lead_byte: None, ..st };
                        if 0xD800 <= unit <= 0xDBFF {
                            (State { lead_surrogate: Some(unit as u32), ..st }, Out::Continue, rest)
                        } else if 0xDC00 <= unit <= 0xDFFF {
                            (st, Out::Error, rest)
                        } else {
                            (st, Out::Point(unit as u32), rest)
                        }
                    },
                }
            },
        },
    }
}

/// Bytes still queued count 4, a held leading surrogate 6, a held leading
/// byte 3; every step that does not finish lowers this.
pub open spec fn weight(st: State, queue: Seq<u8>) -> int {
    4 * queue.len() + (if st.lead_surrogate is Some { 6int } else { 0 }) + (if st.lead_byte is Some {
        3int
    } else {
        0
    })
}

/// Read one item from `queue`: the first byte and the rest, or
/// end-of-queue and the (empty) queue.
pub open spec fn read(queue: Seq<u8>) -> (Option<u8>, Seq<u8>) {
    if queue.len() > 0 {
        (Some(queue[0]), queue.subrange(1, queue.len() as int))
    } else {
        (None, queue)
    }
}

proof fn lemma_weight_decreases(st: State, queue: Seq<u8>)
    ensures
        ({
            let (byte, rest) = read(queue);
            let (st2, out, q2) = step(st, byte, rest);
            !(out is Finished) ==> 0 <= weight(st2, q2) < weight(st, queue)
        }),
{
}

/// "Process a queue" over `queue` from state `st`; `fatal` selects the
/// error mode. `None` is the error "fatal" mode returns.
pub open spec fn run(fatal: bool, st: State, queue: Seq<u8>) -> Option<Seq<u32>>
    decreases weight(st, queue),
{
    let (byte, rest) = read(queue);
    let (st2, out, q2) = step(st, byte, rest);
    if out is Finished {
        Some(seq![])
    } else if weight(st2, q2) < weight(st, queue) {
        match out {
            Out::Point(c) => match run(fatal, st2, q2) {
                Some(o) => Some(seq![c] + o),
                None => None,
            },
            Out::Error => if fatal {
                None
            } else {
                match run(fatal, st2, q2) {
                    Some(o) => Some(seq![0xFFFDu32] + o),
                    None => None,
                }
            },
            _ => run(fatal, st2, q2),
        }
    } else {
        // Unreachable (lemma_weight_decreases).
        None
    }
}

/// The spec's state as this file's.
pub open spec fn state_of(d: Utf16Decoder) -> State {
    State { lead_byte: d.leading_byte, lead_surrogate: d.leading_surrogate, big_endian: d.is_utf16be }
}

/// The spec's error mode as this file's flag.
pub open spec fn mode_of(fatal: bool) -> crate::utf8::spec::ErrorMode {
    if fatal {
        crate::utf8::spec::ErrorMode::Fatal
    } else {
        crate::utf8::spec::ErrorMode::Replacement
    }
}

/// The spec's position is where the literal queue starts: a held leading
/// byte is the byte before it. (And a held leading surrogate is one, as
/// in every state an input reaches.)
pub open spec fn aligned(d: Utf16Decoder, input: Seq<u8>, i: nat) -> bool {
    &&& super::lemmas::wf(d)
    &&& match d.leading_byte {
        Some(b) => 1 <= i && input[i - 1] == b,
        None => true,
    }
}

proof fn lemma_arith(high: u8, low: u8, ls: u32)
    ensures
        (((high as u32) << 8u32) + low as u32) as u32 == high * 256 + low,
        (high * 256 + low) / 256 == high,
        (high * 256 + low) % 256 == low,
        0xD800 <= ls <= 0xDBFF ==> ((ls - 0xD800) as u32) << 10u32 == (ls - 0xD800) * 1024,
{
    let h = high as u32;
    let l = low as u32;
    assert(h < 256 && l < 256 ==> ((h << 8u32) + l) as u32 == h * 256 + l) by (bit_vector);
    assert((high * 256 + low) / 256 == high) by (nonlinear_arith)
        requires
            low < 256,
    ;
    assert((high * 256 + low) % 256 == low) by (nonlinear_arith)
        requires
            low < 256,
    ;
    if 0xD800 <= ls <= 0xDBFF {
        let x = (ls - 0xD800) as u32;
        assert(x <= 0x3FF ==> x << 10u32 == x * 1024) by (bit_vector);
    }
}

/// A spec handler result and this file's are the same result.
pub open spec fn same(r: crate::utf8::spec::HandlerResult, o: Out) -> bool {
    match (r, o) {
        (crate::utf8::spec::HandlerResult::Finished, Out::Finished) => true,
        (crate::utf8::spec::HandlerResult::CodePoint(c), Out::Point(p)) => c == p,
        (crate::utf8::spec::HandlerResult::Error, Out::Error) => true,
        (crate::utf8::spec::HandlerResult::Continue, Out::Continue) => true,
        _ => false,
    }
}

/// What one step of each must agree on.
pub open spec fn steps_agree(d: Utf16Decoder, input: Seq<u8>, i: nat) -> bool {
    let s = handler(d, crate::utf8::spec::item_at(input, i));
    let j = next_position(input, i, s);
    let (byte, rest) = read(input.subrange(i as int, input.len() as int));
    let (st2, out, q2) = step(state_of(d), byte, rest);
    &&& st2 == state_of(s.decoder)
    &&& same(s.result, out)
    &&& j <= input.len()
    &&& q2 == input.subrange(j as int, input.len() as int)
    &&& aligned(s.decoder, input, j)
}

/// A step with a held leading byte and leading surrogate.
proof fn lemma_step_pair(d: Utf16Decoder, input: Seq<u8>, i: nat, lb: u8, ls: u32)
    requires
        i < input.len(),
        aligned(d, input, i),
        d.leading_byte == Some(lb),
        d.leading_surrogate == Some(ls),
    ensures
        steps_agree(d, input, i),
{
    let b = input[i as int];
    lemma_arith(lb, b, ls);
    lemma_arith(b, lb, ls);
    let q = input.subrange(i as int, input.len() as int);
    assert(read(q).0 == Some(b));
    assert(read(q).1 =~= input.subrange((i + 1) as int, input.len() as int));
    let s = handler(d, crate::utf8::spec::item_at(input, i));
    if s.restored {
        let (st2, out, q2) = step(state_of(d), Some(b), read(q).1);
        assert(q2 =~= input.subrange((i - 1) as int, input.len() as int));
    }
}

/// A step with a held leading byte and no leading surrogate.
proof fn lemma_step_unit(d: Utf16Decoder, input: Seq<u8>, i: nat, lb: u8)
    requires
        i < input.len(),
        aligned(d, input, i),
        d.leading_byte == Some(lb),
        d.leading_surrogate is None,
    ensures
        steps_agree(d, input, i),
{
    let b = input[i as int];
    lemma_arith(lb, b, 0);
    lemma_arith(b, lb, 0);
    let q = input.subrange(i as int, input.len() as int);
    assert(read(q).0 == Some(b));
    assert(read(q).1 =~= input.subrange((i + 1) as int, input.len() as int));
}

/// One step of each agrees.
proof fn lemma_step(d: Utf16Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
        aligned(d, input, i),
    ensures
        steps_agree(d, input, i),
{
    let q = input.subrange(i as int, input.len() as int);
    if i < input.len() {
        match (d.leading_byte, d.leading_surrogate) {
            (Some(lb), Some(ls)) => lemma_step_pair(d, input, i, lb, ls),
            (Some(lb), None) => lemma_step_unit(d, input, i, lb),
            (None, _) => {
                assert(read(q).0 == Some(input[i as int]));
                assert(read(q).1 =~= input.subrange((i + 1) as int, input.len() as int));
            },
        }
    } else {
        assert(q =~= seq![]);
    }
}

/// The literal queue gives what the spec gives, step by step.
proof fn lemma_run(fatal: bool, d: Utf16Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
        aligned(d, input, i),
    ensures
        run(fatal, state_of(d), input.subrange(i as int, input.len() as int)) == process_queue(
            mode_of(fatal),
            d,
            input,
            i,
        ),
    decreases measure(d, input, i),
{
    let q = input.subrange(i as int, input.len() as int);
    let s = handler(d, crate::utf8::spec::item_at(input, i));
    let j = next_position(input, i, s);
    lemma_step(d, input, i);
    lemma_weight_decreases(state_of(d), q);
    if !(s.result is Finished) {
        lemma_run(fatal, s.decoder, input, j);
    }
}

/// The literal queue transcription equals the spec on every input, in
/// both modes, for UTF-16BE and UTF-16LE.
pub proof fn lemma_equals_spec(fatal: bool, is_utf16be: bool, input: Seq<u8>)
    ensures
        run(
            fatal,
            State { lead_byte: None, lead_surrogate: None, big_endian: is_utf16be },
            input,
        ) == process_queue(mode_of(fatal), initial_decoder(is_utf16be), input, 0),
{
    lemma_run(fatal, initial_decoder(is_utf16be), input, 0);
    assert(input.subrange(0, input.len() as int) =~= input);
}

} // verus!
