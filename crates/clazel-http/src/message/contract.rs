//! Contracts the executable message functions must be proven to meet, and
//! the two properties of the spec that make an incremental parser safe.
//! Each exec function's `ensures` clause is exactly one of these predicates
//! (applied to the views of its arguments and result), and its `requires`
//! clause is the matching `*_requires` predicate where there is one, so
//! reviewing these and [`super::spec`] is enough to know what the
//! implementation guarantees.
//!
//! The parser is incremental: it is given bytes as they arrive and keeps a
//! state. Its view is everything it has been given (`received`) and whether
//! the request was `HEAD`; every answer it gives is the spec's answer for
//! all of `received`, so feeding it the bytes in any split gives the same
//! result as parsing them at once.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `ResponseParser::new(request_is_head: bool)`: nothing
/// received yet.
pub open spec fn new_ensures(request_is_head: bool, received: Seq<u8>, head: bool) -> bool {
    received == Seq::<u8>::empty() && head == request_is_head
}

/// Precondition of `ResponseParser::feed(&mut self, bytes: &[u8]) -> Parse`:
/// the parser has not answered anything but `Incomplete` yet.
pub open spec fn feed_requires(received: Seq<u8>, request_is_head: bool) -> bool {
    parse_response(received, request_is_head) is Incomplete
}

/// Contract for `ResponseParser::feed`: the bytes are appended to what was
/// received, and the answer is the spec's for all of it.
pub open spec fn feed_ensures(old_received: Seq<u8>, bytes: Seq<u8>, new_received: Seq<u8>, request_is_head: bool, output: Parse) -> bool {
    new_received == old_received + bytes && output == parse_response(new_received, request_is_head)
}

/// Precondition of `ResponseParser::close(self) -> Parse`, called when the
/// server has closed the connection: as for `feed`.
pub open spec fn close_requires(received: Seq<u8>, request_is_head: bool) -> bool {
    parse_response(received, request_is_head) is Incomplete
}

/// Contract for `ResponseParser::close`.
pub open spec fn close_ensures(received: Seq<u8>, request_is_head: bool, output: Parse) -> bool {
    output == parse_response_at_close(received, request_is_head)
}

/// Contract for `serialize_request(&RequestBuf) -> Option<Vec<u8>>`: the
/// bytes of a valid request, and `None` for any other. The check is the
/// function's, not a precondition, because its callers include unverified
/// code (the network shell), which cannot be held to a `requires`; so no
/// caller can put a CR, LF or other control into the request line or a
/// field.
pub open spec fn serialize_request_ensures(r: Request, output: Option<Seq<u8>>) -> bool {
    output == if is_valid_request(r) {
        Some(serialize_request(r))
    } else {
        None
    }
}

// ===========================================================================
// Properties of the spec, proven in `lemmas.rs`.
// ===========================================================================

/// `late`, the answer for more bytes, keeps what `early` decided: a
/// decision is never taken back, and a finished response stays the same
/// response, with only more bytes after it.
pub open spec fn extends(early: Parse, late: Parse) -> bool {
    match early {
        Parse::Incomplete => true,
        Parse::Done { response: r1, rest: rest1 } => match late {
            Parse::Done { response: r2, rest: rest2 } => r1 == r2 && rest1.len() <= rest2.len()
                && rest2.take(rest1.len() as int) == rest1,
            _ => false,
        },
        Parse::Invalid => late is Invalid,
        Parse::Unsupported => late is Unsupported,
    }
}

/// Monotonicity: whatever `input` decides, `input + more` decides the
/// same. (`theorem_monotone` in `lemmas.rs` proves this for all inputs.)
pub open spec fn monotone(input: Seq<u8>, more: Seq<u8>, request_is_head: bool) -> bool {
    extends(parse_response(input, request_is_head), parse_response(input + more, request_is_head))
}

/// No decision before the data: every proper prefix of the octets a
/// response was parsed from (`input` without the `rest` after it) is
/// `Incomplete`. (`theorem_no_early_decision` in `lemmas.rs` proves this
/// for all inputs.)
pub open spec fn no_early_decision(input: Seq<u8>, request_is_head: bool) -> bool {
    match parse_response(input, request_is_head) {
        Parse::Done { response: _, rest } => forall|k: int| 0 <= k < input.len() - rest.len()
            ==> parse_response(#[trigger] input.take(k), request_is_head) is Incomplete,
        _ => true,
    }
}

} // verus!
