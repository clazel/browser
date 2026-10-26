//! RFC 8446 §5.1–§5.2: bounded incremental accumulation of one TLS record.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-5.1>.
//!
//! Modelling choices:
//! - The existing record parser is authoritative and is called with
//!   `protected = true`; connection policy handles the returned CCS frame.
//! - The buffer owns only a prefix of one record. It stops on the exact first
//!   complete or invalid record boundary and never buffers a suffix.
//! - Consumed bytes are owned by this buffer. The caller retains/resubmits
//!   only the unconsumed suffix. A completed record is cleared by take.
//! - A parser failure is retained in the buffer and repeated without consuming
//!   more input; `take` clears bytes so the connection controller can discard
//!   or otherwise dispose of the failed prefix.
//! - The limit is the five-byte header plus the protected maximum ciphertext.
//!   It is a framing resource bound, not a handshake or connection limit.
//! - This module does not decrypt, reassemble handshake messages, or decide
//!   whether a record's content is permitted at the current protocol phase.
//!   RFC prose has no numbered algorithm steps.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Maximum accumulated protected-record prefix: header plus ciphertext bound.
pub const MAX_BUFFER: usize = crate::spec::RECORD_HEADER + crate::spec::MAX_CIPHERTEXT;

/// Result of considering the bytes currently held for one record.
pub enum Status {
    /// The current bytes are a valid prefix, but the record is incomplete.
    Pending,
    /// Exactly one complete record is present, with no suffix buffered.
    Complete,
    /// The existing record parser rejected the prefix with this alert.
    Fail(u8),
}

/// Abstract owned prefix maintained by one native `Buffer`.
pub type State = Seq<u8>;

/// One feed result: updated prefix, input bytes copied, and parser state.
pub struct Feed {
    /// Prefix retained by the buffer after this call.
    pub buffer: Seq<u8>,
    /// Number of bytes copied from this input slice.
    pub consumed: nat,
    /// Parser state of the resulting buffer.
    pub status: Status,
}

/// Parse the current prefix in protected mode and map parser errors to alerts.
pub open spec fn status(buffer: Seq<u8>) -> Status {
    match crate::spec::read_record(buffer, true) {
        crate::spec::Read::NeedMore => Status::Pending,
        crate::spec::Read::Fail(error) => Status::Fail(crate::spec::alert_of(error)),
        crate::spec::Read::Done(_, rest) => {
            if rest.len() == 0 { Status::Complete } else { Status::Fail(crate::spec::UNEXPECTED_MESSAGE) }
        },
    }
}

/// Buffer invariant: bounded, and any complete parse is exactly at its boundary.
pub open spec fn wf(buffer: State) -> bool {
    buffer.len() <= MAX_BUFFER && match crate::spec::read_record(buffer, true) {
        crate::spec::Read::Done(_, rest) => rest.len() == 0,
        _ => true,
    }
}

/// Explicit contract for the externally visible status.
pub open spec fn status_matches(buffer: Seq<u8>, result: Status) -> bool {
    match (result, crate::spec::read_record(buffer, true)) {
        (Status::Pending, crate::spec::Read::NeedMore) => true,
        (Status::Complete, crate::spec::Read::Done(_, rest)) => rest.len() == 0,
        (Status::Fail(alert), crate::spec::Read::Fail(error)) => alert == crate::spec::alert_of(error),
        _ => false,
    }
}

/// Append bytewise, stopping at the first complete record or parser error.
pub open spec fn feed(buffer: Seq<u8>, input: Seq<u8>) -> Feed
    decreases input.len(),
{
    match status(buffer) {
        Status::Complete => Feed { buffer, consumed: 0, status: Status::Complete },
        Status::Fail(alert) => Feed { buffer, consumed: 0, status: Status::Fail(alert) },
        Status::Pending => {
            if input.len() == 0 {
                Feed { buffer, consumed: 0, status: Status::Pending }
            } else {
                let appended = buffer.push(input[0]);
                match crate::spec::read_record(appended, true) {
                    crate::spec::Read::NeedMore => {
                        let tail = feed(appended, input.skip(1));
                        Feed { buffer: tail.buffer, consumed: tail.consumed + 1, status: tail.status }
                    },
                    crate::spec::Read::Fail(error) => Feed {
                        buffer: appended,
                        consumed: 1,
                        status: Status::Fail(crate::spec::alert_of(error)),
                    },
                    crate::spec::Read::Done(_, _) => Feed {
                        buffer: appended,
                        consumed: 1,
                        status: Status::Complete,
                    },
                }
            }
        },
    }
}

/// Construction is the empty, incomplete prefix.
pub open spec fn new() -> State { Seq::empty() }

/// Taking returns every accumulated byte and resets only the buffered prefix.
pub open spec fn take(buffer: State) -> (Seq<u8>, State) { (buffer, Seq::empty()) }

/// Current buffered byte count.
pub open spec fn len(buffer: State) -> nat { buffer.len() }

/// Whether the buffer currently owns no bytes.
pub open spec fn is_empty(buffer: State) -> bool { buffer.len() == 0 }
} // verus!
