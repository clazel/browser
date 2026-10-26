//! RFC 8446 §5.1–§5.2: bounded incremental accumulation of one record.
use super::framing_spec::State;
use crate::record::ReadOut;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Parser status after a feed attempt.
#[derive(Debug, PartialEq, Eq)]
pub enum Status {
    /// The prefix is valid so far but needs more bytes.
    Pending,
    /// One exact record is buffered; no suffix was copied.
    Complete,
    /// The protected record parser rejected the buffered bytes.
    Fail(u8),
}
impl View for Status {
    type V = super::framing_spec::Status;
    open spec fn view(&self) -> Self::V {
        match self {
            Status::Pending => super::framing_spec::Status::Pending,
            Status::Complete => super::framing_spec::Status::Complete,
            Status::Fail(alert) => super::framing_spec::Status::Fail(*alert),
        }
    }
}

/// Bounded bytes of one record prefix in an immutable record mode.
pub struct Buffer {
    bytes: Vec<u8>,
    protected: bool,
}
impl View for Buffer {
    type V = State;
    closed spec fn view(&self) -> State { self.bytes@ }
}
impl Buffer {
    /// Immutable parser mode selected at construction.
    pub closed spec fn protected_mode(&self) -> bool { self.protected }

    /// Buffer invariant: bounded and complete exactly at the first record boundary.
    pub open spec fn wf(&self) -> bool {
        super::framing_spec::wf_mode(self@, self.protected_mode())
    }

    /// Invariant under an explicit parser mode.
    pub closed spec fn wf_mode(&self, protected: bool) -> bool {
        super::framing_spec::wf_mode(self@, protected)
    }

    /// Start with no buffered bytes.
    pub fn new() -> (out: Self)
        ensures super::framing_contract::new_ensures(out@), out.wf(), out.protected_mode(),
    {
        Buffer { bytes: Vec::new(), protected: true }
    }

    /// Start an unprotected framer for the initial Hello exchange.
    pub fn new_plaintext() -> (out: Self)
        ensures out.wf_mode(false), !out.protected_mode(), super::framing_contract::new_ensures(out@),
    {
        Buffer { bytes: Vec::new(), protected: false }
    }

    /// Number of owned prefix bytes.
    pub fn len(&self) -> (out: usize)
        requires self.protected_mode(), self.wf(),
        ensures super::framing_contract::len_ensures(self@, out as nat),
    {
        self.bytes.len()
    }

    /// Whether no bytes are currently buffered.
    pub fn is_empty(&self) -> (out: bool)
        requires self.wf(),
        ensures super::framing_contract::is_empty_mode_ensures(self.protected_mode(), self@, out),
    {
        self.bytes.is_empty()
    }

    /// Whether this mode's byte prefix is empty.
    pub fn is_empty_mode(&self, protected: bool) -> (out: bool)
        requires self.protected_mode() == protected, self.wf_mode(protected),
        ensures super::framing_contract::is_empty_mode_ensures(protected, self@, out),
    {
        self.bytes.is_empty()
    }

    /// Return all held bytes and clear the buffer for the next record.
    pub fn take(&mut self) -> (out: Vec<u8>)
        requires super::framing_spec::wf_mode(old(self)@, self.protected_mode()),
        ensures final(self).wf_mode(old(self).protected_mode()),
            final(self).protected_mode() == old(self).protected_mode(), super::framing_contract::take_mode_ensures(
            old(self).protected_mode(), old(self)@, out@, final(self)@),
    {
        let mut out = Vec::new();
        out.extend_from_slice(self.bytes.as_slice());
        proof { assert(out@ == old(self)@); }
        self.bytes.clear();
        proof { assert(self.bytes@ =~= Seq::<u8>::empty()); }
        out
    }

    fn parse_status(&self) -> (out: Status)
        requires self.wf_mode(self.protected_mode()),
        ensures out@ == super::framing_spec::status_mode(self@, self.protected),
    {
        match crate::record::read_record(self.bytes.as_slice(), self.protected) {
            ReadOut::NeedMore => Status::Pending,
            ReadOut::Fail(error) => Status::Fail(crate::encode::alert_for(error).description),
            ReadOut::Done(_, rest) => {
                if rest.is_empty() { Status::Complete }
                else { Status::Fail(crate::spec::UNEXPECTED_MESSAGE) }
            },
        }
    }

    /// Consume only enough caller input to complete or reject the first record.
    /// Consumed bytes move into this bounded buffer; the caller keeps the suffix.
    pub fn feed(&mut self, input: &[u8]) -> (out: (usize, Status))
        requires super::framing_spec::wf_mode(old(self)@, self.protected_mode()),
        ensures final(self).wf_mode(old(self).protected_mode()), final(self).protected_mode() == old(self).protected_mode(),
            super::framing_spec::wf_mode(final(self)@, old(self).protected_mode()),
            final(self)@ == old(self)@ + input@.take(out.0 as int),
            out.0 as nat <= input@.len(),
            super::framing_contract::feed_mode_ensures(old(self).protected_mode(), old(self)@, input@,
                super::framing_spec::Feed { buffer: final(self)@, consumed: out.0 as nat, status: out.1@ }),
    {
        let ghost initial = self@;
        proof { assert(self.wf_mode(self.protected_mode())); }
        let mut consumed = 0usize;
        let mut status = self.parse_status();
        proof {
            assert(super::framing_spec::feed_mode(initial, input@, self.protected)
                == super::framing_spec::Feed {
                    buffer: super::framing_spec::feed_mode(initial, input@, self.protected).buffer,
                    consumed: super::framing_spec::feed_mode(initial, input@, self.protected).consumed,
                    status: super::framing_spec::feed_mode(initial, input@, self.protected).status,
                });
            assert(input@.skip(0) =~= input@);
            assert(super::framing_spec::feed_mode(initial, input@, self.protected)
                == (super::framing_spec::Feed {
                    buffer: super::framing_spec::feed_mode(initial, input@.skip(0), self.protected).buffer,
                    consumed: 0 + super::framing_spec::feed_mode(initial, input@.skip(0), self.protected).consumed,
                    status: super::framing_spec::feed_mode(initial, input@.skip(0), self.protected).status,
                }));
        }
        while matches!(status, Status::Pending) && consumed < input.len()
            invariant
                self.wf_mode(self.protected_mode()),
                consumed <= input.len(),
                self@ == initial + input@.take(consumed as int),
                status@ == super::framing_spec::status_mode(self@, self.protected),
                super::framing_spec::feed_mode(initial, input@, self.protected)
                    == (super::framing_spec::Feed {
                        buffer: super::framing_spec::feed_mode(self@, input@.skip(consumed as int), self.protected).buffer,
                        consumed: consumed as nat
                            + super::framing_spec::feed_mode(self@, input@.skip(consumed as int), self.protected).consumed,
                        status: super::framing_spec::feed_mode(self@, input@.skip(consumed as int), self.protected).status,
                    }),
            decreases input.len() - consumed,
        {
            proof { super::framing_lemmas::lemma_need_more_bound_mode(self@, self.protected); }
            let ghost before = self@;
            let byte = match input.get(consumed) {
                Some(value) => *value,
                None => return (consumed, status),
            };
            proof {
                assert(input@.skip(consumed as int)[0] == byte);
                assert(input@.skip(consumed as int).skip(1) =~= input@.skip(consumed as int + 1));
            }
            self.bytes.push(byte);
            let next = consumed.saturating_add(1);
            match crate::record::read_record(self.bytes.as_slice(), self.protected) {
                ReadOut::NeedMore => {
                    status = Status::Pending;
                    proof {
                        super::framing_lemmas::lemma_one_byte_rest_empty_mode(before, byte, self.protected);
                        super::framing_lemmas::lemma_feed_step_mode(before, input@.skip(consumed as int), self.protected);
                    }
                },
                ReadOut::Fail(error) => {
                    status = Status::Fail(crate::encode::alert_for(error).description);
                    proof {
                        super::framing_lemmas::lemma_feed_step_mode(before, input@.skip(consumed as int), self.protected);
                    }
                },
                ReadOut::Done(_, rest) => {
                    if rest.is_empty() {
                        status = Status::Complete;
                    } else {
                        status = Status::Fail(crate::spec::UNEXPECTED_MESSAGE);
                    }
                    proof {
                        super::framing_lemmas::lemma_one_byte_rest_empty_mode(before, byte, self.protected);
                        super::framing_lemmas::lemma_feed_step_mode(before, input@.skip(consumed as int), self.protected);
                    }
                },
            }
            consumed = next;
            assert(self.wf_mode(self.protected_mode()));
            assert(status@ == super::framing_spec::status_mode(self@, self.protected));
        }
        proof {
            assert(input@.skip(0) =~= input@);
            super::framing_lemmas::lemma_feed_stops_mode(self@, input@.skip(consumed as int), self.protected);
            assert(super::framing_spec::feed_mode(initial, input@, self.protected)
                == super::framing_spec::Feed { buffer: self@, consumed: consumed as nat, status: status@ });
        }
        (consumed, status)
    }
}
impl Default for Buffer {
    fn default() -> (out: Self) ensures super::framing_contract::new_ensures(out@) {
        Buffer::new()
    }
}
} // verus!
