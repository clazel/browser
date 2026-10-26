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

/// Bounded bytes of a single protected record prefix.
pub struct Buffer {
    bytes: Vec<u8>,
}
impl View for Buffer {
    type V = State;
    closed spec fn view(&self) -> State { self.bytes@ }
}
impl Buffer {
    /// Buffer invariant: bounded and complete exactly at the first record boundary.
    pub closed spec fn wf(&self) -> bool { super::framing_spec::wf(self@) }

    /// Start with no buffered bytes.
    pub fn new() -> (out: Self)
        ensures super::framing_contract::new_ensures(out@),
    {
        Buffer { bytes: Vec::new() }
    }

    /// Number of owned prefix bytes.
    pub fn len(&self) -> (out: usize)
        requires self.wf(),
        ensures super::framing_contract::len_ensures(self@, out as nat),
    {
        self.bytes.len()
    }

    /// Whether no bytes are currently buffered.
    pub fn is_empty(&self) -> (out: bool)
        requires self.wf(),
        ensures super::framing_contract::is_empty_ensures(self@, out),
    {
        self.bytes.is_empty()
    }

    /// Return all held bytes and clear the buffer for the next record.
    pub fn take(&mut self) -> (out: Vec<u8>)
        requires old(self).wf(),
        ensures super::framing_contract::take_ensures(old(self)@, out@, final(self)@),
    {
        let mut out = Vec::new();
        out.extend_from_slice(self.bytes.as_slice());
        proof { assert(out@ == old(self)@); }
        self.bytes.clear();
        proof { assert(self.bytes@ =~= Seq::<u8>::empty()); }
        out
    }

    fn parse_status(&self) -> (out: Status)
        requires self.wf(),
        ensures out@ == super::framing_spec::status(self@),
    {
        match crate::record::read_record(self.bytes.as_slice(), true) {
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
        requires old(self).wf(),
        ensures final(self).wf(),
            final(self)@ == old(self)@ + input@.take(out.0 as int),
            out.0 as nat <= input@.len(),
            super::framing_contract::feed_ensures(old(self)@, input@,
                super::framing_spec::Feed { buffer: final(self)@, consumed: out.0 as nat, status: out.1@ }),
    {
        let ghost initial = self@;
        let mut consumed = 0usize;
        let mut status = self.parse_status();
        proof {
            assert(super::framing_spec::feed(initial, input@)
                == super::framing_spec::Feed {
                    buffer: super::framing_spec::feed(initial, input@).buffer,
                    consumed: super::framing_spec::feed(initial, input@).consumed,
                    status: super::framing_spec::feed(initial, input@).status,
                });
            assert(input@.skip(0) =~= input@);
            assert(super::framing_spec::feed(initial, input@)
                == (super::framing_spec::Feed {
                    buffer: super::framing_spec::feed(initial, input@.skip(0)).buffer,
                    consumed: 0 + super::framing_spec::feed(initial, input@.skip(0)).consumed,
                    status: super::framing_spec::feed(initial, input@.skip(0)).status,
                }));
        }
        while matches!(status, Status::Pending) && consumed < input.len()
            invariant
                self.wf(),
                consumed <= input.len(),
                self@ == initial + input@.take(consumed as int),
                status@ == super::framing_spec::status(self@),
                super::framing_spec::feed(initial, input@)
                    == (super::framing_spec::Feed {
                        buffer: super::framing_spec::feed(self@, input@.skip(consumed as int)).buffer,
                        consumed: consumed as nat
                            + super::framing_spec::feed(self@, input@.skip(consumed as int)).consumed,
                        status: super::framing_spec::feed(self@, input@.skip(consumed as int)).status,
                    }),
            decreases input.len() - consumed,
        {
            proof { super::framing_lemmas::lemma_need_more_bound(self@); }
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
            match crate::record::read_record(self.bytes.as_slice(), true) {
                ReadOut::NeedMore => {
                    status = Status::Pending;
                    proof {
                        super::framing_lemmas::lemma_one_byte_rest_empty(before, byte);
                        super::framing_lemmas::lemma_feed_step(before, input@.skip(consumed as int));
                    }
                },
                ReadOut::Fail(error) => {
                    status = Status::Fail(crate::encode::alert_for(error).description);
                    proof {
                        super::framing_lemmas::lemma_feed_step(before, input@.skip(consumed as int));
                    }
                },
                ReadOut::Done(_, rest) => {
                    if rest.is_empty() {
                        status = Status::Complete;
                    } else {
                        status = Status::Fail(crate::spec::UNEXPECTED_MESSAGE);
                    }
                    proof {
                        super::framing_lemmas::lemma_one_byte_rest_empty(before, byte);
                        super::framing_lemmas::lemma_feed_step(before, input@.skip(consumed as int));
                    }
                },
            }
            consumed = next;
            assert(self.wf());
            assert(status@ == super::framing_spec::status(self@));
        }
        proof {
            assert(input@.skip(0) =~= input@);
            super::framing_lemmas::lemma_feed_stops(self@, input@.skip(consumed as int));
            assert(super::framing_spec::feed(initial, input@)
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
