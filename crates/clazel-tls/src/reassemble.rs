//! The executable reassembly of handshake messages from records (RFC 8446
//! §5.1), proven to meet [`super::spec::feed_record`] and
//! [`super::spec::feed_ccs`]. The buffer holds the bytes of at most one
//! unfinished message, fewer than `HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY`
//! ([`super::lemmas_record::lemma_feed_bound`]), and while a record is
//! appended at most [`super::spec::REASSEMBLY_BOUND`] bytes.

use super::reader::byte_at;
use super::spec::{
    Alert, CT_ALERT, CT_APPLICATION_DATA, CT_CHANGE_CIPHER_SPEC, CT_HANDSHAKE, ErrKind,
    HANDSHAKE_HEADER, MAX_HANDSHAKE_BODY,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a record gave to the layer above: [`super::spec::Event`].
#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    /// Complete handshake messages, each as its whole encoding.
    Messages(Vec<Vec<u8>>),
    /// An alert.
    Alert(Alert),
    /// Application data.
    AppData(Vec<u8>),
    /// A dropped change_cipher_spec record.
    Ignored,
}

/// The spec view of a list of byte vectors.
pub open spec fn views_bytes(ms: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    ms.map_values(|m: Vec<u8>| m@)
}

impl View for Event {
    type V = super::spec::Event;

    open spec fn view(&self) -> super::spec::Event {
        match self {
            Event::Messages(ms) => super::spec::Event::Messages(views_bytes(ms@)),
            Event::Alert(a) => super::spec::Event::Alert(*a),
            Event::AppData(d) => super::spec::Event::AppData(d@),
            Event::Ignored => super::spec::Event::Ignored,
        }
    }
}

/// The exec result of a feed, with the state after it, as the spec's
/// result: an error leaves the connection dead, so its state is not
/// compared.
pub open spec fn res_event(r: Result<Event, ErrKind>, after: super::spec::Reasm) -> super::spec::Res<
    (super::spec::Event, super::spec::Reasm),
> {
    match r {
        Ok(ev) => super::spec::Res::Ok((ev@, after)),
        Err(k) => super::spec::Res::Err(k),
    }
}

/// Prepend messages to the result of [`super::spec::extract_messages`].
pub open spec fn prepend(
    ms: Seq<Seq<u8>>,
    r: super::spec::Res<(Seq<Seq<u8>>, Seq<u8>)>,
) -> super::spec::Res<(Seq<Seq<u8>>, Seq<u8>)> {
    match r {
        super::spec::Res::Err(e) => super::spec::Res::Err(e),
        super::spec::Res::Ok((more, rest)) => super::spec::Res::Ok((ms + more, rest)),
    }
}

/// The reassembler: the bytes of the unfinished handshake message. After a
/// method returns an error the connection is dead and the reassembler must
/// not be used again: the contracts say nothing about its state then.
pub struct Reassembler {
    buf: Vec<u8>,
}

impl View for Reassembler {
    type V = super::spec::Reasm;

    closed spec fn view(&self) -> super::spec::Reasm {
        super::spec::Reasm { buf: self.buf@ }
    }
}

impl Reassembler {
    /// The buffer holds fewer bytes than a message header and the largest
    /// body: the reassembler is bounded. Every method keeps it.
    pub open spec fn wf(&self) -> bool {
        self@.buf.len() < HANDSHAKE_HEADER + MAX_HANDSHAKE_BODY
    }

    /// The state before any record ([`super::spec::reasm_new`]).
    pub fn new() -> (r: Reassembler)
        ensures
            r@ == super::spec::reasm_new(),
            r.wf(),
    {
        Reassembler { buf: Vec::new() }
    }

    /// §5.1: whether no message has begun, as is required at a key
    /// change ([`super::spec::at_message_boundary`]).
    pub fn at_message_boundary(&self) -> (b: bool)
        ensures
            b == super::spec::at_message_boundary(self@),
    {
        self.buf.is_empty()
    }

    /// Take the whole messages off the front of the buffer
    /// ([`super::spec::extract_messages`]).
    fn extract(&mut self) -> (out: Result<Vec<Vec<u8>>, ErrKind>)
        ensures
            match out {
                Ok(ms) => super::spec::extract_messages(old(self)@.buf) == super::spec::Res::<
                    (Seq<Seq<u8>>, Seq<u8>),
                >::Ok((views_bytes(ms@), final(self)@.buf)),
                Err(k) => super::spec::extract_messages(old(self)@.buf) == super::spec::Res::<
                    (Seq<Seq<u8>>, Seq<u8>),
                >::Err(k),
            },
            out is Ok ==> final(self).wf(),
    {
        let ghost orig = old(self)@.buf;
        proof {
            assert(self.buf@ == orig);
        }
        let mut msgs: Vec<Vec<u8>> = Vec::new();
        let mut start: usize = 0;
        proof {
            assert(views_bytes(msgs@) =~= Seq::<Seq<u8>>::empty());
            assert(orig.skip(0) =~= orig);
            assert(prepend(seq![], super::spec::extract_messages(orig)) == super::spec::extract_messages(orig)) by {
                match super::spec::extract_messages(orig) {
                    super::spec::Res::Err(e) => {},
                    super::spec::Res::Ok((more, rest)) => {
                        assert(seq![] + more =~= more);
                    },
                }
            }
        }
        loop
            invariant
                start <= self.buf@.len(),
                self.buf@ == orig,
                super::spec::extract_messages(orig) == prepend(
                    views_bytes(msgs@),
                    super::spec::extract_messages(orig.skip(start as int)),
                ),
            ensures
                super::spec::extract_messages(orig.skip(start as int)) == super::spec::Res::<
                    (Seq<Seq<u8>>, Seq<u8>),
                >::Ok((seq![], orig.skip(start as int))),
            decreases self.buf@.len() - start,
        {
            // start <= len, so this does not saturate.
            let avail = self.buf.len().saturating_sub(start);
            if avail < HANDSHAKE_HEADER {
                proof {
                    assert(orig.skip(start as int).len() < HANDSHAKE_HEADER);
                }
                break;
            }
            // start + 3 < len: the three length bytes are in range, and
            // these sums do not saturate.
            let b1 = byte_at(self.buf.as_slice(), start.saturating_add(1));
            let b2 = byte_at(self.buf.as_slice(), start.saturating_add(2));
            let b3 = byte_at(self.buf.as_slice(), start.saturating_add(3));
            let ghost window = orig.skip(start as int);
            proof {
                assert(window.subrange(1, 4)[0] == orig[start as int + 1]);
                assert(window.subrange(1, 4)[1] == orig[start as int + 2]);
                assert(window.subrange(1, 4)[2] == orig[start as int + 3]);
                super::lemmas_pl::lemma_be_value_3(window.subrange(1, 4));
            }
            // b1 * 65536 + b2 * 256 + b3 < 2^24: no saturation.
            let len: usize = (b1 as usize).saturating_mul(65536).saturating_add((b2 as usize).saturating_mul(256)).saturating_add(
                b3 as usize,
            );
            proof {
                assert(len as nat == super::spec::be_value(window.subrange(1, 4)));
            }
            if len > MAX_HANDSHAKE_BODY {
                proof {
                    assert(super::spec::extract_messages(window) == super::spec::Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(
                        ErrKind::HandshakeTooLarge,
                    ));
                }
                proof {
                    assert(super::spec::extract_messages(orig) == super::spec::Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(
                        ErrKind::HandshakeTooLarge,
                    ));
                }
                return Err(ErrKind::HandshakeTooLarge);
            }
            if avail < HANDSHAKE_HEADER.saturating_add(len) {
                proof {
                    assert(window.len() < HANDSHAKE_HEADER + super::spec::be_value(window.subrange(1, 4)));
                }
                break;
            }
            // HANDSHAKE_HEADER + len <= avail, so these do not saturate.
            let total = HANDSHAKE_HEADER.saturating_add(len);
            let stop = start.saturating_add(total);
            let m = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(self.buf.as_slice(), start, stop));
            proof {
                let m_spec = window.take(total as int);
                assert(m@ =~= m_spec);
                assert(orig.skip(stop as int) =~= window.skip(total as int));
                let tail = window.skip(total as int);
                // One step of extract_messages on `window`.
                assert(super::spec::extract_messages(window) == match super::spec::extract_messages(tail) {
                    super::spec::Res::Err(e) => super::spec::Res::Err(e),
                    super::spec::Res::Ok((ms, rest)) => super::spec::Res::Ok((seq![m_spec] + ms, rest)),
                });
                assert(views_bytes(msgs@.push(m)) =~= views_bytes(msgs@).push(m@));
                match super::spec::extract_messages(tail) {
                    super::spec::Res::Err(e) => {},
                    super::spec::Res::Ok((ms, rest)) => {
                        assert(views_bytes(msgs@) + (seq![m_spec] + ms) =~= views_bytes(msgs@).push(m@) + ms);
                    },
                }
            }
            msgs.push(m);
            start = stop;
        }
        // The bytes from `start` are the start of an unfinished message.
        let ghost window = orig.skip(start as int);
        let rest = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(self.buf.as_slice(), start, self.buf.len()));
        proof {
            assert(views_bytes(msgs@) + Seq::<Seq<u8>>::empty() =~= views_bytes(msgs@));
            super::lemmas_record::lemma_extract_conserves(orig);
        }
        self.buf = rest;
        Ok(msgs)
    }

    /// §5.1: feed one record to the reassembler
    /// ([`super::spec::feed_record`]). `ctype` and `fragment` are what
    /// [`super::record::read_record`] or
    /// [`super::record::decrypt_record`] gave.
    pub fn feed_record(&mut self, ctype: u8, fragment: &[u8]) -> (out: Result<Event, ErrKind>)
        requires
            old(self).wf(),
            fragment.len() <= super::spec::MAX_PLAINTEXT,
        ensures
            out is Ok ==> final(self).wf(),
            res_event(
                out,
                final(self)@,
            ) == super::spec::feed_record(
                old(self)@,
                super::spec::Record { ctype, fragment: fragment@ },
            ),
    {
        if ctype == CT_HANDSHAKE {
            if fragment.is_empty() {
                return Err(ErrKind::ZeroLengthFragment);
            }
            let ghost st0 = old(self)@;
            self.buf.extend_from_slice(fragment);
            proof {
                assert(self.buf@ =~= st0.buf + fragment@);
            }
            // The buffer was below the bound and the fragment is at most
            // MAX_PLAINTEXT, so extract sees at most REASSEMBLY_BOUND bytes.
            match self.extract() {
                Ok(ms) => {
                    proof {
                        super::lemmas_record::lemma_extract_conserves(st0.buf + fragment@);
                        assert(super::spec::extract_messages(st0.buf + fragment@) == super::spec::Res::<
                            (Seq<Seq<u8>>, Seq<u8>),
                        >::Ok((views_bytes(ms@), final(self)@.buf)));
                    }
                    Ok(Event::Messages(ms))
                },
                Err(k) => {
                    proof {
                        assert(res_event(Err(k), final(self)@) == super::spec::Res::<(super::spec::Event, super::spec::Reasm)>::Err(k));
                    }
                    Err(k)
                },
            }
        } else if ctype == CT_ALERT {
            if !self.buf.is_empty() {
                return Err(ErrKind::Interleaved);
            }
            if fragment.is_empty() {
                return Err(ErrKind::ZeroLengthFragment);
            }
            if fragment.len() == 2 {
                let level = byte_at(fragment, 0);
                let description = byte_at(fragment, 1);
                Ok(Event::Alert(Alert { level, description }))
            } else {
                Err(ErrKind::Decode)
            }
        } else if ctype == CT_APPLICATION_DATA {
            if !self.buf.is_empty() {
                return Err(ErrKind::Interleaved);
            }
            Ok(Event::AppData(vstd::slice::slice_to_vec(fragment)))
        } else if ctype == CT_CHANGE_CIPHER_SPEC {
            Err(ErrKind::BadChangeCipherSpec)
        } else {
            Err(ErrKind::UnexpectedContentType)
        }
    }

    /// §5: an unprotected change_cipher_spec record is dropped, unless a
    /// handshake message is unfinished ([`super::spec::feed_ccs`]).
    pub fn feed_ccs(&mut self) -> (out: Result<Event, ErrKind>)
        requires
            old(self).wf(),
        ensures
            out is Ok ==> final(self).wf(),
            res_event(out, final(self)@) == super::spec::feed_ccs(old(self)@),
    {
        if !self.buf.is_empty() {
            return Err(ErrKind::Interleaved);
        }
        Ok(Event::Ignored)
    }
}

} // verus!

impl Default for Reassembler {
    fn default() -> Self {
        Reassembler::new()
    }
}
