//! RFC 8446 §4.1.2–§4.1.4, §5 and Appendix D.4: the client bootstrap through
//! the final ServerHello. Record framing, negotiation and transcript updates
//! are delegated to the existing verified modules.
use super::client::{Config, Established, Hello, Outcome};
use crate::connection::framing::{Buffer, Status as FrameStatus};
use crate::reassemble::{Event as ReassemblyEvent, Reassembler};
use crate::record::{Frame, ReadOut};
use crate::schedule::crypto::Crypto;
use crate::spec::Alert;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// Runtime bootstrap phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Initial ClientHello awaits its exact send acknowledgement.
    AwaitClientHelloSend,
    /// The acknowledged ClientHello awaits one server Hello response.
    AwaitServerHello,
    /// ClientHello2 awaits its exact send acknowledgement.
    AwaitClientHello2Send,
    /// Final ServerHello accepted; caller owns the handoff.
    Established,
    /// Bootstrap terminated after a protocol or transport failure.
    Failed,
    /// Peer sent close_notify before final ServerHello.
    Closed,
}
impl View for Mode {
    type V = super::bootstrap_spec::Mode;
    open spec fn view(&self) -> Self::V {
        match self {
            Mode::AwaitClientHelloSend => super::bootstrap_spec::Mode::AwaitClientHelloSend,
            Mode::AwaitServerHello => super::bootstrap_spec::Mode::AwaitServerHello,
            Mode::AwaitClientHello2Send => super::bootstrap_spec::Mode::AwaitClientHello2Send,
            Mode::Established => super::bootstrap_spec::Mode::Established,
            Mode::Failed => super::bootstrap_spec::Mode::Failed,
            Mode::Closed => super::bootstrap_spec::Mode::Closed,
        }
    }
}

/// Caller-visible bootstrap effect.
pub enum Action {
    /// Input was incomplete or a valid dummy CCS was dropped.
    None,
    /// Exact plaintext wire flight; acknowledge these bytes before feeding more input.
    Send(Vec<u8>),
    /// Final Hello parameters, transcript and peer share for the existing join.
    Established(Established),
    /// Peer alert surfaced without sending a reflexive alert.
    Alert(u8),
    /// Local TLS/transport failure; no alert is sent automatically.
    Fail(u8),
    /// Peer close_notify ended bootstrap.
    Close,
}
impl View for Action {
    type V = super::bootstrap_spec::Action;
    open spec fn view(&self) -> Self::V {
        match self {
            Action::None => super::bootstrap_spec::Action::None,
            Action::Send(bytes) => super::bootstrap_spec::Action::Send(bytes@),
            Action::Established(e) => super::bootstrap_spec::Action::Established(e@.0, e@.1, e@.2),
            Action::Alert(alert) => super::bootstrap_spec::Action::Alert(*alert),
            Action::Fail(alert) => super::bootstrap_spec::Action::Fail(*alert),
            Action::Close => super::bootstrap_spec::Action::Close,
        }
    }
}

/// Convert a constructor result to its abstract result.
pub open spec fn start_view<C: Crypto>(out: Result<(Bootstrap<C>, Action), u8>)
    -> Result<(super::bootstrap_spec::State, super::bootstrap_spec::Action), u8> {
    match out {
        Err(alert) => Err(alert),
        Ok((driver, action)) => Ok((driver@.0, action@)),
    }
}

fn receive_hello<C: Crypto>(hello: Hello, crypto: &C, body: &[u8]) -> (out: Result<Outcome, u8>)
    requires hello.wf(), super::client_spec::wf(hello@),
    ensures super::client_contract::receive_ensures(crypto.functions().hash, hello@, body@,
        super::client::outcome_view(out)),
        match out {
            Ok(Outcome::Retry(next, flight)) => next.wf() && flight.len() < 65536,
            _ => true,
        },
{
    let ghost before = hello@;
    let out = hello.receive(crypto, body);
    proof {
        reveal(super::client_contract::receive_ensures);
        match &out {
            Ok(Outcome::Retry(next, flight)) => {
                assert(super::client_spec::receive(crypto.functions().hash, before, body@)
                    == Ok(super::client_spec::Outcome::Retry(next@, flight@)));
                super::bootstrap_lemmas::lemma_receive_retry_flight_bound(
                    crypto.functions().hash, before, body@, next@, flight@);
                assert(super::client_spec::wf(next@));
                assert(next.wf());
                assert(flight.len() < 65536);
            },
            _ => {},
        }
    }
    out
}

/// The action-driven client-side gate through ServerHello processing.
pub struct Bootstrap<C: Crypto> {
    crypto: C,
    mode: Mode,
    hello: Option<Hello>,
    pending_flight: Vec<u8>,
    compatibility: bool,
    reassembler: Reassembler,
    framer: Buffer,
}
impl<C: Crypto> Bootstrap<C> {
    pub closed spec fn state(&self) -> super::bootstrap_spec::State {
        super::bootstrap_spec::State {
            mode: self.mode@,
            hello: match self.hello { Some(hello) => Some(hello@), None => None },
            pending_flight: self.pending_flight@,
            compatibility: self.compatibility,
            reassembly: self.reassembler@,
        }
    }
}
impl<C: Crypto> View for Bootstrap<C> {
    type V = (super::bootstrap_spec::State, Seq<u8>);
    closed spec fn view(&self) -> Self::V { (self.state(), self.framer@) }
}
impl<C: Crypto> Bootstrap<C> {
    /// Abstract cryptographic functions retained by this bootstrap controller.
    pub closed spec fn crypto_functions(&self) -> crate::schedule::spec::Crypto {
        self.crypto.functions()
    }

    /// All retained protocol state and bounded byte buffers are valid.
    pub closed spec fn wf(&self) -> bool {
        super::bootstrap_spec::wf(self.state())
            && match self.hello { Some(hello) => hello.wf(), None => true }
            && self.reassembler.wf() && !self.framer.protected_mode() && self.framer.wf_mode(false)
    }

    fn fail(&mut self, alert: u8) -> (out: Action)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).state().mode == super::bootstrap_spec::Mode::Failed,
            final(self).state().hello is None, final(self).state().pending_flight.len() == 0,
            final(self).state().compatibility == old(self).state().compatibility,
            final(self).state().reassembly == old(self).state().reassembly,
            final(self).state() == super::bootstrap_lemmas::terminal(old(self).state(),
                super::bootstrap_spec::Mode::Failed, old(self).state().reassembly),
            final(self).framer@ == old(self).framer@,
            out@ == super::bootstrap_spec::Action::Fail(alert),
    {
        self.mode = Mode::Failed;
        self.hello = None;
        self.pending_flight.clear();
        proof {
            reveal(Bootstrap::state);
            assert(self.pending_flight@ =~= Seq::<u8>::empty());
        }
        Action::Fail(alert)
    }

    fn close(&mut self) -> (out: Action)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).state().mode == super::bootstrap_spec::Mode::Closed,
            final(self).state().hello is None, final(self).state().pending_flight.len() == 0,
            final(self).state() == super::bootstrap_lemmas::terminal(old(self).state(),
                super::bootstrap_spec::Mode::Closed, old(self).state().reassembly),
            final(self).framer@ == old(self).framer@,
            out@ == super::bootstrap_spec::Action::Close,
    {
        self.mode = Mode::Closed;
        self.hello = None;
        self.pending_flight.clear();
        proof {
            reveal(Bootstrap::state);
            assert(self.pending_flight@ =~= Seq::<u8>::empty());
        }
        Action::Close
    }

    fn peer_alert(&mut self, description: u8) -> (out: Action)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).state().mode == super::bootstrap_spec::Mode::Failed,
            final(self).state().hello is None, final(self).state().pending_flight.len() == 0,
            final(self).state() == super::bootstrap_lemmas::terminal(old(self).state(),
                super::bootstrap_spec::Mode::Failed, old(self).state().reassembly),
            final(self).framer@ == old(self).framer@,
            out@ == super::bootstrap_spec::Action::Alert(description),
    {
        self.mode = Mode::Failed;
        self.hello = None;
        self.pending_flight.clear();
        proof {
            reveal(Bootstrap::state);
            assert(self.pending_flight@ =~= Seq::<u8>::empty());
        }
        Action::Alert(description)
    }

    fn handle_messages(&mut self, messages: Vec<Vec<u8>>) -> (out: Action)
        requires old(self).wf(), old(self).mode == Mode::AwaitServerHello,
        ensures final(self).wf(), final(self).framer@ == old(self).framer@,
            (final(self).state(), out@) == super::bootstrap_lemmas::after_messages(
                old(self).crypto_functions().hash, old(self).state(),
                crate::reassemble::views_bytes(messages@)),
    {
        let ghost before = self.state();
        if messages.is_empty() {
            return Action::None;
        }
        if messages.len() != 1 || !self.reassembler.at_message_boundary() {
            return self.fail(crate::spec::UNEXPECTED_MESSAGE);
        }
        let message = match messages.first() {
            Some(message) => message,
            None => return self.fail(crate::spec::INTERNAL_ERROR),
        };
        let first = match message.first() {
            Some(first) => *first,
            None => return self.fail(crate::spec::UNEXPECTED_MESSAGE),
        };
        if message.len() < crate::spec::HANDSHAKE_HEADER || first != crate::spec::HS_SERVER_HELLO {
            return self.fail(crate::spec::UNEXPECTED_MESSAGE);
        }
        let body = vstd::slice::slice_subrange(message.as_slice(), crate::spec::HANDSHAKE_HEADER, message.len());
        proof { assert(body@ =~= message@.skip(crate::spec::HANDSHAKE_HEADER as int)); }
        self.handle_hello_message(body)
    }

    fn handle_hello_message(&mut self, body: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).mode == Mode::AwaitServerHello,
        ensures final(self).wf(), final(self).framer@ == old(self).framer@,
            (final(self).state(), out@) == super::bootstrap_lemmas::hello_step(
                old(self).crypto_functions().hash, old(self).state(), body@),
    {
        let ghost before = self.state();
        let hello = match self.hello.take() {
            Some(hello) => hello,
            None => return self.fail(crate::spec::INTERNAL_ERROR),
        };
        proof {
            reveal(Bootstrap::wf);
            reveal(Bootstrap::state);
            reveal(super::bootstrap_spec::wf);
            assert(before.hello is Some);
            assert(match before.hello { Some(h) => h == hello@ && super::client_spec::wf(h), None => false });
            assert(super::client_spec::wf(hello@));
            assert(hello.wf());
        }
        let ghost hash = self.crypto_functions().hash;
        let ghost hello_view = hello@;
        let result = receive_hello(hello, &self.crypto, body);
        proof {
            reveal(super::client_contract::receive_ensures);
            assert(super::client::outcome_view(result) == super::client_spec::receive(hash, hello_view, body@));
        }
        match result {
            Err(alert) => {
                self.mode = Mode::Failed;
                self.pending_flight.clear();
                proof {
                    reveal(Bootstrap::wf);
                    reveal(Bootstrap::state);
                    reveal(super::bootstrap_spec::wf);
                    assert(self.pending_flight@ =~= Seq::<u8>::empty());
                    let ghost after = self.state();
                    assert(after == super::bootstrap_lemmas::terminal(before,
                        super::bootstrap_spec::Mode::Failed, before.reassembly));
                }
                Action::Fail(alert)
            },
            Ok(Outcome::Established(established)) => {
                self.mode = Mode::Established;
                proof {
                    reveal(Bootstrap::wf);
                    reveal(Bootstrap::state);
                    reveal(super::bootstrap_spec::wf);
                    assert(self.pending_flight@.len() == 0);
                    assert(self.pending_flight@ =~= Seq::<u8>::empty());
                    let ghost after = self.state();
                    assert(after == super::bootstrap_lemmas::terminal(before,
                        super::bootstrap_spec::Mode::Established, before.reassembly));
                }
                Action::Established(established)
            },
            Ok(Outcome::Retry(next, flight)) => {
                let mut wire = Vec::new();
                if self.compatibility {
                    wire.extend_from_slice(&[20, 3, 3, 0, 1, 1]);
                    proof { assert(wire@ =~= super::bootstrap_spec::compatibility_ccs()); }
                }
                crate::record::write_plaintext(&mut wire, crate::spec::CT_HANDSHAKE, 0x0303, flight.as_slice());
                self.pending_flight = vstd::slice::slice_to_vec(wire.as_slice());
                self.hello = Some(next);
                self.mode = Mode::AwaitClientHello2Send;
                proof {
                    reveal(Bootstrap::wf);
                    reveal(Bootstrap::state);
                    reveal(super::bootstrap_spec::wf);
                    super::bootstrap_lemmas::lemma_receive_retry_flight_bound(
                        hash, hello_view, body@, next@, flight@);
                }
                Action::Send(wire)
            },
        }
    }

    fn handle_alert(&mut self, alert: Alert) -> (out: Action)
        requires old(self).wf(), old(self).mode == Mode::AwaitServerHello,
        ensures final(self).wf(), final(self).framer@ == old(self).framer@,
            (final(self).state(), out@) == if alert.description == crate::spec::CLOSE_NOTIFY {
                (super::bootstrap_lemmas::terminal(old(self).state(),
                    super::bootstrap_spec::Mode::Closed, old(self).state().reassembly),
                    super::bootstrap_spec::Action::Close)
            } else {
                (super::bootstrap_lemmas::terminal(old(self).state(),
                    super::bootstrap_spec::Mode::Failed, old(self).state().reassembly),
                    super::bootstrap_spec::Action::Alert(alert.description))
            },
    {
        if alert.description == crate::spec::CLOSE_NOTIFY {
            self.close()
        } else {
            self.peer_alert(alert.description)
        }
    }

    fn handle_handshake(&mut self, bytes: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).mode == Mode::AwaitServerHello,
            bytes.len() <= crate::spec::MAX_PLAINTEXT,
        ensures final(self).wf(), final(self).framer@ == old(self).framer@,
            (final(self).state(), out@) == super::bootstrap_lemmas::fragment_step(
                old(self).crypto_functions().hash, old(self).state(), bytes@),
    {
        let ghost before = self.state();
        let saved = self.reassembler.snapshot();
        proof {
            reveal(Bootstrap::state);
            reveal(Bootstrap::wf);
            assert(saved@ == before.reassembly);
        }
        match self.reassembler.feed_record(crate::spec::CT_HANDSHAKE, bytes) {
            Err(error) => {
                self.reassembler = saved;
                proof {
                    reveal(Bootstrap::state);
                    reveal(Bootstrap::wf);
                    assert(self.state() == before);
                }
                self.fail(crate::encode::alert_for(error).description)
            },
            Ok(ReassemblyEvent::Messages(messages)) => {
                proof {
                    reveal(Bootstrap::state);
                    reveal(Bootstrap::wf);
                    reveal(super::bootstrap_spec::wf);
                    assert(self.state() == (super::bootstrap_spec::State { reassembly: self.reassembler@, ..before }));
                    assert(self.wf());
                }
                self.handle_messages(messages)
            },
            Ok(_) => {
                proof {
                    reveal(Bootstrap::state);
                    reveal(Bootstrap::wf);
                    reveal(super::bootstrap_spec::wf);
                    assert(self.wf());
                }
                self.fail(crate::spec::UNEXPECTED_MESSAGE)
            },
        }
    }

    fn handle_alert_record(&mut self, bytes: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).mode == Mode::AwaitServerHello,
            bytes.len() <= crate::spec::MAX_PLAINTEXT, bytes.len() != 0,
        ensures final(self).wf(), final(self).framer@ == old(self).framer@,
            (final(self).state(), out@) == match crate::spec::read_alert(bytes@) {
                Some(alert) => super::bootstrap_lemmas::alert_step(old(self).state(),
                    alert.level, alert.description),
                None => (super::bootstrap_lemmas::terminal(old(self).state(),
                    super::bootstrap_spec::Mode::Failed, old(self).state().reassembly),
                    super::bootstrap_spec::Action::Fail(crate::spec::DECODE_ERROR)),
            },
    {
        let ghost before = self.state();
        if bytes.len() != 2 {
            return self.fail(crate::spec::DECODE_ERROR);
        }
        let saved = self.reassembler.snapshot();
        proof {
            reveal(Bootstrap::state);
            reveal(Bootstrap::wf);
            assert(saved@ == before.reassembly);
            assert(bytes@ =~= seq![bytes@[0], bytes@[1]]);
        }
        match self.reassembler.feed_record(crate::spec::CT_ALERT, bytes) {
            Err(error) => {
                self.reassembler = saved;
                proof {
                    reveal(Bootstrap::state);
                    reveal(Bootstrap::wf);
                    assert(self.state() == before);
                }
                self.fail(crate::encode::alert_for(error).description)
            },
            Ok(ReassemblyEvent::Alert(alert)) => {
                proof {
                    reveal(Bootstrap::state);
                    reveal(Bootstrap::wf);
                    reveal(super::bootstrap_spec::wf);
                    assert(self.state() == before);
                    assert(self.wf());
                }
                self.handle_alert(alert)
            },
            Ok(_) => {
                proof {
                    reveal(Bootstrap::state);
                    reveal(Bootstrap::wf);
                    reveal(super::bootstrap_spec::wf);
                    assert(false);
                }
                self.fail(crate::spec::UNEXPECTED_MESSAGE)
            },
        }
    }

    fn handle_record(&mut self, wire: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).mode == Mode::AwaitServerHello,
        ensures final(self).wf(), final(self).framer@ == old(self).framer@,
            (final(self).state(), out@) == super::bootstrap_lemmas::record_step(
                old(self).crypto_functions().hash, old(self).state(), wire@),
    {
        match crate::record::read_record(wire, false) {
            ReadOut::Done(Frame::Ccs, rest) => {
                if !rest.is_empty() { self.fail(crate::spec::UNEXPECTED_MESSAGE) }
                else { Action::None }
            },
            ReadOut::Done(Frame::Plain(typ, bytes), rest) => {
                if !rest.is_empty() { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
                proof {
                    super::bootstrap_lemmas::lemma_plain_fragment_bound(wire@,
                        crate::spec::Record { ctype: typ, fragment: bytes@ }, rest@);
                }
                if typ == crate::spec::CT_HANDSHAKE {
                    self.handle_handshake(bytes)
                } else if typ == crate::spec::CT_ALERT {
                    if bytes.is_empty() { return self.fail(crate::spec::DECODE_ERROR); }
                    self.handle_alert_record(bytes)
                } else {
                    self.fail(crate::spec::UNEXPECTED_MESSAGE)
                }
            },
            ReadOut::Done(_, _) => self.fail(crate::spec::UNEXPECTED_MESSAGE),
            ReadOut::Fail(error) => self.fail(crate::encode::alert_for(error).description),
            ReadOut::NeedMore => self.fail(crate::spec::DECODE_ERROR),
        }
    }

    /// Start with a fresh ClientHello and return the exact plaintext record to send.
    pub fn start(config: Config, crypto: C) -> (out: Result<(Self, Action), u8>)
        ensures super::bootstrap_contract::start_ensures(config@, start_view(out)),
    {
        let ghost config_view = config@;
        let compatibility = !config.session_id.is_empty();
        let started = Hello::start(config);
        let ghost started_view = super::client::start_view(started);
        let (hello, flight) = started?;
        proof {
            assert(started_view == Ok((hello@, flight@)));
            assert(super::client_spec::config_ok(config_view));
            super::client_lemmas::lemma_profile(config_view, seq![]);
            assert(flight@ == crate::spec::write_handshake(1, super::client_spec::body(config_view, seq![])));
            reveal(crate::spec::write_handshake);
            crate::lemmas_pl::lemma_be_bytes_len(super::client_spec::body(config_view, seq![]).len(), 3);
            reveal(crate::spec::write_u24);
            assert(flight@.len() == 4 + super::client_spec::body(config_view, seq![]).len());
            assert(flight.len() < 65536);
        }
        let mut wire = Vec::new();
        crate::record::write_plaintext(&mut wire, crate::spec::CT_HANDSHAKE, 0x0303, flight.as_slice());
        let pending = vstd::slice::slice_to_vec(wire.as_slice());
        let driver = Bootstrap {
            crypto,
            mode: Mode::AwaitClientHelloSend,
            hello: Some(hello),
            pending_flight: pending,
            compatibility,
            reassembler: Reassembler::new(),
            framer: Buffer::new_plaintext(),
        };
        proof {
            assert(super::bootstrap_contract::start_ensures(config_view,
                Ok((driver@.0, super::bootstrap_spec::Action::Send(wire@)))));
        }
        Ok((driver, Action::Send(wire)))
    }

    /// Accept only the exact send completion associated with the current flight.
    pub fn acknowledge_send(&mut self, sent: &[u8]) -> (out: Action)
        requires old(self).wf(),
        ensures final(self).wf(),
            super::bootstrap_contract::acknowledge_ensures(old(self).state(), sent@,
                (final(self).state(), out@)),
    {
        let ghost before = self.state();
        let ghost mode0 = self.mode;
        let ghost pending0 = self.pending_flight@;
        proof {
            reveal(Bootstrap::state);
            assert(before.mode == self.mode@);
            assert(before.mode == mode0@);
            assert(before.pending_flight == self.pending_flight@);
            assert(before.pending_flight == pending0);
        }
        let mode_ok = matches!(self.mode, Mode::AwaitClientHelloSend | Mode::AwaitClientHello2Send);
        let same = crate::handshake::bytes_eq(sent, self.pending_flight.as_slice());
        proof {
            assert(mode_ok == (mode0 == Mode::AwaitClientHelloSend || mode0 == Mode::AwaitClientHello2Send));
            assert(same == (sent@ == pending0));
        }
        if !mode_ok || !same {
            let action = self.fail(crate::spec::INTERNAL_ERROR);
            proof {
                reveal(Bootstrap::state);
                reveal(super::bootstrap_spec::acknowledge);
                assert(super::bootstrap_spec::wf(before));
                assert(action@ == super::bootstrap_spec::Action::Fail(crate::spec::INTERNAL_ERROR));
                let ghost expected = super::bootstrap_spec::acknowledge(before, sent@);
                let ghost after = self.state();
                if !mode_ok {
                    assert(before.mode != super::bootstrap_spec::Mode::AwaitClientHelloSend
                        && before.mode != super::bootstrap_spec::Mode::AwaitClientHello2Send);
                } else {
                    assert(sent@ != pending0);
                    assert(sent@ != before.pending_flight);
                }
                assert(after.mode == expected.0.mode);
                assert(after.hello == expected.0.hello);
                assert(after.pending_flight == expected.0.pending_flight);
                assert(after.compatibility == expected.0.compatibility);
                assert(after.reassembly == expected.0.reassembly);
                assert(after == expected.0);
                assert(action@ == super::bootstrap_spec::acknowledge(before, sent@).1);
            }
            return action;
        }
        proof {
            assert(sent@ == before.pending_flight);
        }
        self.pending_flight.clear();
        self.mode = Mode::AwaitServerHello;
        proof {
            reveal(Bootstrap::state);
            reveal(super::bootstrap_spec::acknowledge);
            assert(super::bootstrap_spec::wf(before));
            assert(mode_ok && same);
            assert(mode0 == Mode::AwaitClientHelloSend || mode0 == Mode::AwaitClientHello2Send);
            assert(before.mode == super::bootstrap_spec::Mode::AwaitClientHelloSend
                || before.mode == super::bootstrap_spec::Mode::AwaitClientHello2Send);
            let ghost expected = super::bootstrap_spec::acknowledge(before, sent@);
            let ghost after = self.state();
            assert(after.mode == expected.0.mode);
            assert(after.hello == expected.0.hello);
            assert(after.pending_flight == expected.0.pending_flight);
            assert(after.compatibility == expected.0.compatibility);
            assert(after.reassembly == expected.0.reassembly);
            assert(after == expected.0);
            assert(super::bootstrap_spec::Action::None == super::bootstrap_spec::acknowledge(before, sent@).1);
        }
        Action::None
    }

    /// Consume no more than one plaintext record prefix; the caller resubmits the suffix.
    pub fn feed(&mut self, input: &[u8]) -> (out: (usize, Action))
        requires old(self).wf(),
        ensures final(self).wf(), out.0 <= input.len(),
            super::bootstrap_contract::feed_exec_ensures(old(self).crypto_functions().hash, old(self)@.0,
                old(self)@.1, input@, out.0 as nat, out.1@, final(self)@.0, final(self)@.1),
    {
        hide(crate::connection::framing_spec::feed_mode);
        let ghost before = self.state();
        let ghost hash = self.crypto_functions().hash;
        let ghost framing0 = self.framer@;
        if !matches!(self.mode, Mode::AwaitServerHello) {
            proof {
                reveal(Bootstrap::state);
                assert(before.mode == self.mode@);
                assert(before.mode != super::bootstrap_spec::Mode::AwaitServerHello);
            }
            return (0, Action::None);
        }
        proof {
            reveal(Bootstrap::state);
            reveal(Bootstrap::wf);
            crate::connection::framing::lemma_wf_mode(&self.framer, false);
        }
        let (consumed, status) = self.framer.feed(input);
        let action = match status {
            FrameStatus::Pending => Action::None,
            FrameStatus::Fail(alert) => self.fail(alert),
            FrameStatus::Complete => {
                let wire = self.framer.take();
                let ghost taken = self.framer@;
                let a = self.handle_record(wire.as_slice());
                proof {
                    reveal(Bootstrap::state);
                    super::bootstrap_lemmas::lemma_feed_complete(hash, before, framing0, input@);
                }
                a
            },
        };
        (consumed, action)
    }

    /// EOF before final ServerHello is a truncation failure.
    pub fn eof(&mut self) -> (out: Action)
        requires old(self).wf(),
        ensures final(self).wf(),
            super::bootstrap_contract::eof_ensures(old(self).state(), final(self).state(), out@),
    {
        let ghost before = self.state();
        match self.mode {
            Mode::Failed | Mode::Closed | Mode::Established => {
                proof {
                    reveal(Bootstrap::state);
                    reveal(super::bootstrap_spec::eof);
                    assert(self.state() == before);
                }
                Action::None
            },
            Mode::AwaitClientHelloSend | Mode::AwaitServerHello | Mode::AwaitClientHello2Send => {
                let action = self.fail(crate::spec::INTERNAL_ERROR);
                proof {
                    reveal(Bootstrap::state);
                    reveal(super::bootstrap_spec::eof);
                    let ghost after = self.state();
                    let ghost expected = super::bootstrap_spec::eof(before).0;
                    assert(after.mode == expected.mode);
                    assert(after.hello == expected.hello);
                    assert(after.pending_flight == expected.pending_flight);
                    assert(after.compatibility == expected.compatibility);
                    assert(after.reassembly == expected.reassembly);
                    assert(self.state() == super::bootstrap_spec::eof(before).0);
                    assert(action@ == super::bootstrap_spec::eof(before).1);
                }
                action
            },
        }
    }
}
} // verus!
