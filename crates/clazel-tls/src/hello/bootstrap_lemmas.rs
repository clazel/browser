//! Size and binding lemmas for bootstrap flights.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// A successful fixed-profile HRR retry always fits one TLSPlaintext record.
pub proof fn lemma_retry_flight_bound(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::client_spec::State, server: Seq<u8>, cookie: Seq<u8>,
    next: super::client_spec::State, flight: Seq<u8>)
    requires super::client_spec::wf(before),
        super::client_spec::retry(hash, before, server, cookie)
            == Ok(super::client_spec::Outcome::Retry(next, flight)),
    ensures next.config == before.config, next.transcript.retried,
        flight == crate::spec::write_handshake(1, super::client_spec::body(next.config, cookie)),
        flight.len() <= 4528, flight.len() < 65536,
{
    super::client_lemmas::lemma_retry_configuration(hash, before, server, cookie, next, flight);
    assert(super::client_spec::cookie_ok(cookie));
    assert(cookie.len() <= super::client_spec::MAX_COOKIE);
    super::client_lemmas::lemma_profile(next.config, cookie);
    reveal(crate::spec::write_handshake);
    crate::lemmas_pl::lemma_be_bytes_len(super::client_spec::body(next.config, cookie).len(), 3);
    reveal(crate::spec::write_u24);
    assert(flight.len() == 4 + super::client_spec::body(next.config, cookie).len());
    assert(flight.len() <= 4528);
}

/// A retry selected by the fixed-profile receive operation has a bounded CH2.
pub proof fn lemma_receive_retry_flight_bound(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::client_spec::State, server: Seq<u8>,
    next: super::client_spec::State, flight: Seq<u8>)
    requires super::client_spec::wf(before),
        super::client_spec::receive(hash, before, server)
            == Ok(super::client_spec::Outcome::Retry(next, flight)),
    ensures next.config == before.config, next.transcript.retried,
        flight.len() <= 4528, flight.len() < 65536,
{
    reveal(super::client_spec::receive);
    match super::spec::validate(before.config.session_id, before.transcript.retried, server) {
        Err(_) => assert(false),
        Ok(super::spec::Selection::Share(_)) => assert(false),
        Ok(super::spec::Selection::Retry(cookie)) => {
            assert(super::client_spec::retry(hash, before, server, cookie)
                == Ok(super::client_spec::Outcome::Retry(next, flight)));
            lemma_retry_flight_bound(hash, before, server, cookie, next, flight);
        },
    }
}

/// A terminal (or failed) bootstrap state: no live Hello, no pending flight.
pub open spec fn terminal(s: super::bootstrap_spec::State, mode: super::bootstrap_spec::Mode,
    reassembly: crate::spec::Reasm) -> super::bootstrap_spec::State {
    super::bootstrap_spec::State { mode, hello: None, pending_flight: seq![],
        compatibility: s.compatibility, reassembly }
}

/// The Hello controller's response to the one ServerHello body.
pub open spec fn hello_step(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: super::bootstrap_spec::State,
    body: Seq<u8>) -> (super::bootstrap_spec::State, super::bootstrap_spec::Action) {
    use super::bootstrap_spec::{Action, Mode};
    let reassembly = s.reassembly;
    match s.hello {
        None => (terminal(s, Mode::Failed, reassembly), Action::Fail(crate::spec::INTERNAL_ERROR)),
        Some(hello) => match super::client_spec::receive(hash, hello, body) {
            Err(alert) => (terminal(s, Mode::Failed, reassembly), Action::Fail(alert)),
            Ok(super::client_spec::Outcome::Established(config, transcript, peer_key)) =>
                (terminal(s, Mode::Established, reassembly),
                    Action::Established(config, transcript, peer_key)),
            Ok(super::client_spec::Outcome::Retry(next, flight)) => {
                let hrr = if s.compatibility {
                    super::bootstrap_spec::compatibility_ccs()
                        + super::bootstrap_spec::handshake_record(flight)
                } else { super::bootstrap_spec::handshake_record(flight) };
                (super::bootstrap_spec::State { mode: Mode::AwaitClientHello2Send,
                    hello: Some(next), pending_flight: hrr, compatibility: s.compatibility,
                    reassembly }, Action::Send(hrr))
            },
        },
    }
}


/// What `bootstrap_spec::receive` does with the messages a handshake record
/// completed. `s` already carries the reassembly state after that record.
pub open spec fn after_messages(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: super::bootstrap_spec::State,
    messages: Seq<Seq<u8>>) -> (super::bootstrap_spec::State, super::bootstrap_spec::Action) {
    use super::bootstrap_spec::{Action, Mode};
    let reassembly = s.reassembly;
    if messages.len() == 0 {
        (s, Action::None)
    } else if messages.len() != 1 || reassembly.buf.len() != 0 {
        (terminal(s, Mode::Failed, reassembly), Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
    } else {
        let message = messages[0];
        if message.len() < crate::spec::HANDSHAKE_HEADER || message[0] != crate::spec::HS_SERVER_HELLO {
            (terminal(s, Mode::Failed, reassembly), Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
        } else {
            let body = message.skip(crate::spec::HANDSHAKE_HEADER as int);
            hello_step(hash, s, body)
        }
    }
}

/// What `bootstrap_spec::receive` does with a handshake fragment.
pub open spec fn fragment_step(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: super::bootstrap_spec::State,
    fragment: Seq<u8>) -> (super::bootstrap_spec::State, super::bootstrap_spec::Action) {
    use super::bootstrap_spec::{Action, Mode};
    match crate::spec::feed_record(s.reassembly,
        crate::spec::Record { ctype: crate::spec::CT_HANDSHAKE, fragment }) {
        crate::spec::Res::Err(error) => (terminal(s, Mode::Failed, s.reassembly),
            Action::Fail(crate::spec::alert_of(error))),
        crate::spec::Res::Ok((crate::spec::Event::Messages(messages), reassembly)) =>
            after_messages(hash, super::bootstrap_spec::State { reassembly, ..s }, messages),
        crate::spec::Res::Ok((_, reassembly)) => (terminal(s, Mode::Failed, reassembly),
            Action::Fail(crate::spec::UNEXPECTED_MESSAGE)),
    }
}

/// What `bootstrap_spec::receive` does with an alert.
pub open spec fn alert_step(s: super::bootstrap_spec::State, level: u8, description: u8)
    -> (super::bootstrap_spec::State, super::bootstrap_spec::Action) {
    use super::bootstrap_spec::{Action, Mode};
    match crate::spec::feed_record(s.reassembly,
        crate::spec::Record { ctype: crate::spec::CT_ALERT, fragment: seq![level, description] }) {
        crate::spec::Res::Err(error) => (terminal(s, Mode::Failed, s.reassembly),
            Action::Fail(crate::spec::alert_of(error))),
        crate::spec::Res::Ok((_, reassembly)) => {
            if description == crate::spec::CLOSE_NOTIFY {
                (terminal(s, Mode::Closed, reassembly), Action::Close)
            } else {
                (terminal(s, Mode::Failed, reassembly), Action::Alert(description))
            }
        },
    }
}

/// `bootstrap_spec::feed`, once a complete record `wire` is framed.
pub open spec fn record_step(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: super::bootstrap_spec::State,
    wire: Seq<u8>) -> (super::bootstrap_spec::State, super::bootstrap_spec::Action) {
    use super::bootstrap_spec::{Action, Mode};
    match crate::spec::read_record(wire, false) {
        crate::spec::Read::Done(frame, rest) => {
            if rest.len() != 0 {
                (terminal(s, Mode::Failed, s.reassembly), Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
            } else {
                match frame {
                    crate::spec::Frame::Ccs => (s, Action::None),
                    crate::spec::Frame::Plain(rec) if rec.ctype == crate::spec::CT_HANDSHAKE =>
                        fragment_step(hash, s, rec.fragment),
                    crate::spec::Frame::Plain(rec) if rec.ctype == crate::spec::CT_ALERT =>
                        match crate::spec::read_alert(rec.fragment) {
                            Some(alert) => alert_step(s, alert.level, alert.description),
                            None => (terminal(s, Mode::Failed, s.reassembly),
                                Action::Fail(crate::spec::DECODE_ERROR)),
                        },
                    _ => (terminal(s, Mode::Failed, s.reassembly),
                        Action::Fail(crate::spec::UNEXPECTED_MESSAGE)),
                }
            }
        },
        crate::spec::Read::Fail(error) => (terminal(s, Mode::Failed, s.reassembly),
            Action::Fail(crate::spec::alert_of(error))),
        crate::spec::Read::NeedMore => (terminal(s, Mode::Failed, s.reassembly),
            Action::Fail(crate::spec::DECODE_ERROR)),
    }
}

/// A completed framed record is handled exactly as `record_step` says.
pub proof fn lemma_feed_complete(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: super::bootstrap_spec::State,
    framing: Seq<u8>, input: Seq<u8>)
    requires s.mode == super::bootstrap_spec::Mode::AwaitServerHello,
        crate::connection::framing_spec::feed_mode(framing, input, false).status
            == crate::connection::framing_spec::Status::Complete,
    ensures ({
        let framed = crate::connection::framing_spec::feed_mode(framing, input, false);
        super::bootstrap_spec::feed(hash, s, framing, input) == super::bootstrap_spec::Feed {
            consumed: framed.consumed, state: record_step(hash, s, framed.buffer).0,
            framing: seq![], action: record_step(hash, s, framed.buffer).1 }
    }),
{
    let framed = crate::connection::framing_spec::feed_mode(framing, input, false);
    match crate::spec::read_record(framed.buffer, false) {
        crate::spec::Read::Done(frame, rest) => {
            if rest.len() == 0 {
                match frame {
                    crate::spec::Frame::Plain(rec) if rec.ctype == crate::spec::CT_ALERT => {
                        match crate::spec::read_alert(rec.fragment) {
                            Some(alert) => {
                                assert(super::bootstrap_spec::receive(hash, s,
                                    super::bootstrap_spec::PeerEvent::Alert(alert.level, alert.description))
                                    == alert_step(s, alert.level, alert.description));
                            },
                            None => {},
                        }
                    },
                    crate::spec::Frame::Plain(rec) if rec.ctype == crate::spec::CT_HANDSHAKE => {
                        assert(super::bootstrap_spec::receive(hash, s,
                            super::bootstrap_spec::PeerEvent::HandshakeFragment(rec.fragment))
                            == fragment_step(hash, s, rec.fragment));
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

/// An unprotected plain record carries at most one record's worth of bytes.
pub proof fn lemma_plain_fragment_bound(wire: Seq<u8>, rec: crate::spec::Record, rest: Seq<u8>)
    requires crate::spec::read_record(wire, false)
        == crate::spec::Read::Done(crate::spec::Frame::Plain(rec), rest),
    ensures rec.fragment.len() <= crate::spec::MAX_PLAINTEXT,
{
}
} // verus!
