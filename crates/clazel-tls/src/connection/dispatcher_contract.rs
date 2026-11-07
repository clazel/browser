//! Refinement contracts for the initial TLS connection dispatcher.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Construction preserves the exact Hello handoff and compatibility-CCS metadata.
pub open spec fn start_ensures(h: crate::traffic::handshake_spec::Handoff, ccs_pending: bool,
    out: super::dispatcher_spec::State) -> bool {
    out == super::dispatcher_spec::start(h, ccs_pending) && super::dispatcher_spec::wf(out)
        && out.auth == Some(h.0) && out.handshake_sender == Some(h.1)
        && out.handshake_receiver == Some(h.2) && out.master == h.3
        && out.ccs_pending == ccs_pending && out.framing == seq![]
        && out.reassembly == crate::spec::reasm_new()
}

/// Active epoch closures remain bound to the exact factory and active keys.
pub open spec fn cipher_bindings(factory: crate::traffic::spec::Cipher,
    ciphers: super::dispatcher_spec::Ciphers, state: super::dispatcher_spec::State) -> bool {
    ciphers.seal == factory.seal && ciphers.open == factory.open
}

/// Initial provider binding follows the handoff's direction labels exactly.
pub open spec fn start_bound_ensures(h: crate::traffic::handshake_spec::Handoff, ccs_pending: bool,
    factory: crate::traffic::spec::Cipher, ciphers: super::dispatcher_spec::Ciphers,
    out: super::dispatcher_spec::State) -> bool {
    start_ensures(h, ccs_pending, out)
        && cipher_bindings(factory, ciphers, out)
}

/// Fatal parser, record, authentication, or I/O failure drops all live keys.
pub open spec fn terminal_ensures(out: super::dispatcher_spec::State, mode: super::dispatcher_spec::Mode) -> bool {
    (mode == super::dispatcher_spec::Mode::Failed || mode == super::dispatcher_spec::Mode::Closed)
        && out == if mode == super::dispatcher_spec::Mode::Failed {
            super::dispatcher_spec::failed()
        } else {
            super::dispatcher_spec::closed()
        }
        && super::dispatcher_spec::wf(out) && super::dispatcher_spec::no_live_secrets(out)
}

/// Every feed is bounded and keeps the lifecycle invariant; while a client
/// flight is outstanding it consumes no peer bytes.
pub open spec fn feed_ensures(before: super::dispatcher_spec::State, input: Seq<u8>,
    consumed: nat, action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool {
    super::dispatcher_spec::wf(before) && super::dispatcher_spec::wf(after)
        && consumed <= input.len()
        && (before.mode == super::dispatcher_spec::Mode::AwaitClientFlight ==> consumed == 0)
        && (before.mode == super::dispatcher_spec::Mode::Ready ==> consumed == 0 && after == before)
        && super::dispatcher_spec::action_refines(action, after)
}

/// Every feed is the dispatcher's own step ([`super::dispatcher_spec::feed`]),
/// exactly: the same octets consumed, the same action and the same state.
pub open spec fn feed_exact(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    ciphers: super::dispatcher_spec::Ciphers, before: super::dispatcher_spec::State, input: Seq<u8>,
    consumed: nat, action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool {
    (consumed, action, after) == super::dispatcher_spec::feed(c, v, ciphers, before, input)
}

/// The acknowledgement is [`super::dispatcher_spec::acknowledge`], exactly.
pub open spec fn acknowledge_exact(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    ciphers: super::dispatcher_spec::Ciphers, before: super::dispatcher_spec::State, sent: Seq<u8>,
    action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool {
    (action, after) == super::dispatcher_spec::acknowledge(c, v, ciphers, before, sent)
}

/// RFC 8446 §5.1: a valid unprotected compatibility CCS record, in a state
/// that still holds authentication, is dropped only at a handshake message
/// boundary; in the middle of a fragmented handshake message it is fatal.
pub open spec fn ccs_record_ensures(ciphers: super::dispatcher_spec::Ciphers, wire: Seq<u8>,
    before: super::dispatcher_spec::State, action: super::dispatcher_spec::Action,
    after: super::dispatcher_spec::State) -> bool {
    (before.auth is Some && crate::spec::read_record(wire, true) is Done
        && crate::spec::read_record(wire, true)->Done_0 is Ccs)
        ==> (action, after) == super::dispatcher_spec::receive_compatibility_ccs(ciphers, before)
}

/// RFC 8446 §6, §6.2, §5.3: a locally detected fatal error puts out the fatal
/// alert sealed under the settled write epoch's next sequence number, taken
/// from the state before the failure, and then holds no key.
pub open spec fn fail_ensures(ciphers: super::dispatcher_spec::Ciphers,
    before: super::dispatcher_spec::State, description: u8, action: super::dispatcher_spec::Action,
    after: super::dispatcher_spec::State) -> bool {
    (action, after) == super::dispatcher_spec::fatal(ciphers, before, description)
        && super::dispatcher_spec::wf(after) && super::dispatcher_spec::no_live_secrets(after)
}

/// RFC 8446 §6, §6.2: a decrypted record that is a fatal alert from the peer
/// (any alert but close_notify and user_canceled, at either level) ends the
/// connection without an answer.
pub open spec fn peer_alert_ensures(ciphers: super::dispatcher_spec::Ciphers,
    before: super::dispatcher_spec::State, ctype: u8, fragment: Seq<u8>,
    action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool {
    fragment.len() <= crate::spec::MAX_PLAINTEXT ==> match crate::spec::feed_record(before.reassembly,
        crate::spec::Record { ctype, fragment }) {
        crate::spec::Res::Ok((crate::spec::Event::Alert(a), _)) => !crate::spec::alert_is_closure(a)
            ==> (action, after) == super::dispatcher_spec::receive_fatal_alert(ciphers, before, a.description),
        _ => true,
    }
}

/// RFC 8446 §6.1: the end of the transport before the peer's close_notify is
/// a truncation; it fails the connection and sends nothing.
pub open spec fn truncation_ensures(before: super::dispatcher_spec::State,
    action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool {
    (before.mode != super::dispatcher_spec::Mode::Failed
        && before.mode != super::dispatcher_spec::Mode::Closed)
        ==> (action, after) == super::dispatcher_spec::die(crate::spec::INTERNAL_ERROR)
}

/// A user_canceled alert is nonfatal in TLS 1.3: report cancellation without
/// mutating directional closure or key state.
pub open spec fn user_canceled_ensures(before: super::dispatcher_spec::State,
    action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool {
    after == before && action is Cancelled
}

/// A protected client flight remains pending until the exact wire bytes are acknowledged.
pub open spec fn await_flight_ensures(before: super::dispatcher_spec::State,
    after: super::dispatcher_spec::State, server_messages: Seq<Seq<u8>>,
    protected_flight: Seq<u8>, wire: Seq<u8>) -> bool {
    super::dispatcher_spec::wf(before) && before.mode == super::dispatcher_spec::Mode::Handshake
        && super::dispatcher_spec::finished_is_last(server_messages)
        && super::dispatcher_spec::wf(after) && after.mode == super::dispatcher_spec::Mode::AwaitClientFlight
        && crate::spec::at_message_boundary(after.reassembly) && after.framing.len() == 0
        && after.pending_flight == wire && wire.len() > 0
        && wire == if before.ccs_pending {
            super::dispatcher_spec::compatibility_ccs_record() + protected_flight
        } else {
            protected_flight
        }
        && after.auth is Some && after.handshake_sender is Some && after.handshake_receiver is Some
        && after.master == before.master && after.ccs_pending == false
}

/// The acknowledgement gate derives the application traffic secrets from the
/// already-checkpointed Transcript-Hash through server Finished (§7.3).
pub open spec fn ready_after_ack_ensures(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    before: super::dispatcher_spec::State, acknowledgement: Seq<u8>, after: super::dispatcher_spec::State) -> bool {
    match (before.auth, before.handshake_sender, before.handshake_receiver) {
        (Some(auth), Some(_), Some(_)) => {
            let (auth_after, action) = crate::auth::spec::step(c, v, auth, crate::auth::spec::Input::SentFinished);
            let client_secret = crate::schedule::spec::expand_label(c, before.master,
                crate::schedule::spec::Label::ClientApplication, auth.application_hash, 32);
            let server_secret = crate::schedule::spec::expand_label(c, before.master,
                crate::schedule::spec::Label::ServerApplication, auth.application_hash, 32);
            super::dispatcher_spec::wf(before) && before.mode == super::dispatcher_spec::Mode::AwaitClientFlight
                && acknowledgement == before.pending_flight && action is Ready
                && super::dispatcher_spec::wf(after) && after.mode == super::dispatcher_spec::Mode::Ready
                && after.auth == Some(auth_after) && after.handshake_sender is None && after.handshake_receiver is None
                && after.client_application_secret == client_secret
                && after.server_application_secret == server_secret
                && after.master.len() == 0 && after.pending_flight.len() == 0
        },
        _ => false,
    }
}

/// §7.1, §7.3: the transducer starts from the two application traffic secrets
/// the handshake derived, both directions at sequence number 0, and from a
/// state that `wf` says is past the server Finished (Auth's phase is `Ready`).
/// `wf` also says no handshake message or record is partly received, so
/// nothing is left behind (§5.1: a key change falls on a record boundary).
pub open spec fn handoff_ensures(c: crate::schedule::spec::Crypto, before: super::dispatcher_spec::State,
    out: Result<super::post_handshake_spec::State, u8>) -> bool {
    out == super::post_handshake_spec::start(c, before.client_application_secret, before.server_application_secret)
}

/// The acknowledgement must match the entire saved flight before Auth can
/// release application traffic keys; a mismatch is terminal.
pub open spec fn acknowledgement_ensures(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    before: super::dispatcher_spec::State, acknowledgement: Seq<u8>, action: super::dispatcher_spec::Action,
    after: super::dispatcher_spec::State) -> bool {
    if before.mode == super::dispatcher_spec::Mode::AwaitClientFlight
        && acknowledgement == before.pending_flight {
        ready_after_ack_ensures(c, v, before, acknowledgement, after) && action is Ready
    } else {
        terminal_ensures(after, super::dispatcher_spec::Mode::Failed) && action is Fail
    }
}
} // verus!
