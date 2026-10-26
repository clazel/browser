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
        && super::dispatcher_spec::action_refines(action, after)
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
        && after.application_sender is None && after.application_receiver is None
        && after.master == before.master && after.ccs_pending == false
}

/// The acknowledgement gate installs fresh application epochs from the
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
                && after.application_sender == match crate::traffic::spec::start(c, client_secret) {
                    Ok(s) => Some(s), Err(_) => None,
                }
                && after.application_receiver == match crate::traffic::spec::start(c, server_secret) {
                    Ok(s) => Some(s), Err(_) => None,
                }
                && after.client_application_secret == client_secret
                && after.server_application_secret == server_secret
                && after.master.len() == 0 && after.pending_flight.len() == 0
        },
        _ => false,
    }
}

/// A local KeyUpdate is protected under the old send epoch and saved verbatim
/// until the I/O layer acknowledges the complete record.
pub open spec fn prepare_update_ensures(c: crate::schedule::spec::Crypto,
    ciphers: super::dispatcher_spec::Ciphers, before: super::dispatcher_spec::State,
    request: u8, is_response: bool, after: super::dispatcher_spec::State) -> bool
{
    before.mode == super::dispatcher_spec::Mode::Ready
        && before.pending_update_request is None
        && request <= 1
        && (!is_response || request == 0)
        && is_response == before.response_due
        && after == super::dispatcher_spec::prepare_key_update(c, ciphers, before, request, is_response)
        && super::dispatcher_spec::wf(after)
        && (if after.mode == super::dispatcher_spec::Mode::Ready {
            after.pending_update_request == Some(request)
                && after.pending_update_is_response == is_response
        } else {
            terminal_ensures(after, super::dispatcher_spec::Mode::Failed)
        })
}

/// A received KeyUpdate rotates only the peer's receive direction and queues
/// the requested response before the next application send.
pub open spec fn receive_update_ensures(c: crate::schedule::spec::Crypto,
    ciphers: super::dispatcher_spec::Ciphers, before: super::dispatcher_spec::State,
    request: u8, action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State) -> bool
{
    before.mode == super::dispatcher_spec::Mode::Ready && request <= 1
        && after == super::dispatcher_spec::receive_key_update_and_respond(c, ciphers, before, request)
        && super::dispatcher_spec::wf(after)
        && (if after.mode == super::dispatcher_spec::Mode::Failed {
            terminal_ensures(after, super::dispatcher_spec::Mode::Failed) && action is Fail
        } else {
            after.server_application_secret == crate::schedule::spec::next_traffic_secret(c, before.server_application_secret)
                && after.client_application_secret == before.client_application_secret
                && super::dispatcher_spec::action_refines(action, after)
        })
}

/// Exact acknowledgements rotate the client send epoch to sequence zero.
/// A mismatched acknowledgement is connection-fatal.
pub open spec fn key_update_ack_ensures(c: crate::schedule::spec::Crypto,
    ciphers: super::dispatcher_spec::Ciphers, before: super::dispatcher_spec::State,
    sent: Seq<u8>, action: super::dispatcher_spec::Action,
    after: super::dispatcher_spec::State) -> bool
{
    if before.mode == super::dispatcher_spec::Mode::Ready
        && before.pending_update_request is Some && sent == before.pending_update_wire {
        after == super::dispatcher_spec::acknowledge_key_update_and_respond(c, ciphers, before, sent)
            && super::dispatcher_spec::wf(after)
            && action_refines_key_update_ack(action, before, after)
    } else {
        terminal_ensures(after, super::dispatcher_spec::Mode::Failed)
            && action is Fail
    }
}

pub open spec fn action_refines_key_update_ack(action: super::dispatcher_spec::Action,
    before: super::dispatcher_spec::State, after: super::dispatcher_spec::State) -> bool
{
    match action {
        super::dispatcher_spec::Action::Send(wire) => after.mode == super::dispatcher_spec::Mode::Ready
            && after.pending_update_request is Some && wire == after.pending_update_wire,
        super::dispatcher_spec::Action::None => after.pending_update_request is None
            && after.application_sender is Some && before.application_sender is Some,
        super::dispatcher_spec::Action::Fail(_) => terminal_ensures(after, super::dispatcher_spec::Mode::Failed),
        _ => false,
    }
}

/// RFC 8446 §4.6.1: a valid ticket is consumed and discarded in the
/// non-resumption profile; it does not change the authenticated connection.
pub open spec fn discarded_ticket_ensures(before: super::dispatcher_spec::State,
    messages: Seq<Seq<u8>>, action: super::dispatcher_spec::Action,
    after: super::dispatcher_spec::State) -> bool {
    before.mode == super::dispatcher_spec::Mode::Ready
        && messages.len() == 1
        && crate::spec::at_message_boundary(before.reassembly)
        && super::dispatcher_spec::valid_discarded_ticket(messages[0])
        ==> after == before && action is None
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
