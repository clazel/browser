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
    (match state.handshake_sender {
        Some(epoch) => crate::traffic::contract::sealed_bound(factory, epoch.key, ciphers.handshake_seal),
        None => true,
    })
        && (match state.handshake_receiver {
            Some(epoch) => crate::traffic::contract::opened_bound(factory, epoch.key, ciphers.handshake_open),
            None => true,
        })
        && (match state.application_sender {
            Some(epoch) => crate::traffic::contract::sealed_bound(factory, epoch.key, ciphers.application_seal),
            None => true,
        })
        && (match state.application_receiver {
            Some(epoch) => crate::traffic::contract::opened_bound(factory, epoch.key, ciphers.application_open),
            None => true,
        })
}

/// Initial provider binding follows the handoff's direction labels exactly.
pub open spec fn start_bound_ensures(h: crate::traffic::handshake_spec::Handoff, ccs_pending: bool,
    factory: crate::traffic::spec::Cipher, ciphers: super::dispatcher_spec::Ciphers,
    out: super::dispatcher_spec::State) -> bool {
    start_ensures(h, ccs_pending, out)
        && crate::traffic::contract::sealed_bound(factory, h.1.key, ciphers.handshake_seal)
        && crate::traffic::contract::opened_bound(factory, h.2.key, ciphers.handshake_open)
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
                && after.master.len() == 0 && after.pending_flight.len() == 0
        },
        _ => false,
    }
}
} // verus!
