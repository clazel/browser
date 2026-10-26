//! Refinement contracts for the action-driven Hello bootstrap.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// Construction emits exactly the initial ClientHello plaintext record.
pub open spec fn start_ensures(config: super::client_spec::Config,
    out: Result<(super::bootstrap_spec::State, super::bootstrap_spec::Action), u8>) -> bool {
    out == super::bootstrap_spec::start(config)
        && match out {
            Ok((state, super::bootstrap_spec::Action::Send(wire))) => super::bootstrap_spec::wf(state)
                && state.mode == super::bootstrap_spec::Mode::AwaitClientHelloSend
                && state.pending_flight == wire,
            Ok(_) => false,
            Err(_) => true,
        }
}

/// Only the exact pending flight opens the peer-input gate.
pub open spec fn acknowledge_ensures(before: super::bootstrap_spec::State,
    sent: Seq<u8>, out: (super::bootstrap_spec::State, super::bootstrap_spec::Action)) -> bool {
    super::bootstrap_spec::wf(before)
        && out == super::bootstrap_spec::acknowledge(before, sent)
        && super::bootstrap_spec::wf(out.0)
        && match out.1 {
            super::bootstrap_spec::Action::None =>
                out.0.mode == super::bootstrap_spec::Mode::AwaitServerHello
                    && out.0.pending_flight.len() == 0,
            super::bootstrap_spec::Action::Fail(_) =>
                out.0.mode == super::bootstrap_spec::Mode::Failed
                    && out.0.pending_flight.len() == 0,
            _ => false,
        }
}

/// One complete decoded peer event follows the bootstrap transition model.
pub open spec fn receive_ensures(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::bootstrap_spec::State, event: super::bootstrap_spec::PeerEvent,
    after: super::bootstrap_spec::State, action: super::bootstrap_spec::Action) -> bool {
    super::bootstrap_spec::wf(before)
        && before.mode == super::bootstrap_spec::Mode::AwaitServerHello
        && (after, action) == super::bootstrap_spec::receive(hash, before, event)
        && super::bootstrap_spec::wf(after)
}

/// Raw input consumes exactly one plaintext record prefix and follows the lifecycle model.
pub open spec fn feed_ensures(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::bootstrap_spec::State, framing: Seq<u8>, input: Seq<u8>,
    out: super::bootstrap_spec::Feed) -> bool {
    super::bootstrap_spec::wf(before)
        && crate::connection::framing_spec::wf_mode(framing, false)
        && out == super::bootstrap_spec::feed(hash, before, framing, input)
        && out.consumed <= input.len()
        && super::bootstrap_spec::wf(out.state)
        && crate::connection::framing_spec::wf_mode(out.framing, false)
}

/// Runtime stream feed refines the byte-prefix model and returns the exact boundary.
pub open spec fn feed_exec_ensures(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::bootstrap_spec::State, framing: Seq<u8>, input: Seq<u8>,
    consumed: nat, action: super::bootstrap_spec::Action,
    after: super::bootstrap_spec::State, final_framing: Seq<u8>) -> bool {
    let expected = super::bootstrap_spec::feed(hash, before, framing, input);
    consumed == expected.consumed
        && action == expected.action
        && after == expected.state
        && final_framing == expected.framing
}

/// EOF is terminal before the final ServerHello and inert after terminality.
pub open spec fn eof_ensures(before: super::bootstrap_spec::State,
    after: super::bootstrap_spec::State, action: super::bootstrap_spec::Action) -> bool {
    super::bootstrap_spec::wf(before)
        && (after, action) == super::bootstrap_spec::eof(before)
        && super::bootstrap_spec::wf(after)
}
} // verus!
