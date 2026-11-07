//! What the joined client is proven to do: a step of the Hello or application
//! stage is the running machine's own step, each handoff starts the next
//! machine from what the last one derived, and plaintext comes from the
//! transducer alone. A step of the flight is bounded, not equated: see
//! [`flight_step_ensures`].
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// The providers the machines run over.
pub struct Models {
    /// Hash, HMAC and HKDF.
    pub crypto: crate::schedule::spec::Crypto,
    /// X25519.
    pub exchange: crate::hello::join_spec::KeyExchange,
    /// The AEAD.
    pub cipher: crate::traffic::spec::Cipher,
    /// The certificate and signature checks.
    pub verification: crate::auth::spec::Verification,
}

/// §7.1, §7.3: the dispatcher starts from the handshake keys derived from the
/// accepted ServerHello and our scalar, in the Hello handoff's exact state.
pub open spec fn flight_started(m: Models, established: crate::hello::bootstrap_spec::Action,
    scalar: Seq<u8>, state: super::dispatcher_spec::State) -> bool
{
    match established {
        crate::hello::bootstrap_spec::Action::Established(config, transcript, peer_key) =>
            match crate::traffic::handshake_spec::start(m.crypto, m.exchange, config, transcript, peer_key, scalar) {
                Ok(h) => state == super::dispatcher_spec::start(h,
                    crate::traffic::handshake_spec::needs_ccs(config, transcript)),
                Err(_) => false,
            },
        _ => false,
    }
}

/// §7.3: the transducer starts from the application traffic secrets of a
/// dispatcher that reached `Ready`, so past the server Finished.
pub open spec fn app_started(m: Models, state: super::post_handshake_spec::State) -> bool {
    exists|ready: super::dispatcher_spec::State| #![auto]
        ready.mode == super::dispatcher_spec::Mode::Ready
            && super::dispatcher_spec::wf(ready)
            && super::dispatcher_contract::handoff_ensures(m.crypto, ready, Ok(state))
}

/// One step from the Hello stage is `Bootstrap`'s own, and the dispatcher
/// starts only from its `Established`.
pub open spec fn hello_step_ensures(m: Models, boot: crate::hello::bootstrap_spec::State, framing: Seq<u8>,
    scalar: Seq<u8>, input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    let expected = crate::hello::bootstrap_spec::feed(m.crypto.hash, boot, framing, input);
    consumed == expected.consumed
        && match expected.action {
            crate::hello::bootstrap_spec::Action::None =>
                out.stage == super::driver_spec::Stage::Hello(expected.state, expected.framing)
                    && out.send.len() == 0 && out.status == super::driver_spec::Status::Handshaking,
            crate::hello::bootstrap_spec::Action::Send(wire) =>
                out.send == wire || out == super::driver_spec::hello_failure(crate::spec::INTERNAL_ERROR),
            crate::hello::bootstrap_spec::Action::Established(_, _, _) => match out.stage {
                super::driver_spec::Stage::Flight(state) => flight_started(m, expected.action, scalar, state)
                    && out.send.len() == 0,
                _ => out.stage == super::driver_spec::Stage::Ended,
            },
            crate::hello::bootstrap_spec::Action::Alert(a) => out == super::driver_spec::peer_failed(a),
            crate::hello::bootstrap_spec::Action::Fail(a) => out == super::driver_spec::hello_failure(a),
            crate::hello::bootstrap_spec::Action::Close => out == super::driver_spec::hello_closed(),
        }
}

/// One step of the flight: it consumes no more than its input, sends nothing
/// while it stays in the flight, and the only way out to the transducer is
/// `Ready`. This does not say the result equals the dispatcher's step.
pub open spec fn flight_step_ensures(m: Models, before: super::dispatcher_spec::State,
    input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    consumed <= input.len()
        && match out.stage {
            super::driver_spec::Stage::Hello(_, _) => false,
            super::driver_spec::Stage::Flight(after) => out.status == super::driver_spec::Status::Handshaking
                && super::dispatcher_spec::wf(after) && out.send.len() == 0,
            super::driver_spec::Stage::App(state) => app_started(m, state)
                && out.status == super::driver_spec::Status::Open,
            super::driver_spec::Stage::Ended => super::driver_spec::is_final(out.status),
        }
}

/// One step of the flight is the dispatcher's own `feed`, exactly: the same
/// octets consumed, and its action and state carried through `flight_out`. The
/// executable does not yet meet this: see `flight_step_ensures`.
pub open spec fn flight_step_exact(m: Models, before: super::dispatcher_spec::State,
    input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    let ciphers = super::dispatcher_spec::Ciphers { seal: m.cipher.seal, open: m.cipher.open };
    let r = super::dispatcher_spec::feed(m.crypto, m.verification, ciphers, before, input);
    consumed == r.0 && out == super::driver_spec::flight_out(m.crypto, m.verification, ciphers, r.1, r.2)
}

/// One step of application traffic is the transducer's own, exactly.
pub open spec fn app_step_ensures(m: Models, before: super::post_handshake_spec::State,
    input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    let r = super::post_handshake_spec::step(m.crypto, m.cipher, before, super::post_handshake_spec::Input::Bytes(input));
    consumed == r.2 && out == super::driver_spec::carry_out(m.cipher, r.0, r.1)
}

/// One step of the joined client, whichever machine is running.
pub open spec fn step_ensures(m: Models, before: super::driver_spec::Stage, scalar: Seq<u8>, input: Seq<u8>,
    consumed: nat, out: super::driver_spec::Step) -> bool
{
    match before {
        super::driver_spec::Stage::Hello(boot, framing) =>
            hello_step_ensures(m, boot, framing, scalar, input, consumed, out) && out.deliver.len() == 0,
        super::driver_spec::Stage::Flight(state) =>
            flight_step_ensures(m, state, input, consumed, out) && out.deliver.len() == 0,
        super::driver_spec::Stage::App(state) => app_step_ensures(m, state, input, consumed, out),
        super::driver_spec::Stage::Ended => consumed == 0 && out.send.len() == 0 && out.deliver.len() == 0
            && out.stage == super::driver_spec::Stage::Ended,
    }
}

/// Sending application data is the transducer's `send_application`, and
/// nothing before the handshake ends.
pub open spec fn send_ensures(m: Models, before: super::driver_spec::Stage, data: Seq<u8>,
    out: super::driver_spec::Step) -> bool
{
    match before {
        super::driver_spec::Stage::App(state) => {
            let r = super::post_handshake_spec::send_application(m.crypto, m.cipher, state, data);
            out == super::driver_spec::carry_out(m.cipher, r.0, r.1)
        },
        _ => out.send.len() == 0,
    }
}

/// Closing is the transducer's `close` once it runs. Before the ServerHello
/// it is a plaintext close_notify.
pub open spec fn close_ensures(m: Models, before: super::driver_spec::Stage, out: super::driver_spec::Step) -> bool {
    match before {
        super::driver_spec::Stage::App(state) => {
            let r = super::post_handshake_spec::close(m.cipher, state);
            out == super::driver_spec::carry_out(m.cipher, r.0, r.1)
        },
        super::driver_spec::Stage::Hello(_, _) => out == super::driver_spec::hello_closed(),
        super::driver_spec::Stage::Flight(state) => out == super::driver_spec::flight_closed(
            super::dispatcher_spec::close_wire(super::dispatcher_spec::Ciphers { seal: m.cipher.seal, open: m.cipher.open }, state)),
        super::driver_spec::Stage::Ended => out.send.len() == 0,
    }
}
} // verus!
