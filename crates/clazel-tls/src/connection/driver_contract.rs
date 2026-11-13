//! What the joined client is proven to do: a step of any stage is the running
//! machine's own step, each handoff starts the next machine from what the last
//! one derived, and plaintext comes from the transducer alone.
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

/// §7.1, §7.3: what the bootstrap's `Established` comes to. The handshake
/// keys are derived from the accepted ServerHello and our scalar, and the
/// dispatcher starts from them in the handoff's exact state
/// ([`flight_started`]), sending nothing. If they cannot be derived (§7.4.2's
/// all-zero shared secret, a scalar that is not the one offered), it is a
/// local failure before the handshake keys (`driver_spec` choice 4).
pub open spec fn established_step(m: Models, established: crate::hello::bootstrap_spec::Action,
    scalar: Seq<u8>) -> super::driver_spec::Step
{
    match established {
        crate::hello::bootstrap_spec::Action::Established(config, transcript, peer_key) =>
            match crate::traffic::handshake_spec::start(m.crypto, m.exchange, config, transcript, peer_key, scalar) {
                Ok(h) => super::driver_spec::Step { send: seq![], deliver: seq![],
                    stage: super::driver_spec::Stage::Flight(super::dispatcher_spec::start(h,
                        crate::traffic::handshake_spec::needs_ccs(config, transcript))),
                    status: super::driver_spec::Status::Handshaking },
                Err(alert) => super::driver_spec::hello_failure(alert),
            },
        _ => super::driver_spec::hello_failure(crate::spec::INTERNAL_ERROR),
    }
}

/// RFC 8446 §4.1.2 and §5.1: the start. The bootstrap's first record (the
/// initial ClientHello) goes out and is acknowledged at once (`driver_spec`
/// choice 2), and the Hello stage waits with an empty framer. A
/// configuration the bootstrap refuses ends the connection with its alert,
/// nothing sent.
pub open spec fn connect_ensures(m: Models, config: crate::hello::client_spec::Config,
    out: super::driver_spec::Step) -> bool
{
    let failed = |alert: u8| super::driver_spec::Step { send: seq![], deliver: seq![],
        stage: super::driver_spec::Stage::Ended,
        status: super::driver_spec::Status::Failed(alert, super::driver_spec::Origin::NotSent) };
    match crate::hello::bootstrap_spec::start(config) {
        Ok((s0, crate::hello::bootstrap_spec::Action::Send(wire))) => {
            let (s1, a1) = crate::hello::bootstrap_spec::acknowledge(m.crypto.hash, s0, wire);
            if a1 is None {
                out == super::driver_spec::Step { send: wire, deliver: seq![],
                    stage: super::driver_spec::Stage::Hello(s1, seq![]),
                    status: super::driver_spec::Status::Handshaking }
            } else {
                out == failed(crate::spec::INTERNAL_ERROR)
            }
        },
        Ok(_) => out == failed(crate::spec::INTERNAL_ERROR),
        Err(alert) => out == failed(alert),
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
            // ClientHello2 goes out and is acknowledged at once (driver_spec
            // choice 2); the acknowledgement then processes the messages the
            // HelloRetryRequest's record held after it (RFC 8446 §5.1).
            crate::hello::bootstrap_spec::Action::Send(wire) => {
                let (acked, after) = crate::hello::bootstrap_spec::acknowledge(m.crypto.hash, expected.state, wire);
                match after {
                    crate::hello::bootstrap_spec::Action::None =>
                        out.send == wire && out.status == super::driver_spec::Status::Handshaking
                            && out.stage == super::driver_spec::Stage::Hello(acked, expected.framing),
                    crate::hello::bootstrap_spec::Action::Established(_, _, _) => out == super::driver_spec::Step {
                        send: wire + established_step(m, after, scalar).send,
                        ..established_step(m, after, scalar)
                    },
                    crate::hello::bootstrap_spec::Action::Fail(a) => out == super::driver_spec::Step {
                        send: wire + super::driver_spec::hello_failure(a).send,
                        ..super::driver_spec::hello_failure(a)
                    },
                    _ => out == super::driver_spec::hello_failure(crate::spec::INTERNAL_ERROR),
                }
            },
            crate::hello::bootstrap_spec::Action::Established(_, _, _) =>
                out == established_step(m, expected.action, scalar),
            crate::hello::bootstrap_spec::Action::Alert(a) => out == super::driver_spec::peer_failed(a),
            crate::hello::bootstrap_spec::Action::Fail(a) => out == super::driver_spec::hello_failure(a),
            crate::hello::bootstrap_spec::Action::Close => out == super::driver_spec::hello_closed(),
        }
}

/// One step of the flight: it consumes no more than its input, sends nothing
/// while it stays in the flight, and the only way out to the transducer is
/// `Ready`.
pub open spec fn flight_step_bounds(m: Models, before: super::dispatcher_spec::State,
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
/// octets consumed, and its action and state carried through `flight_out`.
pub open spec fn flight_step_exact(m: Models, before: super::dispatcher_spec::State,
    input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    let ciphers = super::dispatcher_spec::Ciphers { seal: m.cipher.seal, open: m.cipher.open };
    let r = super::dispatcher_spec::feed(m.crypto, m.verification, ciphers, before, input);
    consumed == r.0 && out == super::driver_spec::flight_out(m.crypto, m.verification, ciphers, r.1, r.2)
}

/// One step of the flight, exactly and with what that implies spelled out.
pub open spec fn flight_step_ensures(m: Models, before: super::dispatcher_spec::State,
    input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    flight_step_exact(m, before, input, consumed, out) && flight_step_bounds(m, before, input, consumed, out)
}

/// One step of application traffic is the transducer's own, exactly.
pub open spec fn app_step_ensures(m: Models, before: super::post_handshake_spec::State,
    input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    let r = super::post_handshake_spec::step(m.crypto, m.cipher, before, super::post_handshake_spec::Input::Bytes(input));
    consumed == r.2 && out == super::driver_spec::carry_out(m.cipher, r.0, r.1)
}

/// One step of the joined client, whichever machine is running. `status`
/// is where the connection was before it; once ended, nothing changes.
pub open spec fn step_ensures(m: Models, before: super::driver_spec::Stage, status: super::driver_spec::Status,
    scalar: Seq<u8>, input: Seq<u8>, consumed: nat, out: super::driver_spec::Step) -> bool
{
    match before {
        super::driver_spec::Stage::Hello(boot, framing) =>
            hello_step_ensures(m, boot, framing, scalar, input, consumed, out) && out.deliver.len() == 0,
        super::driver_spec::Stage::Flight(state) =>
            flight_step_ensures(m, state, input, consumed, out) && out.deliver.len() == 0,
        super::driver_spec::Stage::App(state) => app_step_ensures(m, state, input, consumed, out),
        super::driver_spec::Stage::Ended => consumed == 0 && out == unchanged(before, status),
    }
}

/// Nothing sent or delivered, and the connection where it was.
pub open spec fn unchanged(stage: super::driver_spec::Stage, status: super::driver_spec::Status)
    -> super::driver_spec::Step
{
    super::driver_spec::Step { send: seq![], deliver: seq![], stage, status }
}

/// Sending application data is the transducer's `send_application`, and
/// nothing, with the connection unchanged, before the handshake ends or
/// after it ended.
pub open spec fn send_ensures(m: Models, before: super::driver_spec::Stage, status: super::driver_spec::Status,
    data: Seq<u8>, out: super::driver_spec::Step) -> bool
{
    match before {
        super::driver_spec::Stage::App(state) => {
            let r = super::post_handshake_spec::send_application(m.crypto, m.cipher, state, data);
            out == super::driver_spec::carry_out(m.cipher, r.0, r.1)
        },
        _ => out == unchanged(before, status),
    }
}

/// Closing is the transducer's `close` once it runs. Before the ServerHello
/// it is a plaintext close_notify.
pub open spec fn close_ensures(m: Models, before: super::driver_spec::Stage, status: super::driver_spec::Status,
    out: super::driver_spec::Step) -> bool
{
    match before {
        super::driver_spec::Stage::App(state) => {
            let r = super::post_handshake_spec::close(m.cipher, state);
            out == super::driver_spec::carry_out(m.cipher, r.0, r.1)
        },
        super::driver_spec::Stage::Hello(_, _) => out == super::driver_spec::hello_closed(),
        super::driver_spec::Stage::Flight(state) => out == super::driver_spec::flight_closed(
            super::dispatcher_spec::close_wire(super::dispatcher_spec::Ciphers { seal: m.cipher.seal, open: m.cipher.open }, state)),
        super::driver_spec::Stage::Ended => out == unchanged(before, status),
    }
}

/// RFC 8446 §6.1: the end of the transport (the server's direction of it
/// ended) is [`super::driver_spec::eof`], exactly (`driver_spec` choice 7).
/// While a machine runs the connection ends as `Failed(_, Origin::Truncated)`,
/// never `Closed`, after our close_notify, the record a close would send at
/// that point, if our write side is open; on an `Ended` stage nothing
/// changes. `status` is where the connection was before the call.
pub open spec fn eof_ensures(m: Models, before: super::driver_spec::Stage, status: super::driver_spec::Status,
    out: super::driver_spec::Step) -> bool
{
    out == super::driver_spec::eof(m.crypto, m.cipher, before, status)
}
} // verus!
