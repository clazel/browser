//! Facts proven about [`super::driver_spec`]'s end of the transport (choice
//! 7), for any key schedule and any AEAD. RFC 8446 §6.1.
//!
//! - **Never end-of-data.** The end of the transport never reports `Closed`,
//!   the joined client's end-of-data, unless the connection had already
//!   ended as `Closed` before it; while a machine runs it is always a
//!   truncation, `Failed(_, Origin::Truncated)` ([`lemma_eof_never_end_of_data`]).
//!   §6.1: "the TLS implementation MUST receive a "close_notify" alert
//!   before indicating end-of-data to the application layer."
//! - **Our close_notify.** While our write side is open, the end of the
//!   transport sends exactly the record a close sends at that point; after
//!   our close_notify, an error alert, or the end of the connection, it
//!   sends nothing ([`lemma_eof_sends_our_close_notify`]). §6.1: "Each party
//!   MUST send a "close_notify" alert before closing its write side of the
//!   connection, unless it has already sent some error alert."
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// The end of the transport never indicates end-of-data: its status is
/// `Closed` only when the connection had already ended as `Closed` (an
/// `Ended` stage, which it leaves as it was), and while a machine runs it is
/// `Failed(_, Origin::Truncated)`. It always leaves the stage `Ended` and
/// delivers nothing.
pub proof fn lemma_eof_never_end_of_data(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    stage: super::driver_spec::Stage, status: super::driver_spec::Status)
    ensures
        super::driver_spec::eof(c, f, stage, status).stage == super::driver_spec::Stage::Ended,
        super::driver_spec::eof(c, f, stage, status).deliver.len() == 0,
        !(stage is Ended) ==> super::driver_spec::eof(c, f, stage, status).status is Failed
            && super::driver_spec::eof(c, f, stage, status).status->Failed_1 == super::driver_spec::Origin::Truncated,
        super::driver_spec::eof(c, f, stage, status).status is Closed ==> stage is Ended && status is Closed,
{
}

/// While our write side is open the end of the transport sends exactly what
/// a close would send at that point (`driver_contract::close_ensures`): the
/// plaintext close_notify of [`super::driver_spec::hello_closed`] while the
/// bootstrap waits, the dispatcher's sealed close_notify
/// ([`super::dispatcher_spec::closing`]) during the server's flight, and the
/// transducer's ([`super::post_handshake_spec::close`]) while both directions
/// are open. Otherwise (our close_notify sent, an error alert, the connection
/// ended) it sends nothing.
pub proof fn lemma_eof_sends_our_close_notify(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    stage: super::driver_spec::Stage, status: super::driver_spec::Status)
    ensures
        match stage {
            super::driver_spec::Stage::Hello(boot, _) =>
                if boot.mode == crate::hello::bootstrap_spec::Mode::AwaitClientHelloSend
                    || boot.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello
                    || boot.mode == crate::hello::bootstrap_spec::Mode::AwaitClientHello2Send {
                    super::driver_spec::eof(c, f, stage, status).send == super::driver_spec::hello_closed().send
                } else {
                    super::driver_spec::eof(c, f, stage, status).send.len() == 0
                },
            super::driver_spec::Stage::Flight(s) => {
                let ciphers = super::dispatcher_spec::Ciphers { seal: f.seal, open: f.open };
                if s.mode != super::dispatcher_spec::Mode::Failed && s.mode != super::dispatcher_spec::Mode::Closed {
                    super::driver_spec::eof(c, f, stage, status).send
                        == super::driver_spec::flight_closed(super::dispatcher_spec::close_wire(ciphers, s)).send
                } else {
                    super::driver_spec::eof(c, f, stage, status).send.len() == 0
                }
            },
            super::driver_spec::Stage::App(s) =>
                if s.phase == super::post_handshake_spec::Phase::Open {
                    super::driver_spec::eof(c, f, stage, status).send == super::driver_spec::carry_out(f,
                        super::post_handshake_spec::close(f, s).0, super::post_handshake_spec::close(f, s).1).send
                } else {
                    super::driver_spec::eof(c, f, stage, status).send.len() == 0
                },
            super::driver_spec::Stage::Ended => super::driver_spec::eof(c, f, stage, status).send.len() == 0,
        },
{
    match stage {
        super::driver_spec::Stage::App(s) => {
            let closing = super::post_handshake_spec::close(f, s);
            if s.phase == super::post_handshake_spec::Phase::Open {
                assert(closing.0.end == super::post_handshake_spec::End::Continue);
                assert(Seq::<u8>::empty() + super::driver_spec::concat(closing.0.wires)
                    =~= super::driver_spec::concat(closing.0.wires));
            } else {
                let o = super::post_handshake_spec::step(c, f, s, super::post_handshake_spec::Input::Closed).0;
                assert(o.wires.len() == 0);
                assert(super::driver_spec::concat(o.wires) =~= Seq::<u8>::empty());
            }
        },
        _ => {},
    }
}
} // verus!
