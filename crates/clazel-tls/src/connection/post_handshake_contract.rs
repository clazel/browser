//! Refinement contracts for the post-handshake transducer
//! (`post_handshake_spec`): what each executable operation is proven to
//! satisfy, written in terms of the spec's functions. RFC 8446 §4.6, §5,
//! §6.1 and §7.2.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// The number of input bytes an input holds (`Closed` holds none).
pub open spec fn input_len(input: super::post_handshake_spec::Input) -> nat {
    match input {
        super::post_handshake_spec::Input::Bytes(wire) => wire.len(),
        super::post_handshake_spec::Input::Closed => 0,
    }
}

/// Construction is the spec's `start`: both epochs at sequence number 0, and
/// the invariant holds.
pub open spec fn start_ensures(c: crate::schedule::spec::Crypto, client_secret: Seq<u8>,
    server_secret: Seq<u8>, out: Result<super::post_handshake_spec::State, u8>) -> bool
{
    out == super::post_handshake_spec::start(c, client_secret, server_secret)
        && match out {
            Ok(s) => super::post_handshake_spec::wf(s),
            Err(_) => true,
        }
}

/// One step is the spec's `step`, keeps the invariant, and never claims to
/// have consumed more than it was given. The actions are the spec's
/// `actions` of its output.
pub open spec fn step_ensures(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    before: super::post_handshake_spec::State, input: super::post_handshake_spec::Input,
    actions: Seq<super::post_handshake_spec::Action>, consumed: nat,
    after: super::post_handshake_spec::State) -> bool
{
    let r = super::post_handshake_spec::step(c, f, before, input);
    super::post_handshake_spec::wf(after)
        && after == r.1
        && consumed == r.2
        && actions == super::post_handshake_spec::actions(r.0)
        && consumed <= input_len(input)
}

/// Sending application data is the spec's `send_application`.
pub open spec fn send_application_ensures(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, before: super::post_handshake_spec::State, data: Seq<u8>,
    actions: Seq<super::post_handshake_spec::Action>,
    after: super::post_handshake_spec::State) -> bool
{
    let r = super::post_handshake_spec::send_application(c, f, before, data);
    super::post_handshake_spec::wf(after)
        && after == r.1
        && actions == super::post_handshake_spec::actions(r.0)
}

/// A client-initiated key update is the spec's `update_keys`.
pub open spec fn update_keys_ensures(c: crate::schedule::spec::Crypto,
    f: crate::traffic::spec::Cipher, before: super::post_handshake_spec::State, request_peer: bool,
    actions: Seq<super::post_handshake_spec::Action>,
    after: super::post_handshake_spec::State) -> bool
{
    let r = super::post_handshake_spec::update_keys(c, f, before, request_peer);
    super::post_handshake_spec::wf(after)
        && after == r.1
        && actions == super::post_handshake_spec::actions(r.0)
}

/// A client-initiated close is the spec's `close`.
pub open spec fn close_ensures(f: crate::traffic::spec::Cipher,
    before: super::post_handshake_spec::State, actions: Seq<super::post_handshake_spec::Action>,
    after: super::post_handshake_spec::State) -> bool
{
    let r = super::post_handshake_spec::close(f, before);
    super::post_handshake_spec::wf(after)
        && after == r.1
        && actions == super::post_handshake_spec::actions(r.0)
}

/// A connection that ended retains no key, secret or partial input.
pub open spec fn ended_ensures(s: super::post_handshake_spec::State) -> bool {
    s.phase != super::post_handshake_spec::Phase::Open
        ==> s.sender is None && s.receiver is None && s.client_secret.len() == 0
            && s.server_secret.len() == 0 && s.reassembly.buf.len() == 0
}
} // verus!
