//! RFC 8446 §4.6, §5, §6.1, §7.2 and §7.3: the executable post-handshake
//! transducer, written to meet [`super::post_handshake_spec`] through
//! [`super::post_handshake_contract`]. Every operation computes one spec
//! function over the traffic epochs, the reassembler and the handshake
//! parser that are proven elsewhere in this crate.
use super::post_handshake_spec as spec;
use crate::reassemble::{Event as ReassemblyEvent, Reassembler};
use crate::schedule::crypto::Crypto;
use crate::traffic::exec::{Decryptor, Encryptor, Read as TrafficRead};
use crate::traffic::provider::Factory;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Whether the connection is live ([`spec::Phase`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// Application traffic keys are installed in both directions.
    Open,
    /// The connection ended in order.
    Closed,
    /// The connection failed.
    Failed,
}
impl View for Phase {
    type V = spec::Phase;
    open spec fn view(&self) -> spec::Phase {
        match self {
            Phase::Open => spec::Phase::Open,
            Phase::Closed => spec::Phase::Closed,
            Phase::Failed => spec::Phase::Failed,
        }
    }
}

/// What the transducer is given ([`spec::Input`]).
#[derive(Debug, PartialEq, Eq)]
pub enum Input<'a> {
    /// Bytes of the server's stream, starting at a record boundary.
    Bytes(&'a [u8]),
    /// The transport closed.
    Closed,
}
impl<'a> View for Input<'a> {
    type V = spec::Input;
    open spec fn view(&self) -> spec::Input {
        match self {
            Input::Bytes(wire) => spec::Input::Bytes(wire@),
            Input::Closed => spec::Input::Closed,
        }
    }
}

/// One effect, in the order it happens ([`spec::Action`]).
#[derive(Debug, PartialEq, Eq)]
pub enum Action {
    /// A whole protected record to put on the wire.
    Send(Vec<u8>),
    /// Plaintext application data from the server, in order.
    Deliver(Vec<u8>),
    /// The connection ended in order (`close_notify`).
    Close,
    /// The connection ended with this alert description.
    Fail(u8),
}
impl View for Action {
    type V = spec::Action;
    open spec fn view(&self) -> spec::Action {
        match self {
            Action::Send(wire) => spec::Action::Send(wire@),
            Action::Deliver(data) => spec::Action::Deliver(data@),
            Action::Close => spec::Action::Close,
            Action::Fail(alert) => spec::Action::Fail(*alert),
        }
    }
}

enum End {
    Continue,
    Close,
    Fail(u8),
}
impl View for End {
    type V = spec::End;
    open spec fn view(&self) -> spec::End {
        match self {
            End::Continue => spec::End::Continue,
            End::Close => spec::End::Close,
            End::Fail(alert) => spec::End::Fail(*alert),
        }
    }
}

/// [`spec::Out`]: records, plaintext, end.
struct Out {
    wires: Vec<Vec<u8>>,
    delivered: Vec<u8>,
    end: End,
}
impl View for Out {
    type V = spec::Out;
    open spec fn view(&self) -> spec::Out {
        spec::Out {
            wires: crate::reassemble::views_bytes(self.wires@),
            delivered: self.delivered@,
            end: self.end@,
        }
    }
}
impl Out {
    fn quiet() -> (o: Out)
        ensures o@ == spec::quiet(),
    {
        let o = Out { wires: Vec::new(), delivered: Vec::new(), end: End::Continue };
        proof { assert(o@ =~= spec::quiet()); }
        o
    }

    fn ending(end: End) -> (o: Out)
        ensures o@ == (spec::Out { wires: seq![], delivered: seq![], end: end@ }),
    {
        let o = Out { wires: Vec::new(), delivered: Vec::new(), end };
        proof { assert(o@ =~= (spec::Out { wires: seq![], delivered: seq![], end: end@ })); }
        o
    }

    fn one(wire: Vec<u8>, end: End) -> (o: Out)
        ensures o@ == (spec::Out { wires: seq![wire@], delivered: seq![], end: end@ }),
    {
        let ghost w = wire@;
        let wires: Vec<Vec<u8>> = vec![wire];
        let o = Out { wires, delivered: Vec::new(), end };
        proof {
            assert(crate::reassemble::views_bytes(o.wires@) =~= seq![w]);
            assert(o@ =~= (spec::Out { wires: seq![w], delivered: seq![], end: end@ }));
        }
        o
    }

    fn then(self, other: Out) -> (o: Out)
        ensures o@ == spec::then(self@, other@),
    {
        let mut wires = self.wires;
        let mut more = other.wires;
        wires.append(&mut more);
        let o = Out { wires, delivered: other.delivered, end: other.end };
        proof {
            let a = crate::reassemble::views_bytes(self.wires@);
            let b = crate::reassemble::views_bytes(other.wires@);
            assert(crate::reassemble::views_bytes(self.wires@ + other.wires@) =~= a + b);
            assert(o@ =~= spec::then(self@, other@));
        }
        o
    }
}

/// The actions of an output, in order: every `Send`, the `Deliver` if there is
/// plaintext, then `Close` or `Fail` ([`spec::actions`]).
fn into_actions(out: Out) -> (r: Vec<Action>)
    ensures crate::types::views(r@) =~= spec::actions(out@),
{
    let ghost want = out@;
    let ghost wire_views = crate::reassemble::views_bytes(out.wires@);
    let wires = out.wires;
    let mut r: Vec<Action> = Vec::new();
    let mut i: usize = 0;
    while i < wires.len()
        invariant
            i <= wires.len(),
            wire_views == crate::reassemble::views_bytes(wires@),
            crate::types::views(r@) =~= Seq::new(i as nat, |j: int| spec::Action::Send(wire_views[j])),
        decreases wires.len() - i,
    {
        let copy = match wires.get(i) {
            Some(w) => vstd::slice::slice_to_vec(w.as_slice()),
            None => Vec::new(),
        };
        proof {
            crate::types::lemma_views_push(r@, Action::Send(copy));
            assert(wire_views[i as int] == wires@[i as int]@);
            assert(copy@ == wires@[i as int]@);
        }
        r.push(Action::Send(copy));
        i = i.saturating_add(1);
        proof {
            assert(Seq::new(i as nat, |j: int| spec::Action::Send(wire_views[j]))
                =~= Seq::new((i - 1) as nat, |j: int| spec::Action::Send(wire_views[j]))
                    .push(spec::Action::Send(wire_views[i - 1])));
        }
    }
    if !out.delivered.is_empty() {
        let copy = vstd::slice::slice_to_vec(out.delivered.as_slice());
        proof { crate::types::lemma_views_push(r@, Action::Deliver(copy)); }
        r.push(Action::Deliver(copy));
    }
    match out.end {
        End::Continue => {},
        End::Close => {
            proof { crate::types::lemma_views_push(r@, Action::Close); }
            r.push(Action::Close);
        },
        End::Fail(alert) => {
            proof { crate::types::lemma_views_push(r@, Action::Fail(alert)); }
            r.push(Action::Fail(alert));
        },
    }
    proof {
        assert(wires@.len() == i);
        assert(crate::types::views(r@) =~= spec::actions(want));
    }
    r
}

/// The key-explicit seal function an AEAD object computes is the factory's
/// function at its key ([`spec::seal_of`]).
proof fn lemma_seal_closure(f: crate::traffic::spec::Cipher, ep: crate::traffic::spec::State,
    g: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>)
    requires forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] g(n, ad, p) == (f.seal)(ep.key, n, ad, p),
    ensures g == spec::seal_of(f, ep),
{
    assert(g =~= spec::seal_of(f, ep));
}

/// The key-explicit open function an AEAD object computes is the factory's
/// function at its key ([`spec::open_of`]).
proof fn lemma_open_closure(f: crate::traffic::spec::Cipher, ep: crate::traffic::spec::State,
    g: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>)
    requires forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] g(n, ad, ct) == (f.open)(ep.key, n, ad, ct),
    ensures g == spec::open_of(f, ep),
{
    assert(g =~= spec::open_of(f, ep));
}

/// A fresh epoch starts at sequence number zero, unfailed, from a secret of
/// `Hash.length` bytes ([`crate::traffic::spec::start`]).
proof fn lemma_start_fresh(c: crate::schedule::spec::Crypto, secret: Seq<u8>)
    ensures match crate::traffic::spec::start(c, secret) {
        Ok(ep) => ep.next == Some(0u64) && !ep.failed && secret.len() == 32,
        Err(_) => true,
    },
{}

/// Reading a record never consumes more than the input holds: `consumed` is
/// `wire.len()` less what [`crate::spec::read_record`] left over.
proof fn lemma_consumed_bounded(open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    s: crate::traffic::spec::State, wire: Seq<u8>, typ: u8, content: Seq<u8>, used: nat)
    requires crate::traffic::spec::receive(open, s, wire).1 == crate::traffic::spec::Read::Record(typ, content, used),
    ensures used <= wire.len(),
{
    crate::lemmas_record::lemma_read_record_canonical(wire, true);
}

/// The client after the handshake: both application epochs, their traffic
/// secrets and the unfinished handshake message, if any.
pub struct PostHandshake<C: Crypto, F: Factory> {
    crypto: C,
    factory: F,
    phase: Phase,
    sender: Option<Encryptor<F::Cipher>>,
    receiver: Option<Decryptor<F::Cipher>>,
    client_secret: Vec<u8>,
    server_secret: Vec<u8>,
    reassembler: Reassembler,
}
impl<C: Crypto, F: Factory> View for PostHandshake<C, F> {
    type V = spec::State;
    closed spec fn view(&self) -> spec::State {
        spec::State {
            phase: self.phase@,
            sender: match self.sender { Some(e) => Some(e@), None => None },
            receiver: match self.receiver { Some(e) => Some(e@), None => None },
            client_secret: self.client_secret@,
            server_secret: self.server_secret@,
            reassembly: self.reassembler@,
        }
    }
}
impl<C: Crypto, F: Factory> PostHandshake<C, F> {
    /// The lifecycle invariant, the epochs' and the reassembler's own
    /// invariants, and the binding of every live epoch to the factory.
    pub closed spec fn wf(&self) -> bool {
        spec::wf(self@) && self.resources_wf() && self.bound()
    }

    closed spec fn resources_wf(&self) -> bool {
        (match self.sender { Some(e) => e.wf(), None => true })
            && (match self.receiver { Some(e) => e.wf(), None => true })
            && self.reassembler.wf()
    }

    closed spec fn bound(&self) -> bool {
        (match self.sender {
            Some(e) => forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] e.seal_spec(n, ad, p)
                == (self.factory.functions().seal)(e@.key, n, ad, p),
            None => true,
        }) && (match self.receiver {
            Some(e) => forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] e.open_spec(n, ad, ct)
                == (self.factory.functions().open)(e@.key, n, ad, ct),
            None => true,
        })
    }

    /// The abstract key-schedule functions this connection derives keys with.
    pub closed spec fn crypto_functions(&self) -> crate::schedule::spec::Crypto { self.crypto.functions() }

    /// The abstract AEAD functions of this connection's cipher factory.
    pub closed spec fn cipher_functions(&self) -> crate::traffic::spec::Cipher { self.factory.functions() }

    /// §7.1, §7.3: start from the client and server application traffic
    /// secrets, both directions at sequence number zero.
    pub fn new(crypto: C, factory: F, client_secret: &[u8], server_secret: &[u8]) -> (out: Result<Self, u8>)
        ensures match out {
            Ok(p) => p.wf() && p.crypto_functions() == crypto.functions()
                && p.cipher_functions() == factory.functions()
                && super::post_handshake_contract::start_ensures(crypto.functions(), client_secret@,
                    server_secret@, Ok(p@)),
            Err(a) => super::post_handshake_spec::start(crypto.functions(), client_secret@, server_secret@)
                == Err::<spec::State, u8>(a),
        },
    {
        let sender = Encryptor::new(&crypto, &factory, client_secret)?;
        let receiver = Decryptor::new(&crypto, &factory, server_secret)?;
        proof {
            lemma_start_fresh(crypto.functions(), client_secret@);
            lemma_start_fresh(crypto.functions(), server_secret@);
        }
        let out = PostHandshake {
            crypto,
            factory,
            phase: Phase::Open,
            sender: Some(sender),
            receiver: Some(receiver),
            client_secret: vstd::slice::slice_to_vec(client_secret),
            server_secret: vstd::slice::slice_to_vec(server_secret),
            reassembler: Reassembler::new(),
        };
        proof {
            assert(out@ =~= (spec::State {
                phase: spec::Phase::Open,
                sender: Some(sender@),
                receiver: Some(receiver@),
                client_secret: client_secret@,
                server_secret: server_secret@,
                reassembly: crate::spec::reasm_new(),
            }));
        }
        Ok(out)
    }

    /// Whether the connection can still send and receive.
    pub fn is_open(&self) -> (out: bool)
        ensures out == (self@.phase == spec::Phase::Open),
    {
        matches!(self.phase, Phase::Open)
    }

    fn terminal(&mut self, phase: Phase)
        requires phase == Phase::Failed || phase == Phase::Closed,
        ensures
            final(self)@ == (if phase == Phase::Failed { spec::failed() } else { spec::closed() }),
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        self.phase = phase;
        self.sender = None;
        self.receiver = None;
        self.client_secret.clear();
        self.server_secret.clear();
        self.reassembler = Reassembler::new();
        proof {
            if phase == Phase::Failed {
                assert(self@ =~= spec::failed());
            } else {
                assert(self@ =~= spec::closed());
            }
        }
    }

    fn die(&mut self, alert: u8) -> (out: Out)
        ensures
            out@ == spec::die(alert).0, final(self)@ == spec::die(alert).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        self.terminal(Phase::Failed);
        Out::ending(End::Fail(alert))
    }

    /// §5.2, §5.3: protect `content` under the next sequence number of the
    /// send epoch. Only that epoch changes.
    fn seal_record(&mut self, typ: u8, content: &[u8]) -> (out: Result<Vec<u8>, u8>)
        requires old(self).resources_wf(), old(self).bound(),
        ensures
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
            final(self)@.phase == old(self)@.phase,
            final(self)@.receiver == old(self)@.receiver,
            final(self)@.client_secret == old(self)@.client_secret,
            final(self)@.server_secret == old(self)@.server_secret,
            final(self)@.reassembly == old(self)@.reassembly,
            match old(self)@.sender {
                Some(tx) => {
                    let r = spec::send_record(old(self).cipher_functions(), tx, typ, content@);
                    final(self)@.sender == Some(r.0) && crate::traffic::exec::sent_view(out) == r.1
                },
                None => out == Err::<Vec<u8>, u8>(80u8) && final(self)@.sender == old(self)@.sender,
            },
    {
        let ghost f = self.cipher_functions();
        match self.sender.as_mut() {
            None => Err(crate::spec::INTERNAL_ERROR),
            Some(tx) => {
                let ghost before = tx@;
                let ghost seal_before = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| tx.seal_spec(n, ad, p);
                proof { lemma_seal_closure(f, before, seal_before); }
                tx.seal(typ, content, 0)
            },
        }
    }

    /// §5.2, §5.3: authenticate and open the first record of `wire` under the
    /// receive epoch. Only that epoch changes.
    fn open_record(&mut self, wire: &[u8]) -> (out: TrafficRead)
        requires old(self).resources_wf(), old(self).bound(), old(self)@.receiver is Some,
        ensures
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
            final(self)@.phase == old(self)@.phase,
            final(self)@.sender == old(self)@.sender,
            final(self)@.client_secret == old(self)@.client_secret,
            final(self)@.server_secret == old(self)@.server_secret,
            final(self)@.reassembly == old(self)@.reassembly,
            match old(self)@.receiver {
                Some(rx) => {
                    let r = crate::traffic::spec::receive(spec::open_of(old(self).cipher_functions(), rx), rx, wire@);
                    final(self)@.receiver == Some(r.0) && out@ == r.1
                },
                None => false,
            },
    {
        let ghost f = self.cipher_functions();
        match self.receiver.as_mut() {
            None => TrafficRead::Fail(crate::spec::INTERNAL_ERROR),
            Some(rx) => {
                let ghost before = rx@;
                let ghost open_before = |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| rx.open_spec(n, ad, ct);
                proof { lemma_open_closure(f, before, open_before); }
                rx.open(wire)
            },
        }
    }

    /// §6.2: the fatal alert goes out under the current client key, if it can,
    /// and the connection fails.
    fn fatal(&mut self, alert: u8) -> (out: Out)
        requires old(self).resources_wf(), old(self).bound(),
        ensures
            out@ == spec::fatal(old(self).cipher_functions(), old(self)@, alert).0,
            final(self)@ == spec::fatal(old(self).cipher_functions(), old(self)@, alert).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        let mut content: Vec<u8> = Vec::new();
        crate::encode::write_alert(&mut content, crate::spec::Alert {
            level: crate::spec::LEVEL_FATAL,
            description: alert,
        });
        proof {
            assert(content@ =~= crate::spec::write_alert(crate::spec::Alert {
                level: crate::spec::LEVEL_FATAL,
                description: alert,
            }));
        }
        match self.seal_record(crate::spec::CT_ALERT, content.as_slice()) {
            Ok(wire) => {
                self.terminal(Phase::Failed);
                Out::one(wire, End::Fail(alert))
            },
            Err(_) => self.die(alert),
        }
    }

    /// §6.1: `close_notify` goes out under the current client key, if it can,
    /// and the connection ends in order.
    fn close_connection(&mut self) -> (out: Out)
        requires old(self).resources_wf(), old(self).bound(),
        ensures
            out@ == spec::close_connection(old(self).cipher_functions(), old(self)@).0,
            final(self)@ == spec::close_connection(old(self).cipher_functions(), old(self)@).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        let mut content: Vec<u8> = Vec::new();
        crate::encode::write_alert(&mut content, crate::spec::Alert {
            level: crate::spec::LEVEL_WARNING,
            description: crate::spec::CLOSE_NOTIFY,
        });
        proof {
            assert(content@ =~= crate::spec::write_alert(crate::spec::Alert {
                level: crate::spec::LEVEL_WARNING,
                description: crate::spec::CLOSE_NOTIFY,
            }));
        }
        match self.seal_record(crate::spec::CT_ALERT, content.as_slice()) {
            Ok(wire) => {
                self.terminal(Phase::Closed);
                Out::one(wire, End::Close)
            },
            Err(_) => {
                self.terminal(Phase::Closed);
                Out::ending(End::Close)
            },
        }
    }

    /// §7.2, §7.3: move the client write secret on and install its keys.
    fn rotate_sender(&mut self) -> (out: Result<(), u8>)
        requires old(self).resources_wf(), old(self).bound(), old(self)@.client_secret.len() == 32,
        ensures
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
            match out {
                Ok(_) => spec::rotated_sender(old(self).crypto_functions(), old(self)@)
                    == Ok::<spec::State, u8>(final(self)@),
                Err(a) => spec::rotated_sender(old(self).crypto_functions(), old(self)@)
                    == Err::<spec::State, u8>(a) && final(self)@ == old(self)@,
            },
    {
        let next = crate::schedule::exec::update_secret(&self.crypto, self.client_secret.as_slice());
        match Encryptor::new(&self.crypto, &self.factory, next.as_slice()) {
            Err(a) => Err(a),
            Ok(tx) => {
                let ghost tx_view = tx@;
                self.sender = Some(tx);
                self.client_secret = next;
                proof {
                    assert(self@ =~= (spec::State { sender: Some(tx_view), client_secret: next@, ..old(self)@ }));
                }
                Ok(())
            },
        }
    }

    /// §7.2, §7.3: move the server read secret on and install its keys.
    fn rotate_receiver(&mut self) -> (out: Result<(), u8>)
        requires old(self).resources_wf(), old(self).bound(), old(self)@.server_secret.len() == 32,
        ensures
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
            match out {
                Ok(_) => spec::rotated_receiver(old(self).crypto_functions(), old(self)@)
                    == Ok::<spec::State, u8>(final(self)@),
                Err(a) => spec::rotated_receiver(old(self).crypto_functions(), old(self)@)
                    == Err::<spec::State, u8>(a) && final(self)@ == old(self)@,
            },
    {
        let next = crate::schedule::exec::update_secret(&self.crypto, self.server_secret.as_slice());
        match Decryptor::new(&self.crypto, &self.factory, next.as_slice()) {
            Err(a) => Err(a),
            Ok(rx) => {
                let ghost rx_view = rx@;
                self.receiver = Some(rx);
                self.server_secret = next;
                proof {
                    assert(self@ =~= (spec::State { receiver: Some(rx_view), server_secret: next@, ..old(self)@ }));
                }
                Ok(())
            },
        }
    }

    /// §4.6.3: KeyUpdate(`request`) under the current client key, then the
    /// client write keys move on.
    fn send_key_update(&mut self, request: u8) -> (out: Out)
        requires old(self).wf(),
        ensures
            out@ == spec::send_key_update(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, request).0,
            final(self)@ == spec::send_key_update(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, request).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        if !matches!(self.phase, Phase::Open) { return Out::quiet(); }
        let mut body: Vec<u8> = Vec::new();
        crate::encode::write_key_update(&mut body, request);
        let mut message: Vec<u8> = Vec::new();
        proof { assert(body.len() == 1); }
        crate::encode::write_handshake(&mut message, crate::spec::HS_KEY_UPDATE, body.as_slice());
        proof {
            assert(message@ =~= crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE,
                crate::spec::write_key_update(request)));
        }
        match self.seal_record(crate::spec::CT_HANDSHAKE, message.as_slice()) {
            Err(a) => self.die(a),
            Ok(wire) => {
                proof { lemma_start_fresh(self.crypto_functions(), self.client_secret@); }
                match self.rotate_sender() {
                    Ok(_) => Out::one(wire, End::Continue),
                    Err(a) => {
                        self.terminal(Phase::Failed);
                        Out::one(wire, End::Fail(a))
                    },
                }
            },
        }
    }

    /// §5, §5.3: one application data record, behind a KeyUpdate when the
    /// send epoch is on its last sequence number.
    fn send_data_record(&mut self, data: &[u8]) -> (out: Out)
        requires old(self).wf(), !spec::needs_rekey(old(self)@),
        ensures
            out@ == spec::send_data_record(old(self).cipher_functions(), old(self)@, data@).0,
            final(self)@ == spec::send_data_record(old(self).cipher_functions(), old(self)@, data@).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        match self.seal_record(crate::spec::CT_APPLICATION_DATA, data) {
            Ok(wire) => Out::one(wire, End::Continue),
            Err(a) => self.die(a),
        }
    }

    fn send_application_out(&mut self, data: &[u8]) -> (out: Out)
        requires old(self).wf(),
        ensures
            out@ == spec::send_application(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, data@).0,
            final(self)@ == spec::send_application(old(self).crypto_functions(),
                old(self).cipher_functions(), old(self)@, data@).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        if !matches!(self.phase, Phase::Open) { return Out::quiet(); }
        let rekey = match self.sender.as_ref() {
            Some(tx) => match tx.next_sequence() {
                Some(n) => n == u64::MAX,
                None => false,
            },
            None => false,
        };
        if rekey {
            let first = self.send_key_update(crate::spec::UPDATE_NOT_REQUESTED);
            if !matches!(self.phase, Phase::Open) { return first; }
            proof {
                lemma_start_fresh(self.crypto_functions(), self@.client_secret);
                assert(!spec::needs_rekey(self@));
            }
            let second = self.send_data_record(data);
            first.then(second)
        } else {
            self.send_data_record(data)
        }
    }

    /// §5: send one application data record of at most 2^14 bytes; a longer
    /// one fails the connection with `record_overflow` (the caller
    /// fragments).
    pub fn send_application(&mut self, data: &[u8]) -> (out: Vec<Action>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            super::post_handshake_contract::send_application_ensures(old(self).crypto_functions(),
                old(self).cipher_functions(), old(self)@, data@, crate::types::views(out@), final(self)@),
    {
        let o = self.send_application_out(data);
        into_actions(o)
    }

    /// §4.6.3: a client-initiated KeyUpdate, asking the server to update its
    /// keys as well when `request_peer` is set.
    pub fn update_keys(&mut self, request_peer: bool) -> (out: Vec<Action>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            super::post_handshake_contract::update_keys_ensures(old(self).crypto_functions(),
                old(self).cipher_functions(), old(self)@, request_peer, crate::types::views(out@),
                final(self)@),
    {
        let request = if request_peer { crate::spec::UPDATE_REQUESTED } else { crate::spec::UPDATE_NOT_REQUESTED };
        let o = self.send_key_update(request);
        into_actions(o)
    }

    /// §6.1: send `close_notify` and end the connection. Nothing if it
    /// already ended.
    pub fn close(&mut self) -> (out: Vec<Action>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            super::post_handshake_contract::close_ensures(old(self).cipher_functions(), old(self)@,
                crate::types::views(out@), final(self)@),
    {
        let o = if matches!(self.phase, Phase::Open) { self.close_connection() } else { Out::quiet() };
        into_actions(o)
    }

    /// §4.6.3, §5.1: a valid KeyUpdate that must end its record at a message
    /// boundary; the read keys move on and a requested reply goes out.
    fn key_update_received(&mut self, request: u8, last: bool) -> (out: Out)
        requires old(self).wf(),
        ensures
            out@ == spec::key_update_received(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, request, last).0,
            final(self)@ == spec::key_update_received(old(self).crypto_functions(),
                old(self).cipher_functions(), old(self)@, request, last).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        if !last || !self.reassembler.at_message_boundary() {
            return self.fatal(crate::spec::UNEXPECTED_MESSAGE);
        }
        match self.rotate_receiver() {
            Err(a) => self.fatal(a),
            Ok(_) => {
                if request == crate::spec::UPDATE_REQUESTED {
                    proof {
                        lemma_start_fresh(self.crypto_functions(), self@.server_secret);
                    }
                    self.send_key_update(crate::spec::UPDATE_NOT_REQUESTED)
                } else {
                    Out::quiet()
                }
            },
        }
    }

    /// §4.6: one complete handshake message after the handshake.
    fn message(&mut self, m: &[u8], last: bool) -> (out: Out)
        requires old(self).wf(),
        ensures
            out@ == spec::message(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, m@, last).0,
            final(self)@ == spec::message(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, m@, last).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        if m.is_empty() { return self.fatal(crate::spec::UNEXPECTED_MESSAGE); }
        let t = crate::reader::byte_at(m, 0);
        if !(t == crate::spec::HS_NEW_SESSION_TICKET || t == crate::spec::HS_KEY_UPDATE) {
            return self.fatal(crate::spec::UNEXPECTED_MESSAGE);
        }
        let parsed = crate::handshake::parse_handshake(m, crate::schedule::spec::HASH_LEN);
        match parsed {
            Err(k) => self.fatal(crate::encode::alert_for(k).description),
            // §4.6.1: parsed, then ignored.
            Ok(crate::types::HsMsg::NewSessionTicket(_)) => Out::quiet(),
            Ok(crate::types::HsMsg::KeyUpdate(r)) => self.key_update_received(r, last),
            Ok(_) => self.fatal(crate::spec::UNEXPECTED_MESSAGE),
        }
    }

    /// The complete messages of one record from index `i`, in order.
    fn messages(&mut self, ms: &Vec<Vec<u8>>, i: usize) -> (out: Out)
        requires old(self).wf(), i <= ms.len(),
        ensures
            out@ == spec::messages(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, crate::reassemble::views_bytes(ms@).skip(i as int)).0,
            final(self)@ == spec::messages(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, crate::reassemble::views_bytes(ms@).skip(i as int)).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
        decreases ms.len() - i,
    {
        if i >= ms.len() { return Out::quiet(); }
        let next = i.saturating_add(1);
        let last = next == ms.len();
        let message = match ms.get(i) {
            Some(m) => m,
            None => return self.die(crate::spec::INTERNAL_ERROR),
        };
        let first = self.message(message.as_slice(), last);
        if !matches!(self.phase, Phase::Open) { return first; }
        proof {
            let views = crate::reassemble::views_bytes(ms@);
            assert(views.skip(i as int)[0] == ms@[i as int]@);
            assert(views.skip(i as int).skip(1) =~= views.skip(next as int));
        }
        let second = self.messages(ms, next);
        first.then(second)
    }

    /// §5.1, §6: what one authenticated record does.
    fn record(&mut self, typ: u8, content: &[u8]) -> (out: Out)
        requires old(self).wf(), content.len() <= crate::spec::MAX_PLAINTEXT,
        ensures
            out@ == spec::record(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, typ, content@).0,
            final(self)@ == spec::record(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, typ, content@).1,
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        match self.reassembler.feed_record(typ, content) {
            Err(k) => {
                self.reassembler = Reassembler::new();
                self.fatal(crate::encode::alert_for(k).description)
            },
            Ok(ReassemblyEvent::AppData(data)) => {
                let o = Out { wires: Vec::new(), delivered: data, end: End::Continue };
                proof { assert(o@ =~= (spec::Out { wires: seq![], delivered: o.delivered@, end: spec::End::Continue })); }
                o
            },
            Ok(ReassemblyEvent::Alert(a)) => {
                if a.description == crate::spec::CLOSE_NOTIFY { self.close_connection() }
                else { self.die(a.description) }
            },
            Ok(ReassemblyEvent::Messages(ms)) => {
                proof {
                    assert(crate::reassemble::views_bytes(ms@).skip(0) =~= crate::reassemble::views_bytes(ms@));
                }
                self.messages(&ms, 0)
            },
            Ok(ReassemblyEvent::Ignored) => self.fatal(crate::spec::UNEXPECTED_MESSAGE),
        }
    }

    /// §5.1–§5.3: authenticate and open the first record of `wire`, and act
    /// on it. Returns what it did and how many input bytes it consumed.
    fn receive(&mut self, wire: &[u8]) -> (r: (Out, usize))
        requires old(self).wf(),
        ensures
            r.0@ == spec::receive(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, wire@).0,
            final(self)@ == spec::receive(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, wire@).1,
            r.1 as nat == spec::receive(old(self).crypto_functions(), old(self).cipher_functions(),
                old(self)@, wire@).2,
            r.1 <= wire.len(),
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        let ghost s = self@;
        let ghost f = self.cipher_functions();
        let read = self.open_record(wire);
        match read {
            TrafficRead::NeedMore => (Out::quiet(), 0),
            TrafficRead::Fail(a) => {
                let o = self.fatal(a);
                (o, wire.len())
            },
            TrafficRead::Record(typ, content, used) => {
                proof {
                    match s.receiver {
                        Some(rx) => {
                            let r = crate::traffic::spec::receive(spec::open_of(f, rx), rx, wire@);
                            crate::traffic::lemmas::lemma_plaintext_release(spec::open_of(f, rx), rx, wire@,
                                typ, content@, used as nat);
                            lemma_consumed_bounded(spec::open_of(f, rx), rx, wire@, typ, content@, used as nat);
                        },
                        None => {},
                    }
                }
                let o = self.record(typ, content.as_slice());
                (o, used)
            },
        }
    }

    /// The transducer: one step on one input. Processes up to the end of the
    /// first complete record of `Bytes` and says how many bytes that was; the
    /// caller resubmits the rest ([`spec::step`]).
    pub fn step(&mut self, input: Input<'_>) -> (out: (usize, Vec<Action>))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            super::post_handshake_contract::step_ensures(old(self).crypto_functions(),
                old(self).cipher_functions(), old(self)@, input@, crate::types::views(out.1@),
                out.0 as nat, final(self)@),
    {
        match input {
            Input::Bytes(wire) => {
                if matches!(self.phase, Phase::Open) {
                    let (o, consumed) = self.receive(wire);
                    (consumed, into_actions(o))
                } else {
                    (wire.len(), into_actions(Out::quiet()))
                }
            },
            Input::Closed => {
                if matches!(self.phase, Phase::Open) {
                    let o = self.die(crate::spec::INTERNAL_ERROR);
                    (0, into_actions(o))
                } else {
                    (0, into_actions(Out::quiet()))
                }
            },
        }
    }
}
} // verus!
