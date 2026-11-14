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
    /// Our `close_notify` went out; the server can still be read.
    WriteClosed,
    /// The server's `close_notify` came in; the client can still write.
    ReadClosed,
    /// Both directions ended in order.
    Closed,
    /// The connection failed.
    Failed,
}
impl View for Phase {
    type V = spec::Phase;
    open spec fn view(&self) -> spec::Phase {
        match self {
            Phase::Open => spec::Phase::Open,
            Phase::WriteClosed => spec::Phase::WriteClosed,
            Phase::ReadClosed => spec::Phase::ReadClosed,
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
    /// The server's direction of the transport ended: no more bytes will
    /// arrive. Not its `close_notify` (`post_handshake_spec` item 14).
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
    /// The server's `close_notify`: end of data; the write side goes on.
    PeerClosed,
    /// Both directions ended in order (`close_notify`).
    Close,
    /// The connection ended with this alert description.
    Fail(u8),
    /// §6: the peer's fatal alert ended the connection; it is not answered.
    PeerAlert(u8),
}
impl View for Action {
    type V = spec::Action;
    open spec fn view(&self) -> spec::Action {
        match self {
            Action::Send(wire) => spec::Action::Send(wire@),
            Action::Deliver(data) => spec::Action::Deliver(data@),
            Action::PeerClosed => spec::Action::PeerClosed,
            Action::Close => spec::Action::Close,
            Action::Fail(alert) => spec::Action::Fail(*alert),
            Action::PeerAlert(alert) => spec::Action::PeerAlert(*alert),
        }
    }
}

/// [`spec::End`]. Public, as `Action` is: the open `View` body names its
/// constructors wherever `View` is visible, which Verus refuses for a
/// private type.
pub enum End {
    /// The connection goes on.
    Continue,
    /// The server's `close_notify`; the write side goes on.
    PeerClosed,
    /// Both directions ended with `close_notify`.
    Close,
    /// Fatal, with this alert description.
    Fail(u8),
    /// The peer's fatal alert, with its description.
    PeerAlert(u8),
}
impl View for End {
    type V = spec::End;
    open spec fn view(&self) -> spec::End {
        match self {
            End::Continue => spec::End::Continue,
            End::PeerClosed => spec::End::PeerClosed,
            End::Close => spec::End::Close,
            End::Fail(alert) => spec::End::Fail(*alert),
            End::PeerAlert(alert) => spec::End::PeerAlert(*alert),
        }
    }
}

/// [`spec::Out`]: records, plaintext, end. Public for the reason `End` is.
pub struct Out {
    /// Protected records to send, in order.
    pub wires: Vec<Vec<u8>>,
    /// Plaintext to deliver; empty means no `Deliver` action.
    pub delivered: Vec<u8>,
    /// Whether the connection ended.
    pub end: End,
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
        proof {
            assert(crate::reassemble::views_bytes(o.wires@) =~= seq![]);
            assert(o@ =~= spec::quiet());
        }
        o
    }

    fn ending(end: End) -> (o: Out)
        ensures o@ == (spec::Out { wires: seq![], delivered: seq![], end: end@ }),
    {
        let o = Out { wires: Vec::new(), delivered: Vec::new(), end };
        proof {
            assert(crate::reassemble::views_bytes(o.wires@) =~= seq![]);
            assert(o@ =~= (spec::Out { wires: seq![], delivered: seq![], end: end@ }));
        }
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
        let ghost first = self@;
        let ghost second = other@;
        let ghost first_wires = self.wires@;
        let ghost second_wires = other.wires@;
        let mut wires = self.wires;
        let mut more = other.wires;
        wires.append(&mut more);
        let o = Out { wires, delivered: other.delivered, end: other.end };
        proof {
            let a = crate::reassemble::views_bytes(first_wires);
            let b = crate::reassemble::views_bytes(second_wires);
            assert(crate::reassemble::views_bytes(first_wires + second_wires) =~= a + b);
            assert(o@ =~= spec::then(first, second));
        }
        o
    }
}

/// The actions of an output, in order: every `Send`, the `Deliver` if there is
/// plaintext, then `PeerClosed`, `Close`, `Fail` or `PeerAlert`
/// ([`spec::actions`]).
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
        End::PeerClosed => {
            proof { crate::types::lemma_views_push(r@, Action::PeerClosed); }
            r.push(Action::PeerClosed);
        },
        End::Close => {
            proof { crate::types::lemma_views_push(r@, Action::Close); }
            r.push(Action::Close);
        },
        End::Fail(alert) => {
            proof { crate::types::lemma_views_push(r@, Action::Fail(alert)); }
            r.push(Action::Fail(alert));
        },
        End::PeerAlert(alert) => {
            proof { crate::types::lemma_views_push(r@, Action::PeerAlert(alert)); }
            r.push(Action::PeerAlert(alert));
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
    key_update_owed: bool,
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
            key_update_owed: self.key_update_owed,
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
            key_update_owed: false,
        };
        proof {
            assert(out@ =~= (spec::State {
                phase: spec::Phase::Open,
                sender: Some(sender@),
                receiver: Some(receiver@),
                client_secret: client_secret@,
                server_secret: server_secret@,
                reassembly: crate::spec::reasm_new(),
                key_update_owed: false,
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

    /// Which directions are still open.
    pub fn phase(&self) -> (out: Phase)
        ensures out@ == self@.phase,
    {
        self.phase
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
        self.key_update_owed = false;
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

    /// §6: the peer's fatal alert: not answered, and every key is dropped.
    fn peer_alert(&mut self, description: u8) -> (out: Out)
        ensures
            out@ == spec::peer_alert(description).0, final(self)@ == spec::peer_alert(description).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        self.terminal(Phase::Failed);
        Out::ending(End::PeerAlert(description))
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
            final(self)@.key_update_owed == old(self)@.key_update_owed,
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
            final(self)@.key_update_owed == old(self)@.key_update_owed,
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

    /// §6.1: the write side has ended; both have once the read side has too.
    fn finish_write(&mut self) -> (out: End)
        requires old(self).resources_wf(), old(self).bound(),
        ensures
            out@ == spec::finish_write(old(self)@).0,
            final(self)@ == spec::finish_write(old(self)@).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        if matches!(self.phase, Phase::ReadClosed) {
            self.terminal(Phase::Closed);
            End::Close
        } else {
            self.phase = Phase::WriteClosed;
            self.sender = None;
            self.client_secret.clear();
            proof { assert(self@ =~= spec::finish_write(old(self)@).1); }
            End::Continue
        }
    }

    /// §6.1: the server's `close_notify` ended the read side; both have
    /// ended once the write side has too.
    fn peer_closed(&mut self) -> (out: Out)
        requires old(self).resources_wf(), old(self).bound(),
        ensures
            out@ == spec::peer_closed(old(self)@).0,
            final(self)@ == spec::peer_closed(old(self)@).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        if matches!(self.phase, Phase::WriteClosed) {
            self.terminal(Phase::Closed);
            Out::ending(End::Close)
        } else {
            self.phase = Phase::ReadClosed;
            self.receiver = None;
            self.server_secret.clear();
            self.reassembler = Reassembler::new();
            proof { assert(self@ =~= spec::peer_closed(old(self)@).1); }
            Out::ending(End::PeerClosed)
        }
    }

    /// §6.1: `close_notify` goes out under the current client key, if it can,
    /// and the write side ends.
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
                let end = self.finish_write();
                proof { assert(self@ =~= spec::finish_write(old(self)@).1); }
                Out::one(wire, end)
            },
            Err(_) => {
                let end = self.finish_write();
                proof { assert(self@ =~= spec::finish_write(old(self)@).1); }
                Out::ending(end)
            },
        }
    }

    /// §6.1: the end of the transport before the server's `close_notify`
    /// (`post_handshake_spec` item 14). While the write side is open our
    /// `close_notify` goes out first, as [`Self::close`] would send it; then
    /// the connection fails with `internal_error`.
    fn truncated(&mut self) -> (out: Out)
        requires old(self).resources_wf(), old(self).bound(),
        ensures
            out@ == spec::truncated(old(self).cipher_functions(), old(self)@).0,
            final(self)@ == spec::truncated(old(self).cipher_functions(), old(self)@).1,
            final(self).resources_wf(), final(self).bound(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
    {
        let ghost before = self@;
        let ghost f = self.cipher_functions();
        if matches!(self.phase, Phase::Open | Phase::ReadClosed) {
            let closing = self.close_connection();
            let ghost wires = closing@.wires;
            self.terminal(Phase::Failed);
            let o = Out { wires: closing.wires, delivered: Vec::new(), end: End::Fail(crate::spec::INTERNAL_ERROR) };
            proof {
                assert(o@.wires == wires);
                assert(o.delivered@ =~= Seq::<u8>::empty());
                assert(o@ =~= spec::truncated(f, before).0);
            }
            o
        } else {
            self.die(crate::spec::INTERNAL_ERROR)
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
                // The new epoch is `traffic::spec::wf`, as `Encryptor::new`
                // proves; the spec alone cannot say so of the derived lengths.
                Ok(_) => spec::rotated_sender(old(self).crypto_functions(), old(self)@)
                    == Ok::<spec::State, u8>(final(self)@)
                    && match final(self)@.sender { Some(tx) => crate::traffic::spec::wf(tx), None => false },
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
                // As `rotate_sender`'s: the new epoch is `traffic::spec::wf`.
                Ok(_) => spec::rotated_receiver(old(self).crypto_functions(), old(self)@)
                    == Ok::<spec::State, u8>(final(self)@)
                    && match final(self)@.receiver { Some(rx) => crate::traffic::spec::wf(rx), None => false },
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
        if !matches!(self.phase, Phase::Open | Phase::ReadClosed) { return Out::quiet(); }
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
                    Ok(_) => {
                        // The fresh epoch is unfailed at sequence number 0
                        // from a 32-byte secret: `wf` of the rotated state.
                        proof { lemma_start_fresh(self.crypto_functions(), self@.client_secret); }
                        Out::one(wire, End::Continue)
                    },
                    Err(a) => {
                        self.terminal(Phase::Failed);
                        Out::one(wire, End::Fail(a))
                    },
                }
            },
        }
    }

    /// §5, §5.3: one application data record under the current client key.
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

    /// [`Self::send_application`], as its output.
    pub fn send_application_out(&mut self, data: &[u8]) -> (out: Out)
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
        if !matches!(self.phase, Phase::Open | Phase::ReadClosed) { return Out::quiet(); }
        let rekey = match self.sender.as_ref() {
            Some(tx) => match tx.next_sequence() {
                Some(n) => n == u64::MAX,
                None => false,
            },
            None => false,
        };
        // §4.6.3: an owed answer goes first; §5.3: so does a rekey. One
        // KeyUpdate serves both, and nothing is owed after it.
        if self.key_update_owed || rekey {
            self.key_update_owed = false;
            proof { assert(self@ =~= (spec::State { key_update_owed: false, ..old(self)@ })); }
            let first = self.send_key_update(crate::spec::UPDATE_NOT_REQUESTED);
            if !matches!(self.phase, Phase::Open | Phase::ReadClosed) { return first; }
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

    /// [`Self::close`], as its output.
    pub fn close_out(&mut self) -> (out: Out)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
            out@ == spec::close(old(self).cipher_functions(), old(self)@).0,
            final(self)@ == spec::close(old(self).cipher_functions(), old(self)@).1,
    {
        if matches!(self.phase, Phase::Open | Phase::ReadClosed) { self.close_connection() } else { Out::quiet() }
    }

    /// §6.1: send `close_notify` and end the write side. Nothing if it
    /// already ended.
    pub fn close(&mut self) -> (out: Vec<Action>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            super::post_handshake_contract::close_ensures(old(self).cipher_functions(), old(self)@,
                crate::types::views(out@), final(self)@),
    {
        let o = self.close_out();
        into_actions(o)
    }

    /// §4.6.3, §5.1: a valid KeyUpdate that must end its record at a message
    /// boundary; the read keys move on, and on `update_requested` one answer
    /// is owed until the next application data (nothing is sent here).
    fn key_update_received(&mut self, request: u8, last: bool) -> (out: Out)
        requires old(self).wf(), spec::can_read(old(self)@),
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
                    let ghost rotated = self@;
                    self.key_update_owed = true;
                    proof { assert(self@ =~= (spec::State { key_update_owed: true, ..rotated })); }
                    Out::quiet()
                } else {
                    Out::quiet()
                }
            },
        }
    }

    /// §4.6: one complete handshake message after the handshake.
    fn message(&mut self, m: &[u8], last: bool) -> (out: Out)
        requires old(self).wf(), spec::can_read(old(self)@),
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
            Ok(crate::types::HsMsg::KeyUpdate(r)) => self.key_update_received(r, last),
            // §4.6.1: parsed, then ignored. The type check above leaves only
            // NewSessionTicket here.
            Ok(_) => Out::quiet(),
        }
    }

    /// The complete messages of one record from index `i`, in order.
    fn messages(&mut self, ms: &Vec<Vec<u8>>, i: usize) -> (out: Out)
        requires old(self).wf(), spec::can_read(old(self)@), i <= ms.len(),
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
        if !matches!(self.phase, Phase::Open | Phase::WriteClosed) { return first; }
        proof {
            let views = crate::reassemble::views_bytes(ms@);
            assert(views.skip(i as int)[0] == ms@[i as int]@);
            assert(views.skip(i as int).skip(1) =~= views.skip(next as int));
        }
        let second = self.messages(ms, next);
        first.then(second)
    }

    /// §5.1, §6: what one authenticated record does.
    #[verifier::rlimit(30)]
    fn record(&mut self, typ: u8, content: &[u8]) -> (out: Out)
        requires old(self).wf(), spec::can_read(old(self)@), content.len() <= crate::spec::MAX_PLAINTEXT,
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
                proof {
                    assert(crate::reassemble::views_bytes(o.wires@) =~= seq![]);
                    assert(o@ =~= (spec::Out { wires: seq![], delivered: o.delivered@, end: spec::End::Continue }));
                }
                o
            },
            Ok(ReassemblyEvent::Alert(a)) => {
                if a.description == crate::spec::CLOSE_NOTIFY {
                    let o = self.peer_closed();
                    proof { assert(self@ =~= spec::peer_closed(old(self)@).1); }
                    o
                } else if a.description == crate::spec::USER_CANCELED { Out::quiet() }
                else { self.peer_alert(a.description) }
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
        requires old(self).wf(), spec::can_read(old(self)@),
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
        let (consumed, o) = self.step_out(input);
        (consumed, into_actions(o))
    }

    /// [`Self::step`], as its output.
    pub fn step_out(&mut self, input: Input<'_>) -> (out: (usize, Out))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_functions() == old(self).cipher_functions(),
            out.1@ == spec::step(old(self).crypto_functions(), old(self).cipher_functions(), old(self)@, input@).0,
            final(self)@ == spec::step(old(self).crypto_functions(), old(self).cipher_functions(), old(self)@, input@).1,
            out.0 as nat == spec::step(old(self).crypto_functions(), old(self).cipher_functions(), old(self)@, input@).2,
            out.0 as nat <= super::post_handshake_contract::input_len(input@),
    {
        match input {
            Input::Bytes(wire) => {
                if matches!(self.phase, Phase::Open | Phase::WriteClosed) {
                    let (o, consumed) = self.receive(wire);
                    (consumed, o)
                } else {
                    (wire.len(), Out::quiet())
                }
            },
            Input::Closed => {
                if matches!(self.phase, Phase::Open | Phase::WriteClosed) {
                    let o = self.truncated();
                    (0, o)
                } else {
                    (0, Out::quiet())
                }
            },
        }
    }
}
} // verus!
