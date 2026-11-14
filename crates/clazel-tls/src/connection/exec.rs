//! RFC 8446 §5, §7.3 and Appendix A.1: ordered initial-flight dispatch.
use super::framing::{Buffer, Status as FrameStatus};
use super::post_handshake_exec::PostHandshake;
use crate::auth::exec::{Action as AuthAction, Auth, Input as AuthInput};
use crate::auth::verify::Verifier;
use crate::reassemble::{Event as ReassemblyEvent, Reassembler};
use crate::record::{Frame, ReadOut};
use crate::schedule::crypto::Crypto;
use crate::schedule::spec::Label;
use crate::traffic::exec::{Decryptor, Encryptor, Read as TrafficRead};
use crate::traffic::handshake::HandshakeKeys;
use crate::traffic::provider::{Factory, KeyedAead};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// Native dispatcher phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Receive and authenticate the server handshake flight.
    Handshake,
    /// Wait for the client-flight send acknowledgement.
    AwaitClientFlight,
    /// The application traffic secrets are derived; call `into_post_handshake`.
    Ready,
    /// Fatal error; all connection secrets are dropped.
    Failed,
    /// Transport closed; all connection secrets are dropped.
    Closed,
}
impl View for Mode {
    type V = super::dispatcher_spec::Mode;
    closed spec fn view(&self) -> Self::V {
        match self {
            Mode::Handshake => super::dispatcher_spec::Mode::Handshake,
            Mode::AwaitClientFlight => super::dispatcher_spec::Mode::AwaitClientFlight,
            Mode::Ready => super::dispatcher_spec::Mode::Ready,
            Mode::Failed => super::dispatcher_spec::Mode::Failed,
            Mode::Closed => super::dispatcher_spec::Mode::Closed,
        }
    }
}

/// One ordered I/O effect from the dispatcher.
#[derive(Debug, PartialEq, Eq)]
pub enum Action {
    /// Incomplete input or a complete record without an outward effect.
    None,
    /// Exact protected client flight awaiting its send acknowledgement.
    Send(Vec<u8>),
    /// The client flight was acknowledged; call `into_post_handshake`.
    Ready,
    /// Permitted dummy compatibility CCS was dropped.
    Ignored,
    /// The peer sent a nonfatal user_canceled closure alert.
    Cancelled,
    /// RFC 8446 §6.2: a fatal error detected here, with its alert description
    /// and, when a settled write epoch could seal it, the protected fatal
    /// alert record, which the caller sends as the connection's last record.
    /// Every key has been dropped.
    Fail(u8, Option<Vec<u8>>),
    /// RFC 8446 §6: the peer's fatal alert. Nothing is sent in reply, and
    /// every key has been dropped.
    PeerAlert(u8),
    /// §6.1: the connection closed during the flight, with our sealed
    /// close_notify, or `None` when no epoch can seal it.
    Close(Option<Vec<u8>>),
}
/// The view of an optional protected record.
pub open spec fn wire_view(wire: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match wire { Some(bytes) => Some(bytes@), None => None }
}
impl View for Action {
    type V = super::dispatcher_spec::Action;
    open spec fn view(&self) -> Self::V {
        match self {
            Action::None => super::dispatcher_spec::Action::None,
            Action::Send(bytes) => super::dispatcher_spec::Action::Send(bytes@),
            Action::Ready => super::dispatcher_spec::Action::Ready,
            Action::Ignored => super::dispatcher_spec::Action::Ignored,
            Action::Cancelled => super::dispatcher_spec::Action::Cancelled,
            Action::Fail(alert, wire) => super::dispatcher_spec::Action::Fail(*alert,
                match wire { Some(bytes) => Some(bytes@), None => None }),
            Action::PeerAlert(alert) => super::dispatcher_spec::Action::PeerAlert(*alert),
            Action::Close(wire) => super::dispatcher_spec::Action::Close(
                match wire { Some(bytes) => Some(bytes@), None => None }),
        }
    }
}

/// Owns the handshake epochs and the initial TLS authentication flight.
pub struct Connection<C: Crypto, F: Factory, V: Verifier> {
    crypto: C,
    factory: F,
    verifier: V,
    mode: Mode,
    auth: Option<Auth>,
    handshake_sender: Option<Encryptor<F::Cipher>>,
    handshake_receiver: Option<Decryptor<F::Cipher>>,
    master: Vec<u8>,
    client_application_secret: Vec<u8>,
    server_application_secret: Vec<u8>,
    reassembler: Reassembler,
    framer: Buffer,
    ccs_pending: bool,
    pending_flight: Vec<u8>,
}
impl<C: Crypto, F: Factory, V: Verifier> View for Connection<C, F, V> {
    type V = super::dispatcher_spec::State;
    closed spec fn view(&self) -> Self::V { self.state() }
}
impl<C: Crypto, F: Factory, V: Verifier> Connection<C, F, V> {
    pub closed spec fn state(&self) -> super::dispatcher_spec::State {
        super::dispatcher_spec::State {
            mode: self.mode@,
            auth: match self.auth { Some(auth) => Some(auth@), None => None },
            handshake_sender: match self.handshake_sender { Some(epoch) => Some(epoch@), None => None },
            handshake_receiver: match self.handshake_receiver { Some(epoch) => Some(epoch@), None => None },
            master: self.master@,
            client_application_secret: self.client_application_secret@,
            server_application_secret: self.server_application_secret@,
            reassembly: self.reassembler@,
            framing: self.framer@,
            ccs_pending: self.ccs_pending,
            pending_flight: self.pending_flight@,
        }
    }
}

fn step_auth<C: Crypto, V: Verifier>(auth: &mut Auth, crypto: &C, verifier: &V, input: AuthInput<'_>) -> (out: AuthAction)
    requires old(auth).wf(),
    ensures final(auth).wf(), crate::auth::contract::send_safe(final(auth)@, out@),
        crate::auth::contract::step_ensures(crypto.functions(), verifier.functions(), old(auth)@, input@, final(auth)@, out@),
{
    let out = auth.step(crypto, verifier, input);
    proof {
        crate::auth::lemmas::lemma_step(crypto.functions(), verifier.functions(), old(auth)@, input@);
        assert(crate::auth::contract::send_safe(final(auth)@, out@));
    }
    out
}

fn step_auth_exact<C: Crypto, V: Verifier>(auth: &mut Auth, crypto: &C, verifier: &V, input: AuthInput<'_>) -> (out: AuthAction)
    requires old(auth).wf(),
    ensures crate::auth::contract::step_ensures(crypto.functions(), verifier.functions(), old(auth)@, input@, final(auth)@, out@),
{
    auth.step(crypto, verifier, input)
}

fn copy_body(bytes: &[u8]) -> (out: Vec<u8>)
    ensures out@ == bytes@,
{
    vstd::slice::slice_to_vec(bytes)
}

/// The key-explicit seal function an AEAD object computes is the factory's
/// function at its key ([`super::dispatcher_spec::seal_with`]).
proof fn lemma_seal_with(ciphers: super::dispatcher_spec::Ciphers, epoch: crate::traffic::spec::State,
    g: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>)
    requires forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] g(n, ad, p) == (ciphers.seal)(epoch.key, n, ad, p),
    ensures g == super::dispatcher_spec::seal_with(ciphers, epoch),
{
    assert(g =~= super::dispatcher_spec::seal_with(ciphers, epoch));
}

/// RFC 8446 §5.2, §5.3, §6.2: seal one alert record under `sender`'s next
/// sequence number; `None` when the epoch refuses (failed or spent).
fn seal_alert<A: KeyedAead>(sender: &mut Encryptor<A>, Ghost(ciphers): Ghost<super::dispatcher_spec::Ciphers>,
    content: &[u8]) -> (out: Option<Vec<u8>>)
    requires old(sender).wf(),
        forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] old(sender).seal_spec(n, ad, p)
            == (ciphers.seal)(old(sender)@.key, n, ad, p),
    ensures wire_view(out) == match crate::traffic::spec::send(super::dispatcher_spec::seal_with(ciphers, old(sender)@),
            old(sender)@, crate::spec::CT_ALERT, content@, 0).1 {
            Ok(record) => Some(record),
            Err(_) => None,
        },
{
    let ghost epoch = sender@;
    let ghost seal_before = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| sender.seal_spec(n, ad, p);
    proof { lemma_seal_with(ciphers, epoch, seal_before); }
    sender.seal(crate::spec::CT_ALERT, content, 0).ok()
}

/// The key-explicit open function an AEAD object computes is the factory's
/// function at its key ([`super::dispatcher_spec::open_with`]).
proof fn lemma_open_with(ciphers: super::dispatcher_spec::Ciphers, epoch: crate::traffic::spec::State,
    g: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>)
    requires forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] g(n, ad, ct) == (ciphers.open)(epoch.key, n, ad, ct),
    ensures g == super::dispatcher_spec::open_with(ciphers, epoch),
{
    assert(g =~= super::dispatcher_spec::open_with(ciphers, epoch));
}

/// §5.2, §5.3: seal the client flight under `sender`'s next sequence number.
fn seal_flight<A: KeyedAead>(sender: &mut Encryptor<A>, Ghost(ciphers): Ghost<super::dispatcher_spec::Ciphers>,
    flight: &[u8]) -> (out: Result<Vec<u8>, u8>)
    requires old(sender).wf(),
        forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] old(sender).seal_spec(n, ad, p)
            == (ciphers.seal)(old(sender)@.key, n, ad, p),
    ensures final(sender).wf(),
        forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] final(sender).seal_spec(n, ad, p)
            == (ciphers.seal)(final(sender)@.key, n, ad, p),
        (final(sender)@, crate::traffic::exec::sent_view(out)) == crate::traffic::spec::send(
            super::dispatcher_spec::seal_with(ciphers, old(sender)@), old(sender)@, crate::spec::CT_HANDSHAKE, flight@, 0),
{
    let ghost epoch = sender@;
    let ghost seal_before = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| sender.seal_spec(n, ad, p);
    proof { lemma_seal_with(ciphers, epoch, seal_before); }
    sender.seal(crate::spec::CT_HANDSHAKE, flight, 0)
}

/// §5.2: open one protected record under `receiver`'s next sequence number.
fn open_record<A: KeyedAead>(receiver: &mut Decryptor<A>, Ghost(ciphers): Ghost<super::dispatcher_spec::Ciphers>,
    wire: &[u8]) -> (out: TrafficRead)
    requires old(receiver).wf(),
        forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] old(receiver).open_spec(n, ad, ct)
            == (ciphers.open)(old(receiver)@.key, n, ad, ct),
    ensures final(receiver).wf(),
        forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] final(receiver).open_spec(n, ad, ct)
            == (ciphers.open)(final(receiver)@.key, n, ad, ct),
        (final(receiver)@, out@) == crate::traffic::spec::receive(
            super::dispatcher_spec::open_with(ciphers, old(receiver)@), old(receiver)@, wire@),
{
    let ghost epoch = receiver@;
    let ghost open_before = |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| receiver.open_spec(n, ad, ct);
    proof { lemma_open_with(ciphers, epoch, open_before); }
    receiver.open(wire)
}

/// §4.4.4, §5.1: [`super::dispatcher_spec::finished_out_of_place`].
fn finished_misplaced(messages: &[Vec<u8>], boundary: bool) -> (out: bool)
    ensures out == super::dispatcher_spec::finished_out_of_place(crate::reassemble::views_bytes(messages@), boundary),
{
    let ghost views = crate::reassemble::views_bytes(messages@);
    let mut i: usize = 0;
    proof { assert(views.skip(0) =~= views); }
    while i < messages.len()
        invariant
            i <= messages.len(),
            views == crate::reassemble::views_bytes(messages@),
            super::dispatcher_spec::finished_out_of_place(views, boundary)
                == super::dispatcher_spec::finished_out_of_place(views.skip(i as int), boundary),
        decreases messages.len() - i,
    {
        let ghost rest = views.skip(i as int);
        let message = match messages.get(i) {
            Some(message) => message,
            None => return false,
        };
        proof {
            assert(rest[0] == message@);
            assert(rest.skip(1) =~= views.skip(i + 1));
        }
        if !message.is_empty() && crate::reader::byte_at(message.as_slice(), 0) == crate::spec::HS_FINISHED
            && (i.saturating_add(1) != messages.len() || !boundary) {
            return true;
        }
        i = i.saturating_add(1);
    }
    proof { assert(views.skip(i as int).len() == 0); }
    false
}

impl<C: Crypto, F: Factory, V: Verifier> Connection<C, F, V> where F::Cipher: KeyedAead {
    /// Every send epoch is well formed and bound to the factory's seal
    /// function at its key: what sealing a fatal alert needs.
    pub closed spec fn senders_wf(&self) -> bool {
        match self.handshake_sender { Some(epoch) => epoch.wf() && forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>|
            #[trigger] epoch.seal_spec(n, ad, p) == (self.factory.functions().seal)(epoch@.key, n, ad, p), None => true }
    }

    /// The lifecycle and resource invariant exposed to callers.
    pub closed spec fn wf(&self) -> bool { super::dispatcher_spec::wf(self.state()) }

    /// Native buffers and every live AEAD object satisfy their local invariants.
    pub closed spec fn resources_wf(&self) -> bool {
        (match self.handshake_sender { Some(epoch) => epoch.wf(), None => true })
            && (match self.handshake_receiver { Some(epoch) => epoch.wf(), None => true })
            && self.reassembler.wf() && super::framing_spec::wf(self.framer@) && self.framer.wf()
            && self.framer.protected_mode()
    }

    /// Authentication state remains valid independently of record/key resources.
    pub closed spec fn auth_wf(&self) -> bool {
        match self.auth { Some(auth) => auth.wf(), None => self.mode == Mode::Failed || self.mode == Mode::Closed }
    }

    /// Every live epoch retains the exact cipher factory function and installed key.
    pub closed spec fn cipher_bindings_wf(&self) -> bool {
        (match self.handshake_sender { Some(epoch) => forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>|
            #[trigger] epoch.seal_spec(n, ad, p) == (self.factory.functions().seal)(epoch@.key, n, ad, p), None => true })
            && (match self.handshake_receiver { Some(epoch) => forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>|
                #[trigger] epoch.open_spec(n, ad, ct) == (self.factory.functions().open)(epoch@.key, n, ad, ct), None => true })
    }

    /// Abstract key-schedule provider model retained by this connection.
    pub closed spec fn crypto_functions(&self) -> crate::schedule::spec::Crypto { self.crypto.functions() }

    /// Keyed cipher functions retained across application epoch updates.
    pub closed spec fn cipher_models(&self) -> super::dispatcher_spec::Ciphers {
        super::dispatcher_spec::cipher_models(self.factory.functions(), self@)
    }

    /// The abstract AEAD functions of this connection's cipher factory.
    pub closed spec fn cipher_functions(&self) -> crate::traffic::spec::Cipher { self.factory.functions() }

    /// Abstract certificate/signature policy retained by this connection.
    pub closed spec fn verifier_functions(&self) -> crate::auth::spec::Verification { self.verifier.functions() }

    /// Consume the checked Hello handoff. The caller has already processed
    /// ClientHello2 and, for HRR, sent the required dummy CCS before that message.
    pub fn new(keys: HandshakeKeys<F::Cipher>, crypto: C, factory: F, verifier: V) -> (out: Self)
        requires keys.wf(),
            forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] keys.seal_spec(n, ad, p) == (factory.functions().seal)(keys@.1.key, n, ad, p),
            forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] keys.open_spec(n, ad, ct) == (factory.functions().open)(keys@.2.key, n, ad, ct),
        ensures out.wf(), out.auth_wf(), out.resources_wf(), out.cipher_bindings_wf(), out@ == super::dispatcher_spec::start(keys@, keys.ccs_pending_spec()),
            out.crypto_functions() == crypto.functions(), out.cipher_functions() == factory.functions(),
            out.verifier_functions() == verifier.functions(),
    {
        let ccs_pending = keys.needs_compatibility_ccs();
        let ghost handoff = keys@;
        let ghost old_seal = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| keys.seal_spec(n, ad, p);
        let ghost old_open = |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| keys.open_spec(n, ad, ct);
        let (auth, sender, receiver, master) = keys.into_parts();
        let out = Connection {
            crypto, factory, verifier, mode: Mode::Handshake,
            auth: Some(auth), handshake_sender: Some(sender), handshake_receiver: Some(receiver),
            master,
            client_application_secret: Vec::new(), server_application_secret: Vec::new(),
            reassembler: Reassembler::new(), framer: Buffer::new(), ccs_pending,
            pending_flight: Vec::new(),
        };
        proof {
            reveal(Connection::wf);
            assert(out@ == super::dispatcher_spec::start(handoff, ccs_pending));
            assert(super::dispatcher_spec::wf(out@));
            assert(out.reassembler.wf());
            assert(super::framing_spec::wf(out.framer@));
            assert(out.framer.wf());
            assert(match out.auth { Some(auth) => auth.wf(), None => true });
            assert(match out.handshake_sender { Some(epoch) => epoch.wf(), None => true });
            assert(match out.handshake_receiver { Some(epoch) => epoch.wf(), None => true });
            assert(sender@.key == handoff.1.key);
            assert(receiver@.key == handoff.2.key);
            assert(crate::traffic::contract::seal_preserved(old_seal,
                |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| sender.seal_spec(n, ad, p)));
            assert(crate::traffic::contract::open_preserved(old_open,
                |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| receiver.open_spec(n, ad, ct)));
            assert forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] sender.seal_spec(n, ad, p)
                == (out.factory.functions().seal)(sender@.key, n, ad, p) by {
                reveal(crate::traffic::contract::seal_preserved);
                assert(sender.seal_spec(n, ad, p) == old_seal(n, ad, p));
                assert(old_seal(n, ad, p) == (out.factory.functions().seal)(handoff.1.key, n, ad, p));
            }
            assert forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] receiver.open_spec(n, ad, ct)
                == (out.factory.functions().open)(receiver@.key, n, ad, ct) by {
                reveal(crate::traffic::contract::open_preserved);
                assert(receiver.open_spec(n, ad, ct) == old_open(n, ad, ct));
                assert(old_open(n, ad, ct) == (out.factory.functions().open)(handoff.2.key, n, ad, ct));
            }
            assert(out.wf());
            assert(out.cipher_bindings_wf());
        }
        out
    }

    /// Current phase of the connection dispatcher.
    pub fn mode(&self) -> (out: Mode) ensures out@ == self@.mode { self.mode }

    fn terminal(&mut self, mode: Mode)
        requires mode == Mode::Failed || mode == Mode::Closed,
        ensures final(self).wf(), final(self).resources_wf(), final(self)@ == if mode == Mode::Failed {
            super::dispatcher_spec::failed()
        } else {
            super::dispatcher_spec::closed()
        },
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_models() == old(self).cipher_models(),
            final(self).verifier_functions() == old(self).verifier_functions(),
    {
        self.mode = mode;
        self.auth = None;
        self.handshake_sender = None;
        self.handshake_receiver = None;
        self.master.clear();
        self.client_application_secret.clear();
        self.server_application_secret.clear();
        self.reassembler = Reassembler::new();
        self.framer = Buffer::new();
        self.ccs_pending = false;
        self.pending_flight.clear();
        proof {
            reveal(Connection::wf);
            reveal(Connection::resources_wf);
            assert(self.framer.wf());
            assert(self.wf());
        }
    }

    /// RFC 8446 §6, §6.2, §5.3: a fatal error detected here. The fatal alert
    /// is sealed under the settled write epoch's next sequence number, if
    /// there is one ([`super::dispatcher_spec::alert_epoch`]), and only then
    /// is every key dropped.
    fn fail(&mut self, alert: u8) -> (out: Action)
        requires old(self).senders_wf(),
        ensures
            final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            final(self)@ == super::dispatcher_spec::failed(),
            super::dispatcher_contract::fail_ensures(old(self).cipher_models(), old(self)@, alert, out@, final(self)@),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_models() == old(self).cipher_models(),
            final(self).verifier_functions() == old(self).verifier_functions(),
    {
        let ghost before = self@;
        let ghost ciphers = self.cipher_models();
        let mut content: Vec<u8> = Vec::new();
        crate::encode::write_alert(&mut content, crate::spec::Alert {
            level: crate::spec::LEVEL_FATAL,
            description: alert,
        });
        proof {
            assert(content@ =~= super::dispatcher_spec::fatal_alert(alert));
            assert(ciphers.seal == self.factory.functions().seal);
        }
        let wire = match self.mode {
            Mode::Handshake => match self.handshake_sender.as_mut() {
                Some(sender) => {
                    let ghost epoch = sender@;
                    proof { assert(before.handshake_sender == Some(epoch)); }
                    let sealed = seal_alert(sender, Ghost(ciphers), content.as_slice());
                    proof {
                        assert(super::dispatcher_spec::alert_epoch(before) == Some(epoch));
                        assert(wire_view(sealed) == super::dispatcher_spec::alert_wire(ciphers, before, alert));
                    }
                    sealed
                },
                None => {
                    proof { assert(super::dispatcher_spec::alert_epoch(before) is None); }
                    None
                },
            },
            Mode::AwaitClientFlight | Mode::Ready | Mode::Failed | Mode::Closed => {
                proof { assert(super::dispatcher_spec::alert_epoch(before) is None); }
                None
            },
        };
        let ghost sent = wire_view(wire);
        proof { assert(sent == super::dispatcher_spec::alert_wire(ciphers, before, alert)); }
        self.terminal(Mode::Failed);
        let out = Action::Fail(alert, wire);
        proof {
            assert(out@ == super::dispatcher_spec::Action::Fail(alert, sent));
            assert((out@, self@) == super::dispatcher_spec::fatal(ciphers, before, alert));
            assert(super::dispatcher_spec::no_live_secrets(self@));
        }
        out
    }

    /// RFC 8446 §6, §6.2: the peer's fatal alert. It is not answered; every
    /// key is dropped.
    fn peer_alert(&mut self, alert: u8) -> (out: Action)
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            (out@, final(self)@) == super::dispatcher_spec::receive_fatal_alert(old(self).cipher_models(),
                old(self)@, alert),
    {
        self.terminal(Mode::Failed);
        Action::PeerAlert(alert)
    }

    /// §6.1: close during the flight. Our close_notify is sealed under the
    /// settled write epoch, if there is one, and then every key is dropped.
    fn close(&mut self) -> (out: Action)
        requires old(self).senders_wf(),
        ensures final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            (out@, final(self)@) == super::dispatcher_spec::closing(old(self).cipher_models(), old(self)@),
    {
        let ghost before = self@;
        let ghost ciphers = self.cipher_models();
        let mut content: Vec<u8> = Vec::new();
        crate::encode::write_alert(&mut content, crate::spec::Alert {
            level: crate::spec::LEVEL_WARNING,
            description: crate::spec::CLOSE_NOTIFY,
        });
        proof {
            assert(content@ =~= super::dispatcher_spec::close_notify_alert());
            assert(ciphers.seal == self.factory.functions().seal);
        }
        let wire = match self.mode {
            Mode::Handshake => match self.handshake_sender.as_mut() {
                Some(sender) => {
                    let ghost epoch = sender@;
                    proof { assert(before.handshake_sender == Some(epoch)); }
                    let sealed = seal_alert(sender, Ghost(ciphers), content.as_slice());
                    proof {
                        assert(super::dispatcher_spec::alert_epoch(before) == Some(epoch));
                        assert(wire_view(sealed) == super::dispatcher_spec::close_wire(ciphers, before));
                    }
                    sealed
                },
                None => {
                    proof { assert(super::dispatcher_spec::alert_epoch(before) is None); }
                    None
                },
            },
            Mode::AwaitClientFlight | Mode::Ready | Mode::Failed | Mode::Closed => {
                proof { assert(super::dispatcher_spec::alert_epoch(before) is None); }
                None
            },
        };
        let ghost sent = wire_view(wire);
        proof { assert(sent == super::dispatcher_spec::close_wire(ciphers, before)); }
        self.terminal(Mode::Closed);
        let out = Action::Close(wire);
        proof { assert(out@ == super::dispatcher_spec::Action::Close(sent)); }
        out
    }

    /// §6.1: close from our side during the flight.
    pub fn close_write(&mut self) -> (out: Action)
        requires old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(),
            (out@, final(self)@) == super::dispatcher_spec::closing(super::dispatcher_spec::Ciphers {
                seal: old(self).cipher_functions().seal, open: old(self).cipher_functions().open }, old(self)@),
    {
        self.close()
    }

    fn protect_client_flight(&mut self, flight: &[u8]) -> (out: Result<Vec<u8>, u8>)
        requires old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).resources_wf(), final(self).cipher_bindings_wf(),
            (final(self)@, crate::traffic::exec::sent_view(out))
                == super::dispatcher_spec::protect_client_flight(old(self).cipher_models(), old(self)@, flight@),
    {
        if flight.is_empty() || flight.len() > crate::spec::MAX_PLAINTEXT { return Err(crate::spec::INTERNAL_ERROR); }
        let ghost ciphers = self.cipher_models();
        let sender = match self.handshake_sender.as_mut() {
            Some(sender) => sender,
            None => return Err(crate::spec::INTERNAL_ERROR),
        };
        let protected = seal_flight(sender, Ghost(ciphers), flight)?;
        let mut out = Vec::new();
        if self.ccs_pending {
            out.extend_from_slice(&[20, 3, 3, 0, 1, 1]);
            proof { assert(out@ =~= super::dispatcher_spec::compatibility_ccs_record()); }
        }
        let ghost prefix = out@;
        out.extend_from_slice(protected.as_slice());
        proof {
            assert(out@ =~= prefix + protected@);
            assert(prefix + protected@ =~= if old(self).ccs_pending {
                super::dispatcher_spec::compatibility_ccs_record() + protected@
            } else {
                protected@
            });
        }
        self.ccs_pending = false;
        Ok(out)
    }

    fn send_action(&mut self, flight: Vec<u8>) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
            old(self).auth is Some,
            match old(self)@.auth { Some(auth) => auth.phase == crate::auth::spec::Phase::SendFinished, None => false },
            crate::spec::at_message_boundary(old(self)@.reassembly), old(self)@.framing.len() == 0,
            old(self)@.handshake_sender is Some, old(self)@.handshake_receiver is Some,
            old(self)@.master.len() == 32, old(self)@.pending_flight.len() == 0,
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
            (out@, final(self)@) == super::dispatcher_spec::send_flight(old(self).cipher_models(), old(self)@, flight@),
    {
        let ghost before = self@;
        let ghost ciphers = self.cipher_models();
        let wire = match self.protect_client_flight(flight.as_slice()) {
            Ok(wire) => wire,
            Err(alert) => return self.fail(alert),
        };
        proof { super::dispatcher_lemmas::lemma_protected_flight_nonempty(ciphers, before, flight@); }
        self.pending_flight.extend_from_slice(wire.as_slice());
        self.mode = Mode::AwaitClientFlight;
        proof {
            reveal(Connection::wf);
            reveal(Connection::resources_wf);
            assert(self.resources_wf());
            assert(self@.mode == super::dispatcher_spec::Mode::AwaitClientFlight);
            assert(self@.handshake_sender is Some);
            assert(self@.handshake_receiver is Some);
            assert(self@.master.len() == 32);
            assert(!self.ccs_pending);
            assert(self.pending_flight@ =~= wire@);
            assert(self@.pending_flight.len() > 0);
            assert(self@.auth is Some);
            assert(match self@.auth { Some(auth) => auth.phase == crate::auth::spec::Phase::SendFinished, None => false });
            assert(crate::spec::at_message_boundary(self@.reassembly));
            assert(self.framer@.len() == 0);
            assert(self.wf());
        }
        let out = Action::Send(wire);
        proof {
            reveal(<Action as View>::view);
            assert(super::dispatcher_spec::action_refines(out@, self@));
        }
        out
    }

    fn run_auth_message(&mut self, typ: u8, body: Vec<u8>) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
            (out@, final(self)@) == super::dispatcher_spec::run_auth(old(self).crypto_functions(), old(self).verifier_functions(),
                old(self).cipher_models(), old(self)@, typ, body@),
    {
        let auth = match self.auth.as_mut() {
            Some(auth) => auth,
            None => return self.fail(crate::spec::INTERNAL_ERROR),
        };
        let action = step_auth(auth, &self.crypto, &self.verifier, AuthInput::Handshake(typ, body.as_slice()));
        proof {
            reveal(Connection::resources_wf);
            assert(self.resources_wf());
            assert(self.framer.wf());
        }
        match action {
            AuthAction::None => Action::None,
            AuthAction::Send(flight) => {
                if !self.reassembler.at_message_boundary() || !self.framer.is_empty() {
                    self.fail(crate::spec::UNEXPECTED_MESSAGE)
                } else {
                    self.send_action(flight)
                }
            },
            AuthAction::Fail(alert) => self.fail(alert),
            AuthAction::Close => self.close(),
            AuthAction::Ready | AuthAction::Deliver(_) => self.fail(crate::spec::INTERNAL_ERROR),
        }
    }

    fn process_one(&mut self, message: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
            (out@, final(self)@) == super::dispatcher_spec::process_one(old(self).crypto_functions(), old(self).verifier_functions(),
                old(self).cipher_models(), old(self)@, message@),
            out@ is None ==> final(self)@.mode == super::dispatcher_spec::Mode::Handshake,
    {
        if message.len() < crate::spec::HANDSHAKE_HEADER { return self.fail(crate::spec::DECODE_ERROR); }
        let typ = crate::reader::byte_at(message, 0);
        let bytes = vstd::slice::slice_subrange(message, crate::spec::HANDSHAKE_HEADER, message.len());
        proof { assert(bytes@ =~= message@.skip(crate::spec::HANDSHAKE_HEADER as int)); }
        self.run_auth_message(typ, copy_body(bytes))
    }

    fn process_messages(&mut self, messages: Vec<Vec<u8>>) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
            (out@, final(self)@) == super::dispatcher_spec::process_messages(old(self).crypto_functions(), old(self).verifier_functions(),
                old(self).cipher_models(), old(self)@, crate::reassemble::views_bytes(messages@)),
    {
        hide(super::dispatcher_spec::process_one);
        hide(super::dispatcher_spec::wf);
        let ghost views = crate::reassemble::views_bytes(messages@);
        let ghost c = self.crypto_functions();
        let ghost v = self.verifier_functions();
        let ghost ciphers = self.cipher_models();
        let ghost before = self@;
        if finished_misplaced(messages.as_slice(), self.reassembler.at_message_boundary()) {
            return self.fail(crate::spec::UNEXPECTED_MESSAGE);
        }
        let mut index: usize = 0;
        proof { assert(views.skip(0) =~= views); }
        while index < messages.len()
            invariant
                index <= messages.len(),
                views == crate::reassemble::views_bytes(messages@),
                self.crypto_functions() == c, self.verifier_functions() == v, self.cipher_models() == ciphers,
                c == old(self).crypto_functions(), v == old(self).verifier_functions(),
                ciphers == old(self).cipher_models(), before == old(self)@,
                !super::dispatcher_spec::finished_out_of_place(views, super::dispatcher_spec::message_boundary(before)),
                self.cipher_functions() == old(self).cipher_functions(),
                self.wf(), self.auth_wf(), self.resources_wf(), self.cipher_bindings_wf(),
                self@.mode == super::dispatcher_spec::Mode::Handshake,
                super::dispatcher_spec::run_messages(c, v, ciphers, before, views)
                    == super::dispatcher_spec::run_messages(c, v, ciphers, self@, views.skip(index as int)),
            decreases messages.len() - index,
        {
            let ghost rest = views.skip(index as int);
            let message = match messages.get(index) {
                Some(message) => message,
                None => return self.fail(crate::spec::INTERNAL_ERROR),
            };
            proof {
                assert(rest[0] == message@);
                assert(rest.skip(1) =~= views.skip(index + 1));
            }
            let ghost at = self@;
            let action = self.process_one(message.as_slice());
            proof {
                assert(rest.len() > 0);
                assert((action@, self@) == super::dispatcher_spec::process_one(c, v, ciphers, at, rest[0]));
                if !(action@ is None) {
                    assert(super::dispatcher_spec::run_messages(c, v, ciphers, at, rest) == (action@, self@));
                }
            }
            if !matches!(action, Action::None) { return action; }
            index = index.saturating_add(1);
        }
        proof { assert(views.skip(index as int).len() == 0); }
        Action::None
    }

    fn handle_plaintext(&mut self, typ: u8, bytes: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
            super::dispatcher_contract::peer_alert_ensures(old(self).cipher_models(), old(self)@, typ, bytes@,
                out@, final(self)@),
            (out@, final(self)@) == super::dispatcher_spec::receive_plaintext(old(self).crypto_functions(), old(self).verifier_functions(),
                old(self).cipher_models(), old(self)@, typ, bytes@),
    {
        if bytes.len() > crate::spec::MAX_PLAINTEXT { return self.fail(crate::spec::RECORD_OVERFLOW); }
        let ghost before = self@;
        let fed = self.reassembler.feed_record(typ, bytes);
        let ghost fed_view = crate::reassemble::res_event(fed, self.reassembler@);
        proof {
            assert(fed_view == crate::spec::feed_record(before.reassembly,
                crate::spec::Record { ctype: typ, fragment: bytes@ }));
        }
        match fed {
            Err(error) => self.fail(crate::encode::alert_for(error).description),
            Ok(ReassemblyEvent::Messages(messages)) => {
                proof {
                    reveal(Connection::wf);
                    reveal(Connection::resources_wf);
                    reveal(super::dispatcher_spec::wf);
                    assert(self@.mode == super::dispatcher_spec::Mode::Handshake);
                    assert(self@.auth is Some);
                    assert(self@.handshake_sender is Some);
                    assert(self@.handshake_receiver is Some);
                    assert(self@.master.len() == 32);
                    assert(self@.pending_flight.len() == 0);
                    assert(self.wf());
                    assert(self.auth_wf());
                    assert(self.resources_wf());
                    assert(self.cipher_bindings_wf());
                }
                self.process_messages(messages)
            },
            // §5: no application data before the handshake ends.
            Ok(ReassemblyEvent::AppData(_)) => self.fail(crate::spec::UNEXPECTED_MESSAGE),
            Ok(ReassemblyEvent::Alert(alert)) => {
                if alert.description == crate::spec::CLOSE_NOTIFY {
                    self.close()
                } else if alert.description == crate::spec::USER_CANCELED {
                    Action::Cancelled
                } else {
                    // RFC 8446 §6, §6.2: the peer's fatal alert is not answered.
                    let out = self.peer_alert(alert.description);
                    proof {
                        assert(!crate::spec::alert_is_closure(alert));
                        assert(fed_view is Ok);
                        assert(super::dispatcher_contract::peer_alert_ensures(
                            old(self).cipher_models(), before, typ, bytes@, out@, self@));
                    }
                    out
                }
            },
            Ok(ReassemblyEvent::Ignored) => Action::Ignored,
        }
    }

    fn handle_record(&mut self, wire: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
            super::dispatcher_contract::ccs_record_ensures(old(self).cipher_models(), wire@, old(self)@, out@, final(self)@),
            (out@, final(self)@) == super::dispatcher_spec::receive_record(old(self).crypto_functions(), old(self).verifier_functions(),
                old(self).cipher_models(), old(self)@, wire@),
    {
        match crate::record::read_record(wire, true) {
            ReadOut::Done(Frame::Ccs, _) => {
                let auth = match self.auth.as_ref() {
                    Some(auth) => auth,
                    None => return self.fail(crate::spec::INTERNAL_ERROR),
                };
                // RFC 8446 §5.1: handshake messages "MUST NOT be interleaved with
                // other record types", so a compatibility CCS is dropped only at a
                // message boundary; inside a fragmented message it is fatal.
                if !matches!(auth.phase(), crate::auth::spec::Phase::SendFinished | crate::auth::spec::Phase::Ready)
                    && self.reassembler.at_message_boundary() {
                    Action::Ignored
                } else {
                    self.fail(crate::spec::UNEXPECTED_MESSAGE)
                }
            },
            ReadOut::Done(Frame::Protected(_, _), _) => {
                let ghost ciphers = self.cipher_models();
                let receiver = match self.handshake_receiver.as_mut() {
                    Some(receiver) => receiver,
                    None => return self.fail(crate::spec::INTERNAL_ERROR),
                };
                let read = open_record(receiver, Ghost(ciphers), wire);
                match read {
                    TrafficRead::Record(typ, bytes, consumed) => {
                        if consumed != wire.len() { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
                        self.handle_plaintext(typ, bytes.as_slice())
                    },
                    TrafficRead::NeedMore => self.fail(crate::spec::DECODE_ERROR),
                    TrafficRead::Fail(alert) => self.fail(alert),
                }
            },
            ReadOut::Fail(error) => self.fail(crate::encode::alert_for(error).description),
            ReadOut::NeedMore | ReadOut::Done(_, _) => self.fail(crate::spec::UNEXPECTED_MESSAGE),
        }
    }

    /// Accumulate exactly one record prefix. Bytes after its boundary remain
    /// caller-owned; the caller must resubmit that suffix after the returned action.
    pub fn feed(&mut self, input: &[u8]) -> (out: (usize, Action))
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(), out.0 <= input.len(),
            super::dispatcher_contract::feed_ensures(old(self)@, input@, out.0 as nat, out.1@, final(self)@),
            super::dispatcher_contract::feed_exact(old(self).crypto_functions(), old(self).verifier_functions(),
                super::dispatcher_spec::Ciphers { seal: old(self).cipher_functions().seal, open: old(self).cipher_functions().open },
                old(self)@, input@, out.0 as nat, out.1@, final(self)@),
    {
        if matches!(self.mode, Mode::AwaitClientFlight | Mode::Ready | Mode::Failed | Mode::Closed) {
            return (0, Action::None);
        }
        let (consumed, status) = self.framer.feed(input);
        let result = match status {
            FrameStatus::Pending => {
                proof {
                    reveal(Connection::wf);
                    reveal(Connection::state);
                    reveal(super::dispatcher_spec::wf);
                    assert(self.wf());
                }
                (consumed, Action::None)
            },
            FrameStatus::Fail(alert) => (consumed, self.fail(alert)),
            FrameStatus::Complete => {
                let wire = self.framer.take();
                let action = self.handle_record(wire.as_slice());
                proof { reveal(Connection::wf); reveal(super::dispatcher_spec::wf); assert(self.wf()); }
                (consumed, action)
            },
        };
        proof {
            reveal(super::dispatcher_contract::feed_ensures);
            reveal(<Action as View>::view);
            reveal(super::dispatcher_spec::wf);
            assert(self.wf());
            assert(result.0 as nat <= input@.len());
            assert(old(self)@.mode == super::dispatcher_spec::Mode::AwaitClientFlight ==> result.0 == 0);
            assert(old(self)@.mode == super::dispatcher_spec::Mode::Ready ==> result.0 == 0);
            match result.1@ {
                super::dispatcher_spec::Action::Send(wire) => {
                    assert(self@.mode == super::dispatcher_spec::Mode::AwaitClientFlight);
                    assert(self@.pending_flight == wire);
                },
                super::dispatcher_spec::Action::Ready => assert(self@.mode == super::dispatcher_spec::Mode::Ready),
                super::dispatcher_spec::Action::Fail(_, _) => assert(super::dispatcher_contract::terminal_ensures(self@, super::dispatcher_spec::Mode::Failed)),
                super::dispatcher_spec::Action::PeerAlert(_) => assert(super::dispatcher_contract::terminal_ensures(self@, super::dispatcher_spec::Mode::Failed)),
                super::dispatcher_spec::Action::Close(_) => assert(super::dispatcher_contract::terminal_ensures(self@, super::dispatcher_spec::Mode::Closed)),
                _ => {},
            }
            assert(super::dispatcher_contract::feed_ensures(old(self)@, input@,
                result.0 as nat, result.1@, self@));
        }
        result
    }

    /// Acknowledge the exact client flight returned by `feed` before the
    /// application traffic secrets are derived.
    pub fn acknowledge_client_flight(&mut self, sent: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_contract::acknowledgement_ensures(old(self).crypto_functions(), old(self).verifier_functions(),
                old(self)@, sent@, out@, final(self)@),
            super::dispatcher_contract::acknowledge_exact(old(self).crypto_functions(), old(self).verifier_functions(),
                super::dispatcher_spec::Ciphers { seal: old(self).cipher_functions().seal, open: old(self).cipher_functions().open },
                old(self)@, sent@, out@, final(self)@),
    {
        if !matches!(self.mode, Mode::AwaitClientFlight) || sent != self.pending_flight.as_slice() {
            return self.fail(crate::spec::INTERNAL_ERROR);
        }
        let ghost before = self@;
        proof {
            assert(before.mode == super::dispatcher_spec::Mode::AwaitClientFlight);
            assert(sent@ == before.pending_flight);
        }
        let auth = match self.auth.as_mut() {
            Some(auth) => auth,
            None => return self.fail(crate::spec::INTERNAL_ERROR),
        };
        match step_auth_exact(auth, &self.crypto, &self.verifier, AuthInput::SentFinished) {
            AuthAction::Ready => {},
            AuthAction::Fail(alert) => return self.fail(alert),
            _ => return self.fail(crate::spec::INTERNAL_ERROR),
        }
        let ghost after_auth = self@;
        proof {
            assert(after_auth.auth is Some);
            assert(match after_auth.auth { Some(a) => a.phase == crate::auth::spec::Phase::Ready && a.client_sent, None => false });
        }
        let hash = match self.auth.as_ref() {
            Some(auth) => auth.application_hash(),
            None => return self.fail(crate::spec::INTERNAL_ERROR),
        };
        let master = self.master.as_slice();
        let client_secret = crate::schedule::exec::expand_label(&self.crypto, master,
            Label::ClientApplication, hash, 32);
        let server_secret = crate::schedule::exec::expand_label(&self.crypto, master,
            Label::ServerApplication, hash, 32);
        let out = Action::Ready;
        self.handshake_sender = None;
        self.handshake_receiver = None;
        self.client_application_secret = client_secret;
        self.server_application_secret = server_secret;
        self.master.clear();
        self.pending_flight.clear();
        self.mode = Mode::Ready;
        proof {
            reveal(super::dispatcher_contract::acknowledgement_ensures);
            reveal(super::dispatcher_contract::ready_after_ack_ensures);
            assert(out@ is Ready);
            assert(super::dispatcher_contract::ready_after_ack_ensures(
                old(self).crypto_functions(), old(self).verifier_functions(), before, sent@, self@));
        }
        out
    }

    /// RFC 8446 §7.1, §7.3: the handshake is over, and the post-handshake
    /// transducer takes over from the two application traffic secrets, both
    /// directions at sequence number 0. A connection is consumed by this, so
    /// no second machine holds those secrets.
    pub fn into_post_handshake(self) -> (out: Result<PostHandshake<C, F>, u8>)
        requires self.wf(), self@.mode == super::dispatcher_spec::Mode::Ready,
        ensures
            match out {
                Ok(p) => p.wf() && p.crypto_functions() == self.crypto_functions()
                    && p.cipher_functions() == self.cipher_functions()
                    && super::dispatcher_contract::handoff_ensures(self.crypto_functions(), self@, Ok(p@)),
                Err(a) => super::dispatcher_contract::handoff_ensures(self.crypto_functions(), self@, Err(a)),
            },
    {
        PostHandshake::new(self.crypto, self.factory, self.client_application_secret.as_slice(),
            self.server_application_secret.as_slice())
    }

    /// RFC 8446 §6.1: the server's direction of the transport ended. Before
    /// its close_notify that is a truncation ([`super::dispatcher_spec::eof`]):
    /// our close_notify goes out, sealed as [`Self::close_write`] would seal
    /// it, and the connection fails with `internal_error`, which is not sent.
    /// After an error alert or a close_notify it does nothing.
    pub fn eof(&mut self) -> (out: Action)
        requires old(self).wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures
            final(self).crypto_functions() == old(self).crypto_functions(), final(self).cipher_functions() == old(self).cipher_functions(),
            final(self).wf(),
            super::dispatcher_contract::truncation_ensures(super::dispatcher_spec::Ciphers {
                seal: old(self).cipher_functions().seal, open: old(self).cipher_functions().open }, old(self)@, out@,
                final(self)@),
    {
        if matches!(self.mode, Mode::Failed | Mode::Closed) {
            Action::None
        } else {
            let closing = self.close();
            let ghost closed_view = closing@;
            let wire = match closing {
                Action::Close(wire) => wire,
                _ => None,
            };
            proof {
                assert(closed_view == super::dispatcher_spec::Action::Close(wire_view(wire)));
            }
            self.terminal(Mode::Failed);
            Action::Fail(crate::spec::INTERNAL_ERROR, wire)
        }
    }
}
} // verus!
