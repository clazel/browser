//! RFC 8446 §5, §7.3 and Appendix A.1: ordered initial-flight dispatch.
use super::framing::{Buffer, Status as FrameStatus};
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
    /// Application traffic keys are installed.
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
    /// Application epochs installed after the client flight acknowledgement.
    Ready,
    /// Plaintext released through the Auth delivery gate.
    Deliver(Vec<u8>),
    /// Permitted dummy compatibility CCS was dropped.
    Ignored,
    /// Fatal error; this action does not send an alert automatically.
    Fail(u8),
    /// Peer close_notify or local close.
    Close,
}
impl View for Action {
    type V = super::dispatcher_spec::Action;
    open spec fn view(&self) -> Self::V {
        match self {
            Action::None => super::dispatcher_spec::Action::None,
            Action::Send(bytes) => super::dispatcher_spec::Action::Send(bytes@),
            Action::Ready => super::dispatcher_spec::Action::Ready,
            Action::Deliver(bytes) => super::dispatcher_spec::Action::Deliver(bytes@),
            Action::Ignored => super::dispatcher_spec::Action::Ignored,
            Action::Fail(alert) => super::dispatcher_spec::Action::Fail(*alert),
            Action::Close => super::dispatcher_spec::Action::Close,
        }
    }
}

/// Owns both traffic directions and the initial TLS authentication flight.
pub struct Connection<C: Crypto, F: Factory, V: Verifier> {
    crypto: C,
    factory: F,
    verifier: V,
    mode: Mode,
    auth: Option<Auth>,
    handshake_sender: Option<Encryptor<F::Cipher>>,
    handshake_receiver: Option<Decryptor<F::Cipher>>,
    application_sender: Option<Encryptor<F::Cipher>>,
    application_receiver: Option<Decryptor<F::Cipher>>,
    master: Vec<u8>,
    client_application_secret: Vec<u8>,
    server_application_secret: Vec<u8>,
    pending_update_secret: Vec<u8>,
    pending_update_wire: Vec<u8>,
    pending_update_request: Option<u8>,
    pending_update_is_response: bool,
    response_due: bool,
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
            application_sender: match self.application_sender { Some(epoch) => Some(epoch@), None => None },
            application_receiver: match self.application_receiver { Some(epoch) => Some(epoch@), None => None },
            master: self.master@,
            client_application_secret: self.client_application_secret@,
            server_application_secret: self.server_application_secret@,
            reassembly: self.reassembler@,
            framing: self.framer@,
            ccs_pending: self.ccs_pending,
            pending_flight: self.pending_flight@,
            pending_update_secret: self.pending_update_secret@,
            pending_update_wire: self.pending_update_wire@,
            pending_update_request: self.pending_update_request,
            pending_update_is_response: self.pending_update_is_response,
            response_due: self.response_due,
        }
    }
}

fn step_auth<C: Crypto, V: Verifier>(auth: &mut Auth, crypto: &C, verifier: &V, input: AuthInput<'_>) -> (out: AuthAction)
    requires old(auth).wf(),
    ensures final(auth).wf(), crate::auth::contract::send_safe(final(auth)@, out@),
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

fn parse_key_update_wire(message: &[u8]) -> Result<u8, u8> {
    match crate::handshake::parse_handshake(message, crate::schedule::spec::HASH_LEN) {
        Ok(crate::types::HsMsg::KeyUpdate(request)) => Ok(request),
        Ok(_) => Err(crate::spec::UNEXPECTED_MESSAGE),
        Err(error) => Err(crate::encode::alert_for(error).description),
    }
}

impl<C: Crypto, F: Factory, V: Verifier> Connection<C, F, V> where F::Cipher: KeyedAead {
    /// The lifecycle and resource invariant exposed to callers.
    pub closed spec fn wf(&self) -> bool { super::dispatcher_spec::wf(self.state()) }

    /// Native buffers and every live AEAD object satisfy their local invariants.
    pub closed spec fn resources_wf(&self) -> bool {
        (match self.handshake_sender { Some(epoch) => epoch.wf(), None => true })
            && (match self.handshake_receiver { Some(epoch) => epoch.wf(), None => true })
            && (match self.application_sender { Some(epoch) => epoch.wf(), None => true })
            && (match self.application_receiver { Some(epoch) => epoch.wf(), None => true })
            && self.reassembler.wf() && super::framing_spec::wf(self.framer@) && self.framer.wf()
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
            && (match self.application_sender { Some(epoch) => forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>|
                #[trigger] epoch.seal_spec(n, ad, p) == (self.factory.functions().seal)(epoch@.key, n, ad, p), None => true })
            && (match self.application_receiver { Some(epoch) => forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>|
                #[trigger] epoch.open_spec(n, ad, ct) == (self.factory.functions().open)(epoch@.key, n, ad, ct), None => true })
    }

    /// Abstract key-schedule provider model retained by this connection.
    pub closed spec fn crypto_functions(&self) -> crate::schedule::spec::Crypto { self.crypto.functions() }

    /// Keyed cipher functions retained across application epoch updates.
    pub closed spec fn cipher_models(&self) -> super::dispatcher_spec::Ciphers {
        super::dispatcher_spec::cipher_models(self.factory.functions(), self@)
    }

    /// Abstract certificate/signature policy retained by this connection.
    pub closed spec fn verifier_functions(&self) -> crate::auth::spec::Verification { self.verifier.functions() }

    /// Consume the checked Hello handoff. The caller has already processed
    /// ClientHello2 and, for HRR, sent the required dummy CCS before that message.
    pub fn new(keys: HandshakeKeys<F::Cipher>, crypto: C, factory: F, verifier: V) -> (out: Self)
        requires keys.wf(),
            forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] keys.seal_spec(n, ad, p) == (factory.functions().seal)(keys@.1.key, n, ad, p),
            forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] keys.open_spec(n, ad, ct) == (factory.functions().open)(keys@.2.key, n, ad, ct),
        ensures out.wf(), out.auth_wf(), out.resources_wf(), out.cipher_bindings_wf(), out@ == super::dispatcher_spec::start(keys@, keys.ccs_pending_spec()),
    {
        let ccs_pending = keys.needs_compatibility_ccs();
        let ghost handoff = keys@;
        let ghost old_seal = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| keys.seal_spec(n, ad, p);
        let ghost old_open = |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| keys.open_spec(n, ad, ct);
        let (auth, sender, receiver, master) = keys.into_parts();
        let out = Connection {
            crypto, factory, verifier, mode: Mode::Handshake,
            auth: Some(auth), handshake_sender: Some(sender), handshake_receiver: Some(receiver),
            application_sender: None, application_receiver: None, master,
            client_application_secret: Vec::new(), server_application_secret: Vec::new(),
            pending_update_secret: Vec::new(), pending_update_wire: Vec::new(),
            pending_update_request: None, pending_update_is_response: false, response_due: false,
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
            assert(match out.application_sender { Some(epoch) => epoch.wf(), None => true });
            assert(match out.application_receiver { Some(epoch) => epoch.wf(), None => true });
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
        self.application_sender = None;
        self.application_receiver = None;
        self.master.clear();
        self.client_application_secret.clear();
        self.server_application_secret.clear();
        self.pending_update_secret.clear();
        self.pending_update_wire.clear();
        self.pending_update_request = None;
        self.pending_update_is_response = false;
        self.response_due = false;
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

    fn fail(&mut self, alert: u8) -> (out: Action)
        ensures final(self).wf(), final(self).resources_wf(), final(self)@ == super::dispatcher_spec::failed(), out@ == super::dispatcher_spec::Action::Fail(alert),
    {
        self.terminal(Mode::Failed);
        Action::Fail(alert)
    }

    fn close(&mut self) -> (out: Action)
        ensures final(self).wf(), final(self).resources_wf(), final(self)@ == super::dispatcher_spec::closed(), out@ == super::dispatcher_spec::Action::Close,
    {
        self.terminal(Mode::Closed);
        Action::Close
    }

    fn protect_client_flight(&mut self, flight: &[u8]) -> (out: Result<Vec<u8>, u8>)
        requires old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self).mode == Mode::Handshake,
        ensures final(self).resources_wf(), final(self).cipher_bindings_wf(),
            final(self)@.auth == old(self)@.auth,
            final(self)@.handshake_receiver == old(self)@.handshake_receiver,
            final(self)@.application_sender == old(self)@.application_sender,
            final(self)@.application_receiver == old(self)@.application_receiver,
            final(self)@.master == old(self)@.master,
            final(self)@.client_application_secret == old(self)@.client_application_secret,
            final(self)@.server_application_secret == old(self)@.server_application_secret,
            final(self)@.pending_update_secret == old(self)@.pending_update_secret,
            final(self)@.pending_update_wire == old(self)@.pending_update_wire,
            final(self)@.pending_update_request == old(self)@.pending_update_request,
            final(self)@.pending_update_is_response == old(self)@.pending_update_is_response,
            final(self)@.response_due == old(self)@.response_due,
            final(self)@.reassembly == old(self)@.reassembly,
            final(self)@.framing == old(self)@.framing,
            final(self)@.mode == old(self)@.mode,
            final(self)@.pending_flight == old(self)@.pending_flight,
            match out {
                Ok(_) => !final(self).ccs_pending && final(self)@.handshake_sender is Some,
                Err(_) => true,
            },
    {
        if flight.is_empty() || flight.len() > crate::spec::MAX_PLAINTEXT { return Err(crate::spec::INTERNAL_ERROR); }
        let sender = match self.handshake_sender.as_mut() {
            Some(sender) => sender,
            None => return Err(crate::spec::INTERNAL_ERROR),
        };
        let protected = sender.seal(crate::spec::CT_HANDSHAKE, flight, 0)?;
        let mut out = Vec::new();
        if self.ccs_pending {
            out.extend_from_slice(&[20, 3, 3, 0, 1, 1]);
        }
        out.extend_from_slice(protected.as_slice());
        self.ccs_pending = false;
        Ok(out)
    }

    fn send_action(&mut self, flight: Vec<u8>) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
            old(self).auth is Some,
            match old(self)@.auth { Some(auth) => auth.phase == crate::auth::spec::Phase::SendFinished, None => false },
            crate::spec::at_message_boundary(old(self)@.reassembly), old(self)@.framing.len() == 0,
            old(self)@.handshake_sender is Some, old(self)@.handshake_receiver is Some,
            old(self)@.application_sender is None, old(self)@.application_receiver is None,
            old(self)@.master.len() == 32, old(self)@.pending_flight.len() == 0,
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
    {
        let wire = match self.protect_client_flight(flight.as_slice()) {
            Ok(wire) => wire,
            Err(alert) => return self.fail(alert),
        };
        if wire.is_empty() { return self.fail(crate::spec::INTERNAL_ERROR); }
        self.pending_flight.extend_from_slice(wire.as_slice());
        self.mode = Mode::AwaitClientFlight;
        proof {
            reveal(Connection::wf);
            reveal(Connection::resources_wf);
            assert(self.resources_wf());
            assert(self@.mode == super::dispatcher_spec::Mode::AwaitClientFlight);
            assert(self@.handshake_sender is Some);
            assert(self@.handshake_receiver is Some);
            assert(self@.application_sender is None);
            assert(self@.application_receiver is None);
            assert(self@.master.len() == 32);
            assert(!self.ccs_pending);
            assert(self@.pending_flight.len() > 0);
            assert(self.pending_flight@ == wire@);
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
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
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
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
    {
        if message.len() < crate::spec::HANDSHAKE_HEADER { return self.fail(crate::spec::DECODE_ERROR); }
        let typ = match message.first() {
            Some(value) => *value,
            None => return self.fail(crate::spec::DECODE_ERROR),
        };
        let bytes = match message.get(crate::spec::HANDSHAKE_HEADER..) {
            Some(body) => body,
            None => return self.fail(crate::spec::DECODE_ERROR),
        };
        self.run_auth_message(typ, copy_body(bytes))
    }

    fn process_messages(&mut self, messages: Vec<Vec<u8>>) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(), old(self)@.mode == super::dispatcher_spec::Mode::Handshake,
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
    {
        let mut has_finished = false;
        let mut i: usize = 0;
        while i < messages.len()
            invariant i <= messages.len(), self.wf(), self.auth_wf(), self.resources_wf(), self.cipher_bindings_wf(), self@.mode == super::dispatcher_spec::Mode::Handshake,
            decreases messages.len() - i,
        {
            let message = match messages.get(i) {
                Some(message) => message,
                None => return self.fail(crate::spec::INTERNAL_ERROR),
            };
            if message.first() == Some(&crate::spec::HS_FINISHED) {
                has_finished = true;
                if i.saturating_add(1) != messages.len() || !self.reassembler.at_message_boundary() {
                    return self.fail(crate::spec::UNEXPECTED_MESSAGE);
                }
            }
            i = i.saturating_add(1);
        }
        if has_finished && !self.reassembler.at_message_boundary() {
            return self.fail(crate::spec::UNEXPECTED_MESSAGE);
        }
        proof { reveal(Connection::wf); assert(self.wf()); }
        let mut index: usize = 0;
        while index < messages.len()
            invariant index <= messages.len(), self.wf(), self.auth_wf(), self.resources_wf(), self.cipher_bindings_wf(), self@.mode == super::dispatcher_spec::Mode::Handshake,
            decreases messages.len() - index,
        {
            let message = match messages.get(index) {
                Some(message) => message,
                None => return self.fail(crate::spec::INTERNAL_ERROR),
            };
            let action = self.process_one(message.as_slice());
            if action != Action::None { return action; }
            if !matches!(self.mode, Mode::Handshake) { return self.fail(crate::spec::INTERNAL_ERROR); }
            index = index.saturating_add(1);
        }
        Action::None
    }

    fn process_post_handshake_messages(&mut self, messages: Vec<Vec<u8>>) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
            old(self)@.mode == super::dispatcher_spec::Mode::Ready,
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
    {
        if messages.is_empty() { return Action::None; }
        if messages.len() != 1 || !self.reassembler.at_message_boundary() {
            return self.fail(crate::spec::UNEXPECTED_MESSAGE);
        }
        let message = match messages.first() {
            Some(message) => message,
            None => return self.fail(crate::spec::DECODE_ERROR),
        };
        match parse_key_update_wire(message.as_slice()) {
            Ok(request) => if request <= 1 { self.receive_key_update(request) }
                else { self.fail(crate::spec::ILLEGAL_PARAMETER) },
            Err(alert) => self.fail(alert),
        }
    }

    fn handle_plaintext(&mut self, typ: u8, bytes: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
    {
        if bytes.len() > crate::spec::MAX_PLAINTEXT { return self.fail(crate::spec::RECORD_OVERFLOW); }
        match self.reassembler.feed_record(typ, bytes) {
            Err(error) => self.fail(crate::encode::alert_for(error).description),
            Ok(ReassemblyEvent::Messages(messages)) => {
                if matches!(self.mode, Mode::Handshake) {
                    proof {
                        reveal(Connection::wf);
                        reveal(Connection::resources_wf);
                        reveal(super::dispatcher_spec::wf);
                        assert(self@.mode == super::dispatcher_spec::Mode::Handshake);
                        assert(self@.auth is Some);
                        assert(self@.handshake_sender is Some);
                        assert(self@.handshake_receiver is Some);
                        assert(self@.application_sender is None);
                        assert(self@.application_receiver is None);
                        assert(self@.master.len() == 32);
                        assert(self@.pending_flight.len() == 0);
                        assert(self.wf());
                        assert(self.auth_wf());
                        assert(self.resources_wf());
                        assert(self.cipher_bindings_wf());
                    }
                    self.process_messages(messages)
                } else if matches!(self.mode, Mode::Ready) {
                    proof {
                        reveal(Connection::wf);
                        reveal(Connection::state);
                        reveal(Connection::auth_wf);
                        reveal(Connection::resources_wf);
                        reveal(Connection::cipher_bindings_wf);
                        reveal(super::dispatcher_spec::wf);
                        assert(self@.mode == super::dispatcher_spec::Mode::Ready);
                        assert(self@.application_sender is Some);
                        assert(self@.application_receiver is Some);
                        assert(self@.auth is Some);
                        assert(self@.client_application_secret.len() == 32);
                        assert(self@.server_application_secret.len() == 32);
                        assert(self.wf());
                        assert(self.auth_wf());
                        assert(self.resources_wf());
                        assert(self.cipher_bindings_wf());
                    }
                    self.process_post_handshake_messages(messages)
                } else { self.fail(crate::spec::UNEXPECTED_MESSAGE) }
            },
            Ok(ReassemblyEvent::AppData(bytes)) => {
                if !matches!(self.mode, Mode::Ready) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
                let auth = match self.auth.as_mut() {
                    Some(auth) => auth,
                    None => return self.fail(crate::spec::INTERNAL_ERROR),
                };
                match step_auth_exact(auth, &self.crypto, &self.verifier, AuthInput::Application(bytes.as_slice())) {
                    AuthAction::Deliver(bytes) => Action::Deliver(bytes),
                    AuthAction::Fail(alert) => self.fail(alert),
                    AuthAction::Close => self.close(),
                    _ => self.fail(crate::spec::INTERNAL_ERROR),
                }
            },
            Ok(ReassemblyEvent::Alert(alert)) => {
                if alert.description == 0 { self.close() }
                else { self.fail(alert.description) }
            },
            Ok(ReassemblyEvent::Ignored) => Action::Ignored,
        }
    }

    fn handle_record(&mut self, wire: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_spec::action_refines(out@, final(self)@),
    {
        match crate::record::read_record(wire, true) {
            ReadOut::Done(Frame::Ccs, _) => {
                let auth = match self.auth.as_ref() {
                    Some(auth) => auth,
                    None => return self.fail(crate::spec::INTERNAL_ERROR),
                };
                if matches!(self.mode, Mode::Handshake)
                    && !matches!(auth.phase(), crate::auth::spec::Phase::SendFinished | crate::auth::spec::Phase::Ready) {
                    Action::Ignored
                } else {
                    self.fail(crate::spec::UNEXPECTED_MESSAGE)
                }
            },
            ReadOut::Done(Frame::Protected(_, _), _) => {
                let read = match self.mode {
                    Mode::Handshake => match self.handshake_receiver.as_mut() {
                        Some(receiver) => receiver.open(wire),
                        None => return self.fail(crate::spec::INTERNAL_ERROR),
                    },
                    Mode::Ready => match self.application_receiver.as_mut() {
                        Some(receiver) => receiver.open(wire),
                        None => return self.fail(crate::spec::INTERNAL_ERROR),
                    },
                    Mode::AwaitClientFlight => return Action::None,
                    Mode::Failed | Mode::Closed => return Action::None,
                };
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
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(), out.0 <= input.len(),
            super::dispatcher_contract::feed_ensures(old(self)@, input@, out.0 as nat, out.1@, final(self)@),
    {
        if matches!(self.mode, Mode::AwaitClientFlight | Mode::Failed | Mode::Closed) {
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
            match result.1@ {
                super::dispatcher_spec::Action::Send(wire) => {
                    if self@.mode == super::dispatcher_spec::Mode::AwaitClientFlight {
                        assert(self@.pending_flight == wire);
                    } else {
                        assert(self@.mode == super::dispatcher_spec::Mode::Ready);
                        assert(self@.pending_update_wire == wire);
                    }
                },
                super::dispatcher_spec::Action::Ready => assert(self@.mode == super::dispatcher_spec::Mode::Ready),
                super::dispatcher_spec::Action::Deliver(_) => assert(self@.mode == super::dispatcher_spec::Mode::Ready),
                super::dispatcher_spec::Action::Fail(_) => assert(super::dispatcher_contract::terminal_ensures(self@, super::dispatcher_spec::Mode::Failed)),
                super::dispatcher_spec::Action::Close => assert(super::dispatcher_contract::terminal_ensures(self@, super::dispatcher_spec::Mode::Closed)),
                _ => {},
            }
            assert(super::dispatcher_contract::feed_ensures(old(self)@, input@,
                result.0 as nat, result.1@, self@));
        }
        result
    }

    /// Acknowledge the exact client flight returned by `feed` before either
    /// direction changes to application traffic keys.
    pub fn acknowledge_client_flight(&mut self, sent: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_contract::acknowledgement_ensures(old(self).crypto_functions(), old(self).verifier_functions(),
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
        let sender = match Encryptor::new(&self.crypto, &self.factory, client_secret.as_slice()) {
            Ok(sender) => sender,
            Err(alert) => return self.fail(alert),
        };
        let receiver = match Decryptor::new(&self.crypto, &self.factory, server_secret.as_slice()) {
            Ok(receiver) => receiver,
            Err(alert) => return self.fail(alert),
        };
        let out = Action::Ready;
        self.handshake_sender = None;
        self.handshake_receiver = None;
        self.application_sender = Some(sender);
        self.application_receiver = Some(receiver);
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

    /// Protect a KeyUpdate using the current client application epoch. The
    /// next secret is installed only by `acknowledge_key_update` after the
    /// caller confirms that these exact wire bytes were sent.
    fn queue_key_update(&mut self, request: u8, is_response: bool) -> (out: Result<Vec<u8>, u8>)
        requires old(self).wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
            old(self)@.mode == super::dispatcher_spec::Mode::Ready,
            old(self)@.pending_update_request is None,
            request <= 1, (!is_response || request == 0), is_response == old(self)@.response_due,
        ensures final(self).wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            final(self).crypto_functions() == old(self).crypto_functions(),
            final(self).cipher_models() == old(self).cipher_models(),
            final(self).verifier_functions() == old(self).verifier_functions(),
            match out {
                Ok(wire) => super::dispatcher_spec::prepare_key_update(old(self).crypto_functions(),
                old(self).cipher_models(),
                old(self)@, request, is_response) == final(self)@
                    && wire@ == final(self)@.pending_update_wire
                    && super::dispatcher_spec::action_refines(super::dispatcher_spec::Action::Send(wire@), final(self)@),
                Err(_) => super::dispatcher_contract::terminal_ensures(final(self)@, super::dispatcher_spec::Mode::Failed)
                    && super::dispatcher_spec::prepare_key_update(old(self).crypto_functions(),
                        old(self).cipher_models(), old(self)@, request, is_response) == super::dispatcher_spec::failed(),
            },
    {
        let ghost before = self@;
        let ghost ciphers = self.cipher_models();
        if request > 1 || (is_response && request != 0) || self.pending_update_request.is_some() || is_response != self.response_due {
            return Err(crate::spec::INTERNAL_ERROR);
        }
        let next_secret = crate::schedule::exec::update_secret(&self.crypto, self.client_application_secret.as_slice());
        let mut body = Vec::new();
        crate::encode::write_key_update(&mut body, request);
        let mut message = Vec::new();
        crate::encode::write_handshake(&mut message, crate::spec::HS_KEY_UPDATE, body.as_slice());
        let wire_result = match self.application_sender.as_mut() {
            Some(sender) => sender.seal(crate::spec::CT_HANDSHAKE, message.as_slice(), 0),
            None => Err(crate::spec::INTERNAL_ERROR),
        };
        let wire = match wire_result {
            Ok(wire) => wire,
            Err(alert) => {
                self.terminal(Mode::Failed);
                return Err(alert);
            },
        };
        self.pending_update_secret = next_secret;
        self.pending_update_wire.extend_from_slice(wire.as_slice());
        self.pending_update_request = Some(request);
        self.pending_update_is_response = is_response;
        if is_response { self.response_due = false; }
        proof {
            reveal(Connection::wf);
            reveal(Connection::state);
            reveal(super::dispatcher_spec::wf);
            reveal(super::dispatcher_spec::prepare_key_update);
            reveal(crate::traffic::contract::send_ensures);
            reveal(crate::traffic::spec::send);
            reveal(crate::spec::encrypt_record);
            reveal(crate::spec::additional_data);
            assert(next_secret@ == crate::schedule::spec::next_traffic_secret(self.crypto_functions(), before.client_application_secret));
            assert(next_secret.len() == 32);
            assert(before.application_sender is Some);
            assert(body@ == crate::spec::write_key_update(request));
            assert(message@ == crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, body@));
            match before.application_sender {
                Some(old_sender) => match old_sender.next {
                Some(n) => assert(wire@ == crate::spec::encrypt_record(
                    |nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>| (ciphers.seal)(old_sender.key, nonce, ad, plaintext),
                    16, old_sender.iv, n, crate::spec::CT_HANDSHAKE, message@, 0)) by {
                    reveal(crate::traffic::spec::send);
                    reveal(crate::spec::encrypt_record);
                    reveal(crate::spec::additional_data);
                },
                None => assert(false),
                },
                None => assert(false),
            }
            assert(self.pending_update_wire@ == wire@);
            assert(self.pending_update_secret@ == next_secret@);
            assert(self.pending_update_request == Some(request));
            assert(self.pending_update_is_response == is_response);
            assert(self.response_due == (if is_response { false } else { before.response_due }));
            assert(self@.mode == super::dispatcher_spec::Mode::Ready);
            assert(self@.application_sender is Some);
            assert(self@.application_receiver is Some);
            assert(match self@.auth { Some(auth) => auth.phase == crate::auth::spec::Phase::Ready, None => false });
            assert(self.client_application_secret@.len() == 32);
            assert(self.server_application_secret@.len() == 32);
            assert(self.pending_update_secret@.len() == 32);
            assert(self.pending_update_wire@.len() == wire@.len());
            assert(match self.pending_update_request { Some(r) => r <= 1, None => false });
            assert(self.pending_update_is_response ==> self.pending_update_request == Some(0));
            assert(self.pending_flight@.len() == 0);
            assert(!self.ccs_pending);
            assert(self.master@.len() == 0);
            assert(self.wf());
            assert(self@ == super::dispatcher_spec::prepare_key_update(self.crypto_functions(), ciphers,
                before, request, is_response));
        }
        Ok(wire)
    }

    /// Handle one complete post-handshake KeyUpdate body. The receive epoch
    /// changes immediately; a requested response is queued as KeyUpdate(0).
    fn receive_key_update(&mut self, request: u8) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
            old(self)@.mode == super::dispatcher_spec::Mode::Ready, request <= 1,
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_contract::receive_update_ensures(old(self).crypto_functions(),
                old(self).cipher_models(), old(self)@, request, out@, final(self)@)
                && match out@ {
                    super::dispatcher_spec::Action::Send(wire) => final(self)@.pending_update_wire == wire,
                    _ => true,
                },
    {
        let ghost before = self@;
        let ghost ciphers = self.cipher_models();
        if request > 1 { return self.fail(crate::spec::ILLEGAL_PARAMETER); }
        let next_secret = crate::schedule::exec::update_secret(&self.crypto, self.server_application_secret.as_slice());
        proof {
            assert(next_secret.len() == crate::schedule::spec::HASH_LEN);
            assert(next_secret@ == crate::schedule::spec::next_traffic_secret(self.crypto_functions(), self.server_application_secret@));
            reveal(crate::traffic::spec::start);
            assert(crate::traffic::spec::start(self.crypto_functions(), next_secret@) is Ok);
        }
        let receiver = match Decryptor::new(&self.crypto, &self.factory, next_secret.as_slice()) {
            Ok(receiver) => receiver,
            Err(alert) => return self.fail(alert),
        };
        let ghost receiver_view = receiver@;
        self.application_receiver = Some(receiver);
        self.server_application_secret = next_secret;
        if request == 1 { self.response_due = true; }
        proof {
            reveal(Connection::state);
            reveal(super::dispatcher_spec::receive_key_update);
            assert(next_secret@ == crate::schedule::spec::next_traffic_secret(self.crypto_functions(), before.server_application_secret));
            assert(self@.application_receiver == Some(receiver_view));
            assert(self@ == super::dispatcher_spec::receive_key_update(self.crypto_functions(), before, request));
        }
        if self.response_due && self.pending_update_request.is_none() {
            let out = match self.queue_key_update(0, true) {
                Ok(wire) => Action::Send(wire),
                Err(alert) => return self.fail(alert),
            };
            proof {
                reveal(super::dispatcher_spec::receive_key_update_and_respond);
                assert(self@ == super::dispatcher_spec::receive_key_update_and_respond(self.crypto_functions(), ciphers, before, request));
                match out@ {
                    super::dispatcher_spec::Action::Send(wire) => assert(self@.pending_update_wire == wire),
                    _ => assert(false),
                }
                assert(super::dispatcher_spec::action_refines(out@, self@));
            }
            out
        } else {
            proof {
                reveal(super::dispatcher_spec::receive_key_update_and_respond);
                assert(self@ == super::dispatcher_spec::receive_key_update_and_respond(self.crypto_functions(), ciphers, before, request));
            }
            Action::None
        }
    }

    /// Confirm the exact KeyUpdate record was sent before the send epoch
    /// changes. If a peer request arrived while it was pending, queue the
    /// required KeyUpdate(0) immediately after this acknowledgement.
    pub fn acknowledge_key_update(&mut self, sent: &[u8]) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
            super::dispatcher_contract::key_update_ack_ensures(old(self).crypto_functions(),
                old(self).cipher_models(), old(self)@, sent@, out@, final(self)@),
    {
        if !matches!(self.mode, Mode::Ready) || self.pending_update_request.is_none()
            || sent != self.pending_update_wire.as_slice() {
            return self.fail(crate::spec::INTERNAL_ERROR);
        }
        let ghost before = self@;
        proof {
            assert(sent@ =~= before.pending_update_wire);
            assert(sent@ == before.pending_update_wire);
            assert(before.pending_update_request is Some);
        }
        let ghost ciphers = self.cipher_models();
        let mut next_secret = Vec::new();
        next_secret.extend_from_slice(self.pending_update_secret.as_slice());
        self.pending_update_secret.clear();
        proof {
            assert(next_secret.len() == crate::schedule::spec::HASH_LEN);
            reveal(crate::traffic::spec::start);
            assert(crate::traffic::spec::start(self.crypto_functions(), next_secret@) is Ok);
        }
        let sender = match Encryptor::new(&self.crypto, &self.factory, next_secret.as_slice()) {
            Ok(sender) => sender,
            Err(alert) => return self.fail(alert),
        };
        let ghost sender_view = sender@;
        proof {
            reveal(crate::traffic::contract::start_ensures);
            reveal(crate::traffic::spec::start);
            assert(crate::traffic::contract::start_ensures(self.crypto_functions(), next_secret@, Ok(sender_view)));
            assert(crate::traffic::spec::start(self.crypto_functions(), next_secret@) == Ok(sender_view));
        }
        self.application_sender = Some(sender);
        self.client_application_secret = next_secret;
        self.pending_update_wire.clear();
        self.pending_update_request = None;
        self.pending_update_is_response = false;
        proof {
            reveal(Connection::state);
            reveal(super::dispatcher_spec::acknowledge_key_update);
            assert(next_secret@ == before.pending_update_secret);
            assert(self.pending_update_secret@ == seq![]);
            assert(self.pending_update_wire@ == seq![]);
            assert(self.pending_update_request is None);
            assert(!self.pending_update_is_response);
            assert(self.client_application_secret@ == before.pending_update_secret);
            assert(self.server_application_secret@ == before.server_application_secret);
            assert(self@.application_sender == Some(sender_view));
            assert(self@.application_receiver == before.application_receiver);
            assert(self@.auth == before.auth);
            assert(self@.handshake_sender == before.handshake_sender);
            assert(self@.handshake_receiver == before.handshake_receiver);
            assert(self@.master == before.master);
            assert(self@.client_application_secret == before.pending_update_secret);
            assert(self@.server_application_secret == before.server_application_secret);
            assert(self@.reassembly == before.reassembly);
            assert(self@.framing == before.framing);
            assert(self@.pending_flight == before.pending_flight);
            assert(self@.ccs_pending == before.ccs_pending);
            assert(self@.response_due == before.response_due);
            assert(self@ == super::dispatcher_spec::acknowledge_key_update(self.crypto_functions(), before, sent@));
        }
        let ghost acknowledged = self@;
        if self.response_due {
            let ghost queued_from = self@;
            let out = match self.queue_key_update(0, true) {
                Ok(wire) => Action::Send(wire),
                Err(alert) => {
                    proof {
                        reveal(super::dispatcher_spec::acknowledge_key_update_and_respond);
                        reveal(super::dispatcher_spec::prepare_key_update);
                        assert(acknowledged == super::dispatcher_spec::acknowledge_key_update(
                            self.crypto_functions(), before, sent@));
                        assert(queued_from == acknowledged);
                        assert(super::dispatcher_spec::prepare_key_update(
                            self.crypto_functions(), ciphers, acknowledged, 0, true) == super::dispatcher_spec::failed());
                        assert(super::dispatcher_spec::acknowledge_key_update_and_respond(
                            self.crypto_functions(), ciphers, before, sent@) == super::dispatcher_spec::failed());
                    }
                    let failed = self.fail(alert);
                    proof {
                        reveal(super::dispatcher_contract::key_update_ack_ensures);
                        assert(super::dispatcher_contract::terminal_ensures(self@, super::dispatcher_spec::Mode::Failed));
                        assert(failed@ is Fail);
                        assert(super::dispatcher_contract::key_update_ack_ensures(
                            old(self).crypto_functions(), old(self).cipher_models(), old(self)@,
                            sent@, failed@, self@));
                    }
                    return failed;
                },
            };
            proof {
                reveal(super::dispatcher_spec::acknowledge_key_update_and_respond);
                assert(self@ == super::dispatcher_spec::acknowledge_key_update_and_respond(
                    self.crypto_functions(), ciphers, before, sent@));
                match out@ {
                    super::dispatcher_spec::Action::Send(wire) => assert(self@.pending_update_wire == wire),
                    _ => assert(false),
                }
                assert(super::dispatcher_spec::action_refines(out@, self@));
            }
            out
        } else {
            proof {
                reveal(super::dispatcher_spec::acknowledge_key_update_and_respond);
                assert(self@ == super::dispatcher_spec::acknowledge_key_update_and_respond(
                    self.crypto_functions(), ciphers, before, sent@));
            }
            Action::None
        }
    }

    /// Ask the peer to update its send keys, or perform an unrequested local
    /// update. A new request waits while an earlier KeyUpdate is unacknowledged.
    pub fn request_key_update(&mut self, request_peer_update: bool) -> (out: Action)
        requires old(self).wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
    {
        if !matches!(self.mode, Mode::Ready) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
        if self.pending_update_request.is_some() { return Action::None; }
        if self.response_due {
            return match self.queue_key_update(0, true) {
                Ok(wire) => Action::Send(wire),
                Err(alert) => self.fail(alert),
            };
        }
        let request = if request_peer_update { 1 } else { 0 };
        match self.queue_key_update(request, false) {
            Ok(wire) => Action::Send(wire),
            Err(alert) => self.fail(alert),
        }
    }

    /// Protect application bytes only after both Finished conditions and the
    /// exact client-flight send acknowledgement.
    pub fn send_application(&mut self, plaintext: &[u8], padding: usize) -> (out: Action)
        requires old(self).wf(), old(self).auth_wf(), old(self).resources_wf(), old(self).cipher_bindings_wf(),
        ensures final(self).wf(), final(self).auth_wf(), final(self).resources_wf(), final(self).cipher_bindings_wf(),
    {
        if !matches!(self.mode, Mode::Ready) { return self.fail(crate::spec::UNEXPECTED_MESSAGE); }
        if self.pending_update_request.is_some() || self.response_due { return Action::None; }
        let sender = match self.application_sender.as_mut() {
            Some(sender) => sender,
            None => return self.fail(crate::spec::INTERNAL_ERROR),
        };
        match sender.seal(crate::spec::CT_APPLICATION_DATA, plaintext, padding) {
            Ok(wire) => Action::Send(wire),
            Err(alert) => self.fail(alert),
        }
    }

    /// EOF without a received close_notify is a local transport failure.
    pub fn eof(&mut self) -> (out: Action)
        requires old(self).wf(),
        ensures final(self).wf(),
    {
        if matches!(self.mode, Mode::Failed | Mode::Closed) { Action::None }
        else { self.fail(crate::spec::INTERNAL_ERROR) }
    }
}
} // verus!
