//! RFC 8446 §4.1, §5, §6 and §7.3: the joined client, written to meet
//! [`super::driver_contract`]. It holds no key of its own: each stage owns one
//! machine, and a machine that has handed over is gone.
use super::driver_contract as contract;
use super::driver_spec as spec;
use super::exec::{Action as ConnAction, Connection};
use super::post_handshake_exec::{End, Input, Out, PostHandshake};
use crate::auth::verify::Verifier;
use crate::hello::bootstrap::{Action as BootAction, Bootstrap};
use crate::hello::client::Config;
use crate::hello::key_exchange::KeyExchange;
use crate::schedule::crypto::Crypto;
use crate::traffic::provider::{Factory, KeyedAead};
use core::fmt;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Where a [`Failure`] came from ([`spec::Origin`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Origin {
    /// The client detected it, and the fatal alert is the last record sent:
    /// in plaintext before the handshake keys, protected from then on.
    Sent,
    /// The client detected it, and no alert could be sent.
    NotSent,
    /// The server sent this fatal alert. It is not answered.
    Peer,
    /// The transport closed before a close_notify (§6.1); nothing was sent.
    Truncated,
}
impl View for Origin {
    type V = spec::Origin;
    open spec fn view(&self) -> spec::Origin {
        match self {
            Origin::Sent => spec::Origin::Sent,
            Origin::NotSent => spec::Origin::NotSent,
            Origin::Peer => spec::Origin::Peer,
            Origin::Truncated => spec::Origin::Truncated,
        }
    }
}

/// A fatal end of the connection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Failure {
    /// The RFC 8446 §6.2 `AlertDescription`.
    pub alert: u8,
    /// Who raised it, and whether it went on the wire.
    pub origin: Origin,
}

/// Where the connection is ([`spec::Status`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// The handshake is running.
    Handshaking,
    /// The handshake completed: application data flows both ways.
    Open,
    /// Our close_notify has been sent; the server's has not arrived.
    /// Application data from the server is still delivered.
    Closing,
    /// Both close_notify alerts have been seen. Final.
    Closed,
    /// The connection failed. Final.
    Failed(Failure),
}
impl View for State {
    type V = spec::Status;
    open spec fn view(&self) -> spec::Status {
        match self {
            State::Handshaking => spec::Status::Handshaking,
            State::Open => spec::Status::Open,
            State::Closing => spec::Status::Closing,
            State::Closed => spec::Status::Closed,
            State::Failed(f) => spec::Status::Failed(f.alert, f.origin@),
        }
    }
}

/// What a call produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Output {
    /// Octets for the transport, in order.
    pub send: Vec<u8>,
    /// Plaintext from the server, in order.
    pub deliver: Vec<u8>,
    /// Where the connection is now.
    pub state: State,
}

/// The machine that is running.
enum Stage<C: Crypto, K: KeyExchange, F: Factory, V: Verifier> {
    /// Through the ServerHello, with what the next stage needs.
    Hello {
        boot: Bootstrap<C>,
        crypto: C,
        exchange: K,
        factory: F,
        verifier: V,
        scalar: Vec<u8>,
    },
    /// The server's protected flight.
    Flight { conn: Connection<C, F, V> },
    /// Application traffic.
    App { app: PostHandshake<C, F> },
}

/// One TLS 1.3 client connection over its providers, without its socket.
pub struct Driver<C: Crypto, K: KeyExchange, F: Factory, V: Verifier> {
    stage: Option<Stage<C, K, F, V>>,
    state: State,
    models: Ghost<contract::Models>,
}

/// §5.1, §6: [`spec::plaintext_alert`].
pub fn plaintext_alert(level: u8, description: u8) -> (out: Vec<u8>)
    ensures out@ == spec::plaintext_alert(level, description),
{
    let mut out: Vec<u8> = Vec::new();
    out.push(crate::spec::CT_ALERT);
    out.push(3u8);
    out.push(3u8);
    out.push(0u8);
    out.push(2u8);
    out.push(level);
    out.push(description);
    proof { assert(out@ =~= spec::plaintext_alert(level, description)); }
    out
}

/// The records of `wires`, one after the other ([`spec::concat`]).
fn concat(wires: &Vec<Vec<u8>>) -> (out: Vec<u8>)
    ensures out@ == spec::concat(crate::reassemble::views_bytes(wires@)),
{
    let ghost views = crate::reassemble::views_bytes(wires@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < wires.len()
        invariant
            i <= wires.len(),
            views == crate::reassemble::views_bytes(wires@),
            out@ == spec::concat(views.take(i as int)),
        decreases wires.len() - i,
    {
        let ghost before = out@;
        if let Some(wire) = wires.get(i) {
            out.extend_from_slice(wire.as_slice());
            proof {
                assert(views[i as int] == wire@);
                assert(views.take(i + 1).drop_last() =~= views.take(i as int));
                assert(views.take(i + 1).last() == wire@);
            }
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(views.len() == wires.len());
        assert(views.take(i as int) =~= views);
    }
    out
}

fn quiet(state: State) -> (out: Output)
    ensures out.send@.len() == 0, out.deliver@.len() == 0, out.state == state,
{
    Output { send: Vec::new(), deliver: Vec::new(), state }
}

impl<C: Crypto, K: KeyExchange, F: Factory, V: Verifier> Driver<C, K, F, V> where F::Cipher: KeyedAead {
    /// The running machine's abstract state.
    pub closed spec fn stage(&self) -> spec::Stage {
        match self.stage {
            None => spec::Stage::Ended,
            Some(Stage::Hello { boot, .. }) => spec::Stage::Hello(boot@.0, boot@.1),
            Some(Stage::Flight { conn }) => spec::Stage::Flight(conn@),
            Some(Stage::App { app }) => spec::Stage::App(app@),
        }
    }

    /// Our X25519 scalar, while the key exchange is ahead.
    pub closed spec fn scalar(&self) -> Seq<u8> {
        match self.stage {
            Some(Stage::Hello { scalar, .. }) => scalar@,
            _ => seq![],
        }
    }

    /// The providers this connection runs over.
    pub closed spec fn models(&self) -> contract::Models { self.models@ }

    /// Each machine is well formed, over this connection's providers.
    pub closed spec fn wf(&self) -> bool {
        match self.stage {
            None => spec::is_final(self.state@),
            Some(Stage::Hello { boot, crypto, exchange, factory, verifier, scalar }) => boot.wf()
                && self.state == State::Handshaking && scalar.len() == 32
                && boot.crypto_functions() == self.models@.crypto
                && crypto.functions() == self.models@.crypto
                && exchange.functions() == self.models@.exchange
                && factory.functions() == self.models@.cipher,
            Some(Stage::Flight { conn }) => conn.wf() && conn.auth_wf() && conn.resources_wf()
                && conn.cipher_bindings_wf() && self.state == State::Handshaking
                && conn.crypto_functions() == self.models@.crypto
                && conn.cipher_functions() == self.models@.cipher,
            Some(Stage::App { app }) => app.wf() && (self.state == State::Open || self.state == State::Closing)
                && app.crypto_functions() == self.models@.crypto
                && app.cipher_functions() == self.models@.cipher,
        }
    }

    /// Where the connection is.
    pub closed spec fn status(&self) -> State { self.state }

    /// Where the connection is.
    pub fn state(&self) -> (out: State)
        ensures out == self.status(),
    {
        self.state
    }

    /// Start a connection. `scalar` is our X25519 private key and `config`
    /// carries its public key. `crypto` is two providers of the same
    /// functions: `Bootstrap` keeps one and the dispatcher takes the other.
    pub fn connect(config: Config, scalar: Vec<u8>, hello_crypto: C, crypto: C, exchange: K, factory: F,
        verifier: V) -> (out: (Self, Output))
        requires scalar.len() == 32, hello_crypto.functions() == crypto.functions(),
        ensures out.0.wf(),
            out.0.models().crypto == crypto.functions(),
            out.0.models().exchange == exchange.functions(),
            out.0.models().cipher == factory.functions(),
    {
        let ghost models = contract::Models {
            crypto: crypto.functions(),
            exchange: exchange.functions(),
            cipher: factory.functions(),
        };
        match Bootstrap::start(config, hello_crypto) {
            Ok((mut boot, BootAction::Send(wire))) => {
                if matches!(boot.acknowledge_send(wire.as_slice()), BootAction::None) {
                    let state = State::Handshaking;
                    let driver = Driver {
                        stage: Some(Stage::Hello { boot, crypto, exchange, factory, verifier, scalar }),
                        state,
                        models: Ghost(models),
                    };
                    (driver, Output { send: wire, deliver: Vec::new(), state })
                } else {
                    Self::failed_at_start(crate::spec::INTERNAL_ERROR, Ghost(models))
                }
            },
            Ok(_) => Self::failed_at_start(crate::spec::INTERNAL_ERROR, Ghost(models)),
            Err(alert) => Self::failed_at_start(alert, Ghost(models)),
        }
    }

    fn failed_at_start(alert: u8, models: Ghost<contract::Models>) -> (out: (Self, Output))
        ensures out.0.wf(), out.0.models() == models@,
    {
        let state = State::Failed(Failure { alert, origin: Origin::NotSent });
        (Driver { stage: None, state, models }, quiet(state))
    }

    /// End the connection with this state and these octets.
    fn ended(&mut self, send: Vec<u8>, deliver: Vec<u8>, state: State) -> (out: Output)
        requires spec::is_final(state@),
        ensures final(self).wf(), final(self).models() == old(self).models(),
            final(self).stage() == spec::Stage::Ended,
            out.send == send, out.deliver == deliver, out.state == state, final(self).state == state,
    {
        self.stage = None;
        self.state = state;
        Output { send, deliver, state }
    }

    /// [`spec::settle`]: `prefix` is already sent and `deliver` delivered.
    fn settle(&mut self, prefix: Vec<u8>, deliver: Vec<u8>, o: Out, app: PostHandshake<C, F>) -> (out: Output)
        requires app.wf(), app.crypto_functions() == old(self).models().crypto,
            app.cipher_functions() == old(self).models().cipher,
        ensures final(self).wf(), final(self).models() == old(self).models(),
            contract_step(out, final(self)) == spec::settle(prefix@, deliver@, o@, app@),
    {
        let wires = concat(&o.wires);
        let mut send = prefix;
        let ghost first = send@;
        let mut rest = wires;
        let ghost second = rest@;
        send.append(&mut rest);
        proof { assert(send@ =~= first + second); }
        let ghost state_view = app@;
        match o.end {
            End::Continue => {
                let state = if matches!(app.phase(), super::post_handshake_exec::Phase::WriteClosed) {
                    State::Closing
                } else {
                    State::Open
                };
                self.stage = Some(Stage::App { app });
                self.state = state;
                Output { send, deliver, state }
            },
            End::Close => self.ended(send, deliver, State::Closed),
            End::Fail(alert) => {
                let origin = if send.len() > 0 { Origin::Sent } else { Origin::NotSent };
                self.ended(send, deliver, State::Failed(Failure { alert, origin }))
            },
            End::PeerAlert(alert) => {
                self.ended(send, deliver, State::Failed(Failure { alert, origin: Origin::Peer }))
            },
            End::PeerClosed => {
                self.ended(send, deliver, State::Failed(Failure { alert: crate::spec::INTERNAL_ERROR, origin: Origin::NotSent }))
            },
        }
    }

    /// [`spec::carry_out`].
    fn carry_out(&mut self, o: Out, mut app: PostHandshake<C, F>) -> (out: Output)
        requires app.wf(), app.crypto_functions() == old(self).models().crypto,
            app.cipher_functions() == old(self).models().cipher,
        ensures final(self).wf(), final(self).models() == old(self).models(),
            contract_step(out, final(self)) == spec::carry_out(old(self).models().cipher, o@, app@),
    {
        if matches!(o.end, End::PeerClosed) {
            let sent = concat(&o.wires);
            let second = app.close_out();
            self.settle(sent, o.delivered, second, app)
        } else {
            self.settle(Vec::new(), o.delivered, Out { wires: o.wires, delivered: Vec::new(), end: o.end }, app)
        }
    }

    /// A failure the dispatcher reported, after `prefix` ([`spec::flight_failure`]).
    fn flight_failed(&mut self, prefix: Vec<u8>, alert: u8, wire: Option<Vec<u8>>) -> (out: Output)
        ensures final(self).wf(), final(self).models() == old(self).models(),
            final(self).stage() == spec::Stage::Ended, spec::is_final(out.state@),
            out.deliver@.len() == 0,
    {
        let mut send = prefix;
        match wire {
            Some(mut record) => {
                send.append(&mut record);
                self.ended(send, Vec::new(), State::Failed(Failure { alert, origin: Origin::Sent }))
            },
            None => self.ended(send, Vec::new(), State::Failed(Failure { alert, origin: Origin::NotSent })),
        }
    }

    /// The client flight is on its way: acknowledge it, and hand over to the
    /// transducer at `Ready`.
    fn acknowledge(&mut self, mut conn: Connection<C, F, V>, wire: Vec<u8>) -> (out: Output)
        requires conn.wf(), conn.auth_wf(), conn.resources_wf(), conn.cipher_bindings_wf(),
            conn.crypto_functions() == old(self).models().crypto,
            conn.cipher_functions() == old(self).models().cipher,
        ensures final(self).wf(), final(self).models() == old(self).models(),
            out.deliver@.len() == 0,
            match final(self).stage() {
                spec::Stage::App(state) => contract::app_started(final(self).models(), state)
                    && out.state == State::Open,
                spec::Stage::Ended => spec::is_final(out.state@),
                _ => false,
            },
    {
        let ack = conn.acknowledge_client_flight(wire.as_slice());
        match ack {
            ConnAction::Ready => {
                let ghost ready = conn@;
                let ghost m = self.models();
                match conn.into_post_handshake() {
                    Ok(app) => {
                        let ghost state = app@;
                        proof {
                            assert(ready.mode == super::dispatcher_spec::Mode::Ready);
                            assert(super::dispatcher_contract::handoff_ensures(m.crypto, ready, Ok(state)));
                            assert(contract::app_started(m, state));
                        }
                        self.stage = Some(Stage::App { app });
                        self.state = State::Open;
                        Output { send: wire, deliver: Vec::new(), state: State::Open }
                    },
                    Err(alert) => self.ended(wire, Vec::new(), State::Failed(Failure { alert, origin: Origin::NotSent })),
                }
            },
            ConnAction::Fail(alert, record) => self.flight_failed(wire, alert, record),
            _ => self.ended(wire, Vec::new(), State::Failed(Failure { alert: crate::spec::INTERNAL_ERROR, origin: Origin::NotSent })),
        }
    }

    /// One step of the server's flight.
    fn flight_step(&mut self, mut conn: Connection<C, F, V>, input: &[u8]) -> (out: (usize, Output))
        requires conn.wf(), conn.auth_wf(), conn.resources_wf(), conn.cipher_bindings_wf(),
            conn.crypto_functions() == old(self).models().crypto,
            conn.cipher_functions() == old(self).models().cipher,
        ensures final(self).wf(), final(self).models() == old(self).models(),
            out.0 <= input.len(), out.1.deliver@.len() == 0,
            contract::flight_step_ensures(old(self).models(), conn@, input@, out.0 as nat,
                contract_step(out.1, final(self))),
    {
        let ghost before = conn@;
        let (consumed, action) = conn.feed(input);
        let out = match action {
            ConnAction::None | ConnAction::Ignored | ConnAction::Cancelled => {
                self.stage = Some(Stage::Flight { conn });
                self.state = State::Handshaking;
                quiet(State::Handshaking)
            },
            ConnAction::Send(wire) => self.acknowledge(conn, wire),
            ConnAction::Ready => self.ended(Vec::new(), Vec::new(),
                State::Failed(Failure { alert: crate::spec::INTERNAL_ERROR, origin: Origin::NotSent })),
            ConnAction::Fail(alert, record) => self.flight_failed(Vec::new(), alert, record),
            ConnAction::PeerAlert(alert) => self.ended(Vec::new(), Vec::new(),
                State::Failed(Failure { alert, origin: Origin::Peer })),
            ConnAction::Close => self.ended(Vec::new(), Vec::new(), State::Closed),
        };
        (consumed, out)
    }

    /// A local failure before the handshake keys ([`spec::hello_failure`]).
    fn hello_failed(&mut self, alert: u8) -> (out: Output)
        ensures final(self).wf(), final(self).models() == old(self).models(),
            contract_step(out, final(self)) == spec::hello_failure(alert),
    {
        let send = plaintext_alert(crate::spec::LEVEL_FATAL, alert);
        let deliver = Vec::new();
        proof { assert(deliver@ =~= seq![]); }
        self.ended(send, deliver, State::Failed(Failure { alert, origin: Origin::Sent }))
    }

    /// §7.1, §7.3: the key exchange and the handshake epochs, then the dispatcher.
    fn establish(&mut self, established: crate::hello::client::Established, crypto: C, exchange: K, factory: F,
        verifier: V, scalar: Vec<u8>) -> (out: Output)
        requires established.wf(), scalar.len() == 32,
            crypto.functions() == old(self).models().crypto,
            exchange.functions() == old(self).models().exchange,
            factory.functions() == old(self).models().cipher,
        ensures final(self).wf(), final(self).models() == old(self).models(),
            out.deliver@.len() == 0,
            match final(self).stage() {
                spec::Stage::Flight(state) => contract::flight_started(old(self).models(),
                    crate::hello::bootstrap_spec::Action::Established(established@.0, established@.1, established@.2),
                    scalar@, state) && out.send@.len() == 0 && out.state == State::Handshaking,
                spec::Stage::Ended => true,
                _ => false,
            },
    {
        let ghost e = established@;
        let ghost m = self.models();
        match established.into_record_auth(&crypto, &exchange, &factory, scalar.as_slice()) {
            Ok(keys) => {
                proof {
                    let seal = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| keys.seal_spec(n, ad, p);
                    let open = |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| keys.open_spec(n, ad, ct);
                    assert(crate::traffic::handshake_contract::cipher_bound(factory.functions(), keys@, seal, open));
                    assert forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] keys.seal_spec(n, ad, p)
                        == (factory.functions().seal)(keys@.1.key, n, ad, p) by {
                        assert(seal(n, ad, p) == (factory.functions().seal)(keys@.1.key, n, ad, p));
                    }
                    assert forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] keys.open_spec(n, ad, ct)
                        == (factory.functions().open)(keys@.2.key, n, ad, ct) by {
                        assert(open(n, ad, ct) == (factory.functions().open)(keys@.2.key, n, ad, ct));
                    }
                }
                let conn = Connection::new(keys, crypto, factory, verifier);
                self.stage = Some(Stage::Flight { conn });
                self.state = State::Handshaking;
                quiet(State::Handshaking)
            },
            Err(alert) => self.hello_failed(alert),
        }
    }

    /// One step through the ServerHello.
    fn hello_step(&mut self, mut boot: Bootstrap<C>, crypto: C, exchange: K, factory: F, verifier: V,
        scalar: Vec<u8>, input: &[u8]) -> (out: (usize, Output))
        requires boot.wf(), scalar.len() == 32,
            boot.crypto_functions() == old(self).models().crypto,
            crypto.functions() == old(self).models().crypto,
            exchange.functions() == old(self).models().exchange,
            factory.functions() == old(self).models().cipher,
        ensures final(self).wf(), final(self).models() == old(self).models(),
            out.0 <= input.len(), out.1.deliver@.len() == 0,
            contract::hello_step_ensures(old(self).models(), boot@.0, boot@.1, scalar@, input@, out.0 as nat,
                contract_step(out.1, final(self))),
    {
        hide(crate::hello::bootstrap_spec::feed);
        let (consumed, action) = boot.feed(input);
        let out = match action {
            BootAction::None => {
                self.stage = Some(Stage::Hello { boot, crypto, exchange, factory, verifier, scalar });
                self.state = State::Handshaking;
                quiet(State::Handshaking)
            },
            // A HelloRetryRequest: ClientHello2, with the dummy
            // change_cipher_spec before it when required (D.4).
            BootAction::Send(wire) => {
                if matches!(boot.acknowledge_send(wire.as_slice()), BootAction::None) {
                    self.stage = Some(Stage::Hello { boot, crypto, exchange, factory, verifier, scalar });
                    self.state = State::Handshaking;
                    Output { send: wire, deliver: Vec::new(), state: State::Handshaking }
                } else {
                    self.hello_failed(crate::spec::INTERNAL_ERROR)
                }
            },
            BootAction::Established(established) => self.establish(established, crypto, exchange, factory, verifier, scalar),
            BootAction::Alert(alert) => self.ended(Vec::new(), Vec::new(),
                State::Failed(Failure { alert, origin: Origin::Peer })),
            BootAction::Fail(alert) => self.hello_failed(alert),
            // §6.1: answer close_notify with ours.
            BootAction::Close => self.ended(plaintext_alert(crate::spec::LEVEL_WARNING, crate::spec::CLOSE_NOTIFY),
                Vec::new(), State::Closed),
        };
        (consumed, out)
    }

    /// Run the current machine on the input, up to one record. Returns the
    /// octets consumed; the caller resubmits the rest.
    pub fn step(&mut self, input: &[u8]) -> (out: (usize, Output))
        requires old(self).wf(),
        ensures final(self).wf(), final(self).models() == old(self).models(), out.0 <= input.len(),
            contract::step_ensures(old(self).models(), old(self).stage(), old(self).scalar(), input@,
                out.0 as nat, contract_step(out.1, final(self))),
    {
        match self.stage.take() {
            None => (0, quiet(self.state)),
            Some(Stage::App { mut app }) => {
                let (consumed, o) = app.step_out(Input::Bytes(input));
                (consumed, self.carry_out(o, app))
            },
            Some(Stage::Flight { conn }) => self.flight_step(conn, input),
            Some(Stage::Hello { boot, crypto, exchange, factory, verifier, scalar }) => {
                self.hello_step(boot, crypto, exchange, factory, verifier, scalar, input)
            },
        }
    }

    /// Protect up to one record of application data.
    pub fn send(&mut self, data: &[u8]) -> (out: Output)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).models() == old(self).models(),
            contract::send_ensures(old(self).models(), old(self).stage(), data@, contract_step(out, final(self))),
    {
        match self.stage.take() {
            Some(Stage::App { mut app }) => {
                let o = app.send_application_out(data);
                self.carry_out(o, app)
            },
            other => {
                self.stage = other;
                quiet(self.state)
            },
        }
    }

    /// §6.1: close from our side.
    pub fn close(&mut self) -> (out: Output)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).models() == old(self).models(),
            contract::close_ensures(old(self).models(), old(self).stage(), contract_step(out, final(self))),
    {
        match self.stage.take() {
            None => quiet(self.state),
            Some(Stage::App { mut app }) => {
                let o = app.close_out();
                self.carry_out(o, app)
            },
            Some(Stage::Flight { .. }) => self.ended(Vec::new(), Vec::new(), State::Closed),
            Some(Stage::Hello { .. }) => self.ended(plaintext_alert(crate::spec::LEVEL_WARNING, crate::spec::CLOSE_NOTIFY),
                Vec::new(), State::Closed),
        }
    }

    /// §6.1: the transport ended. Before a close_notify that is a truncation.
    pub fn eof(&mut self) -> (out: Output)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).models() == old(self).models(),
            final(self).stage() == spec::Stage::Ended, spec::is_final(out.state@),
            out.send@.len() == 0, out.deliver@.len() == 0,
    {
        let alert = match self.stage.take() {
            None => return quiet(self.state),
            Some(Stage::App { mut app }) => {
                let (_, o) = app.step_out(Input::Closed);
                match o.end {
                    End::Fail(alert) => alert,
                    _ => crate::spec::INTERNAL_ERROR,
                }
            },
            Some(Stage::Flight { mut conn }) => match conn.eof() {
                ConnAction::Fail(alert, _) => alert,
                _ => crate::spec::INTERNAL_ERROR,
            },
            Some(Stage::Hello { mut boot, .. }) => match boot.eof() {
                BootAction::Fail(alert) => alert,
                _ => crate::spec::INTERNAL_ERROR,
            },
        };
        self.ended(Vec::new(), Vec::new(), State::Failed(Failure { alert, origin: Origin::Truncated }))
    }
}

/// The step an [`Output`] and the machine after it amount to.
pub open spec fn contract_step<C: Crypto, K: KeyExchange, F: Factory, V: Verifier>(out: Output,
    after: &Driver<C, K, F, V>) -> spec::Step where F::Cipher: KeyedAead
{
    spec::Step { send: out.send@, deliver: out.deliver@, stage: after.stage(), status: out.state@ }
}
} // verus!

impl State {
    /// `Closed` or `Failed`: nothing more will be sent or delivered.
    pub fn is_final(self) -> bool {
        matches!(self, State::Closed | State::Failed(_))
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = alert_name(self.alert).unwrap_or("unknown alert");
        match self.origin {
            Origin::Sent => write!(f, "{name} ({}), sent to the server", self.alert),
            Origin::NotSent => write!(f, "{name} ({}), not sent", self.alert),
            Origin::Peer => write!(f, "{name} ({}), from the server", self.alert),
            Origin::Truncated => write!(f, "connection closed without close_notify"),
        }
    }
}

/// RFC 8446 §6.2: the name of an `AlertDescription`.
pub fn alert_name(description: u8) -> Option<&'static str> {
    Some(match description {
        0 => "close_notify",
        10 => "unexpected_message",
        20 => "bad_record_mac",
        22 => "record_overflow",
        40 => "handshake_failure",
        42 => "bad_certificate",
        43 => "unsupported_certificate",
        44 => "certificate_revoked",
        45 => "certificate_expired",
        46 => "certificate_unknown",
        47 => "illegal_parameter",
        48 => "unknown_ca",
        49 => "access_denied",
        50 => "decode_error",
        51 => "decrypt_error",
        70 => "protocol_version",
        71 => "insufficient_security",
        80 => "internal_error",
        86 => "inappropriate_fallback",
        90 => "user_canceled",
        109 => "missing_extension",
        110 => "unsupported_extension",
        112 => "unrecognized_name",
        113 => "bad_certificate_status_response",
        115 => "unknown_psk_identity",
        116 => "certificate_required",
        120 => "no_application_protocol",
        _ => return None,
    })
}
