//! RFC 8446 §4.1.2/§4.1.4 ClientHello generation and owned retry progression.
use crate::schedule::crypto::Crypto;
use crate::transcript::exec::Transcript;
use crate::transcript::spec::Kind;
use crate::types::{ClientHello, Extension};
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Captured target, entropy and public X25519 input for the fixed client profile.
pub struct Config {
    /// The typed target host: server_name (DNS only) and later certificate validation.
    pub host: crate::host::exec::Host,
    /// Captured validity-check time.
    pub now: u64,
    /// Fresh 32-byte ClientHello random from the future entropy join.
    pub random: Vec<u8>,
    /// At most 32 bytes; nonempty requests middlebox compatibility.
    pub session_id: Vec<u8>,
    /// Raw 32-byte X25519 public input, checked against the scalar at the join.
    pub public_key: Vec<u8>,
}
impl View for Config {
    type V = super::client_spec::Config;
    open spec fn view(&self) -> super::client_spec::Config {
        super::client_spec::Config { host: self.host@, now: self.now, random: self.random@,
            session_id: self.session_id@, public_key: self.public_key@ }
    }
}
/// Exact scheme list offered for CV and certificate signatures (§4.2.3).
pub fn signatures() -> (out: Vec<u16>)
    ensures out@ == super::client_spec::signatures(),
{
    let out = vec![0x0403u16, 0x0804u16, 0x0805u16, 0x0806u16, 0x0807u16,
        0x0401u16, 0x0501u16, 0x0601u16];
    proof { assert(out@ =~= super::client_spec::signatures()); }
    out
}
/// Fixed profile's actual initial extension types, matching the body builder.
pub fn extension_types(config: &Config) -> (out: Vec<u16>)
    ensures out@ == (if crate::host::spec::sni_host_name(config.host@) is Some { seq![0u16] } else { seq![] })
        + seq![43u16, 13u16, 10u16, 51u16],
{
    let mut out = Vec::new();
    if config.host.sni_host_name().is_some() { out.push(0); }
    out.push(43); out.push(13); out.push(10); out.push(51);
    proof {
        assert(out@ =~= (if crate::host::spec::sni_host_name(config.host@) is Some { seq![0u16] } else { seq![] })
            + seq![43u16, 13u16, 10u16, 51u16]);
    }
    out
}
/// RFC 6066 §3: one DNS server_name, the host's DNS name.
fn server_name(host: &[u8]) -> (out: Vec<u8>)
    requires 1 <= host.len() <= 253,
    ensures out@ == crate::spec::write_server_name_ch(seq![crate::spec::ServerName { host_name: host@ }]),
{
    proof { reveal_with_fuel(crate::spec::write_list, 4); }
    let mut name = vec![0u8];
    crate::writer::push_vec(&mut name, host, 65535);
    proof { super::client_lemmas::lemma_vec_len(host@, 65535); }
    let mut out = Vec::new();
    crate::writer::push_vec(&mut out, name.as_slice(), 65535);
    proof { assert(out@ =~= crate::spec::write_server_name_ch(seq![crate::spec::ServerName { host_name: host@ }])); }
    out
}
/// §4.2.8: exactly one initial X25519 share.
fn key_share(key: &[u8]) -> (out: Vec<u8>)
    requires key.len() == 32,
    ensures out@ == crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: key@ }]),
{
    proof { reveal_with_fuel(crate::spec::write_list, 4); }
    let mut entry = Vec::new();
    crate::writer::push_u16(&mut entry, 29);
    crate::writer::push_vec(&mut entry, key, 65535);
    proof { super::client_lemmas::lemma_vec_len(key@, 65535); crate::lemmas_pl::lemma_be_bytes_len(29, 2); }
    let mut out = Vec::new();
    crate::writer::push_vec(&mut out, entry.as_slice(), 65535);
    proof { assert(out@ =~= crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: key@ }])); }
    out
}
/// §4.1.2: encode the fixed profile and optional exact HRR cookie extension_data.
fn build(config: &Config, cookie: &[u8]) -> (out: Vec<u8>)
    requires super::client_contract::build_requires(config@, cookie@),
    ensures super::client_contract::build_ensures(config@, cookie@, out@),
{
    let sni = config.host.sni_host_name();
    let name = match sni { Some(host) => server_name(host), None => Vec::new() };
    let share = key_share(config.public_key.as_slice());
    let schemes = signatures();
    let mut sig_data = Vec::new();
    let mut sig_list = Vec::new();
    crate::encode::push_u16s(&mut sig_list, schemes.as_slice());
    proof { crate::lemmas_pl::lemma_write_u16s_len(schemes@); }
    crate::writer::push_vec(&mut sig_data, sig_list.as_slice(), 65534);
    let versions: &[u8] = &[2u8, 3u8, 4u8];
    let groups: &[u8] = &[0u8, 2u8, 0u8, 29u8];
    let mut es = Vec::new();
    if sni.is_some() { es.push(Extension { etype: 0, data: name.as_slice() }); }
    es.push(Extension { etype: 43, data: versions });
    es.push(Extension { etype: 13, data: sig_data.as_slice() });
    es.push(Extension { etype: 10, data: groups });
    es.push(Extension { etype: 51, data: share.as_slice() });
    if !cookie.is_empty() { es.push(Extension { etype: 44, data: cookie }); }
    let ch = ClientHello { legacy_version: 0x0303, random: config.random.as_slice(),
        session_id: config.session_id.as_slice(), cipher_suites: vec![0x1303u16],
        compression: &[0u8], extensions: es };
    proof {
        assert(sig_data@ =~= crate::spec::write_signature_schemes(super::client_spec::signatures()));
        assert(versions@ =~= seq![2u8, 3u8, 4u8]);
        assert(groups@ =~= seq![0u8, 2u8, 0u8, 29u8]);
        assert(crate::types::views(ch.extensions@) =~= super::client_spec::extensions(config@, cookie@));
        assert(ch.cipher_suites@ =~= seq![0x1303u16]);
        assert(ch.compression@ =~= seq![0u8]);
        assert(ch@ == super::client_spec::client_hello(config@, cookie@));
        super::client_lemmas::lemma_profile(config@, cookie@);
    }
    let mut out = Vec::new();
    crate::encode::write_client_hello(&mut out, &ch);
    proof { assert(out@ =~= super::client_spec::body(config@, cookie@)); }
    out
}
/// Pending owned Hello exchange; no Clone or recovery after consuming failure.
pub struct Hello {
    config: Config,
    transcript: Transcript,
}
impl View for Hello {
    type V = super::client_spec::State;
    closed spec fn view(&self) -> super::client_spec::State {
        super::client_spec::State { config: self.config@, transcript: self.transcript@ }
    }
}
/// Negotiated inputs to the key-exchange/authentication join.
pub struct Established {
    config: Config,
    transcript: Transcript,
    peer_key: Vec<u8>,
}
impl View for Established {
    type V = (super::client_spec::Config, crate::transcript::spec::State, Seq<u8>);
    closed spec fn view(&self) -> Self::V { (self.config@, self.transcript@, self.peer_key@) }
}
/// One retry flight or completed Hello negotiation (not peer authentication).
pub enum Outcome {
    /// Send this exact CH2 handshake encoding before receiving the next Hello.
    Retry(Hello, Vec<u8>),
    /// Server parameters and transcript ready for key agreement.
    Established(Established),
}
/// View of a consuming server-Hello result.
pub open spec fn outcome_view(out: Result<Outcome, u8>) -> Result<super::client_spec::Outcome, u8> {
    match out {
        Err(e) => Err(e),
        Ok(Outcome::Retry(h, b)) => Ok(super::client_spec::Outcome::Retry(h@, b@)),
        Ok(Outcome::Established(e)) => Ok(super::client_spec::Outcome::Established(e@.0, e@.1, e@.2)),
    }
}
/// View of construction and its exact first flight.
pub open spec fn start_view(out: Result<(Hello, Vec<u8>), u8>) -> Result<(super::client_spec::State, Seq<u8>), u8> {
    match out { Err(e) => Err(e), Ok((h, b)) => Ok((h@, b@)) }
}
impl Established {
    /// Preconditions established by successful Hello receive, before key agreement.
    pub open spec fn wf(&self) -> bool { super::join_contract::established_wf(self@.0, self@.1, self@.2) }

    /// RFC 8446 §7.3: start authentication with client-send/server-receive epochs.
    /// The caller still supplies the connection driver and production providers.
    pub fn into_record_auth<C: Crypto, K: super::key_exchange::KeyExchange, F: crate::traffic::provider::Factory>(self,
        crypto: &C, exchange: &K, factory: &F, private_key: &[u8]) -> (out: Result<crate::traffic::handshake::HandshakeKeys<F::Cipher>, u8>)
        requires self.wf(),
        ensures crate::traffic::handshake_contract::start_ensures(crypto.functions(), exchange.functions(),
            self@.0, self@.1, self@.2, private_key@, crate::traffic::handshake::result_view(out)),
            match out { Ok(h) => h.wf()
                && h.ccs_pending_spec() == crate::traffic::handshake_spec::needs_ccs(self@.0, self@.1)
                && crate::traffic::handshake_contract::cipher_bound(factory.functions(), h@,
                    |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| h.seal_spec(n, ad, p),
                    |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| h.open_spec(n, ad, ct)), Err(_) => true },
    {
        crate::traffic::handshake::start(self.config, self.transcript, self.peer_key, crypto, exchange, factory, private_key)
    }

    /// RFC 8446 §7.1/§7.4.2: bind the caller's private scalar to the share sent,
    /// derive secrets and start (not finish) peer authentication.
    pub fn into_auth<C: Crypto, K: super::key_exchange::KeyExchange>(self, crypto: &C,
        exchange: &K, private_key: &[u8]) -> (out: Result<(crate::auth::exec::Auth, Vec<u8>), u8>)
        requires self.wf(),
        ensures super::join_contract::into_auth_ensures(crypto.functions(), exchange.functions(),
            self@.0, self@.1, self@.2, private_key@, super::join::result_view(out)),
    {
        super::join::into_auth(self.config, self.transcript, self.peer_key, crypto, exchange, private_key)
    }

    /// Consume the handoff; the transcript includes the accepted final ServerHello.
    pub fn into_parts(self) -> (out: (Config, Transcript, Vec<u8>))
        ensures out.0@ == self@.0, out.1@ == self@.1, out.2@ == self@.2,
    { (self.config, self.transcript, self.peer_key) }
}
impl Hello {
    /// Invariant established by start and each accepted retry.
    pub open spec fn wf(&self) -> bool { super::client_spec::wf(self@) }
    /// §4.1.2/§4.4.1: retain exactly the ClientHello whose encoding is returned.
    pub fn start(config: Config) -> (out: Result<(Self, Vec<u8>), u8>)
        ensures super::client_contract::start_ensures(config@, start_view(out)),
    {
        if !config.host.is_ok() || config.random.len() != 32
            || config.session_id.len() > 32 || config.public_key.len() != 32 { return Err(80); }
        let b = build(&config, &[]);
        let transcript = match Transcript::new(b.as_slice()) { Ok(t) => t, Err(_) => return Err(80) };
        let mut flight = Vec::new();
        crate::encode::write_handshake(&mut flight, 1, b.as_slice());
        Ok((Hello { config, transcript }, flight))
    }
    /// §4.1.4: record a validated cookie-only HRR and the generated CH2.
    fn retry<C: Crypto>(self, crypto: &C, server: &[u8], cookie: &[u8]) -> (out: Result<Outcome, u8>)
        requires self.wf(),
        ensures outcome_view(out) == super::client_spec::retry(crypto.functions().hash, self@, server@, cookie@),
            match out { Ok(Outcome::Retry(h, _)) => h.wf(), _ => true },
    {
        if cookie.len() > super::client_spec::MAX_COOKIE { return Err(80); }
        if !cookie.is_empty() && crate::extension::cookie(cookie).is_none() { return Err(80); }
        let config = self.config;
        let mut transcript = self.transcript;
        if transcript.push(crypto, Kind::HelloRetryRequest, server).is_err() { return Err(80); }
        let b = build(&config, cookie);
        if transcript.push(crypto, Kind::ClientHello, b.as_slice()).is_err() { return Err(80); }
        let mut flight = Vec::new();
        crate::encode::write_handshake(&mut flight, 1, b.as_slice());
        Ok(Outcome::Retry(Hello {config, transcript}, flight))
    }
    /// §4.1.3: retain the accepted final ServerHello before handing over.
    fn established<C: Crypto>(self, crypto: &C, server: &[u8], key: &[u8]) -> (out: Result<Outcome, u8>)
        requires self.wf(),
        ensures outcome_view(out) == super::client_spec::established(crypto.functions().hash, self@, server@, key@),
    {
        let config = self.config;
        let mut transcript = self.transcript;
        if transcript.push(crypto, Kind::ServerHello, server).is_err() { return Err(80); }
        let mut peer_key = Vec::new(); peer_key.extend_from_slice(key);
        proof { assert(peer_key@ =~= key@); }
        Ok(Outcome::Established(Established { config, transcript, peer_key }))
    }
    /// §4.1.3/§4.1.4: consume a pending exchange, using its retained session/retry state.
    /// The driver must send the previous returned flight before this call.
    pub fn receive<C: Crypto>(self, crypto: &C, server: &[u8]) -> (out: Result<Outcome, u8>)
        requires self.wf(),
        ensures super::client_contract::receive_ensures(crypto.functions().hash, self@, server@, outcome_view(out)),
    {
        let selected = super::exec::validate(self.config.session_id.as_slice(), self.transcript.retried(), server);
        match selected {
            Err(alert) => Err(alert),
            Ok(super::exec::Selection::Share(key)) => self.established(crypto, server, key),
            Ok(super::exec::Selection::Retry(cookie)) => self.retry(crypto, server, cookie),
        }
    }
}
} // verus!
