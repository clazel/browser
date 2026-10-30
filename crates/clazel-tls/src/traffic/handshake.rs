//! RFC 8446 §7.1/§7.3: install Hello's handshake secrets in the correct directions.
use super::exec::{Decryptor, Encryptor};
use super::provider::{Factory, KeyedAead};
use crate::auth::exec::Auth;
use crate::hello::client::Config;
use crate::hello::key_exchange::KeyExchange;
use crate::schedule::crypto::Crypto;
use crate::transcript::exec::Transcript;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Initial handshake record keys and authentication state; not a connection driver.
pub struct HandshakeKeys<A: KeyedAead> {
    auth: Auth,
    sender: Encryptor<A>,
    receiver: Decryptor<A>,
    master: Vec<u8>,
    ccs_pending: bool,
}
impl<A: KeyedAead> View for HandshakeKeys<A> {
    type V = super::handshake_spec::Handoff;
    closed spec fn view(&self) -> Self::V { (self.auth@, self.sender@, self.receiver@, self.master@) }
}
/// View of installed handshake state, including both independent record counters.
pub open spec fn result_view<A: KeyedAead>(out: Result<HandshakeKeys<A>, u8>) -> Result<super::handshake_spec::Handoff, u8> {
    match out { Err(e) => Err(e), Ok(h) => Ok(h@) }
}
impl<A: KeyedAead> HandshakeKeys<A> {
    /// Authentication and both fixed-profile record epochs are well formed.
    pub closed spec fn wf(&self) -> bool {
        self.auth.wf() && self.sender.wf() && self.receiver.wf() && self.master.len() == 32
    }
    /// Cipher function for client handshake records, retaining its installed key.
    pub closed spec fn seal_spec(&self, n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>) -> Seq<u8> { self.sender.seal_spec(n, ad, p) }
    /// Cipher function for server handshake records, retaining its installed key.
    pub closed spec fn open_spec(&self, n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>) -> Option<Seq<u8>> { self.receiver.open_spec(n, ad, ct) }
    /// Compatibility metadata captured from the actual Hello exchange.
    pub closed spec fn ccs_pending_spec(&self) -> bool { self.ccs_pending }
    /// Whether the post-Hello client flight needs a preceding dummy CCS.
    pub fn needs_compatibility_ccs(&self) -> (out: bool) ensures out == self.ccs_pending_spec() { self.ccs_pending }
    /// Consume the handoff for the future record driver. It must preserve Auth's
    /// delivery gate, message boundaries, send ordering and key-phase transitions.
    pub fn into_parts(self) -> (out: (Auth, Encryptor<A>, Decryptor<A>, Vec<u8>))
        requires self.wf(),
        ensures out.0@ == self@.0, out.1@ == self@.1, out.2@ == self@.2, out.3@ == self@.3,
            out.0.wf(), out.1.wf(), out.2.wf(), out.3.len() == 32,
            super::contract::seal_preserved(|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| self.seal_spec(n, ad, p),
                |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| out.1.seal_spec(n, ad, p)),
            super::contract::open_preserved(|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| self.open_spec(n, ad, ct),
                |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| out.2.open_spec(n, ad, ct)),
            forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] out.1.seal_spec(n, ad, p) == self.seal_spec(n, ad, p),
            forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] out.2.open_spec(n, ad, ct) == self.open_spec(n, ad, ct),
    { (self.auth, self.sender, self.receiver, self.master) }
}
/// RFC 8446 §7.3: client_handshake_traffic_secret encrypts; server's decrypts.
pub fn start<C: Crypto, K: KeyExchange, F: Factory>(config: Config, transcript: Transcript,
    peer_key: Vec<u8>, crypto: &C, exchange: &K, factory: &F, private_key: &[u8]) -> (out: Result<HandshakeKeys<F::Cipher>, u8>)
    requires crate::hello::join_contract::established_wf(config@, transcript@, peer_key@),
    ensures super::handshake_contract::start_ensures(crypto.functions(), exchange.functions(),
        config@, transcript@, peer_key@, private_key@, result_view(out)),
        match out { Err(_) => true, Ok(h) => h.wf()
            && h.ccs_pending_spec() == super::handshake_spec::needs_ccs(config@, transcript@)
            && (forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] h.seal_spec(n, ad, p) == (factory.functions().seal)(h@.1.key, n, ad, p))
            && (forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] h.open_spec(n, ad, ct) == (factory.functions().open)(h@.2.key, n, ad, ct)) },
{
    let ccs_pending = !config.session_id.is_empty() && !transcript.retried();
    let (auth_config, master) = crate::hello::join::derive(config, &transcript, peer_key, crypto, exchange, private_key)?;
    let sender = Encryptor::new(crypto, factory, auth_config.client_secret.as_slice())?;
    let receiver = Decryptor::new(crypto, factory, auth_config.server_secret.as_slice())?;
    match Auth::start(auth_config, transcript) {
        Err(e) => Err(e), Ok(auth) => Ok(HandshakeKeys { auth, sender, receiver, master, ccs_pending }),
    }
}
} // verus!
