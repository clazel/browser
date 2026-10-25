//! RFC 8446 (August 2018) §5.2–§5.5 and §7.3: one protected traffic-key epoch.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-5.3>.
//!
//! Modelling choices:
//! - ChaCha20-Poly1305 profile: 32-byte key, 12-byte IV, 16-byte tag.
//!   Crypto and keyed AEAD construction are parameters, not implementations.
//! - Separate sender/receiver objects own separate counters. Each starts at
//!   zero for its supplied traffic secret, uses u64::MAX at most once, and
//!   refuses another record instead of wrapping. No in-place reset/rekey API.
//! - The caller must install each distinct direction/epoch's actual secret;
//!   making a second object with the same secret is outside this module's
//!   per-object counter guarantee. KeyUpdate and phase changes are a later join.
//! - Outbound callers fragment content into at most 2^14-byte records.
//!   Padding is checked against the existing TLSCiphertext bound.
//! - Inbound input starts at a record boundary; return the consumed count
//!   so the driver can retain any suffix. NeedMore retains all epoch state.
//! - A complete record's framing, MAC or inner-plaintext failure kills this
//!   epoch. Subsequent operations return local internal_error without AEAD.
//!   The connection driver must propagate this failure to the other direction
//!   and authentication state, send any fatal alert once, and drop the keys.
//! - Compatibility CCS is unprotected and handled by the future connection
//!   driver; this protected epoch rejects it without consuming a nonce.
//! - Decrypted record content is not authenticated application delivery:
//!   handshake reassembly, alert dispatch and the Auth gate remain above it.
//! - No secret-erasure/timing guarantee. RFC §5.3's nonce steps are implemented
//!   by the existing record module; prose elsewhere has no numbered steps.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Keyed AEAD encryption parameter.
pub type Seal = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>;
/// Keyed AEAD authentication/decryption parameter.
pub type Open = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>;
/// Key-explicit functions supplied by the cipher factory.
pub struct Cipher {
    /// key, nonce, additional data, inner plaintext.
    pub seal: Seal,
    /// key, nonce, additional data, ciphertext.
    pub open: Open,
}
/// Metadata for one direction and one immutable installed key.
pub struct State {
    /// Key derived from exactly the supplied traffic secret.
    pub key: Seq<u8>,
    /// Static IV derived with the distinct "iv" label.
    pub iv: Seq<u8>,
    /// Next unused sequence number; None means exhausted, never zero again.
    pub next: Option<u64>,
    /// Fatal state; no further cipher calls or content output.
    pub failed: bool,
}
/// Fixed profile's key/nonce sizes.
pub open spec fn wf(s: State) -> bool { s.key.len() == 32 && s.iv.len() == 12 }
/// §7.3: key and IV use separate labels and empty (not hashed-empty) context.
pub open spec fn start(c: crate::schedule::spec::Crypto, secret: Seq<u8>) -> Result<State, u8> {
    if secret.len() != 32 { Err(80) }
    else { Ok(State {
        key: crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Key, seq![], 32),
        iv: crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Iv, seq![], 12),
        next: Some(0), failed: false }) }
}
/// §5.3: increment once, leaving an explicit exhausted state at the last value.
pub open spec fn advance(s: State) -> State {
    State { next: match s.next {
        None => None,
        Some(n) => if n == u64::MAX { None } else { Some((n as int + 1) as u64) },
    }, ..s }
}
/// §6.2: fatal failure is absorbing for this key epoch.
pub open spec fn failed(s: State) -> State { State { failed: true, ..s } }
/// §5.2/§5.4: validate outbound inner type/content/padding before AEAD.
pub open spec fn send_error(typ: u8, content: Seq<u8>, padding: nat) -> Option<u8> {
    if !(typ == 21 || typ == 22 || typ == 23) { Some(10) }
    else if content.len() > crate::spec::MAX_PLAINTEXT { Some(22) }
    else if content.len() == 0 && (typ == 21 || typ == 22) { Some(10) }
    else if content.len() + 1 + padding + 16 > crate::spec::MAX_CIPHERTEXT { Some(22) }
    else { None }
}
/// §5.2/§5.3: write one complete record using exactly the next unused nonce.
pub open spec fn send(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>, s: State,
    typ: u8, content: Seq<u8>, padding: nat) -> (State, Result<Seq<u8>, u8>)
{
    if s.failed { (s, Err(80)) }
    else {
        match s.next {
            None => (failed(s), Err(80)),
            Some(n) => match send_error(typ, content, padding) {
                Some(alert) => (failed(s), Err(alert)),
                None => (advance(s), Ok(crate::spec::encrypt_record(seal, 16, s.iv, n, typ, content, padding))),
            },
        }
    }
}
/// One protected record, an incomplete prefix, or a fatal local/peer failure.
pub enum Read {
    /// Retain input bytes; do not advance the counter or call AEAD.
    NeedMore,
    /// Inner content type, plaintext content and exact consumed wire-byte count.
    Record(u8, Seq<u8>, nat),
    /// Fatal TLS alert description, not permission to retry under this key.
    Fail(u8),
}
/// §5.2/§5.3: authenticate one complete ciphertext and advance only on success.
pub open spec fn receive(open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, s: State,
    wire: Seq<u8>) -> (State, Read)
{
    if s.failed { (s, Read::Fail(80)) }
    else {
        match s.next {
            None => (failed(s), Read::Fail(80)),
            Some(n) => match crate::spec::read_record(wire, true) {
                crate::spec::Read::NeedMore => (s, Read::NeedMore),
                crate::spec::Read::Fail(error) => (failed(s), Read::Fail(crate::spec::alert_of(error))),
                crate::spec::Read::Done(crate::spec::Frame::Protected(header, encrypted), rest) => {
                    match crate::spec::decrypt_record(open, s.iv, n, header, encrypted) {
                        crate::spec::Res::Err(error) => (failed(s), Read::Fail(crate::spec::alert_of(error))),
                        crate::spec::Res::Ok(record) => (advance(s), Read::Record(record.ctype, record.fragment, (wire.len() - rest.len()) as nat)),
                    }
                },
                _ => (failed(s), Read::Fail(10)),
            },
        }
    }
}
} // verus!
