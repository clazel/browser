//! RFC 8446 §5.2/§5.3/§7.3: separate protected send/receive key epochs.
use super::provider::{Factory, KeyedAead};
use crate::record::{Frame, ReadOut};
use crate::schedule::crypto::Crypto;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
struct Keys<A: KeyedAead> {
    cipher: A,
    iv: Vec<u8>,
    next: Option<u64>,
    failed: bool,
}
impl<A: KeyedAead> View for Keys<A> {
    type V = super::spec::State;
    closed spec fn view(&self) -> super::spec::State {
        super::spec::State { key: self.cipher.key_spec(), iv: self.iv@, next: self.next, failed: self.failed }
    }
}
impl<A: KeyedAead> Keys<A> {
    closed spec fn wf(&self) -> bool {
        super::spec::wf(self@) && self.cipher.nonce_len_spec() == 12 && self.cipher.tag_len_spec() == 16
    }
    fn fail(&mut self, alert: u8) -> (out: u8)
        requires old(self).wf(),
        ensures out == alert, final(self).wf(), final(self)@ == super::spec::failed(old(self)@),
            (forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] final(self).cipher.seal_spec(n, ad, p) == old(self).cipher.seal_spec(n, ad, p)),
            (forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] final(self).cipher.open_spec(n, ad, ct) == old(self).cipher.open_spec(n, ad, ct)),
    { self.failed = true; alert }
    fn advance(&mut self)
        requires old(self).wf(), old(self).next is Some,
        ensures final(self).wf(), final(self)@ == super::spec::advance(old(self)@),
            (forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] final(self).cipher.seal_spec(n, ad, p) == old(self).cipher.seal_spec(n, ad, p)),
            (forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] final(self).cipher.open_spec(n, ad, ct) == old(self).cipher.open_spec(n, ad, ct)),
    {
        self.next = match self.next { Some(n) => n.checked_add(1), None => None };
    }
}
fn make<C: Crypto, F: Factory>(crypto: &C, factory: &F, secret: &[u8]) -> (out: Result<Keys<F::Cipher>, u8>)
    ensures match out {
        Err(e) => super::spec::start(crypto.functions(), secret@) == Err(e),
        Ok(k) => k.wf() && super::spec::start(crypto.functions(), secret@) == Ok(k@)
            && (forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] crate::record::Aead::seal_spec(&k.cipher, n, ad, p) == (factory.functions().seal)(k@.key, n, ad, p))
            && (forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] crate::record::Aead::open_spec(&k.cipher, n, ad, ct) == (factory.functions().open)(k@.key, n, ad, ct)),
    },
{
    if secret.len() != 32 { return Err(80); }
    let key = crate::schedule::exec::write_key(crypto, secret);
    let iv = crate::schedule::exec::write_iv(crypto, secret);
    let cipher = factory.make(key.as_slice());
    Ok(Keys { cipher, iv, next: Some(0), failed: false })
}
/// One immutable installed traffic key and its outbound counter. No Clone/reset.
pub struct Encryptor<A: KeyedAead> { keys: Keys<A> }
/// One immutable installed traffic key and its independent inbound counter.
pub struct Decryptor<A: KeyedAead> { keys: Keys<A> }
impl<A: KeyedAead> View for Encryptor<A> {
    type V = super::spec::State;
    closed spec fn view(&self) -> super::spec::State { self.keys@ }
}
impl<A: KeyedAead> View for Decryptor<A> {
    type V = super::spec::State;
    closed spec fn view(&self) -> super::spec::State { self.keys@ }
}
/// View of an installed send key.
pub open spec fn sender_view<A: KeyedAead>(out: Result<Encryptor<A>, u8>) -> Result<super::spec::State, u8> {
    match out { Err(e) => Err(e), Ok(e) => Ok(e@) }
}
/// View of an installed receive key.
pub open spec fn receiver_view<A: KeyedAead>(out: Result<Decryptor<A>, u8>) -> Result<super::spec::State, u8> {
    match out { Err(e) => Err(e), Ok(e) => Ok(e@) }
}
/// View of protected output bytes or a fatal failure.
pub open spec fn sent_view(out: Result<Vec<u8>, u8>) -> Result<Seq<u8>, u8> {
    match out { Err(e) => Err(e), Ok(b) => Ok(b@) }
}
/// Complete, decrypted record content is still subject to reassembly/auth policy.
#[derive(Debug, PartialEq, Eq)]
pub enum Read {
    /// Retain input bytes; no counter/AEAD effect.
    NeedMore,
    /// Inner type, content and exact bytes consumed from the input prefix.
    Record(u8, Vec<u8>, usize),
    /// Fatal alert description; this epoch cannot be used again.
    Fail(u8),
}
impl View for Read {
    type V = super::spec::Read;
    open spec fn view(&self) -> super::spec::Read {
        match self { Read::NeedMore => super::spec::Read::NeedMore,
            Read::Fail(e) => super::spec::Read::Fail(*e),
            Read::Record(t, b, n) => super::spec::Read::Record(*t, b@, *n as nat) }
    }
}
/// §5.2/§5.4: reject invalid outbound content/type/padding before calling AEAD.
fn send_error(typ: u8, content: &[u8], padding: usize) -> (out: Option<u8>)
    ensures out == super::spec::send_error(typ, content@, padding as nat),
        out is None ==> content.len() + 1 + padding <= crate::spec::MAX_PLAINTEXT + 1,
        out is None ==> content.len() + 1 + padding + 16 <= crate::spec::MAX_CIPHERTEXT,
{
    if !(typ == 21 || typ == 22 || typ == 23) { return Some(10); }
    if content.len() > crate::spec::MAX_PLAINTEXT { return Some(22); }
    if content.is_empty() && (typ == 21 || typ == 22) { return Some(10); }
    if padding > crate::spec::MAX_PLAINTEXT { return Some(22); }
    let needed = content.len().saturating_add(padding).saturating_add(1);
    proof { assert(needed == content.len() + padding + 1); }
    if needed > crate::spec::MAX_PLAINTEXT.saturating_add(1) { Some(22) } else { None }
}
impl<A: KeyedAead> Encryptor<A> {
    /// Installed cipher has the fixed tag/nonce sizes and derived key/IV lengths.
    pub closed spec fn wf(&self) -> bool { self.keys.wf() }
    /// Installed cipher's encryption function, with the key retained inside it.
    pub closed spec fn seal_spec(&self, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>) -> Seq<u8> {
        self.keys.cipher.seal_spec(nonce, ad, plaintext)
    }
    /// §7.3: derive and install one direction/epoch's actual traffic secret.
    pub fn new<C: Crypto, F: Factory<Cipher = A>>(crypto: &C, factory: &F, secret: &[u8]) -> (out: Result<Self, u8>)
        ensures super::contract::start_ensures(crypto.functions(), secret@, sender_view(out)),
            match out { Err(_) => true, Ok(e) => e.wf()
                && (forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] e.seal_spec(n, ad, p) == (factory.functions().seal)(e@.key, n, ad, p)) },
    {
        match make(crypto, factory, secret) { Err(e) => Err(e), Ok(keys) => Ok(Encryptor { keys }) }
    }
    /// Next unused counter; None is exhausted, never a request to reset it.
    pub fn next_sequence(&self) -> (out: Option<u64>) ensures out == self@.next { self.keys.next }
    /// §5.2/§5.3: protect one bounded fragment; fatal errors prohibit another use.
    pub fn seal(&mut self, typ: u8, content: &[u8], padding: usize) -> (out: Result<Vec<u8>, u8>)
        requires old(self).wf(),
        ensures final(self).wf(),
            super::contract::send_ensures(|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| old(self).seal_spec(n, ad, p),
                old(self)@, typ, content@, padding as nat, final(self)@, sent_view(out)),
            super::contract::seal_preserved(|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| old(self).seal_spec(n, ad, p),
                |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| final(self).seal_spec(n, ad, p)),
            forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] final(self).seal_spec(n, ad, p) == old(self).seal_spec(n, ad, p),
    {
        if self.keys.failed { return Err(80); }
        let n = match self.keys.next { Some(n) => n, None => return Err(self.keys.fail(80)) };
        if let Some(alert) = send_error(typ, content, padding) { return Err(self.keys.fail(alert)); }
        let bytes = crate::record::encrypt_record(&self.keys.cipher, self.keys.iv.as_slice(), n, typ, content, padding);
        self.keys.advance();
        Ok(bytes)
    }
}
impl<A: KeyedAead> Decryptor<A> {
    /// Installed cipher has the fixed tag/nonce sizes and derived key/IV lengths.
    pub closed spec fn wf(&self) -> bool { self.keys.wf() }
    /// Installed cipher's authentication/decryption function.
    pub closed spec fn open_spec(&self, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>) -> Option<Seq<u8>> {
        self.keys.cipher.open_spec(nonce, ad, ciphertext)
    }
    /// §7.3: derive and install one direction/epoch's actual traffic secret.
    pub fn new<C: Crypto, F: Factory<Cipher = A>>(crypto: &C, factory: &F, secret: &[u8]) -> (out: Result<Self, u8>)
        ensures super::contract::start_ensures(crypto.functions(), secret@, receiver_view(out)),
            match out { Err(_) => true, Ok(e) => e.wf()
                && (forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] e.open_spec(n, ad, ct) == (factory.functions().open)(e@.key, n, ad, ct)) },
    {
        match make(crypto, factory, secret) { Err(e) => Err(e), Ok(keys) => Ok(Decryptor { keys }) }
    }
    /// Next expected counter; unauthenticated/incomplete input does not advance it.
    pub fn next_sequence(&self) -> (out: Option<u64>) ensures out == self@.next { self.keys.next }
    /// §5.1–§5.4: authenticate one complete record prefix; retain any input suffix.
    /// Compatibility CCS must be dispatched separately by the connection driver.
    pub fn open(&mut self, wire: &[u8]) -> (out: Read)
        requires old(self).wf(),
        ensures final(self).wf(),
            super::contract::receive_ensures(|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| old(self).open_spec(n, ad, ct),
                old(self)@, wire@, final(self)@, out@),
            super::contract::open_preserved(|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| old(self).open_spec(n, ad, ct),
                |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| final(self).open_spec(n, ad, ct)),
            forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] final(self).open_spec(n, ad, ct) == old(self).open_spec(n, ad, ct),
    {
        hide(crate::spec::read_record);
        if self.keys.failed { return Read::Fail(80); }
        let n = match self.keys.next { Some(n) => n, None => return Read::Fail(self.keys.fail(80)) };
        match crate::record::read_record(wire, true) {
            ReadOut::NeedMore => Read::NeedMore,
            ReadOut::Fail(error) => Read::Fail(self.keys.fail(crate::encode::alert_for(error).description)),
            ReadOut::Done(Frame::Protected(header, encrypted), rest) => {
                proof { crate::lemmas_record::lemma_read_record_canonical(wire@, true); }
                let consumed = wire.len().saturating_sub(rest.len());
                proof { assert(consumed == wire.len() - rest.len()); }
                match crate::record::decrypt_record(&self.keys.cipher, self.keys.iv.as_slice(), n, header, encrypted) {
                    Err(error) => Read::Fail(self.keys.fail(crate::encode::alert_for(error).description)),
                    Ok((typ, bytes)) => { self.keys.advance(); Read::Record(typ, bytes, consumed) },
                }
            },
            _ => Read::Fail(self.keys.fail(10)),
        }
    }
}
} // verus!
