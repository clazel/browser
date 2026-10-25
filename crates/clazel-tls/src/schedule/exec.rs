//! Executable RFC 8446 key schedule over an abstract crypto provider.
//! Every operation refines `spec`; cryptographic security and provider
//! correctness are not claimed by these orchestration proofs.

use super::crypto::Crypto;
use super::spec::{HASH_LEN, Label};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 8446 §7.1 HkdfLabel labels (and §7.2, §7.3, §4.4.4).
pub fn label_bytes(label: Label) -> (out: &'static [u8])
    ensures out@ == super::spec::label_bytes(label), 1 <= out.len() <= 249,
{
    let out: &[u8] = match label {
        Label::Derived => &[100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8],
        Label::ClientHandshake => &[99u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::ServerHandshake => &[115u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::ClientApplication => &[99u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::ServerApplication => &[115u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::Finished => &[102u8, 105u8, 110u8, 105u8, 115u8, 104u8, 101u8, 100u8],
        Label::Update => &[116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8, 32u8, 117u8, 112u8, 100u8],
        Label::Key => &[107u8, 101u8, 121u8],
        Label::Iv => &[105u8, 118u8],
    };
    proof { assert(out@ =~= super::spec::label_bytes(label)); }
    out
}

/// RFC 8446 §7.1 HkdfLabel, length then label then context.
pub fn hkdf_label(label: &[u8], context: &[u8], length: u16) -> (out: Vec<u8>)
    requires super::contract::label_requires(label@, context@),
    ensures super::contract::label_ensures(label@, context@, length, out@),
{
    let mut out = Vec::new();
    crate::writer::push_u16(&mut out, length);
    let prefix: &[u8] = &[116u8, 108u8, 115u8, 49u8, 51u8, 32u8];
    proof { assert(prefix@ =~= super::spec::prefix()); }
    let mut full_label = Vec::new();
    full_label.extend_from_slice(prefix);
    full_label.extend_from_slice(label);
    crate::writer::push_vec(&mut out, full_label.as_slice(), 255);
    crate::writer::push_vec(&mut out, context, 255);
    proof { assert(out@ =~= super::spec::hkdf_label(label@, context@, length)); }
    out
}

/// RFC 8446 §7.1 HKDF-Expand-Label equation.
pub fn expand_label<C: Crypto>(crypto: &C, secret: &[u8], label: Label,
    context: &[u8], length: u16) -> (out: Vec<u8>)
    requires super::contract::expand_requires(secret@, context@, length),
    ensures out@ == super::spec::expand_label(crypto.functions(), secret@, label, context@, length),
        out.len() == length,
{
    let label = label_bytes(label);
    let info = hkdf_label(label, context, length);
    crypto.expand(secret, info.as_slice(), length)
}

/// RFC 8446 §7.1 Derive-Secret equation, including Hash(empty).
pub fn derive_secret<C: Crypto>(crypto: &C, secret: &[u8], label: Label,
    messages: &[u8]) -> (out: Vec<u8>)
    requires secret.len() == HASH_LEN,
    ensures out@ == super::spec::derive_secret(crypto.functions(), secret@, label, messages@),
        out.len() == HASH_LEN,
{
    let hash = crypto.hash(messages);
    expand_label(crypto, secret, label, hash.as_slice(), HASH_LEN as u16)
}

/// RFC 8446 §7.1: construct the diagram's Hash.length zero octets.
pub fn zeros() -> (out: Vec<u8>)
    ensures out@ == super::spec::zeros(), out.len() == HASH_LEN,
{
    let mut out = Vec::new();
    let mut i: usize = 0;
    while i < HASH_LEN
        invariant i <= HASH_LEN, out@ == Seq::new(i as nat, |j: int| 0u8),
        decreases HASH_LEN - i,
    {
        out.push(0);
        i = i.saturating_add(1);
        proof { assert(out@ =~= Seq::new(i as nat, |j: int| 0u8)); }
    }
    out
}

/// RFC 8446 §7.1 diagram: Early Secret = Extract(0, 0), no PSK.
pub fn early_secret<C: Crypto>(crypto: &C) -> (out: Vec<u8>)
    ensures out@ == super::spec::early_secret(crypto.functions()), out.len() == HASH_LEN,
{
    let zero = zeros();
    crypto.extract(zero.as_slice(), zero.as_slice())
}

/// RFC 8446 §7.1 diagram: derive the salt from Early Secret, then Extract.
pub fn handshake_secret<C: Crypto>(crypto: &C, early: &[u8], dhe: &[u8]) -> (out: Vec<u8>)
    requires early.len() == HASH_LEN, dhe.len() == 32,
    ensures out@ == super::spec::handshake_secret(crypto.functions(), early@, dhe@),
        out.len() == HASH_LEN,
{
    let empty: &[u8] = &[];
    proof { assert(empty@ =~= Seq::<u8>::empty()); }
    let salt = derive_secret(crypto, early, Label::Derived, empty);
    crypto.extract(salt.as_slice(), dhe)
}

/// RFC 8446 §7.1 diagram: derive the salt from Handshake Secret; zero IKM.
pub fn master_secret<C: Crypto>(crypto: &C, handshake: &[u8]) -> (out: Vec<u8>)
    requires handshake.len() == HASH_LEN,
    ensures out@ == super::spec::master_secret(crypto.functions(), handshake@),
        out.len() == HASH_LEN,
{
    let empty: &[u8] = &[];
    proof { assert(empty@ =~= Seq::<u8>::empty()); }
    let salt = derive_secret(crypto, handshake, Label::Derived, empty);
    let zero = zeros();
    crypto.extract(salt.as_slice(), zero.as_slice())
}

/// RFC 8446 §4.4.4: finished_key then HMAC of the transcript hash.
pub fn finished<C: Crypto>(crypto: &C, base: &[u8], messages: &[u8]) -> (out: Vec<u8>)
    requires base.len() == HASH_LEN,
    ensures out@ == super::spec::finished(crypto.functions(), base@, messages@), out.len() == HASH_LEN,
{
    let key = expand_label(crypto, base, Label::Finished, &[], HASH_LEN as u16);
    let hash = crypto.hash(messages);
    crypto.hmac(key.as_slice(), hash.as_slice())
}

/// RFC 8446 §7.2: next traffic secret, empty context (not Hash(empty)).
pub fn update_secret<C: Crypto>(crypto: &C, secret: &[u8]) -> (out: Vec<u8>)
    requires secret.len() == HASH_LEN,
    ensures out@ == super::spec::expand_label(crypto.functions(), secret@, Label::Update,
        Seq::empty(), HASH_LEN as u16), out.len() == HASH_LEN,
{
    expand_label(crypto, secret, Label::Update, &[], HASH_LEN as u16)
}

/// RFC 8446 §7.3: ChaCha20's 32-byte write key, with empty context.
pub fn write_key<C: Crypto>(crypto: &C, secret: &[u8]) -> (out: Vec<u8>)
    requires secret.len() == HASH_LEN,
    ensures out@ == super::spec::expand_label(crypto.functions(), secret@, Label::Key,
        Seq::empty(), 32), out.len() == 32,
{
    expand_label(crypto, secret, Label::Key, &[], 32)
}

/// RFC 8446 §7.3: ChaCha20-Poly1305's 12-byte write IV, empty context.
pub fn write_iv<C: Crypto>(crypto: &C, secret: &[u8]) -> (out: Vec<u8>)
    requires secret.len() == HASH_LEN,
    ensures out@ == super::spec::expand_label(crypto.functions(), secret@, Label::Iv,
        Seq::empty(), 12), out.len() == 12,
{
    expand_label(crypto, secret, Label::Iv, &[], 12)
}

} // verus!
