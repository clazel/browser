//! Concrete KeyUpdate transition facts used by certified mutations.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
pub open spec fn empty_hash(_messages: Seq<u8>) -> Seq<u8> { seq![] }
pub open spec fn empty_extract(_salt: Seq<u8>, _ikm: Seq<u8>) -> Seq<u8> { seq![] }
pub open spec fn empty_expand(_secret: Seq<u8>, _info: Seq<u8>, _length: nat) -> Seq<u8> { seq![] }
pub open spec fn empty_hmac(_key: Seq<u8>, _message: Seq<u8>) -> Seq<u8> { seq![] }
pub open spec fn dummy_seal(_key: Seq<u8>, _nonce: Seq<u8>, _ad: Seq<u8>, _plaintext: Seq<u8>) -> Seq<u8> { seq![] }
pub open spec fn dummy_open(_key: Seq<u8>, _nonce: Seq<u8>, _ad: Seq<u8>, _ciphertext: Seq<u8>) -> Option<Seq<u8>> { None }

pub open spec fn crypto() -> crate::schedule::spec::Crypto {
    crate::schedule::spec::Crypto {
        hash: |messages: Seq<u8>| empty_hash(messages),
        extract: |salt: Seq<u8>, ikm: Seq<u8>| empty_extract(salt, ikm),
        expand: |secret: Seq<u8>, info: Seq<u8>, length: nat| empty_expand(secret, info, length),
        hmac: |key: Seq<u8>, message: Seq<u8>| empty_hmac(key, message),
    }
}

pub open spec fn ciphers() -> super::dispatcher_spec::Ciphers {
    super::dispatcher_spec::Ciphers {
        seal: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, plaintext: Seq<u8>| dummy_seal(key, nonce, ad, plaintext),
        open: |key: Seq<u8>, nonce: Seq<u8>, ad: Seq<u8>, ciphertext: Seq<u8>| dummy_open(key, nonce, ad, ciphertext),
    }
}

pub open spec fn sample_ready_state() -> super::dispatcher_spec::State {
    let epoch = crate::traffic::spec::State {
        key: Seq::new(32, |_i: int| 7u8),
        iv: Seq::new(12, |_i: int| 9u8),
        next: Some(0),
        failed: false,
    };
    super::dispatcher_spec::State {
        mode: super::dispatcher_spec::Mode::Ready,
        application_sender: Some(epoch),
        application_receiver: Some(epoch),
        client_application_secret: Seq::new(32, |_i: int| 11u8),
        server_application_secret: Seq::new(32, |_i: int| 13u8),
        response_due: false,
        ..super::dispatcher_spec::failed()
    }
}

pub open spec fn sample_bad_update_state() -> super::dispatcher_spec::State {
    super::dispatcher_spec::State {
        pending_update_secret: seq![],
        pending_update_wire: seq![7u8],
        pending_update_request: Some(0u8),
        ..sample_ready_state()
    }
}

} // verus!
