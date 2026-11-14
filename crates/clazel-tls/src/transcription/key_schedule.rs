//! RFC 8446 §7: the key schedule, traffic secrets, traffic keys and updates.
//!
//! Modelling choices:
//! - Each box of §7.1's diagram is one function, named for the secret it gives.
//!   Each takes the secret above it. A chain from the top is a composition
//!   ([`handshake_secret`] and [`master_secret`] are the left side).
//! - "PSK" is an argument. "If a given secret is not available, then the 0-value
//!   ... is used", so a client without PSK passes [`zero_value`], and the
//!   branches that only PSK reaches (binder_key, client_early_traffic_secret,
//!   early_exporter_master_secret) are transcribed, but the state machine never
//!   uses them.
//! - `Messages` of Derive-Secret is the list of raw messages, with the flag of
//!   §4.4.1 (see `authentication::transcript_hash`), since "Messages is the
//!   concatenation of the indicated handshake messages" and the synthetic message
//!   is the exception to that. `""` is the empty list with the flag false.
//! - Labels are byte sequences, because an ASCII string is what the text says they
//!   are ("all ASCII strings and do not include a trailing NUL byte"). Their
//!   string is in the comment and `witnesses` compares them with RFC 8448's `info`
//!   bytes, apart from "traffic upd", "ext binder" and "res binder", which that
//!   comparison does not reach.
//! - §7.4.2 for X25519 is in the state machine, where the all-zero check belongs.
//! - §7.5's exporter function is not transcribed: only the two exporter secrets.
//! - The "SHOULD be erased"/"SHOULD delete" of §7.1 and §7.2 are not modelled: a
//!   pure function has no memory to erase.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::authentication::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;

verus! {

/// §7.1: `"tls13 " + Label`'s prefix.
pub open spec fn label_prefix() -> Seq<u8> {
    seq![0x74u8, 0x6c, 0x73, 0x31, 0x33, 0x20]
}

/// §7.1: the HkdfLabel of `Length`, `Label`, `Context`.
/// `struct { uint16 length = Length; opaque label<7..255> = "tls13 " + Label; opaque context<0..255> = Context; } HkdfLabel;`
pub open spec fn hkdf_label(length: nat, label: Seq<u8>, context: Seq<u8>) -> Seq<u8> {
    uint16(length) + write_vector(label_prefix() + label, 255) + write_vector(context, 255)
}

/// §7.1: `HKDF-Expand-Label(Secret, Label, Context, Length) = HKDF-Expand(Secret, HkdfLabel, Length)`.
pub open spec fn hkdf_expand_label(p: Primitives, secret: Seq<u8>, label: Seq<u8>, context: Seq<u8>, length: nat) -> Seq<u8> {
    (p.hkdf_expand)(secret, hkdf_label(length, label, context), length)
}

/// §7.1: `Derive-Secret(Secret, Label, Messages) = HKDF-Expand-Label(Secret, Label, Transcript-Hash(Messages), Hash.length)`.
pub open spec fn derive_secret(p: Primitives, secret: Seq<u8>, label: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    hkdf_expand_label(p, secret, label, transcript_hash(p, messages, retried), hash_length())
}

/// §7.1 "derived".
pub open spec fn label_derived() -> Seq<u8> {
    seq![0x64u8, 0x65, 0x72, 0x69, 0x76, 0x65, 0x64]
}
/// §7.1 "ext binder".
pub open spec fn label_ext_binder() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x74, 0x20, 0x62, 0x69, 0x6e, 0x64, 0x65, 0x72]
}
/// §7.1 "res binder".
pub open spec fn label_res_binder() -> Seq<u8> {
    seq![0x72u8, 0x65, 0x73, 0x20, 0x62, 0x69, 0x6e, 0x64, 0x65, 0x72]
}
/// §7.1 "c e traffic".
pub open spec fn label_c_e_traffic() -> Seq<u8> {
    seq![0x63u8, 0x20, 0x65, 0x20, 0x74, 0x72, 0x61, 0x66, 0x66, 0x69, 0x63]
}
/// §7.1 "e exp master".
pub open spec fn label_e_exp_master() -> Seq<u8> {
    seq![0x65u8, 0x20, 0x65, 0x78, 0x70, 0x20, 0x6d, 0x61, 0x73, 0x74, 0x65, 0x72]
}
/// §7.1 "c hs traffic".
pub open spec fn label_c_hs_traffic() -> Seq<u8> {
    seq![0x63u8, 0x20, 0x68, 0x73, 0x20, 0x74, 0x72, 0x61, 0x66, 0x66, 0x69, 0x63]
}
/// §7.1 "s hs traffic".
pub open spec fn label_s_hs_traffic() -> Seq<u8> {
    seq![0x73u8, 0x20, 0x68, 0x73, 0x20, 0x74, 0x72, 0x61, 0x66, 0x66, 0x69, 0x63]
}
/// §7.1 "c ap traffic".
pub open spec fn label_c_ap_traffic() -> Seq<u8> {
    seq![0x63u8, 0x20, 0x61, 0x70, 0x20, 0x74, 0x72, 0x61, 0x66, 0x66, 0x69, 0x63]
}
/// §7.1 "s ap traffic".
pub open spec fn label_s_ap_traffic() -> Seq<u8> {
    seq![0x73u8, 0x20, 0x61, 0x70, 0x20, 0x74, 0x72, 0x61, 0x66, 0x66, 0x69, 0x63]
}
/// §7.1 "exp master".
pub open spec fn label_exp_master() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x70, 0x20, 0x6d, 0x61, 0x73, 0x74, 0x65, 0x72]
}
/// §7.1 "res master".
pub open spec fn label_res_master() -> Seq<u8> {
    seq![0x72u8, 0x65, 0x73, 0x20, 0x6d, 0x61, 0x73, 0x74, 0x65, 0x72]
}
/// §7.2 "traffic upd".
pub open spec fn label_traffic_upd() -> Seq<u8> {
    seq![0x74u8, 0x72, 0x61, 0x66, 0x66, 0x69, 0x63, 0x20, 0x75, 0x70, 0x64]
}
/// §7.3 "key".
pub open spec fn label_key() -> Seq<u8> {
    seq![0x6bu8, 0x65, 0x79]
}
/// §7.3 "iv".
pub open spec fn label_iv() -> Seq<u8> {
    seq![0x69u8, 0x76]
}
/// §4.4.4 "finished".
pub open spec fn label_finished() -> Seq<u8> {
    seq![0x66u8, 0x69, 0x6e, 0x69, 0x73, 0x68, 0x65, 0x64]
}
/// §4.6.1 "resumption".
pub open spec fn label_resumption() -> Seq<u8> {
    seq![0x72u8, 0x65, 0x73, 0x75, 0x6d, 0x70, 0x74, 0x69, 0x6f, 0x6e]
}

// §7.1's diagram, from the top.

/// §7.1: `0`, `PSK -> HKDF-Extract = Early Secret`.
pub open spec fn early_secret(p: Primitives, psk: Seq<u8>) -> Seq<u8> {
    (p.hkdf_extract)(zero_value(), psk)
}

/// §7.1: `Derive-Secret(., "ext binder" | "res binder", "") = binder_key`.
/// `external`: "the label is 'ext binder' for external PSKs ... and 'res binder'
/// for resumption PSKs".
pub open spec fn binder_key(p: Primitives, early: Seq<u8>, external: bool) -> Seq<u8> {
    derive_secret(p, early, if external { label_ext_binder() } else { label_res_binder() }, seq![], false)
}

/// §7.1: `Derive-Secret(., "c e traffic", ClientHello) = client_early_traffic_secret`.
pub open spec fn client_early_traffic_secret(p: Primitives, early: Seq<u8>, client_hello: Seq<u8>) -> Seq<u8> {
    derive_secret(p, early, label_c_e_traffic(), seq![client_hello], false)
}

/// §7.1: `Derive-Secret(., "e exp master", ClientHello) = early_exporter_master_secret`.
pub open spec fn early_exporter_master_secret(p: Primitives, early: Seq<u8>, client_hello: Seq<u8>) -> Seq<u8> {
    derive_secret(p, early, label_e_exp_master(), seq![client_hello], false)
}

/// §7.1: `Derive-Secret(., "derived", "")`, then `(EC)DHE -> HKDF-Extract = Handshake Secret`.
pub open spec fn handshake_secret(p: Primitives, early: Seq<u8>, ecdhe: Seq<u8>) -> Seq<u8> {
    (p.hkdf_extract)(derive_secret(p, early, label_derived(), seq![], false), ecdhe)
}

/// §7.1: `Derive-Secret(., "c hs traffic", ClientHello...ServerHello) = client_handshake_traffic_secret`.
pub open spec fn client_handshake_traffic_secret(p: Primitives, handshake: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    derive_secret(p, handshake, label_c_hs_traffic(), messages, retried)
}

/// §7.1: `Derive-Secret(., "s hs traffic", ClientHello...ServerHello) = server_handshake_traffic_secret`.
pub open spec fn server_handshake_traffic_secret(p: Primitives, handshake: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    derive_secret(p, handshake, label_s_hs_traffic(), messages, retried)
}

/// §7.1: `Derive-Secret(., "derived", "")`, then `0 -> HKDF-Extract = Master Secret`.
pub open spec fn master_secret(p: Primitives, handshake: Seq<u8>) -> Seq<u8> {
    (p.hkdf_extract)(derive_secret(p, handshake, label_derived(), seq![], false), zero_value())
}

/// §7.1: `Derive-Secret(., "c ap traffic", ClientHello...server Finished) = client_application_traffic_secret_0`.
pub open spec fn client_application_traffic_secret_0(p: Primitives, master: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    derive_secret(p, master, label_c_ap_traffic(), messages, retried)
}

/// §7.1: `Derive-Secret(., "s ap traffic", ClientHello...server Finished) = server_application_traffic_secret_0`.
pub open spec fn server_application_traffic_secret_0(p: Primitives, master: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    derive_secret(p, master, label_s_ap_traffic(), messages, retried)
}

/// §7.1: `Derive-Secret(., "exp master", ClientHello...server Finished) = exporter_master_secret`.
pub open spec fn exporter_master_secret(p: Primitives, master: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    derive_secret(p, master, label_exp_master(), messages, retried)
}

/// §7.1: `Derive-Secret(., "res master", ClientHello...client Finished) = resumption_master_secret`.
pub open spec fn resumption_master_secret(p: Primitives, master: Seq<u8>, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    derive_secret(p, master, label_res_master(), messages, retried)
}

/// §7.2: `application_traffic_secret_N+1 = HKDF-Expand-Label(application_traffic_secret_N, "traffic upd", "", Hash.length)`.
pub open spec fn next_application_traffic_secret(p: Primitives, secret: Seq<u8>) -> Seq<u8> {
    hkdf_expand_label(p, secret, label_traffic_upd(), seq![], hash_length())
}

/// §7.3: `[sender]_write_key = HKDF-Expand-Label(Secret, "key", "", key_length)`.
pub open spec fn write_key(p: Primitives, secret: Seq<u8>) -> Seq<u8> {
    hkdf_expand_label(p, secret, label_key(), seq![], key_length())
}

/// §7.3: `[sender]_write_iv = HKDF-Expand-Label(Secret, "iv", "", iv_length)`.
pub open spec fn write_iv(p: Primitives, secret: Seq<u8>) -> Seq<u8> {
    hkdf_expand_label(p, secret, label_iv(), seq![], iv_length())
}

} // verus!
