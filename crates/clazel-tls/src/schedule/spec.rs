//! RFC 8446 (August 2018), §7.1–§7.3 and §4.4.4.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-7.1>.
//!
//! Modelling choices:
//! - SHA-256 only (Hash.length = 32), for the selected ChaCha20 suite.
//! - No PSK, resumption, early data or exporters in this phase.
//! - Hash, HKDF and HMAC are parameters; this file states no crypto axiom.
//! - Messages are concatenated handshake encodings, including handshake
//!   headers and excluding record headers. The future state machine owns
//!   the transcript boundaries and the HelloRetryRequest transformation.
//! - The RFC's equations and diagram have no numbered steps; comments name
//!   the equation or diagram edge instead.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The SHA-256 hash length used by the selected suite.
pub const HASH_LEN: usize = 32;

/// §7.1–§7.3 and §4.4.4: labels used by the non-PSK client.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Label {
    /// RFC label `derived` (no trailing NUL).
    Derived,
    /// RFC label `c hs traffic` (no trailing NUL).
    ClientHandshake,
    /// RFC label `s hs traffic` (no trailing NUL).
    ServerHandshake,
    /// RFC label `c ap traffic` (no trailing NUL).
    ClientApplication,
    /// RFC label `s ap traffic` (no trailing NUL).
    ServerApplication,
    /// RFC label `finished` (no trailing NUL).
    Finished,
    /// RFC label `traffic upd` (no trailing NUL).
    Update,
    /// RFC label `key` (no trailing NUL).
    Key,
    /// RFC label `iv` (no trailing NUL).
    Iv,
}

/// §7.1: ASCII labels, without the `tls13 ` prefix or a NUL.
pub open spec fn label_bytes(label: Label) -> Seq<u8> {
    match label {
        Label::Derived => seq![100u8, 101u8, 114u8, 105u8, 118u8, 101u8, 100u8],
        Label::ClientHandshake => seq![99u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::ServerHandshake => seq![115u8, 32u8, 104u8, 115u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::ClientApplication => seq![99u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::ServerApplication => seq![115u8, 32u8, 97u8, 112u8, 32u8, 116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8],
        Label::Finished => seq![102u8, 105u8, 110u8, 105u8, 115u8, 104u8, 101u8, 100u8],
        Label::Update => seq![116u8, 114u8, 97u8, 102u8, 102u8, 105u8, 99u8, 32u8, 117u8, 112u8, 100u8],
        Label::Key => seq![107u8, 101u8, 121u8],
        Label::Iv => seq![105u8, 118u8],
    }
}

/// §7.1 HkdfLabel: the domain-separation prefix.
pub open spec fn prefix() -> Seq<u8> {
    seq![116u8, 108u8, 115u8, 49u8, 51u8, 32u8]
}

/// §7.1: `0` in the diagram is Hash.length zero octets, not empty.
pub open spec fn zeros() -> Seq<u8> {
    Seq::new(HASH_LEN as nat, |i: int| 0u8)
}

/// §7.1 HkdfLabel, fields in presentation-language order.
pub open spec fn hkdf_label(label: Seq<u8>, context: Seq<u8>, length: u16) -> Seq<u8> {
    // uint16 length; opaque label<7..255>; opaque context<0..255>.
    crate::spec::write_u16(length)
        + crate::spec::write_vec(prefix() + label, 255)
        + crate::spec::write_vec(context, 255)
}

/// The cryptographic operations in the RFC equations, without assumptions.
pub struct Crypto {
    /// SHA-256.
    pub hash: spec_fn(Seq<u8>) -> Seq<u8>,
    /// HKDF-Extract(Salt, IKM).
    pub extract: spec_fn(Seq<u8>, Seq<u8>) -> Seq<u8>,
    /// HKDF-Expand(PRK, info, length).
    pub expand: spec_fn(Seq<u8>, Seq<u8>, nat) -> Seq<u8>,
    /// HMAC-SHA256(key, message).
    pub hmac: spec_fn(Seq<u8>, Seq<u8>) -> Seq<u8>,
}

/// §7.1 HKDF-Expand-Label equation.
pub open spec fn expand_label(c: Crypto, secret: Seq<u8>, label: Label,
    context: Seq<u8>, length: u16) -> Seq<u8>
{
    (c.expand)(secret, hkdf_label(label_bytes(label), context, length), length as nat)
}

/// §7.1 Derive-Secret equation (hash the messages, even when empty).
pub open spec fn derive_secret(c: Crypto, secret: Seq<u8>, label: Label,
    messages: Seq<u8>) -> Seq<u8>
{
    expand_label(c, secret, label, (c.hash)(messages), HASH_LEN as u16)
}

/// §7.1 diagram, Early Secret; no PSK still performs Extract(0, 0).
pub open spec fn early_secret(c: Crypto) -> Seq<u8> {
    (c.extract)(zeros(), zeros())
}

/// §7.1 diagram, Early -> derived -> Extract with (EC)DHE.
pub open spec fn handshake_secret(c: Crypto, early: Seq<u8>, dhe: Seq<u8>) -> Seq<u8> {
    (c.extract)(derive_secret(c, early, Label::Derived, Seq::empty()), dhe)
}

/// §7.1 diagram, Handshake -> derived -> Extract with zero IKM.
pub open spec fn master_secret(c: Crypto, handshake: Seq<u8>) -> Seq<u8> {
    (c.extract)(derive_secret(c, handshake, Label::Derived, Seq::empty()), zeros())
}

/// §4.4.4 finished_key and verify_data equations.
pub open spec fn finished(c: Crypto, base: Seq<u8>, messages: Seq<u8>) -> Seq<u8> {
    (c.hmac)(expand_label(c, base, Label::Finished, Seq::empty(), HASH_LEN as u16),
        (c.hash)(messages))
}

} // verus!
