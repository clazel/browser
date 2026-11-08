//! A clean-room transcription of RFC 8446 (TLS 1.3) for a client, as Verus
//! spec functions.
//!
//! Written from the RFC's text only. No file of this crate outside this
//! directory was read (its `Cargo.toml` excepted, for its dependencies),
//! nor `clazel-crypto`, `clazel-net`, `docs/TLS-HOSTILE-CASES.md`, sections
//! 3.5d to 3.5g of `docs/phases/phase-3.md`, or any TLS pull request. Its
//! purpose is a later equivalence proof, by a different author, against the
//! crate's spec: a misreading shows up as a failed equivalence at the exact
//! step. This module proves nothing beyond the witnesses in
//! [`witnesses`], and nothing here says the crate's implementation is right.
//!
//! Source, read for the sections cited:
//! - RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>, the
//!   plain-text form fetched from `rfc8446.txt` on 7 November 2026, SHA-256
//!   `47871bc8820a2c3b6ea89f061055577058862cf543686b82d10131239702b3bd`.
//! - RFC 8448, January 2019, <https://www.rfc-editor.org/rfc/rfc8448>,
//!   SHA-256
//!   `6564d1376d1ec744fc7a9993da15ebc1b9be361908b166091f47ef605c537fba`,
//!   for the trace values of [`rfc8448_data`] only.
//! - RFC 6066 §3, §4 and §8, and the RFCs §4.2's table names for the
//!   extensions a server may send (RFC 5764, 6520, 6962, 7250, 7301), with RFC
//!   5890, 1123 and 1035 for host names; [`server_name`] and
//!   [`extension_bodies`] give their hashes or dates.
//!
//! Where each section lives:
//!
//! | Section | File |
//! |---------|------|
//! | §3 presentation language | [`presentation`] |
//! | §4, §4.1 handshake, hellos and their client checks | [`key_exchange`] |
//! | §4.2 extensions | [`extensions`] |
//! | §4.2 the bodies of extensions a client receives | [`extension_bodies`] |
//! | RFC 6066 §3 server_name (§4.4.2.2, §9.2) | [`server_name`] |
//! | Appendix D.4, the client's sending side; the client's configuration | [`middlebox`] |
//! | §4.3, §4.4 server parameters, authentication, transcript | [`authentication`] |
//! | §4.6 post-handshake messages | [`post_handshake`] |
//! | §5 record layer | [`record`] (wire forms), [`connection`] (receiving) |
//! | §6 alerts | [`alerts`] (what is required), [`connection`] (receiving) |
//! | §7 key schedule | [`key_schedule`] |
//! | Appendix A.1 client state machine | [`state_machine`] |
//!
//! Not transcribed, and why: the server side of everything (§4.1.1's server
//! selection, §4.2.11.3, Appendix A.2); PSK and 0-RTT (§4.2.9, §4.2.10,
//! §4.2.11, §4.5 beyond rejecting it, §8); client certificates (§4.4.2.3,
//! §4.6.2 beyond rejecting it; a request is answered by an empty
//! Certificate); the exporter function of §7.5 (the two exporter secrets
//! are transcribed); finite-field and NIST-curve key shares (§4.2.8.1,
//! §4.2.8.2's point format, §7.4.1); X.509 path validation; TLS 1.2 and below
//! beyond detecting and refusing them (§4.1.3, Appendix D.1, D.5); §5.5's
//! advice to rekey before the limits (a SHOULD about when, with nothing to
//! check); what the contents of the other RFCs' extensions mean beyond their
//! syntax and the rules their RFCs give a client (an ALPN protocol, an SCT or an
//! OCSP response is not interpreted; [`extension_bodies`] lists what is
//! checked). Appendix D.4's compatibility records, which D.4 makes optional,
//! are a parameter ([`middlebox::ClientConfig`]).
//!
//! Modelling choices that span files. Each file lists its own as well.
//!
//! 1. **Client only.** No PSK, no early data and no client certificate. The
//!    profile is TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519.
//!    [`key_exchange::client_hello_conforms`] pins the profile on what the
//!    client offers. The receive checks read the offer rather than the
//!    profile, as the RFC words them ("was not offered"), which is why the
//!    RFC 8448 trace of another suite can run through them.
//! 2. **Abstract primitives.** The hash, HKDF-Extract, HKDF-Expand, HMAC,
//!    the AEAD, X25519, signature verification and certificate validation
//!    are fields of [`primitives::Primitives`], `spec_fn`s with no properties
//!    assumed. Hash.length, key_length, iv_length and the AEAD expansion are
//!    the suite's fixed numbers ([`primitives`]).
//! 3. **Numbers are `nat`**, per `docs/SPEC-STYLE.md`, including enum values
//!    of the wire (`nat` holds "future values" and unknown ones, which §3.5
//!    requires a parser to keep). Each enum value is a spec function with the
//!    RFC's name and a short prefix for its enum: `ht_` HandshakeType, `ext_`
//!    ExtensionType, `ct_` ContentType, `ad_` AlertDescription.
//! 4. **An error is a [`alerts::ClientError`]**, one variant per condition
//!    the RFC names, and [`alerts::required_alert`] is §6.2's "which alert".
//!    Where a message breaks several rules, the RFC mostly does not rank them,
//!    so each check is a *list* of every failure in the order of the text
//!    (`..._failures` functions), and the state machine reports the first.
//!    An equivalence against another order should compare acceptance exactly,
//!    and compare a rejection with membership in the list.
//! 5. **A "MUST" of the server that the RFC gives no receiver action for** is
//!    checked by the client only where the text or §6 says what to do; the
//!    rest are named in the file that would have held them.
//! 6. **Where the RFC names no alert** ("abort the handshake" alone), §6's
//!    note decides: syntax is `decode_error`, semantics `illegal_parameter`.
//!    [`alerts`] marks each such choice.

pub mod alerts;
pub mod authentication;
pub mod connection;
pub mod extension_bodies;
pub mod extensions;
pub mod key_exchange;
pub mod key_schedule;
pub mod middlebox;
pub mod post_handshake;
pub mod presentation;
pub mod primitives;
pub mod record;
pub mod rfc8448_data;
pub mod server_name;
pub mod state_machine;
pub mod witnesses;
