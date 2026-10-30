//! The target host of a connection, typed: a DNS name or an IP address
//! (path-validation design Q2, decided 2026-10-29). ClientHello's
//! server_name (RFC 6066 §3) and server authentication (RFC 8446 §4.4.2,
//! the chain validator's reference identity) both read it, so neither
//! re-parses host text.
//!
//! Sources: RFC 6066 (January 2011) §3, "Server Name Indication",
//! <https://www.rfc-editor.org/rfc/rfc6066#section-3>: "HostName" contains
//! "the fully qualified DNS hostname of the server", "represented as a byte
//! string using ASCII encoding without a trailing dot", and "Literal IPv4
//! and IPv6 addresses are not permitted in "HostName"." RFC 9525 §6.2 to
//! §6.4 (a DNS-ID matches only dNSName subjectAltName entries, an IP-ID only
//! iPAddress entries), which the chain validator applies.
//!
//! Modelling choices:
//! - **Two forms.** `Dns` is the ASCII name, `Ip` the address in network
//!   byte order: 4 octets for IPv4, 16 for IPv6 (RFC 5280 §4.2.1.6's
//!   iPAddress form, so the validator compares octets with no text
//!   parsing). Chrome and Firefox behave the same way: they decide IP
//!   versus DNS once, send no SNI for an IP address, and match an IP host
//!   only against iPAddress entries and a DNS host only against dNSName
//!   entries.
//! - **What the caller must do** (the URL layer, `clazel-url`'s host
//!   parser, at the caller; not wired here). For an `https` URL the host is
//!   never opaque or empty (`https` is a special scheme). A URL `Domain`
//!   becomes `Dns` with its code points as ASCII octets (the URL host parser
//!   has already applied domain-to-ASCII: lowercase, A-labels), after
//!   removing one trailing dot if there is one (RFC 6066 §3: "without a
//!   trailing dot"). A URL `Ipv4(n)` becomes `Ip` of the four octets of `n`,
//!   most significant first; a URL `Ipv6(pieces)` becomes `Ip` of the
//!   sixteen octets of its eight pieces, each most significant octet first.
//!   A bracketed IPv6 literal is never a `Dns` name.
//! - **Bounds** (`host_ok`): a DNS name is 1 to 253 octets (RFC 1035 §2.3.4
//!   with the dots, as the previous untyped host was) and does not end in a
//!   dot; an address is 4 or 16 octets. Anything else is the caller's error
//!   and refuses the configuration (internal_error), never reaching the wire.
//! - **No SNI for an address** (`sni_host_name`): RFC 6066 §3's sentence
//!   above. The ClientHello then has no server_name extension at all
//!   (`hello::client_spec::extensions`), so the server cannot answer one in
//!   EncryptedExtensions (RFC 8446 §4.2: a response must answer an offer).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The target host: a DNS name or an IP address (design Q2).
pub enum Host {
    /// A DNS name, ASCII, without a trailing dot (RFC 6066 §3).
    Dns(Seq<u8>),
    /// An IPv4 (4 octets) or IPv6 (16 octets) address, network byte order.
    Ip(Seq<u8>),
}

/// The bounds a host must meet (header, "Bounds").
pub open spec fn host_ok(host: Host) -> bool {
    match host {
        Host::Dns(name) => 1 <= name.len() <= 253 && name.last() != 0x2eu8,
        Host::Ip(address) => address.len() == 4 || address.len() == 16,
    }
}

/// RFC 6066 §3: the HostName to send in server_name, if any. "Literal IPv4
/// and IPv6 addresses are not permitted in "HostName"", so an address has
/// none.
pub open spec fn sni_host_name(host: Host) -> Option<Seq<u8>> {
    match host {
        Host::Dns(name) => Some(name),
        Host::Ip(_) => None,
    }
}

} // verus!
