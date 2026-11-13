//! RFC 8446 (August 2018) §4.1.3, §4.1.4, §4.2.1 and §4.2.8:
//! server Hello acceptance for the initial non-PSK client profile.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-4.1.3>.
//!
//! Modelling choices:
//! - The client offers only TLS 1.3, TLS_CHACHA20_POLY1305_SHA256 (0x1303),
//!   and X25519 (29), with an X25519 share already in ClientHello.
//! - This stateless helper takes the offered session ID and retry flag.
//!   client::Hello supplies them from its captured configuration/transcript
//!   and generates ClientHello, establishing that correspondence.
//! - Therefore only a cookie-only HRR can change ClientHello legally: any
//!   HRR key_share selects either an unoffered group or an existing share.
//! - Retry returns the entire cookie extension_data, including its length,
//!   so the ClientHello builder can copy it verbatim (§4.2.2).
//! - Selection returns the peer's raw 32-byte X25519 public input. It is not
//!   a validated shared secret; the §7.4.2 all-zero shared-secret check,
//!   key exchange and traffic-secret derivation live in the separate join.
//! - Complete handshake bodies use the existing format/extension parser.
//!   Its duplicate, placement and structural errors win before negotiation;
//!   absent `supported_versions` is a protocol-version negotiation failure
//!   (or `illegal_parameter`, below). Multi-fault inputs need only one fatal
//!   alert.
//! - RFC 5246 permits a legacy ServerHello to omit its extension field. A
//!   complete body with that form, or a complete valid extension vector that
//!   lacks `supported_versions`, is classified as `protocol_version` before
//!   the TLS 1.3 parser, unless its Random is the HelloRetryRequest value:
//!   §4.1.3 examines the Random first, and such a message is a
//!   HelloRetryRequest, whose missing `supported_versions` is
//!   `missing_extension` ([`parameters`]). Malformed/truncated vectors
//!   remain `decode_error`.
//! - Such a ServerHello "indicat[es] TLS 1.2 or below" (§4.1.3; Appendix D.1:
//!   without `supported_versions` the server has negotiated a prior
//!   version), so its `random` is checked for the downgrade sentinels first,
//!   and a match is `illegal_parameter` instead of `protocol_version`
//!   ([`below_tls13`]). A ServerHello that carries `supported_versions` is
//!   not checked: one selecting a version before TLS 1.3 is already
//!   `illegal_parameter` (§4.2.1), and one selecting TLS 1.3 does not
//!   indicate TLS 1.2 or below, so §4.1.3 asks nothing of its random. Both
//!   sentinels are checked whatever the `legacy_version`, as §4.1.3 asks of
//!   a TLS 1.3 client ("not equal to either of these values").
//! - Body size inherits the transcript limit; invalid local session IDs and
//!   oversized bodies yield internal_error. RFC prose has no step numbers;
//!   comments name the exact field or clause rather than inventing steps.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Accepted server parameters, not peer authentication.
pub enum Selection {
    /// §4.2.8.2: X25519 public input, exactly 32 bytes.
    Share(Seq<u8>),
    /// §4.2.2: opaque cookie extension_data to echo in ClientHello2.
    Retry(Seq<u8>),
}
/// §4.2 extension lookup; format validation separately rejects duplicates.
pub open spec fn extension(es: Seq<crate::spec::Ext>, typ: u16) -> Option<Seq<u8>>
    decreases es.len(),
{
    if es.len() == 0 { None }
    else if es[0].etype == typ { Some(es[0].data) }
    else { extension(es.skip(1), typ) }
}
/// §4.2: only offered SH extensions, plus the HRR cookie exception.
pub open spec fn offered(es: Seq<crate::spec::Ext>, retry: bool) -> bool
    decreases es.len(),
{
    es.len() == 0 || ((es[0].etype == 43 || es[0].etype == 51
        || (retry && es[0].etype == 44)) && offered(es.skip(1), retry))
}
/// §4.2.1 selected_version first; §4.1.3 session echo, cipher and compression.
/// RFC 8446 Appendix D.1: no selected-version extension identifies a legacy
/// server response, which this TLS 1.3-only client rejects with
/// protocol_version, or with illegal_parameter if its random carries a
/// §4.1.3 downgrade sentinel ([`below_tls13`]).
pub open spec fn parameters(sh: crate::spec::ServerHello, session_id: Seq<u8>) -> Option<u8> {
    match extension(sh.extensions, 43) {
        // §4.1.4: "The server's extensions MUST contain "supported_versions"."
        // No alert is named; §6.2 missing_extension is "a handshake message
        // not containing an extension that is mandatory to send for the
        // offered TLS version". A HelloRetryRequest is a TLS 1.3 message
        // (its Random says so, §4.1.3), so it does not indicate TLS 1.2.
        None => if crate::spec::is_hello_retry_request(sh) { Some(crate::spec::MISSING_EXTENSION) }
            else { Some(below_tls13(sh.random)) },
        Some(data) => match crate::spec::read_supported_versions_sh(data) {
            None => Some(50),
            Some(version) => if version != 0x0304 { Some(47) }
                else if sh.session_id_echo != session_id || sh.cipher_suite != 0x1303
                    || sh.compression != 0 { Some(47) }
                else { None },
        },
    }
}
/// §4.1.4 second/no-op retry, §4.2.8 selected_group checks, §4.2.2 cookie.
pub open spec fn retry(sh: crate::spec::ServerHello, retried: bool) -> Result<Selection, u8> {
    if retried { Err(10) }
    else if extension(sh.extensions, 51) is Some { Err(47) }
    else {
        match extension(sh.extensions, 44) {
            None => Err(47),
            Some(data) => match crate::spec::read_cookie(data) {
                None => Err(50),
                Some(_) => Ok(Selection::Retry(data)),
            },
        }
    }
}
/// §4.2.8 server_share is required without PSK; §4.2.8.2 X25519 length.
pub open spec fn share(sh: crate::spec::ServerHello) -> Result<Selection, u8> {
    match extension(sh.extensions, 51) {
        None => Err(109),
        Some(data) => match crate::spec::read_key_share_sh(data) {
            None => Err(50),
            Some(key) => if key.group != 29 || key.key_exchange.len() != 32 { Err(47) }
                else { Ok(Selection::Share(key.key_exchange)) },
        },
    }
}
/// RFC 8446 §4.1.3: the last 8 bytes of a TLS 1.3 server's Random when it
/// negotiates TLS 1.2: "44 4F 57 4E 47 52 44 01".
pub open spec fn downgrade_tls12() -> Seq<u8> {
    seq![0x44u8, 0x4F, 0x57, 0x4E, 0x47, 0x52, 0x44, 0x01]
}
/// RFC 8446 §4.1.3: the last 8 bytes of a TLS 1.3 server's Random when it
/// negotiates TLS 1.1 or below: "44 4F 57 4E 47 52 44 00".
pub open spec fn downgrade_tls11() -> Seq<u8> {
    seq![0x44u8, 0x4F, 0x57, 0x4E, 0x47, 0x52, 0x44, 0x00]
}
/// RFC 8446 §4.1.3: "TLS 1.3 clients receiving a ServerHello indicating
/// TLS 1.2 or below MUST check that the last 8 bytes are not equal to either
/// of these values." `random` is the 32-byte `Random`.
pub open spec fn downgrade_sentinel(random: Seq<u8>) -> bool {
    random.len() == 32 && (random.subrange(24, 32) == downgrade_tls12()
        || random.subrange(24, 32) == downgrade_tls11())
}
/// RFC 8446 §4.1.3: the alert for a ServerHello indicating TLS 1.2 or below.
/// The sentinel is checked first: "If a match is found, the client MUST
/// abort the handshake with an "illegal_parameter" alert." Without one, this
/// TLS 1.3-only client shares no version with the server (Appendix D.1):
/// protocol_version.
pub open spec fn below_tls13(random: Seq<u8>) -> u8 {
    if downgrade_sentinel(random) { crate::spec::ILLEGAL_PARAMETER } else { crate::spec::PROTOCOL_VERSION }
}
/// §4.1.3 `Random random`: the 32 bytes of a ServerHello body after its
/// two-byte `legacy_version`; empty for a body too short to hold them, which
/// `legacy_server_hello_without_supported_versions` never accepts.
pub open spec fn server_random(body: Seq<u8>) -> Seq<u8> {
    if body.len() < 34 { Seq::empty() } else { body.subrange(2, 34) }
}
/// §4.1.3/§4.1.4 acceptance after format checks.
pub open spec fn parsed(sh: crate::spec::ServerHello, session_id: Seq<u8>, retried: bool) -> Result<Selection, u8> {
    // Appendix D.5: "Any endpoint receiving a Hello message with ...
    // ServerHello.legacy_version set to 0x0300 MUST abort the handshake with a
    // "protocol_version" alert", more specific than §4.2.1's "MUST ignore".
    if sh.legacy_version == 0x0300 { Err(crate::spec::PROTOCOL_VERSION) }
    // §4.1.4: "Upon receipt of a HelloRetryRequest, the client MUST check the
    // legacy_version ... as specified in Section 4.1.3", which says "the
    // legacy_version field MUST be set to 0x0303". No alert is named; §6's
    // note makes a semantically invalid value illegal_parameter.
    else if crate::spec::is_hello_retry_request(sh) && sh.legacy_version != 0x0303 { Err(crate::spec::ILLEGAL_PARAMETER) }
    else {
        match parameters(sh, session_id) {
            Some(alert) => Err(alert),
            None => {
                let is_retry = crate::spec::is_hello_retry_request(sh);
                if !offered(sh.extensions, is_retry) { Err(110) }
                else if is_retry { retry(sh, retried) }
                else { share(sh) }
            },
        }
    }
}
/// §4.1.3 and §4.1.4: accept one complete ServerHello/HRR body.
pub open spec fn validate(session_id: Seq<u8>, retried: bool, body: Seq<u8>) -> Result<Selection, u8> {
    if session_id.len() > 32 || body.len() > crate::transcript::spec::MAX_BODY { Err(80) }
    // §4.1.3: "Upon receiving a message with type server_hello,
    // implementations MUST first examine the Random value and, if it matches
    // this value, process it as described in Section 4.1.4", so a
    // HelloRetryRequest is never read as a legacy ServerHello.
    else if crate::spec::legacy_server_hello_without_supported_versions(body)
        && server_random(body) != crate::spec::hrr_random() {
        // RFC 8446 §4.1.3: without supported_versions the ServerHello
        // indicates TLS 1.2 or below, so the downgrade sentinel decides the
        // alert before the version mismatch does (below_tls13).
        Err(below_tls13(server_random(body)))
    }
    else {
        match crate::spec::parse_handshake_body(2, body, 32) {
            crate::spec::Res::Err(error) => Err(crate::spec::alert_of(error)),
            crate::spec::Res::Ok(crate::spec::HsMsg::ServerHello(sh)) => parsed(sh, session_id, retried),
            _ => Err(10),
        }
    }
}
} // verus!
