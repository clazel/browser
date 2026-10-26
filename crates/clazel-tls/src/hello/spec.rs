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
//!   absent `supported_versions` is a protocol-version negotiation failure.
//!   Multi-fault inputs need only one fatal alert.
//! - For legacy-version fallback, absent and explicit zero-length ServerHello
//!   extension fields both map to an empty extension sequence. The structure
//!   model does not retain which encoding was used; the writer emits the
//!   length-prefixed form, so byte-for-byte round-trip preservation is not claimed.
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
/// server response, which this TLS 1.3-only client rejects with protocol_version.
pub open spec fn parameters(sh: crate::spec::ServerHello, session_id: Seq<u8>) -> Option<u8> {
    match extension(sh.extensions, 43) {
        None => Some(crate::spec::PROTOCOL_VERSION),
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
/// §4.1.3/§4.1.4 acceptance after format checks.
pub open spec fn parsed(sh: crate::spec::ServerHello, session_id: Seq<u8>, retried: bool) -> Result<Selection, u8> {
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
/// §4.1.3 and §4.1.4: accept one complete ServerHello/HRR body.
pub open spec fn validate(session_id: Seq<u8>, retried: bool, body: Seq<u8>) -> Result<Selection, u8> {
    if session_id.len() > 32 || body.len() > crate::transcript::spec::MAX_BODY { Err(80) }
    else {
        match crate::spec::parse_handshake_body(2, body, 32) {
            crate::spec::Res::Err(error) => Err(crate::spec::alert_of(error)),
            crate::spec::Res::Ok(crate::spec::HsMsg::ServerHello(sh)) => parsed(sh, session_id, retried),
            _ => Err(10),
        }
    }
}
} // verus!
