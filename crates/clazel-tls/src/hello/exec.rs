//! RFC 8446 §4.1.3/§4.1.4 server parameter selection, before key derivation.
use crate::types::{Extension, HsMsg, ServerHello};
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Borrowed parameters accepted from one server Hello; not authentication.
#[derive(Debug, PartialEq, Eq)]
pub enum Selection<'a> {
    /// Raw X25519 peer public input; key agreement must still reject zero output.
    Share(&'a [u8]),
    /// Exact cookie extension_data, including the encoded length, to echo.
    Retry(&'a [u8]),
}
impl<'a> View for Selection<'a> {
    type V = super::spec::Selection;
    open spec fn view(&self) -> super::spec::Selection {
        match self {
            Self::Share(bytes) => super::spec::Selection::Share(bytes@),
            Self::Retry(bytes) => super::spec::Selection::Retry(bytes@),
        }
    }
}
/// View of a fallible server selection.
pub open spec fn result_view(out: Result<Selection<'_>, u8>) -> Result<super::spec::Selection, u8> {
    match out { Ok(s) => Ok(s@), Err(e) => Err(e) }
}
spec fn option_view(out: Option<&[u8]>) -> Option<Seq<u8>> {
    match out { Some(b) => Some(b@), None => None }
}
/// §4.2: look up the response data of one extension type.
fn extension<'a>(es: &[Extension<'a>], typ: u16) -> (out: Option<&'a [u8]>)
    ensures option_view(out) == super::spec::extension(crate::types::views(es@), typ),
{
    let ghost all = crate::types::views(es@);
    let mut i = 0;
    proof { assert(all.skip(0) =~= all); }
    while i < es.len()
        invariant i <= es.len(), all == crate::types::views(es@),
            super::spec::extension(all, typ) == super::spec::extension(all.skip(i as int), typ),
        decreases es.len() - i,
    {
        let e = es.get(i)?;
        proof {
            assert(all.skip(i as int)[0] == e@);
            assert(all.skip(i as int).skip(1) =~= all.skip(i + 1));
        }
        if e.etype == typ { return Some(e.data); }
        i = i.checked_add(1)?;
    }
    proof { assert(all.skip(i as int) =~= Seq::empty()); }
    None
}
/// §4.2: enforce offered responses and the HRR cookie exception.
fn offered(es: &[Extension<'_>], retry: bool) -> (out: bool)
    ensures out == super::spec::offered(crate::types::views(es@), retry),
{
    let ghost all = crate::types::views(es@);
    let mut i = 0;
    proof { assert(all.skip(0) =~= all); }
    while i < es.len()
        invariant i <= es.len(), all == crate::types::views(es@),
            super::spec::offered(all, retry) == super::spec::offered(all.skip(i as int), retry),
        decreases es.len() - i,
    {
        let e = match es.get(i) { Some(e) => e, None => return true };
        proof {
            assert(all.skip(i as int)[0] == e@);
            assert(all.skip(i as int).skip(1) =~= all.skip(i + 1));
        }
        if e.etype != 43 && e.etype != 51 && !(retry && e.etype == 44) { return false; }
        i = match i.checked_add(1) { Some(next) => next, None => return true };
    }
    proof { assert(all.skip(i as int) =~= Seq::empty()); }
    true
}
/// §4.2.1 selected version first; §4.1.3 session echo, cipher and compression.
fn parameters(sh: &ServerHello<'_>, session_id: &[u8]) -> (out: Option<u8>)
    ensures out == super::spec::parameters(sh@, session_id@),
{
    match extension(sh.extensions.as_slice(), 43) {
        None => Some(109),
        Some(data) => match crate::extension::supported_versions_sh(data) {
            None => Some(50),
            Some(version) => {
                if version != 0x0304 { return Some(47); }
                let same_session = crate::handshake::bytes_eq(sh.session_id_echo, session_id);
                if !same_session || sh.cipher_suite != 0x1303 || sh.compression != 0 { Some(47) }
                else { None }
            },
        },
    }
}
/// §4.1.4 repeat/no-op HRR and §4.2.8 already-offered group rejection.
fn retry<'a>(sh: &ServerHello<'a>, retried: bool) -> (out: Result<Selection<'a>, u8>)
    ensures result_view(out) == super::spec::retry(sh@, retried),
{
    if retried { return Err(10); }
    if extension(sh.extensions.as_slice(), 51).is_some() { return Err(47); }
    match extension(sh.extensions.as_slice(), 44) {
        None => Err(47),
        Some(data) => match crate::extension::cookie(data) {
            None => Err(50),
            Some(_) => Ok(Selection::Retry(data)),
        },
    }
}
/// §4.2.8 and §4.2.8.2: the offered X25519 share and its wire length.
fn share<'a>(sh: &ServerHello<'a>) -> (out: Result<Selection<'a>, u8>)
    ensures result_view(out) == super::spec::share(sh@),
{
    match extension(sh.extensions.as_slice(), 51) {
        None => Err(109),
        Some(data) => match crate::extension::key_share_sh(data) {
            None => Err(50),
            Some(key) => if key.group != 29 || key.key_exchange.len() != 32 { Err(47) }
                else { Ok(Selection::Share(key.key_exchange)) },
        },
    }
}
/// §4.1.3/§4.1.4: apply negotiation checks after the format parser.
fn parsed<'a>(sh: ServerHello<'a>, session_id: &[u8], retried: bool) -> (out: Result<Selection<'a>, u8>)
    ensures result_view(out) == super::spec::parsed(sh@, session_id@, retried),
{
    if let Some(alert) = parameters(&sh, session_id) { return Err(alert); }
    let is_retry = crate::handshake::is_hello_retry_request(&sh);
    if !offered(sh.extensions.as_slice(), is_retry) { Err(110) }
    else if is_retry { retry(&sh, retried) }
    else { share(&sh) }
}
/// RFC 8446 §4.1.3/§4.1.4: accept one complete server Hello body.
/// The caller must supply the session ID in the actual ClientHello and
/// track accepted retries. This function emits no keys or application data.
pub fn validate<'a>(session_id: &[u8], retried: bool, body: &'a [u8]) -> (out: Result<Selection<'a>, u8>)
    ensures super::contract::validate_ensures(session_id@, retried, body@, result_view(out)),
{
    hide(crate::spec::parse_handshake_body);
    if session_id.len() > 32 || body.len() > crate::transcript::spec::MAX_BODY { return Err(80); }
    match crate::handshake::parse_handshake_body(2, body, 32) {
        Err(error) => Err(crate::encode::alert_for(error).description),
        Ok(HsMsg::ServerHello(sh)) => parsed(sh, session_id, retried),
        _ => Err(10),
    }
}
} // verus!
