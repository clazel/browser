//! RFC 8446 §4.6: post-handshake messages, NewSessionTicket and KeyUpdate.
//!
//! Modelling choices:
//! - A client that does not resume reads a NewSessionTicket and keeps nothing:
//!   "The client MAY use this PSK for future handshakes". The derivation of its
//!   PSK is still transcribed ([`ticket_psk`]).
//! - `ticket_lifetime`: "Servers MUST NOT use any value greater than 604800
//!   seconds" gives the client no action in the text. By §6's note it is a
//!   syntactically correct, semantically invalid message: `illegal_parameter`.
//! - §4.6.1's other server rules (a fresh `ticket_age_add`, a `ticket_nonce`
//!   "unique across all tickets issued on this connection") are not checked: the
//!   first is not observable, and the second has no stated receiver action and
//!   no effect on a client that does not resume.
//! - `early_data` in a NewSessionTicket holds "max_early_data_size"; a client
//!   without 0-RTT never uses it, so its contents are not decoded.
//! - §4.6.2 Post-handshake authentication: the profile never offers
//!   `post_handshake_auth`, so a post-handshake CertificateRequest is always
//!   `unexpected_message`, as §4.6.2 says.

#[allow(unused_imports)]
use vstd::prelude::*;

use super::extensions::Extension;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;

verus! {

/// §4.6.1's struct NewSessionTicket.
pub struct NewSessionTicket {
    /// `uint32 ticket_lifetime;`
    pub ticket_lifetime: nat,
    /// `uint32 ticket_age_add;`
    pub ticket_age_add: nat,
    /// `opaque ticket_nonce<0..255>;`
    pub ticket_nonce: Seq<u8>,
    /// `opaque ticket<1..2^16-1>;`
    pub ticket: Seq<u8>,
    /// `Extension extensions<0..2^16-2>;`
    pub extensions: Seq<Extension>,
}

/// §4.6.1: the structure, from exactly its bytes.
pub open spec fn read_new_session_ticket(body: Seq<u8>) -> Option<NewSessionTicket> {
    if body.len() < 8 {
        None
    } else {
        match read_vector(body.subrange(8, body.len() as int), 0, 255) {
            None => None,
            Some((ticket_nonce, rest)) => match read_vector(rest, 1, 0xffff) {
                None => None,
                Some((ticket, rest)) => match read_extensions(rest, 0, 0xfffe) {
                    None => None,
                    Some((extensions, rest)) =>
                        if rest.len() != 0 {
                            None
                        } else {
                            Some(NewSessionTicket {
                                ticket_lifetime: read_uint(body, 4),
                                ticket_age_add: read_uint(body.subrange(4, 8), 4),
                                ticket_nonce, ticket, extensions,
                            })
                        },
                },
            },
        }
    }
}

/// §4.6.1: the encoded message.
pub open spec fn write_new_session_ticket(message: NewSessionTicket) -> Seq<u8> {
    write_handshake(ht_new_session_ticket(),
        uint32(message.ticket_lifetime) + uint32(message.ticket_age_add)
            + write_vector(message.ticket_nonce, 255) + write_vector(message.ticket, 0xffff)
            + write_extensions(message.extensions))
}

/// §4.6.1: every failure of a NewSessionTicket.
pub open spec fn new_session_ticket_failures(message: NewSessionTicket) -> Seq<ClientError> {
    fails_if(message.ticket_lifetime > 604800, ClientError::TicketLifetimeTooLong)
    // "Clients MUST ignore unrecognized extensions", and §4.2's table.
    + block_rules_failures(message.extensions, TableMessage::Nst)
}

/// §4.6.1: "The PSK associated with the ticket is computed as:
/// HKDF-Expand-Label(resumption_master_secret, 'resumption', ticket_nonce,
/// Hash.length)".
pub open spec fn ticket_psk(p: Primitives, resumption_master_secret: Seq<u8>, ticket_nonce: Seq<u8>) -> Seq<u8> {
    hkdf_expand_label(p, resumption_master_secret, label_resumption(), ticket_nonce, hash_length())
}

/// §4.6.3 update_not_requested(0).
pub open spec fn update_not_requested() -> nat { 0 }
/// §4.6.3 update_requested(1).
pub open spec fn update_requested() -> nat { 1 }

/// §4.6.3: `struct { KeyUpdateRequest request_update; } KeyUpdate;`
pub struct KeyUpdate {
    /// §4.6.3 request_update.
    pub request_update: nat,
}

/// §4.6.3: the structure, from exactly its bytes. Any byte decodes: "If an
/// implementation receives any other value, it MUST terminate the connection with
/// an 'illegal_parameter' alert", a semantic failure.
pub open spec fn read_key_update(body: Seq<u8>) -> Option<KeyUpdate> {
    if body.len() == 1 { Some(KeyUpdate { request_update: body[0] as nat }) } else { None }
}

/// §4.6.3: the encoded message.
pub open spec fn write_key_update(request_update: nat) -> Seq<u8> {
    write_handshake(ht_key_update(), uint8(request_update))
}

/// §4.6.3: the failure of a KeyUpdate.
pub open spec fn key_update_failures(message: KeyUpdate) -> Seq<ClientError> {
    fails_if(message.request_update != update_not_requested() && message.request_update != update_requested(),
        ClientError::KeyUpdateBadRequest)
}

} // verus!
