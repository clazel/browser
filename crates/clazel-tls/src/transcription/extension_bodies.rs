//! RFC 8446 §4.2: the bodies of the extensions a server may send, in every
//! message a client receives (ServerHello, HelloRetryRequest,
//! EncryptedExtensions, CertificateRequest, a Certificate's entries and
//! NewSessionTicket), their syntax, and the alerts for one that is malformed
//! or breaks its RFC's rules.
//!
//! §4.2's table gives, for each extension, the messages it may appear in, and
//! names the RFC that defines it. The rows a server can send, by message:
//!
//! | Message | Extensions (defining RFC) |
//! |---------|---------------------------|
//! | SH  | key_share, pre_shared_key, supported_versions (8446) |
//! | HRR | key_share, cookie, supported_versions (8446) |
//! | EE  | server_name, max_fragment_length (6066); supported_groups, early_data (8446); use_srtp (5764); heartbeat (6520); application_layer_protocol_negotiation (7301); client_certificate_type, server_certificate_type (7250) |
//! | CR  | status_request (6066, 8446 §4.4.2.1); signature_algorithms, certificate_authorities, oid_filters, signature_algorithms_cert (8446); signed_certificate_timestamp (6962) |
//! | CT  | status_request (6066, 8446 §4.4.2.1); signed_certificate_timestamp (6962) |
//! | NST | early_data (8446) |
//!
//! Sources, read for the sections cited, besides RFC 8446 and RFC 6066 (see
//! `mod.rs` and `server_name`): RFC 5764 §4.1.1 and §4.1.3 (use_srtp); RFC 6520
//! §2 (heartbeat); RFC 6962 §3.3 and §3.3.1 (signed_certificate_timestamp); RFC
//! 7250 §3 (the certificate types); RFC 7301 §3.1 and §3.2 (ALPN). All fetched
//! from rfc-editor.org on 8 November 2026.
//!
//! Modelling choices:
//! - **What is checked, and in what order.** For each extension of a received
//!   block, in order: if §4.2's table has no row for it, nothing here (an
//!   unrecognized extension is ignored, or, in a response, is
//!   `extensions::any_not_offered`'s); if its row does not name this message,
//!   nothing here (`extensions::any_not_specified` rejects it); otherwise its
//!   body is decoded by the syntax of its RFC ([`body_well_formed`]), a failure
//!   being `decode_error` (§6: "cannot be parsed according to the syntax"), and,
//!   if it decodes, the rules its RFC gives a well-formed body are checked
//!   ([`body_semantics_valid`]), a failure being `illegal_parameter`. These
//!   failures come after §4.2's block rules in each message's list
//!   (`alerts`, modelling choice 4 of `mod.rs`).
//! - **A body is checked whether or not it was offered.** "not offered" is its
//!   own failure, earlier in the list; a malformed body of an extension that was
//!   not offered is in the list as well.
//! - **Where the existing checks already decode a body**, this file's check
//!   repeats it: a ServerHello's key_share and supported_versions
//!   (`key_exchange::server_hello_failures`) and a CertificateRequest's
//!   signature_algorithms (`authentication::certificate_request_failures`), so a
//!   malformed one is in the list twice. A HelloRetryRequest's three
//!   extensions are all decoded in §4.1.4's own order
//!   (`key_exchange::hello_retry_request_failures`), so the check is not added
//!   there; [`body_well_formed`] still states their syntax, and the witnesses
//!   show that it agrees.
//! - **The other RFCs' syntax is that of their server form**, in the message
//!   §4.2 places it in: RFC 7301's "exactly one 'ProtocolName'", RFC 7250's
//!   `case server:` arm, RFC 5764's server UseSRTPData, RFC 6066's empty
//!   server_name and its CertificateStatus. "exactly one" protocol name and
//!   "a single SRTPProtectionProfile" are counts of a list whose syntax allows
//!   more, so they are rules of a well-formed body, not syntax.
//! - **A request in a CertificateRequest.** status_request in a
//!   CertificateRequest is "an empty 'status_request' extension" (§4.4.2.1).
//!   signed_certificate_timestamp has a CR row but no text in RFC 8446 or RFC
//!   6962 on what its body is there; it is a request for SCTs, and RFC 6962
//!   §3.3.1's request has "empty 'extension_data'", so the same is required. See
//!   the PR's proposed errata.
//! - **Rules of a well-formed body that are checked** (each by RFC 8446 §6's
//!   note where its own RFC names no alert): RFC 6066 §4, a max_fragment_length
//!   response "that differs from the length it requested"; RFC 6520 §2, "an
//!   unknown mode"; RFC 7301 §3.1, "exactly one 'ProtocolName'", and §3.2, a
//!   protocol the client did not advertise (the server "will only select a
//!   protocol if the client supports it"); RFC 5764 §4.1.1, "a single
//!   SRTPProtectionProfile" that the client offered ("MUST NOT select a value
//!   that the client has not offered"), and §4.1.3's MKI rule; RFC 8446 §4.2.5,
//!   "Any given OID MUST NOT appear more than once in the filters list".
//! - **Not checked**, with the reason: the meaning of DER values
//!   (certificate_authorities' names, oid_filters' OIDs and values, the OCSP
//!   response, each SCT), which certificate validation reads, and §4.2.5's
//!   "anyExtendedKeyUsage OID MUST NOT be used in the request", which needs the
//!   DER of a client certificate this client never has; supported_groups in EE
//!   beyond syntax ("Clients MUST NOT act upon any information found in
//!   'supported_groups' prior to successful completion of the handshake"; reading
//!   its syntax is how a message is parsed at all, not acting on it); which
//!   certificate type a server selected (the profile never offers RFC 7250's
//!   extensions, so a response is always "not offered"); early_data in EE and
//!   pre_shared_key in SH, for the same reason (no early data, no PSK);
//!   max_early_data_size's value (the client never sends early data).
//! - Lists of the other RFCs (protocol names, SRTP profiles) hold numbers or
//!   bytes as their RFCs write them: an SRTPProtectionProfile, `uint8[2]`, is the
//!   number of its two bytes, as `CipherSuite` is in `key_exchange`.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::server_name::*;

verus! {

// --------------------------------------------------------------------------
// RFC 8446's own bodies not decoded elsewhere.
// --------------------------------------------------------------------------

/// §4.2.11: in a ServerHello, `uint16 selected_identity;`.
pub open spec fn read_pre_shared_key_server_hello(data: Seq<u8>) -> Option<nat> {
    if data.len() == 2 { Some(read_uint(data, 2)) } else { None }
}

/// §4.2.10: `struct {} Empty;`, the EarlyDataIndication of an
/// EncryptedExtensions.
pub open spec fn early_data_encrypted_extensions_well_formed(data: Seq<u8>) -> bool {
    data.len() == 0
}

/// §4.2.10: `case new_session_ticket: uint32 max_early_data_size;`.
pub open spec fn read_early_data_new_session_ticket(data: Seq<u8>) -> Option<nat> {
    if data.len() == 4 { Some(read_uint(data, 4)) } else { None }
}

/// §4.2.4: the body of `DistinguishedName authorities<3..2^16-1>`, each an
/// `opaque DistinguishedName<1..2^16-1>`.
pub open spec fn read_distinguished_names(body: Seq<u8>) -> Option<Seq<Seq<u8>>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else {
        match read_vector(body, 1, 0xffff) {
            None => None,
            Some((name, rest)) =>
                if rest.len() >= body.len() {
                    None
                } else {
                    match read_distinguished_names(rest) {
                        None => None,
                        Some(tail) => Some(seq![name] + tail),
                    }
                },
        }
    }
}

/// §4.2.4: `struct { DistinguishedName authorities<3..2^16-1>; }
/// CertificateAuthoritiesExtension;`
pub open spec fn read_certificate_authorities(data: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match read_vector(data, 3, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_distinguished_names(body) } else { None },
        None => None,
    }
}

/// §4.2.5: `struct { opaque certificate_extension_oid<1..2^8-1>; opaque
/// certificate_extension_values<0..2^16-1>; } OIDFilter;`
pub struct OidFilter {
    /// §4.2.5 certificate_extension_oid.
    pub certificate_extension_oid: Seq<u8>,
    /// §4.2.5 certificate_extension_values.
    pub certificate_extension_values: Seq<u8>,
}

/// §4.2.5: the body of `OIDFilter filters<0..2^16-1>` as its entries.
pub open spec fn read_oid_filters(body: Seq<u8>) -> Option<Seq<OidFilter>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else {
        match read_vector(body, 1, 0xff) {
            None => None,
            Some((certificate_extension_oid, after_oid)) => match read_vector(after_oid, 0, 0xffff) {
                None => None,
                Some((certificate_extension_values, rest)) =>
                    if rest.len() >= body.len() {
                        None
                    } else {
                        match read_oid_filters(rest) {
                            None => None,
                            Some(tail) => Some(seq![OidFilter { certificate_extension_oid, certificate_extension_values }] + tail),
                        }
                    },
            },
        }
    }
}

/// §4.2.5: `struct { OIDFilter filters<0..2^16-1>; } OIDFilterExtension;`
pub open spec fn read_oid_filter_extension(data: Seq<u8>) -> Option<Seq<OidFilter>> {
    match read_vector(data, 0, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_oid_filters(body) } else { None },
        None => None,
    }
}

/// The OIDs of a filter list, in order.
pub open spec fn filter_oids(filters: Seq<OidFilter>) -> Seq<Seq<u8>>
    decreases filters.len(),
{
    if filters.len() == 0 {
        seq![]
    } else {
        seq![filters[0].certificate_extension_oid] + filter_oids(filters.subrange(1, filters.len() as int))
    }
}

/// Whether no value of the list appears twice.
pub open spec fn has_no_repeated_bytes(values: Seq<Seq<u8>>) -> bool
    decreases values.len(),
{
    if values.len() == 0 {
        true
    } else {
        let tail = values.subrange(1, values.len() as int);
        !list_has(tail, values[0]) && has_no_repeated_bytes(tail)
    }
}

// --------------------------------------------------------------------------
// RFC 6066 §4 and §8 (with RFC 8446 §4.4.2.1).
// --------------------------------------------------------------------------

/// RFC 6066 §4: `enum{ 2^9(1), 2^10(2), 2^11(3), 2^12(4), (255) }
/// MaxFragmentLength;`, one byte.
pub open spec fn read_max_fragment_length(data: Seq<u8>) -> Option<nat> {
    if data.len() == 1 { Some(data[0] as nat) } else { None }
}

/// RFC 6066 §8: `enum { ocsp(1), (255) } CertificateStatusType;`
pub open spec fn status_type_ocsp() -> nat { 1 }

/// RFC 6066 §8, required by RFC 8446 §4.4.2.1 ("the body of the
/// 'status_request' extension from the server MUST be a CertificateStatus
/// structure"): `struct { CertificateStatusType status_type; select
/// (status_type) { case ocsp: OCSPResponse; } response; } CertificateStatus;`
/// with `opaque OCSPResponse<1..2^24-1>;`. The `select` has one arm, so another
/// status_type cannot be parsed.
pub open spec fn read_certificate_status(data: Seq<u8>) -> Option<Seq<u8>> {
    if data.len() < 1 || data[0] as nat != status_type_ocsp() {
        None
    } else {
        match read_vector(data.subrange(1, data.len() as int), 1, 0xff_ffff) {
            Some((response, rest)) => if rest.len() == 0 { Some(response) } else { None },
            None => None,
        }
    }
}

/// RFC 8446 §4.4.2.1: "A server MAY request that a client present an OCSP
/// response with its certificate by sending an empty 'status_request'
/// extension in its CertificateRequest message."
pub open spec fn status_request_certificate_request_well_formed(data: Seq<u8>) -> bool {
    data.len() == 0
}

// --------------------------------------------------------------------------
// RFC 6962 §3.3.
// --------------------------------------------------------------------------

/// RFC 6962 §3.3: the body of `SerializedSCT sct_list <1..2^16-1>`, each an
/// `opaque SerializedSCT<1..2^16-1>`.
pub open spec fn read_serialized_scts(body: Seq<u8>) -> Option<Seq<Seq<u8>>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else {
        match read_vector(body, 1, 0xffff) {
            None => None,
            Some((sct, rest)) =>
                if rest.len() >= body.len() {
                    None
                } else {
                    match read_serialized_scts(rest) {
                        None => None,
                        Some(tail) => Some(seq![sct] + tail),
                    }
                },
        }
    }
}

/// RFC 6962 §3.3: `struct { SerializedSCT sct_list <1..2^16-1>; }
/// SignedCertificateTimestampList;`, which §3.3.1 puts in "extension_data", and
/// RFC 8446 §4.4.2.1 in the CertificateEntry.
pub open spec fn read_signed_certificate_timestamp_list(data: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match read_vector(data, 1, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_serialized_scts(body) } else { None },
        None => None,
    }
}

/// RFC 6962 §3.3.1: the request form, "empty 'extension_data'"; the form of a
/// CertificateRequest's (see the modelling choices).
pub open spec fn signed_certificate_timestamp_request_well_formed(data: Seq<u8>) -> bool {
    data.len() == 0
}

// --------------------------------------------------------------------------
// RFC 5764 §4.1.1.
// --------------------------------------------------------------------------

/// RFC 5764 §4.1.1: `struct { SRTPProtectionProfiles SRTPProtectionProfiles;
/// opaque srtp_mki<0..255>; } UseSRTPData;`
pub struct UseSrtpData {
    /// `SRTPProtectionProfile SRTPProtectionProfiles<2..2^16-1>;`, each
    /// `uint8 SRTPProtectionProfile[2]` as a number.
    pub profiles: Seq<nat>,
    /// `opaque srtp_mki<0..255>;`
    pub srtp_mki: Seq<u8>,
}

/// RFC 5764 §4.1.1: a UseSRTPData, from exactly its bytes.
pub open spec fn read_use_srtp_data(data: Seq<u8>) -> Option<UseSrtpData> {
    match read_vector(data, 2, 0xffff) {
        None => None,
        Some((profile_bytes, rest)) => match read_uint16_list(profile_bytes) {
            None => None,
            Some(profiles) => match read_vector(rest, 0, 255) {
                Some((srtp_mki, rest)) =>
                    if rest.len() == 0 { Some(UseSrtpData { profiles, srtp_mki }) } else { None },
                None => None,
            },
        },
    }
}

// --------------------------------------------------------------------------
// RFC 6520 §2.
// --------------------------------------------------------------------------

/// RFC 6520 §2 peer_allowed_to_send(1).
pub open spec fn heartbeat_peer_allowed_to_send() -> nat { 1 }
/// RFC 6520 §2 peer_not_allowed_to_send(2).
pub open spec fn heartbeat_peer_not_allowed_to_send() -> nat { 2 }

/// RFC 6520 §2: `struct { HeartbeatMode mode; } HeartbeatExtension;`, an enum
/// of `(255)`, so one byte.
pub open spec fn read_heartbeat_mode(data: Seq<u8>) -> Option<nat> {
    if data.len() == 1 { Some(data[0] as nat) } else { None }
}

// --------------------------------------------------------------------------
// RFC 7301 §3.1.
// --------------------------------------------------------------------------

/// RFC 7301 §3.1: the body of `ProtocolName protocol_name_list<2..2^16-1>`,
/// each an `opaque ProtocolName<1..2^8-1>`.
pub open spec fn read_protocol_names(body: Seq<u8>) -> Option<Seq<Seq<u8>>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else {
        match read_vector(body, 1, 0xff) {
            None => None,
            Some((name, rest)) =>
                if rest.len() >= body.len() {
                    None
                } else {
                    match read_protocol_names(rest) {
                        None => None,
                        Some(tail) => Some(seq![name] + tail),
                    }
                },
        }
    }
}

/// RFC 7301 §3.1: `struct { ProtocolName protocol_name_list<2..2^16-1> }
/// ProtocolNameList;`
pub open spec fn read_protocol_name_list(data: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match read_vector(data, 2, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_protocol_names(body) } else { None },
        None => None,
    }
}

// --------------------------------------------------------------------------
// RFC 7250 §3.
// --------------------------------------------------------------------------

/// RFC 7250 §3: the `case server:` arm of ClientCertTypeExtension and
/// ServerCertTypeExtension, one `CertificateType`, which is a one-byte enum.
pub open spec fn certificate_type_server_well_formed(data: Seq<u8>) -> bool {
    data.len() == 1
}

// --------------------------------------------------------------------------
// The syntax of every body a server may send.
// --------------------------------------------------------------------------

/// Whether `data` meets the syntax of the body of `extension_type` in `message`,
/// for every pair §4.2's table allows in a message a client receives. Other
/// pairs have no syntax to check here (see the modelling choices).
pub open spec fn body_well_formed(extension_type: nat, message: TableMessage, data: Seq<u8>) -> bool {
    let t = extension_type;
    match message {
        TableMessage::Sh =>
            // §4.2.8 KeyShareServerHello.
            if t == ext_key_share() { read_key_share_server_hello(data) is Some }
            // §4.2.11 `uint16 selected_identity`.
            else if t == ext_pre_shared_key() { read_pre_shared_key_server_hello(data) is Some }
            // §4.2.1 `ProtocolVersion selected_version`.
            else if t == ext_supported_versions() { read_supported_versions_server(data) is Some }
            else { true },
        TableMessage::Hrr =>
            // §4.2.8 KeyShareHelloRetryRequest.
            if t == ext_key_share() { read_key_share_hello_retry_request(data) is Some }
            // §4.2.2 Cookie.
            else if t == ext_cookie() { read_cookie(data) is Some }
            // §4.2.1 `ProtocolVersion selected_version`.
            else if t == ext_supported_versions() { read_supported_versions_server(data) is Some }
            else { true },
        TableMessage::Ee =>
            // RFC 6066 §3: "SHALL be empty".
            if t == ext_server_name() { server_name_response_well_formed(data) }
            // RFC 6066 §4 MaxFragmentLength.
            else if t == ext_max_fragment_length() { read_max_fragment_length(data) is Some }
            // §4.2.7 NamedGroupList.
            else if t == ext_supported_groups() { read_named_group_list(data) is Some }
            // RFC 5764 §4.1.1 UseSRTPData.
            else if t == ext_use_srtp() { read_use_srtp_data(data) is Some }
            // RFC 6520 §2 HeartbeatExtension.
            else if t == ext_heartbeat() { read_heartbeat_mode(data) is Some }
            // RFC 7301 §3.1 ProtocolNameList.
            else if t == ext_application_layer_protocol_negotiation() { read_protocol_name_list(data) is Some }
            // RFC 7250 §3, `case server:`.
            else if t == ext_client_certificate_type() { certificate_type_server_well_formed(data) }
            else if t == ext_server_certificate_type() { certificate_type_server_well_formed(data) }
            // §4.2.10 `case encrypted_extensions: Empty;`.
            else if t == ext_early_data() { early_data_encrypted_extensions_well_formed(data) }
            else { true },
        TableMessage::Cr =>
            // §4.4.2.1: "an empty 'status_request' extension".
            if t == ext_status_request() { status_request_certificate_request_well_formed(data) }
            // §4.2.3 SignatureSchemeList.
            else if t == ext_signature_algorithms() { read_signature_scheme_list(data) is Some }
            // RFC 6962 §3.3.1's request form; see the modelling choices.
            else if t == ext_signed_certificate_timestamp() { signed_certificate_timestamp_request_well_formed(data) }
            // §4.2.4 CertificateAuthoritiesExtension.
            else if t == ext_certificate_authorities() { read_certificate_authorities(data) is Some }
            // §4.2.5 OIDFilterExtension.
            else if t == ext_oid_filters() { read_oid_filter_extension(data) is Some }
            // §4.2.3: "signature_algorithms_cert ... with the same syntax".
            else if t == ext_signature_algorithms_cert() { read_signature_scheme_list(data) is Some }
            else { true },
        TableMessage::Ct =>
            // §4.4.2.1: "MUST be a CertificateStatus structure".
            if t == ext_status_request() { read_certificate_status(data) is Some }
            // §4.4.2.1, RFC 6962 §3.3 SignedCertificateTimestampList.
            else if t == ext_signed_certificate_timestamp() { read_signed_certificate_timestamp_list(data) is Some }
            else { true },
        TableMessage::Nst =>
            // §4.2.10 `case new_session_ticket: uint32 max_early_data_size;`.
            if t == ext_early_data() { read_early_data_new_session_ticket(data) is Some }
            else { true },
        // A client sends a ClientHello and never receives one.
        TableMessage::Ch => true,
    }
}

// --------------------------------------------------------------------------
// The rules of a well-formed body.
// --------------------------------------------------------------------------

/// The protocols a ClientHello's ALPN extension advertises.
pub open spec fn offered_protocols(offered: Seq<Extension>) -> Seq<Seq<u8>> {
    match find_extension(offered, ext_application_layer_protocol_negotiation()) {
        Some(data) => match read_protocol_name_list(data) {
            Some(names) => names,
            None => seq![],
        },
        None => seq![],
    }
}

/// RFC 7301 §3.1: "the 'ProtocolNameList' MUST contain exactly one
/// 'ProtocolName'"; §3.2: "It is expected that a server will ... only select a
/// protocol if the client supports it", read as: one the client advertised.
pub open spec fn alpn_response_valid(offered: Seq<Extension>, names: Seq<Seq<u8>>) -> bool {
    names.len() == 1 && list_has(offered_protocols(offered), names[0])
}

/// RFC 5764 §4.1.1: "The extension_data field MUST contain a UseSRTPData value
/// with a single SRTPProtectionProfile value that the server has chosen ... The
/// server MUST NOT select a value that the client has not offered." §4.1.3: "If
/// the client detects a nonzero-length MKI in the server's response that is
/// different than the one the client offered, then the client MUST abort the
/// handshake and SHOULD send an invalid_parameter alert." There is no
/// invalid_parameter in TLS; the evident intent is illegal_parameter, which
/// `alerts::required_alert` sends. See the PR's proposed errata.
pub open spec fn use_srtp_response_valid(offered: Seq<Extension>, response: UseSrtpData) -> bool {
    match find_extension(offered, ext_use_srtp()) {
        // Not offered: `extensions::any_not_offered`'s failure.
        None => true,
        Some(offered_data) => match read_use_srtp_data(offered_data) {
            None => true,
            Some(offer) => {
                &&& response.profiles.len() == 1
                &&& list_has(offer.profiles, response.profiles[0])
                &&& (response.srtp_mki.len() == 0 || response.srtp_mki == offer.srtp_mki)
            },
        },
    }
}

/// RFC 6066 §4: "if a client receives a maximum fragment length negotiation
/// response that differs from the length it requested, it MUST also abort the
/// handshake with an 'illegal_parameter' alert." The request is the one byte of
/// the client's own extension. (A value outside the four of the enum differs
/// from any request a client may make, since "The allowed values for this field
/// are: 2^9, 2^10, 2^11, and 2^12".)
pub open spec fn max_fragment_length_response_valid(offered: Seq<Extension>, length: nat) -> bool {
    match find_extension(offered, ext_max_fragment_length()) {
        None => true,
        Some(requested) => read_max_fragment_length(requested) == Some(length),
    }
}

/// The rules of a well-formed body of `extension_type` in `message`, against the
/// extensions the client sent (`offered`), for the pairs whose RFC has any. The
/// body is assumed to have passed [`body_well_formed`].
pub open spec fn body_semantics_valid(offered: Seq<Extension>, extension_type: nat, message: TableMessage, data: Seq<u8>) -> bool {
    let t = extension_type;
    match message {
        TableMessage::Ee =>
            if t == ext_max_fragment_length() {
                max_fragment_length_response_valid(offered, data[0] as nat)
            } else if t == ext_heartbeat() {
                // RFC 6520 §2: "Upon reception of an unknown mode, an error Alert
                // message using illegal_parameter as its AlertDescription MUST be
                // sent in response."
                data[0] as nat == heartbeat_peer_allowed_to_send() || data[0] as nat == heartbeat_peer_not_allowed_to_send()
            } else if t == ext_application_layer_protocol_negotiation() {
                alpn_response_valid(offered, read_protocol_name_list(data)->0)
            } else if t == ext_use_srtp() {
                use_srtp_response_valid(offered, read_use_srtp_data(data)->0)
            } else {
                true
            },
        TableMessage::Cr =>
            if t == ext_oid_filters() {
                // §4.2.5: "Any given OID MUST NOT appear more than once in the
                // filters list."
                has_no_repeated_bytes(filter_oids(read_oid_filter_extension(data)->0))
            } else {
                true
            },
        _ => true,
    }
}

/// The failures of one extension's body (see the modelling choices).
pub open spec fn one_body_failures(offered: Seq<Extension>, extension: Extension, message: TableMessage) -> Seq<ClientError> {
    if extension_table(extension.extension_type) is None || recognized_but_not_specified(extension.extension_type, message) {
        seq![]
    } else if !body_well_formed(extension.extension_type, message, extension.extension_data) {
        // §6: "cannot be parsed according to the syntax".
        seq![ClientError::Malformed]
    } else {
        fails_if(!body_semantics_valid(offered, extension.extension_type, message, extension.extension_data),
            ClientError::ExtensionBodyInvalid(extension.extension_type))
    }
}

/// §4.2 and the RFCs of its table: the failures of the bodies of a block a client
/// receives in `message`, in the block's order. `offered` is the ClientHello's
/// extensions, for a block of responses; a CertificateRequest's and a
/// NewSessionTicket's rules do not depend on it.
pub open spec fn extension_body_failures(offered: Seq<Extension>, extensions: Seq<Extension>, message: TableMessage) -> Seq<ClientError>
    decreases extensions.len(),
{
    if extensions.len() == 0 {
        seq![]
    } else {
        one_body_failures(offered, extensions[0], message)
            + extension_body_failures(offered, extensions.subrange(1, extensions.len() as int), message)
    }
}

} // verus!
