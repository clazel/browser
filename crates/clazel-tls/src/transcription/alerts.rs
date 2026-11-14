//! RFC 8446 §6, the Alert protocol: the alerts, closure against error, and
//! which alert each error requires.
//!
//! Modelling choices:
//! - `AlertLevel` and `AlertDescription` are `nat`; [`read_alert`] keeps
//!   unknown values, since "Unknown Alert types MUST be treated as error
//!   alerts". The level is decoded and then ignored ("the 'level' field can
//!   safely be ignored"; "regardless of the AlertLevel in the message").
//! - "closure alerts" are §6.1's two, `close_notify` and `user_canceled`
//!   ([`is_closure_alert`]). §6.2's "All alerts defined below in this section,
//!   as well as all unknown alerts, are universally considered fatal"
//!   then covers the rest. §6.1's wording "This alert generally has
//!   AlertLevel=warning" fixes how `user_canceled` is sent, not its class.
//! - [`ClientError`] names every condition a client detects, and
//!   [`required_alert`] is the alert for it. "MUST send alert X if it sends
//!   any alert" (§6.2): the model always sends one (`connection::alert_record`).
//! - Conditions for which the RFC says only "abort" or "MUST", and §6's note on
//!   syntax against semantics decides, are marked "(by §6's note)" below.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §6 AlertLevel warning(1).
pub open spec fn level_warning() -> nat { 1 }
/// §6 AlertLevel fatal(2).
pub open spec fn level_fatal() -> nat { 2 }

/// §6 close_notify(0).
pub open spec fn ad_close_notify() -> nat { 0 }
/// §6 unexpected_message(10).
pub open spec fn ad_unexpected_message() -> nat { 10 }
/// §6 bad_record_mac(20).
pub open spec fn ad_bad_record_mac() -> nat { 20 }
/// §6 record_overflow(22).
pub open spec fn ad_record_overflow() -> nat { 22 }
/// §6 handshake_failure(40).
pub open spec fn ad_handshake_failure() -> nat { 40 }
/// §6 bad_certificate(42).
pub open spec fn ad_bad_certificate() -> nat { 42 }
/// §6 unsupported_certificate(43).
pub open spec fn ad_unsupported_certificate() -> nat { 43 }
/// §6 certificate_revoked(44).
pub open spec fn ad_certificate_revoked() -> nat { 44 }
/// §6 certificate_expired(45).
pub open spec fn ad_certificate_expired() -> nat { 45 }
/// §6 certificate_unknown(46).
pub open spec fn ad_certificate_unknown() -> nat { 46 }
/// §6 illegal_parameter(47).
pub open spec fn ad_illegal_parameter() -> nat { 47 }
/// §6 unknown_ca(48).
pub open spec fn ad_unknown_ca() -> nat { 48 }
/// §6 access_denied(49).
pub open spec fn ad_access_denied() -> nat { 49 }
/// §6 decode_error(50).
pub open spec fn ad_decode_error() -> nat { 50 }
/// §6 decrypt_error(51).
pub open spec fn ad_decrypt_error() -> nat { 51 }
/// §6 protocol_version(70).
pub open spec fn ad_protocol_version() -> nat { 70 }
/// §6 insufficient_security(71).
pub open spec fn ad_insufficient_security() -> nat { 71 }
/// §6 internal_error(80).
pub open spec fn ad_internal_error() -> nat { 80 }
/// §6 inappropriate_fallback(86).
pub open spec fn ad_inappropriate_fallback() -> nat { 86 }
/// §6 user_canceled(90).
pub open spec fn ad_user_canceled() -> nat { 90 }
/// §6 missing_extension(109).
pub open spec fn ad_missing_extension() -> nat { 109 }
/// §6 unsupported_extension(110).
pub open spec fn ad_unsupported_extension() -> nat { 110 }
/// §6 unrecognized_name(112).
pub open spec fn ad_unrecognized_name() -> nat { 112 }
/// §6 bad_certificate_status_response(113).
pub open spec fn ad_bad_certificate_status_response() -> nat { 113 }
/// §6 unknown_psk_identity(115).
pub open spec fn ad_unknown_psk_identity() -> nat { 115 }
/// §6 certificate_required(116).
pub open spec fn ad_certificate_required() -> nat { 116 }
/// §6 no_application_protocol(120).
pub open spec fn ad_no_application_protocol() -> nat { 120 }

/// §6.1: the closure alerts. Every other value, unknown ones included, is an
/// error alert (§6, §6.2).
pub open spec fn is_closure_alert(description: nat) -> bool {
    description == ad_close_notify() || description == ad_user_canceled()
}

/// §6: `struct { AlertLevel level; AlertDescription description; } Alert;`, as
/// (level, description). §5.1: "a record with an Alert type MUST contain
/// exactly one message", so the bytes are exactly two.
pub open spec fn read_alert(fragment: Seq<u8>) -> Option<(nat, nat)> {
    if fragment.len() == 2 {
        Some((fragment[0] as nat, fragment[1] as nat))
    } else {
        None
    }
}

/// §6: "All the alerts listed in Section 6.2 MUST be sent with
/// AlertLevel=fatal"; the two of §6.1 are sent as warning (§6.1 says so of
/// user_canceled; RFC 8448's traces show `01 00` for close_notify).
pub open spec fn alert_level_to_send(description: nat) -> nat {
    if is_closure_alert(description) { level_warning() } else { level_fatal() }
}

/// §6: the encoded Alert.
pub open spec fn write_alert(description: nat) -> Seq<u8> {
    seq![alert_level_to_send(description) as u8, description as u8]
}

/// §4.4.2.2: "an appropriate certificate-related alert"; §6.2's certificate
/// alerts, plus the OCSP one, which concerns a certificate's status.
pub open spec fn is_certificate_alert(description: nat) -> bool {
    description == ad_bad_certificate()
    || description == ad_unsupported_certificate()
    || description == ad_certificate_revoked()
    || description == ad_certificate_expired()
    || description == ad_certificate_unknown()
    || description == ad_unknown_ca()
    || description == ad_bad_certificate_status_response()
}

/// Every error a client detects. The doc comment quotes the rule.
pub enum ClientError {
    // ----- unexpected_message -----
    /// §4: "A peer which receives a handshake message in an unexpected order
    /// MUST abort the handshake with an 'unexpected_message' alert."
    UnexpectedHandshakeMessage,
    /// §4.1.4: "If a client receives a second HelloRetryRequest in the same
    /// connection ... it MUST abort the handshake with an 'unexpected_message'
    /// alert."
    SecondHelloRetryRequest,
    /// §4.5: "Servers MUST NOT send this message, and clients receiving it MUST
    /// terminate the connection with an 'unexpected_message' alert."
    EndOfEarlyDataReceived,
    /// §4.6.2: "A client that receives a CertificateRequest message without
    /// having sent the 'post_handshake_auth' extension MUST send an
    /// 'unexpected_message' fatal alert."
    PostHandshakeAuthNotOffered,
    /// §4.6.3: "Implementations that receive a KeyUpdate message prior to
    /// receiving a Finished message MUST terminate the connection with an
    /// 'unexpected_message' alert."
    KeyUpdateBeforeFinished,
    /// §5: "An implementation which receives any other change_cipher_spec value
    /// ... MUST abort the handshake with an 'unexpected_message' alert."
    ChangeCipherSpecBadValue,
    /// §5: "or which receives a protected change_cipher_spec record".
    ChangeCipherSpecProtected,
    /// §5: "If a TLS implementation receives an unexpected record type, it MUST
    /// terminate the connection with an 'unexpected_message' alert", which
    /// also covers a change_cipher_spec "after the peer's Finished message",
    /// premature Application Data (§6.2), and a plaintext record where
    /// protection is engaged (§5.1, §6).
    UnexpectedRecordType,
    /// §5.1: "Handshake messages MUST NOT be interleaved with other record
    /// types." The bullet names no alert; §6.2's unexpected_message is "An
    /// inappropriate message". See `connection::receive_record` for the
    /// exception for change_cipher_spec.
    InterleavedRecord,
    /// §5.1: "Implementations MUST verify that all messages immediately
    /// preceding a key change align with a record boundary; if not, then they
    /// MUST terminate the connection with an 'unexpected_message' alert."
    KeyChangeNotAligned,
    /// §5.4: "Implementations MUST NOT send Handshake and Alert records that
    /// have a zero-length TLSInnerPlaintext.content; if such a message is
    /// received, the receiving implementation MUST terminate the connection
    /// with an 'unexpected_message' alert."
    ZeroLengthContent,
    /// §5.4: "If a receiving implementation does not find a non-zero octet in
    /// the cleartext, it MUST terminate the connection with an
    /// 'unexpected_message' alert."
    NoContentType,

    // ----- illegal_parameter -----
    /// §4.1.3: "A client which receives a legacy_session_id_echo field that
    /// does not match what it sent in the ClientHello MUST abort the handshake
    /// with an 'illegal_parameter' alert."
    SessionIdEchoMismatch,
    /// §4.1.3: "A client which receives a cipher suite that was not offered
    /// MUST abort the handshake with an 'illegal_parameter' alert."
    CipherSuiteNotOffered,
    /// §4.1.3: "legacy_compression_method: A single byte which MUST have the
    /// value 0." (by §6's note)
    CompressionMethodNotZero,
    /// §4.1.3: "If a match is found, the client MUST abort the handshake with
    /// an 'illegal_parameter' alert."
    DowngradeSentinel,
    /// §4.1.4: "the client MUST check the legacy_version ... as specified in
    /// Section 4.1.3", whose text is "MUST be set to 0x0303". (by §6's note)
    RetryLegacyVersion,
    /// §4.1.4: "Clients MUST abort the handshake with an 'illegal_parameter'
    /// alert if the HelloRetryRequest would not result in any change in the
    /// ClientHello."
    RetryWithoutChange,
    /// §4.1.4: "clients MUST check that the cipher suite supplied in the
    /// ServerHello is the same as that in the HelloRetryRequest and otherwise
    /// abort the handshake with an 'illegal_parameter' alert."
    CipherSuiteChanged,
    /// §4.1.4: "a client MUST abort the handshake with an 'illegal_parameter'
    /// alert if the value changes."
    SelectedVersionChanged,
    /// §4.2.1: "If the 'supported_versions' extension in the ServerHello
    /// contains a version not offered by the client or contains a version
    /// prior to TLS 1.3, the client MUST abort the handshake with an
    /// 'illegal_parameter' alert."
    SelectedVersionNotAcceptable,
    /// §4.2: "If an implementation receives an extension which it recognizes
    /// and which is not specified for the message in which it appears, it MUST
    /// abort the handshake with an 'illegal_parameter' alert." §4.3.1 repeats
    /// it for EncryptedExtensions.
    ExtensionNotSpecifiedForMessage,
    /// §4.2: "There MUST NOT be more than one extension of the same type in a
    /// given extension block." (by §6's note)
    DuplicateExtension,
    /// §4.2.8: "(1) the selected_group field corresponds to a group which was
    /// provided in the 'supported_groups' extension in the original
    /// ClientHello".
    RetryGroupNotOffered,
    /// §4.2.8: "(2) the selected_group field does not correspond to a group
    /// which was provided in the 'key_share' extension in the original
    /// ClientHello".
    RetryGroupAlreadyShared,
    /// §4.2.8: "server_share: A single KeyShareEntry value that is in the same
    /// group as one of the client's shares." (by §6's note)
    ServerShareGroupNotOffered,
    /// §4.2.8: "the client MUST verify that the selected NamedGroup in the
    /// ServerHello is the same as that in the HelloRetryRequest. If this check
    /// fails, the client MUST abort the handshake with an 'illegal_parameter'
    /// alert."
    ServerShareGroupChanged,
    /// §4.2.8.2: "32 bytes for X25519." (by §6's note)
    ServerShareWrongLength,
    /// §7.4.2: "Implementations MUST check whether the computed Diffie-Hellman
    /// shared secret is the all-zero value and abort if so". (by §6's note,
    /// whose own example is the DHE share of p - 1, the same small-subgroup
    /// failure)
    SharedSecretAllZero,
    /// §4.3.2: "This field SHALL be zero length unless used for the
    /// post-handshake authentication exchanges". (by §6's note)
    RequestContextNotEmpty,
    /// §4.4.2: "Otherwise (in the case of server authentication), this field
    /// SHALL be zero length." (by §6's note)
    CertificateContextNotEmpty,
    /// §4.4.3: "the signature algorithm MUST be one offered in the client's
    /// 'signature_algorithms' extension". (by §6's note)
    SignatureSchemeNotOffered,
    /// §4.4.3: "RSA signatures MUST use an RSASSA-PSS algorithm"; "The SHA-1
    /// algorithm MUST NOT be used in any signatures of CertificateVerify
    /// messages." (by §6's note)
    SignatureSchemeForbidden,
    /// §4.4.3: "the signature algorithm MUST be compatible with the key in the
    /// sender's end-entity certificate." (by §6's note)
    SignatureSchemeKeyMismatch,
    /// §4.6.1: "Servers MUST NOT use any value greater than 604800 seconds".
    /// (by §6's note)
    TicketLifetimeTooLong,
    /// §4.6.3: "If an implementation receives any other value, it MUST terminate
    /// the connection with an 'illegal_parameter' alert."
    KeyUpdateBadRequest,
    /// The body of a received extension of this type is well formed but breaks a
    /// rule of the RFC that defines it. Each rule is in
    /// `extension_bodies::body_semantics_valid`: RFC 6066 §4 ("if a client
    /// receives a maximum fragment length negotiation response that differs from
    /// the length it requested, it MUST also abort the handshake with an
    /// 'illegal_parameter' alert"), RFC 6520 §2 ("Upon reception of an unknown
    /// mode, an error Alert message using illegal_parameter ... MUST be sent"),
    /// RFC 5764 §4.1.3 (its "invalid_parameter"; see the comment there), and the
    /// rest by §6's note ("syntactically correct but semantically invalid").
    ExtensionBodyInvalid(nat),

    // ----- unsupported_extension -----
    /// §4.2: "Implementations MUST NOT send extension responses if the remote
    /// endpoint did not send the corresponding extension requests ... Upon
    /// receiving such an extension, an endpoint MUST abort the handshake with
    /// an 'unsupported_extension' alert."
    ExtensionNotOffered,

    // ----- missing_extension -----
    /// §4.1.3 ("All TLS 1.3 ServerHello messages MUST contain the
    /// 'supported_versions' extension"), §4.1.4, §9.2 and §6.2.
    SupportedVersionsMissing,
    /// §4.1.3, §9.2 ("'key_share' is REQUIRED for DHE or ECDHE key exchange")
    /// and §6.2.
    KeyShareMissing,
    /// §4.3.2: "The 'signature_algorithms' extension MUST be specified", and
    /// §6.2.
    SignatureAlgorithmsMissing,

    // ----- decode_error -----
    /// §6: "Peers which receive a message which cannot be parsed according to
    /// the syntax (e.g., have a length extending beyond the message boundary or
    /// contain an out-of-range length) MUST terminate the connection with a
    /// 'decode_error' alert."
    Malformed,
    /// §4.4.2.4: "If the server supplies an empty Certificate message, the
    /// client MUST abort the handshake with a 'decode_error' alert."
    EmptyServerCertificate,

    // ----- protocol_version -----
    /// Appendix D.1: "If the version chosen by the server is not supported by
    /// the client (or is not acceptable), the client MUST abort the handshake
    /// with a 'protocol_version' alert." Appendix D.5 says the same of a
    /// legacy_version of 0x0300.
    VersionNotSupported,

    // ----- decrypt_error -----
    /// §4.4.3: "If the verification fails, the receiver MUST terminate the
    /// handshake with a 'decrypt_error' alert."
    CertificateVerifyFailed,
    /// §4.4.4: "Recipients of Finished messages MUST verify that the contents
    /// are correct and if incorrect MUST terminate the connection with a
    /// 'decrypt_error' alert."
    FinishedIncorrect,

    // ----- bad_record_mac -----
    /// §5.2: "If the decryption fails, the receiver MUST terminate the
    /// connection with a 'bad_record_mac' alert."
    DeprotectionFailed,

    // ----- record_overflow -----
    /// §5.1: "An endpoint that receives a record that exceeds this length MUST
    /// terminate the connection with a 'record_overflow' alert."
    PlaintextTooLong,
    /// §5.2: "An endpoint that receives a record from its peer with
    /// TLSCiphertext.length larger than 2^14 + 256 octets MUST terminate the
    /// connection with a 'record_overflow' alert."
    CiphertextTooLong,
    /// §5.4: "the full encoded TLSInnerPlaintext MUST NOT exceed 2^14 + 1
    /// octets"; §6.2 record_overflow: "or a record decrypted to a TLSPlaintext
    /// record with more than 2^14 bytes".
    InnerPlaintextTooLong,

    // ----- certificate alerts -----
    /// §4.4.2.2: "it MUST abort the handshake with an appropriate
    /// certificate-related alert (by default, 'unsupported_certificate')". The
    /// field is what certificate validation named.
    ChainRejected(nat),

    // ----- internal_error -----
    /// §5.3: "If a TLS implementation would need to wrap a sequence number, it
    /// MUST either rekey (Section 4.6.3) or terminate the connection." A reader
    /// cannot rekey its peer. §6.2's internal_error is the closest of the
    /// descriptions.
    SequenceNumberWrap,
}

/// Which alert each error requires. The match follows the groups of
/// [`ClientError`].
pub open spec fn required_alert(error: ClientError) -> nat {
    match error {
        ClientError::UnexpectedHandshakeMessage => ad_unexpected_message(),
        ClientError::SecondHelloRetryRequest => ad_unexpected_message(),
        ClientError::EndOfEarlyDataReceived => ad_unexpected_message(),
        ClientError::PostHandshakeAuthNotOffered => ad_unexpected_message(),
        ClientError::KeyUpdateBeforeFinished => ad_unexpected_message(),
        ClientError::ChangeCipherSpecBadValue => ad_unexpected_message(),
        ClientError::ChangeCipherSpecProtected => ad_unexpected_message(),
        ClientError::UnexpectedRecordType => ad_unexpected_message(),
        ClientError::InterleavedRecord => ad_unexpected_message(),
        ClientError::KeyChangeNotAligned => ad_unexpected_message(),
        ClientError::ZeroLengthContent => ad_unexpected_message(),
        ClientError::NoContentType => ad_unexpected_message(),

        ClientError::SessionIdEchoMismatch => ad_illegal_parameter(),
        ClientError::CipherSuiteNotOffered => ad_illegal_parameter(),
        ClientError::CompressionMethodNotZero => ad_illegal_parameter(),
        ClientError::DowngradeSentinel => ad_illegal_parameter(),
        ClientError::RetryLegacyVersion => ad_illegal_parameter(),
        ClientError::RetryWithoutChange => ad_illegal_parameter(),
        ClientError::CipherSuiteChanged => ad_illegal_parameter(),
        ClientError::SelectedVersionChanged => ad_illegal_parameter(),
        ClientError::SelectedVersionNotAcceptable => ad_illegal_parameter(),
        ClientError::ExtensionNotSpecifiedForMessage => ad_illegal_parameter(),
        ClientError::DuplicateExtension => ad_illegal_parameter(),
        ClientError::RetryGroupNotOffered => ad_illegal_parameter(),
        ClientError::RetryGroupAlreadyShared => ad_illegal_parameter(),
        ClientError::ServerShareGroupNotOffered => ad_illegal_parameter(),
        ClientError::ServerShareGroupChanged => ad_illegal_parameter(),
        ClientError::ServerShareWrongLength => ad_illegal_parameter(),
        ClientError::SharedSecretAllZero => ad_illegal_parameter(),
        ClientError::RequestContextNotEmpty => ad_illegal_parameter(),
        ClientError::CertificateContextNotEmpty => ad_illegal_parameter(),
        ClientError::SignatureSchemeNotOffered => ad_illegal_parameter(),
        ClientError::SignatureSchemeForbidden => ad_illegal_parameter(),
        ClientError::SignatureSchemeKeyMismatch => ad_illegal_parameter(),
        ClientError::TicketLifetimeTooLong => ad_illegal_parameter(),
        ClientError::KeyUpdateBadRequest => ad_illegal_parameter(),
        ClientError::ExtensionBodyInvalid(_) => ad_illegal_parameter(),

        ClientError::ExtensionNotOffered => ad_unsupported_extension(),

        ClientError::SupportedVersionsMissing => ad_missing_extension(),
        ClientError::KeyShareMissing => ad_missing_extension(),
        ClientError::SignatureAlgorithmsMissing => ad_missing_extension(),

        ClientError::Malformed => ad_decode_error(),
        ClientError::EmptyServerCertificate => ad_decode_error(),

        ClientError::VersionNotSupported => ad_protocol_version(),

        ClientError::CertificateVerifyFailed => ad_decrypt_error(),
        ClientError::FinishedIncorrect => ad_decrypt_error(),

        ClientError::DeprotectionFailed => ad_bad_record_mac(),

        ClientError::PlaintextTooLong => ad_record_overflow(),
        ClientError::CiphertextTooLong => ad_record_overflow(),
        ClientError::InnerPlaintextTooLong => ad_record_overflow(),

        // §4.4.2.2 "(by default, 'unsupported_certificate')": what validation
        // names is used if it is a certificate alert at all.
        ClientError::ChainRejected(alert) =>
            if is_certificate_alert(alert) { alert } else { ad_unsupported_certificate() },

        ClientError::SequenceNumberWrap => ad_internal_error(),
    }
}

/// One entry of a failure list: `error` if `violated`, otherwise nothing.
pub open spec fn fails_if(violated: bool, error: ClientError) -> Seq<ClientError> {
    if violated { seq![error] } else { seq![] }
}

} // verus!
