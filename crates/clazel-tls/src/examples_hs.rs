//! Concrete facts about the handshake messages of [`super::spec`]
//! (RFC 8446 §4), proven by evaluating the spec on literal bytes. Each
//! quotes the rule it shows; `mutations.json` breaks each rule in turn
//! and a certificate calls one of these lemmas on the broken spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Thirty-two zero bytes: a `Random` (§4.1.2).
pub open spec fn z32() -> Seq<u8> {
    seq![
        0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ]
}

/// The body of a ClientHello: `legacy_version` 0x0303, `random`, an empty
/// `legacy_session_id`, the one cipher suite 0x1303, the null compression
/// method, and the extensions `supported_versions` (0x0304) and
/// `signature_algorithms` (ecdsa_secp256r1_sha256).
pub open spec fn ch_body() -> Seq<u8> {
    seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 0] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4]
        + seq![0u8, 13, 0, 4, 0, 2, 4, 3]
}

/// The `Handshake` message that holds [`ch_body`]: type 1 and its 58
/// bytes.
pub open spec fn ch_message() -> Seq<u8> {
    seq![1u8, 0, 0, 58] + ch_body()
}

/// The ClientHello that [`ch_message`] is.
pub open spec fn ch_value() -> ClientHello {
    ClientHello {
        legacy_version: 0x0303,
        random: z32(),
        session_id: Seq::<u8>::empty(),
        cipher_suites: seq![0x1303u16],
        compression: seq![0u8],
        extensions: seq![Ext { etype: 43, data: seq![2u8, 3, 4] }, Ext { etype: 13, data: seq![0u8, 2, 4, 3] }],
    }
}

/// §4: the `Handshake` header and the messages with a bare body.
/// "msg_type", then "uint24 length", then the body: a KeyUpdate of 1 byte;
/// a length that does not match is a syntax error (`decode_error`); a type
/// outside Appendix B.3's `select` is `unexpected_message`; "If the
/// request_update field is set to any other value than the defined ones,
/// the receiver MUST terminate the connection with an "illegal_parameter"
/// alert."
pub proof fn lemma_handshake_header()
    ensures
        parse_handshake(seq![24u8, 0, 0, 1, 0], 32) == Res::<HsMsg>::Ok(HsMsg::KeyUpdate(0)),
        parse_handshake(seq![24u8, 0, 0, 1, 1], 32) == Res::<HsMsg>::Ok(HsMsg::KeyUpdate(1)),
        parse_handshake(seq![24u8, 0, 0, 1, 2], 32) == Res::<HsMsg>::Err(ErrKind::InvalidEnum),
        parse_handshake(seq![24u8, 0, 0, 2, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![24u8, 0, 0, 1], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![24u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![24u8, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![24u8, 1, 0, 0, 1], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![0u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType),
        parse_handshake(seq![3u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType),
        parse_handshake(seq![6u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType),
        parse_handshake(seq![254u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType),
        parse_handshake(seq![5u8, 0, 0, 0], 32) == Res::<HsMsg>::Ok(HsMsg::EndOfEarlyData),
        parse_handshake(seq![5u8, 0, 0, 1, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        handshake_type_known(1),
        handshake_type_known(2),
        handshake_type_known(4),
        handshake_type_known(5),
        handshake_type_known(8),
        handshake_type_known(11),
        handshake_type_known(13),
        handshake_type_known(15),
        handshake_type_known(20),
        handshake_type_known(24),
        !handshake_type_known(0),
        !handshake_type_known(3),
        !handshake_type_known(6),
        !handshake_type_known(7),
        !handshake_type_known(12),
        !handshake_type_known(25),
        !handshake_type_known(254),
{
    assert(parse_handshake(seq![24u8, 0, 0, 1, 0], 32) == Res::<HsMsg>::Ok(HsMsg::KeyUpdate(0))) by (compute_only);
    assert(parse_handshake(seq![24u8, 0, 0, 1, 1], 32) == Res::<HsMsg>::Ok(HsMsg::KeyUpdate(1))) by (compute_only);
    assert(parse_handshake(seq![24u8, 0, 0, 1, 2], 32) == Res::<HsMsg>::Err(ErrKind::InvalidEnum)) by (compute_only);
    assert(parse_handshake(seq![24u8, 0, 0, 2, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![24u8, 0, 0, 1], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![24u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![24u8, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![24u8, 1, 0, 0, 1], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![0u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType)) by (compute_only);
    assert(parse_handshake(seq![3u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType)) by (compute_only);
    assert(parse_handshake(seq![6u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType)) by (compute_only);
    assert(parse_handshake(seq![254u8, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::UnexpectedHandshakeType)) by (compute_only);
    assert(parse_handshake(seq![5u8, 0, 0, 0], 32) == Res::<HsMsg>::Ok(HsMsg::EndOfEarlyData)) by (compute_only);
    assert(parse_handshake(seq![5u8, 0, 0, 1, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(handshake_type_known(1)) by (compute_only);
    assert(handshake_type_known(2)) by (compute_only);
    assert(handshake_type_known(4)) by (compute_only);
    assert(handshake_type_known(5)) by (compute_only);
    assert(handshake_type_known(8)) by (compute_only);
    assert(handshake_type_known(11)) by (compute_only);
    assert(handshake_type_known(13)) by (compute_only);
    assert(handshake_type_known(15)) by (compute_only);
    assert(handshake_type_known(20)) by (compute_only);
    assert(handshake_type_known(24)) by (compute_only);
    assert(!handshake_type_known(0)) by (compute_only);
    assert(!handshake_type_known(3)) by (compute_only);
    assert(!handshake_type_known(6)) by (compute_only);
    assert(!handshake_type_known(7)) by (compute_only);
    assert(!handshake_type_known(12)) by (compute_only);
    assert(!handshake_type_known(25)) by (compute_only);
    assert(!handshake_type_known(254)) by (compute_only);
}

/// §4.4.4: `Finished` is `opaque verify_data[Hash.length]`, exactly the
/// hash's length.
pub proof fn lemma_finished()
    ensures
        parse_handshake(seq![20u8, 0, 0, 2, 7, 8], 2) == Res::<HsMsg>::Ok(HsMsg::Finished(seq![7u8, 8])),
        parse_handshake(seq![20u8, 0, 0, 2, 7, 8], 3) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![20u8, 0, 0, 3, 7, 8, 9], 2) == Res::<HsMsg>::Err(ErrKind::Decode),
        // a message that is longer than its length field says is not one.
        parse_handshake(seq![20u8, 0, 0, 2, 7, 8, 9], 3) == Res::<HsMsg>::Err(ErrKind::Decode),
{
    assert(parse_handshake(seq![20u8, 0, 0, 2, 7, 8], 2) == Res::<HsMsg>::Ok(HsMsg::Finished(seq![7u8, 8]))) by (compute_only);
    assert(parse_handshake(seq![20u8, 0, 0, 2, 7, 8], 3) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![20u8, 0, 0, 3, 7, 8, 9], 2) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![20u8, 0, 0, 2, 7, 8, 9], 3) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
}

/// §4.1.2: a ClientHello is read field by field, and the fields' bounds
/// are the declared ones: `legacy_session_id<0..32>`,
/// `cipher_suites<2..2^16-2>`, `legacy_compression_methods<1..2^8-1>`,
/// `extensions<8..2^16-1>`, `random[32]`.
pub proof fn lemma_client_hello_fields()
    ensures
        parse_handshake(ch_message(), 32) == Res::<HsMsg>::Ok(HsMsg::ClientHello(ch_value())),
        // legacy_session_id of 32 bytes is allowed, of 33 is not.
        read_client_hello(seq![3u8, 3] + z32() + seq![32u8] + z32() + seq![0u8, 2, 0x13, 3, 1, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is Some,
        read_client_hello(seq![3u8, 3] + z32() + seq![33u8] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3, 1, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None,
        // cipher_suites needs at least one suite, and a whole number of them.
        read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 0] + seq![1u8, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None,
        read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 3, 0x13, 3, 1, 1, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None,
        // compression needs at least one method.
        read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![0u8] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None,
        // the extensions need at least 8 bytes (floor 8).
        read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 0] + seq![0u8, 7] + seq![0u8, 0x2b, 0, 3, 2, 3, 4]) is None,
        read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 0] + seq![0u8, 8] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is Some,
        // nothing may follow the extensions.
        read_client_hello(ch_body() + seq![0u8]) is None,
        // the random is 32 bytes.
        read_client_hello(seq![3u8, 3, 0, 0, 0]) is None,
{
    assert(parse_handshake(ch_message(), 32) == Res::<HsMsg>::Ok(HsMsg::ClientHello(ch_value()))) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![32u8] + z32() + seq![0u8, 2, 0x13, 3, 1, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is Some) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![33u8] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3, 1, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 0] + seq![1u8, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 3, 0x13, 3, 1, 1, 0, 0, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![0u8] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is None) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 0] + seq![0u8, 7] + seq![0u8, 0x2b, 0, 3, 2, 3, 4]) is None) by (compute_only);
    assert(read_client_hello(seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 0] + seq![0u8, 8] + seq![0u8, 13, 0, 4, 0, 2, 4, 3]) is Some) by (compute_only);
    assert(read_client_hello(ch_body() + seq![0u8]) is None) by (compute_only);
    assert(read_client_hello(seq![3u8, 3, 0, 0, 0]) is None) by (compute_only);
}

/// §4.1.2: "legacy_compression_methods ... MUST contain exactly one byte,
/// set to zero ... If a TLS 1.3 ClientHello is received with any other
/// value in this field, the server MUST abort the handshake with an
/// "illegal_parameter" alert."
pub proof fn lemma_client_hello_compression()
    ensures
        parse_handshake_body(1, seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 1] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3], 32)
            == Res::<HsMsg>::Err(ErrKind::InvalidEnum),
        parse_handshake_body(1, seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![2u8, 0, 0] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3], 32)
            == Res::<HsMsg>::Err(ErrKind::InvalidEnum),
{
    assert(parse_handshake_body(1, seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![1u8, 1] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3], 32)
        == Res::<HsMsg>::Err(ErrKind::InvalidEnum)) by (compute_only);
    assert(parse_handshake_body(1, seq![3u8, 3] + z32() + seq![0u8] + seq![0u8, 2, 0x13, 3] + seq![2u8, 0, 0] + seq![0u8, 15] + seq![0u8, 0x2b, 0, 3, 2, 3, 4] + seq![0u8, 13, 0, 4, 0, 2, 4, 3], 32)
        == Res::<HsMsg>::Err(ErrKind::InvalidEnum)) by (compute_only);
}

/// §4.2: "There MUST NOT be more than one extension of the same type in a
/// given extension block"; an extension the table does not allow in the
/// message is `illegal_parameter`; the structure of the extension data is
/// `decode_error`; "All TLS 1.3 ServerHello messages MUST contain the
/// "supported_versions" extension."
pub proof fn lemma_extension_checks()
    ensures
        check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Sh) is None,
        check_extensions(
            seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 43, data: seq![3u8, 4] }],
            MsgKind::Sh,
        ) == Some(ErrKind::DuplicateExtension),
        check_extensions(
            seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 51, data: seq![0u8, 29] }, Ext { etype: 43, data: seq![3u8, 4] }],
            MsgKind::Hrr,
        ) == Some(ErrKind::DuplicateExtension),
        check_extensions(
            seq![Ext { etype: 1, data: seq![] }, Ext { etype: 2, data: seq![] }],
            MsgKind::Ee,
        ) is None,
        check_extensions(seq![Ext { etype: 0, data: seq![] }], MsgKind::Sh) == Some(ErrKind::ExtensionNotAllowed),
        check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 0, data: seq![] }], MsgKind::Sh)
            == Some(ErrKind::ExtensionNotAllowed),
        check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Ee) == Some(ErrKind::ExtensionNotAllowed),
        check_extensions(seq![Ext { etype: 43, data: seq![3u8] }], MsgKind::Sh) == Some(ErrKind::Decode),
        check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4, 5] }], MsgKind::Sh) == Some(ErrKind::Decode),
        check_extensions(seq![Ext { etype: 1234, data: seq![9u8] }], MsgKind::Sh) is None,
        check_extensions(Seq::<Ext>::empty(), MsgKind::Sh) is None,
        check_extensions(Seq::<Ext>::empty(), MsgKind::Hrr) is None,
        check_extensions(Seq::<Ext>::empty(), MsgKind::Ee) is None,
        check_extensions(Seq::<Ext>::empty(), MsgKind::Ch) is None,
        check_extensions(seq![Ext { etype: 44, data: seq![0u8, 1, 7] }, Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Hrr) is None,
        check_extensions(seq![Ext { etype: 44, data: seq![0u8, 1, 7] }, Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Sh)
            == Some(ErrKind::ExtensionNotAllowed),
        check_extensions(seq![Ext { etype: 1234, data: seq![9u8] }, Ext { etype: 1234, data: seq![] }], MsgKind::Ee)
            == Some(ErrKind::DuplicateExtension),
        check_extensions(
            seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 44, data: seq![0u8] }],
            MsgKind::Hrr,
        ) == Some(ErrKind::Decode),
        check_extensions(
            seq![Ext { etype: 1234, data: seq![9u8] }, Ext { etype: 43, data: seq![3u8, 4] }],
            MsgKind::Sh,
        ) is None,
{
    assert(check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Sh) is None) by (compute_only);
    assert(check_extensions(
        seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 43, data: seq![3u8, 4] }],
        MsgKind::Sh,
    ) == Some(ErrKind::DuplicateExtension)) by (compute_only);
    assert(check_extensions(
        seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 51, data: seq![0u8, 29] }, Ext { etype: 43, data: seq![3u8, 4] }],
        MsgKind::Hrr,
    ) == Some(ErrKind::DuplicateExtension)) by (compute_only);
    assert(check_extensions(seq![Ext { etype: 1, data: seq![] }, Ext { etype: 2, data: seq![] }], MsgKind::Ee) is None)
        by (compute_only);
    assert(check_extensions(seq![Ext { etype: 0, data: seq![] }], MsgKind::Sh) == Some(ErrKind::ExtensionNotAllowed))
        by (compute_only);
    assert(check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 0, data: seq![] }], MsgKind::Sh)
        == Some(ErrKind::ExtensionNotAllowed)) by (compute_only);
    assert(check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Ee) == Some(ErrKind::ExtensionNotAllowed))
        by (compute_only);
    assert(check_extensions(seq![Ext { etype: 43, data: seq![3u8] }], MsgKind::Sh) == Some(ErrKind::Decode)) by (compute_only);
    assert(check_extensions(seq![Ext { etype: 43, data: seq![3u8, 4, 5] }], MsgKind::Sh) == Some(ErrKind::Decode)) by (compute_only);
    assert(check_extensions(seq![Ext { etype: 1234, data: seq![9u8] }], MsgKind::Sh) is None)
        by (compute_only);
    assert(check_extensions(Seq::<Ext>::empty(), MsgKind::Sh) is None) by (compute_only);
    assert(check_extensions(Seq::<Ext>::empty(), MsgKind::Hrr) is None) by (compute_only);
    assert(check_extensions(Seq::<Ext>::empty(), MsgKind::Ee) is None) by (compute_only);
    assert(check_extensions(Seq::<Ext>::empty(), MsgKind::Ch) is None) by (compute_only);
    assert(check_extensions(seq![Ext { etype: 44, data: seq![0u8, 1, 7] }, Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Hrr) is None)
        by (compute_only);
    assert(check_extensions(seq![Ext { etype: 44, data: seq![0u8, 1, 7] }, Ext { etype: 43, data: seq![3u8, 4] }], MsgKind::Sh)
        == Some(ErrKind::ExtensionNotAllowed)) by (compute_only);
    assert(check_extensions(seq![Ext { etype: 1234, data: seq![9u8] }, Ext { etype: 1234, data: seq![] }], MsgKind::Ee)
        == Some(ErrKind::DuplicateExtension)) by (compute_only);
    assert(check_extensions(
        seq![Ext { etype: 43, data: seq![3u8, 4] }, Ext { etype: 44, data: seq![0u8] }],
        MsgKind::Hrr,
    ) == Some(ErrKind::Decode)) by (compute_only);
    assert(check_extensions(
        seq![Ext { etype: 1234, data: seq![9u8] }, Ext { etype: 43, data: seq![3u8, 4] }],
        MsgKind::Sh,
    ) is None) by (compute_only);
}

/// The body of a ServerHello: `legacy_version` 0x0303, `random`, an empty
/// `legacy_session_id_echo`, the suite 0x1303, the null compression
/// method, and the extensions `exts` (the bytes after their length).
pub open spec fn sh_body(random: Seq<u8>, comp: u8, exts: Seq<u8>) -> Seq<u8> {
    seq![3u8, 3] + random + seq![0u8] + seq![0x13u8, 3] + seq![comp] + exts
}

/// `supported_versions` with `selected_version` 0x0304, as an extension.
pub open spec fn sv_ext() -> Seq<u8> {
    seq![0u8, 0x2b, 0, 2, 3, 4]
}

/// §4.1.3 and §4.1.4: a ServerHello, and the HelloRetryRequest that has the
/// same structure but a fixed `Random`; "legacy_compression_method: A single
/// byte which MUST have the value 0"; the extension table distinguishes the
/// two (a `cookie` may be in a HelloRetryRequest and not in a ServerHello).
pub proof fn lemma_server_hello()
    ensures
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 6] + sv_ext()), 32) == Res::<HsMsg>::Ok(
            HsMsg::ServerHello(
                ServerHello {
                    legacy_version: 0x0303,
                    random: z32(),
                    session_id_echo: Seq::<u8>::empty(),
                    cipher_suite: 0x1303,
                    compression: 0,
                    extensions: seq![Ext { etype: 43, data: seq![3u8, 4] }],
                },
            ),
        ),
        parse_handshake_body(2, sh_body(z32(), 1, seq![0u8, 6] + sv_ext()), 32) == Res::<HsMsg>::Err(ErrKind::InvalidEnum),
        is_hello_retry_request(
            ServerHello {
                legacy_version: 0x0303,
                random: hrr_random(),
                session_id_echo: Seq::<u8>::empty(),
                cipher_suite: 0x1303,
                compression: 0,
                extensions: Seq::<Ext>::empty(),
            },
        ),
        is_hello_retry_request(
            ServerHello {
                legacy_version: 0x0303,
                random: seq![0xCFu8, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91, 0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E, 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C],
                session_id_echo: Seq::<u8>::empty(),
                cipher_suite: 0x1303,
                compression: 0,
                extensions: Seq::<Ext>::empty(),
            },
        ),
        !is_hello_retry_request(
            ServerHello {
                legacy_version: 0x0303,
                random: z32(),
                session_id_echo: Seq::<u8>::empty(),
                cipher_suite: 0x1303,
                compression: 0,
                extensions: Seq::<Ext>::empty(),
            },
        ),
        parse_handshake_body(2, sh_body(hrr_random(), 0, seq![0u8, 13] + sv_ext() + seq![0u8, 0x2c, 0, 3, 0, 1, 7]), 32) is Ok,
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 13] + sv_ext() + seq![0u8, 0x2c, 0, 3, 0, 1, 7]), 32)
            == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed),
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 12] + sv_ext() + sv_ext()), 32)
            == Res::<HsMsg>::Err(ErrKind::DuplicateExtension),
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 10] + seq![0u8, 0, 0, 0] + sv_ext()), 32)
            == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed),
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 6, 0x12, 0x34, 0, 2, 0xAA, 0xBB]), 32) is Ok,
        parse_handshake_body(2, sh_body(hrr_random(), 0, seq![0u8, 6, 0x12, 0x34, 0, 2, 0xAA, 0xBB]), 32) is Ok,
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 7, 0, 0x2b, 0, 3, 3, 4, 5]), 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        // RFC 5246's legacy extension syntax permits a five-byte extension vector.
        parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 5, 0x12, 0x34, 0, 1, 9]), 32) is Ok,
{
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 6] + sv_ext()), 32) == Res::<HsMsg>::Ok(
        HsMsg::ServerHello(
            ServerHello {
                legacy_version: 0x0303,
                random: z32(),
                session_id_echo: Seq::<u8>::empty(),
                cipher_suite: 0x1303,
                compression: 0,
                extensions: seq![Ext { etype: 43, data: seq![3u8, 4] }],
            },
        ),
    )) by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 1, seq![0u8, 6] + sv_ext()), 32) == Res::<HsMsg>::Err(ErrKind::InvalidEnum))
        by (compute_only);
    assert(is_hello_retry_request(
        ServerHello {
            legacy_version: 0x0303,
            random: hrr_random(),
            session_id_echo: Seq::<u8>::empty(),
            cipher_suite: 0x1303,
            compression: 0,
            extensions: Seq::<Ext>::empty(),
        },
    )) by (compute_only);
    assert(is_hello_retry_request(
        ServerHello {
            legacy_version: 0x0303,
            random: seq![0xCFu8, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11, 0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91, 0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E, 0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C],
            session_id_echo: Seq::<u8>::empty(),
            cipher_suite: 0x1303,
            compression: 0,
            extensions: Seq::<Ext>::empty(),
        },
    )) by (compute_only);
    assert(!is_hello_retry_request(
        ServerHello {
            legacy_version: 0x0303,
            random: z32(),
            session_id_echo: Seq::<u8>::empty(),
            cipher_suite: 0x1303,
            compression: 0,
            extensions: Seq::<Ext>::empty(),
        },
    )) by (compute_only);
    assert(parse_handshake_body(2, sh_body(hrr_random(), 0, seq![0u8, 13] + sv_ext() + seq![0u8, 0x2c, 0, 3, 0, 1, 7]), 32) is Ok)
        by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 13] + sv_ext() + seq![0u8, 0x2c, 0, 3, 0, 1, 7]), 32)
        == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed)) by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 12] + sv_ext() + sv_ext()), 32)
        == Res::<HsMsg>::Err(ErrKind::DuplicateExtension)) by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 10] + seq![0u8, 0, 0, 0] + sv_ext()), 32)
        == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed)) by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 6, 0x12, 0x34, 0, 2, 0xAA, 0xBB]), 32) is Ok)
        by (compute_only);
    assert(parse_handshake_body(2, sh_body(hrr_random(), 0, seq![0u8, 6, 0x12, 0x34, 0, 2, 0xAA, 0xBB]), 32) is Ok)
        by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 7, 0, 0x2b, 0, 3, 3, 4, 5]), 32) == Res::<HsMsg>::Err(ErrKind::Decode))
        by (compute_only);
    assert(parse_handshake_body(2, sh_body(z32(), 0, seq![0u8, 5, 0x12, 0x34, 0, 1, 9]), 32) is Ok)
        by (compute_only);
}

/// §4.2.1, §4.2.2, §4.2.3, §4.2.7, §4.2.8 and RFC 6066 §3: the structure
/// of each extension's data.
pub proof fn lemma_extension_bodies()
    ensures
        read_supported_versions_ch(seq![2u8, 3, 4]) == Some(seq![0x0304u16]),
        read_supported_versions_ch(seq![4u8, 3, 4, 3, 3]) == Some(seq![0x0304u16, 0x0303]),
        read_supported_versions_ch(seq![0u8]) is None,
        read_supported_versions_ch(seq![1u8, 3]) is None,
        read_supported_versions_ch(seq![3u8, 3, 4, 3]) is None,
        read_supported_versions_ch(seq![2u8, 3, 4, 9]) is None,
        read_supported_versions_sh(seq![3u8, 4]) == Some(0x0304u16),
        read_supported_versions_sh(seq![3u8]) is None,
        read_supported_versions_sh(seq![3u8, 4, 5]) is None,
        read_cookie(seq![0u8, 1, 7]) == Some(seq![7u8]),
        read_cookie(seq![0u8, 0]) is None,
        read_cookie(seq![0u8, 2, 7]) is None,
        read_cookie(seq![0u8, 1, 7, 8]) is None,
        read_signature_schemes(seq![0u8, 2, 4, 3]) == Some(seq![0x0403u16]),
        read_signature_schemes(seq![0u8, 0]) is None,
        read_signature_schemes(seq![0u8, 3, 4, 3, 5]) is None,
        read_named_groups(seq![0u8, 2, 0, 0x1d]) == Some(seq![0x001Du16]),
        read_named_groups(seq![0u8, 0]) is None,
        read_key_share_ch(seq![0u8, 0]) == Some(Seq::<KeyShare>::empty()),
        read_key_share_ch(seq![0u8, 6, 0, 0x1d, 0, 2, 5, 6]) == Some(seq![KeyShare { group: 0x001D, key_exchange: seq![5u8, 6] }]),
        read_key_share_ch(seq![0u8, 4, 0, 0x1d, 0, 0]) is None,
        read_key_share_ch(seq![0u8, 5, 0, 0x1d, 0, 2, 5]) is None,
        read_key_share_hrr(seq![0u8, 0x1d]) == Some(0x001Du16),
        read_key_share_hrr(seq![0u8, 0x1d, 0]) is None,
        read_key_share_sh(seq![0u8, 0x1d, 0, 2, 5, 6]) == Some(KeyShare { group: 0x001D, key_exchange: seq![5u8, 6] }),
        read_key_share_sh(seq![0u8, 0x1d, 0, 2, 5, 6, 7]) is None,
        read_key_share_sh(seq![0u8, 0x1d, 0, 0]) is None,
        read_server_name_ch(seq![0u8, 6, 0, 0, 3, 97, 98, 99]) == Some(seq![ServerName { host_name: seq![97u8, 98, 99] }]),
        read_server_name_ch(seq![0u8, 0]) is None,
        read_server_name_ch(seq![0u8, 6, 1, 0, 3, 97, 98, 99]) is None,
        read_server_name_ch(seq![0u8, 3, 0, 0, 0]) is None,
        server_name_ee_ok(Seq::<u8>::empty()),
        !server_name_ee_ok(seq![0u8]),
{
    assert(read_supported_versions_ch(seq![2u8, 3, 4]) == Some(seq![0x0304u16])) by (compute_only);
    assert(read_supported_versions_ch(seq![4u8, 3, 4, 3, 3]) == Some(seq![0x0304u16, 0x0303])) by (compute_only);
    assert(read_supported_versions_ch(seq![0u8]) is None) by (compute_only);
    assert(read_supported_versions_ch(seq![1u8, 3]) is None) by (compute_only);
    assert(read_supported_versions_ch(seq![3u8, 3, 4, 3]) is None) by (compute_only);
    assert(read_supported_versions_ch(seq![2u8, 3, 4, 9]) is None) by (compute_only);
    assert(read_supported_versions_sh(seq![3u8, 4]) == Some(0x0304u16)) by (compute_only);
    assert(read_supported_versions_sh(seq![3u8]) is None) by (compute_only);
    assert(read_supported_versions_sh(seq![3u8, 4, 5]) is None) by (compute_only);
    assert(read_cookie(seq![0u8, 1, 7]) == Some(seq![7u8])) by (compute_only);
    assert(read_cookie(seq![0u8, 0]) is None) by (compute_only);
    assert(read_cookie(seq![0u8, 2, 7]) is None) by (compute_only);
    assert(read_cookie(seq![0u8, 1, 7, 8]) is None) by (compute_only);
    assert(read_signature_schemes(seq![0u8, 2, 4, 3]) == Some(seq![0x0403u16])) by (compute_only);
    assert(read_signature_schemes(seq![0u8, 0]) is None) by (compute_only);
    assert(read_signature_schemes(seq![0u8, 3, 4, 3, 5]) is None) by (compute_only);
    assert(read_named_groups(seq![0u8, 2, 0, 0x1d]) == Some(seq![0x001Du16])) by (compute_only);
    assert(read_named_groups(seq![0u8, 0]) is None) by (compute_only);
    assert(read_key_share_ch(seq![0u8, 0]) == Some(Seq::<KeyShare>::empty())) by (compute_only);
    assert(read_key_share_ch(seq![0u8, 6, 0, 0x1d, 0, 2, 5, 6]) == Some(seq![KeyShare { group: 0x001D, key_exchange: seq![5u8, 6] }]))
        by (compute_only);
    assert(read_key_share_ch(seq![0u8, 4, 0, 0x1d, 0, 0]) is None) by (compute_only);
    assert(read_key_share_ch(seq![0u8, 5, 0, 0x1d, 0, 2, 5]) is None) by (compute_only);
    assert(read_key_share_hrr(seq![0u8, 0x1d]) == Some(0x001Du16)) by (compute_only);
    assert(read_key_share_hrr(seq![0u8, 0x1d, 0]) is None) by (compute_only);
    assert(read_key_share_sh(seq![0u8, 0x1d, 0, 2, 5, 6]) == Some(KeyShare { group: 0x001D, key_exchange: seq![5u8, 6] })) by (compute_only);
    assert(read_key_share_sh(seq![0u8, 0x1d, 0, 2, 5, 6, 7]) is None) by (compute_only);
    assert(read_key_share_sh(seq![0u8, 0x1d, 0, 0]) is None) by (compute_only);
    assert(read_server_name_ch(seq![0u8, 6, 0, 0, 3, 97, 98, 99]) == Some(seq![ServerName { host_name: seq![97u8, 98, 99] }]))
        by (compute_only);
    assert(read_server_name_ch(seq![0u8, 0]) is None) by (compute_only);
    assert(read_server_name_ch(seq![0u8, 6, 1, 0, 3, 97, 98, 99]) is None) by (compute_only);
    assert(read_server_name_ch(seq![0u8, 3, 0, 0, 0]) is None) by (compute_only);
    assert(server_name_ee_ok(Seq::<u8>::empty())) by (compute_only);
    assert(!server_name_ee_ok(seq![0u8])) by (compute_only);
}

/// §4.3.1, §4.3.2, §4.4.2, §4.4.3 and §4.6.1: the other messages.
pub proof fn lemma_server_messages()
    ensures
        // EncryptedExtensions: Extension extensions<0..2^16-1>.
        parse_handshake(seq![8u8, 0, 0, 2, 0, 0], 32) == Res::<HsMsg>::Ok(HsMsg::EncryptedExtensions(Seq::<Ext>::empty())),
        parse_handshake(seq![8u8, 0, 0, 6, 0, 4, 0, 0, 0, 0], 32)
            == Res::<HsMsg>::Ok(HsMsg::EncryptedExtensions(seq![Ext { etype: 0, data: Seq::<u8>::empty() }])),
        parse_handshake(seq![8u8, 0, 0, 8, 0, 6, 0, 0x2b, 0, 2, 3, 4], 32) == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed),
        parse_handshake(seq![8u8, 0, 0, 7, 0, 5, 0, 0, 0, 1, 5], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![8u8, 0, 0, 3, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        // Certificate: certificate_request_context<0..2^8-1> (empty from a
        // server), CertificateEntry certificate_list<0..2^24-1>.
        parse_handshake(seq![11u8, 0, 0, 4, 0, 0, 0, 0], 32)
            == Res::<HsMsg>::Ok(HsMsg::Certificate(Certificate { context: Seq::<u8>::empty(), entries: Seq::<CertificateEntry>::empty() })),
        parse_handshake(seq![11u8, 0, 0, 12, 0, 0, 0, 8, 0, 0, 3, 1, 2, 3, 0, 0], 32)
            == Res::<HsMsg>::Ok(
            HsMsg::Certificate(
                Certificate {
                    context: Seq::<u8>::empty(),
                    entries: seq![CertificateEntry { cert_data: seq![1u8, 2, 3], extensions: Seq::<Ext>::empty() }],
                },
            ),
        ),
        parse_handshake(seq![11u8, 0, 0, 5, 1, 7, 0, 0, 0], 32)
            == Res::<HsMsg>::Ok(HsMsg::Certificate(Certificate { context: seq![7u8], entries: Seq::<CertificateEntry>::empty() })),
        parse_handshake(seq![11u8, 0, 0, 9, 0, 0, 0, 5, 0, 0, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![11u8, 0, 0, 16, 0, 0, 0, 12, 0, 0, 3, 1, 2, 3, 0, 4, 0, 0, 0, 0], 32)
            == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed),
        parse_handshake(seq![11u8, 0, 0, 16, 0, 0, 0, 12, 0, 0, 3, 1, 2, 3, 0, 4, 0, 18, 0, 0], 32) is Ok,
        // CertificateRequest: extensions<2..2^16-1>.
        parse_handshake(seq![13u8, 0, 0, 3, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![13u8, 0, 0, 11, 0, 0, 8, 0, 13, 0, 4, 0, 2, 4, 3], 32)
            == Res::<HsMsg>::Ok(
            HsMsg::CertificateRequest(
                CertificateRequest {
                    context: Seq::<u8>::empty(),
                    extensions: seq![Ext { etype: 13, data: seq![0u8, 2, 4, 3] }],
                },
            ),
        ),
        parse_handshake(seq![13u8, 0, 0, 7, 0, 0, 4, 0, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed),
        // CertificateVerify.
        parse_handshake(seq![15u8, 0, 0, 6, 8, 7, 0, 2, 1, 2], 32)
            == Res::<HsMsg>::Ok(HsMsg::CertificateVerify(CertificateVerify { algorithm: 0x0807, signature: seq![1u8, 2] })),
        parse_handshake(seq![15u8, 0, 0, 5, 8, 7, 0, 2, 1], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        // NewSessionTicket: ticket<1..2^16-1>, ticket_nonce<0..255>.
        parse_handshake(seq![4u8, 0, 0, 14, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 0], 32)
            == Res::<HsMsg>::Ok(
            HsMsg::NewSessionTicket(
                NewSessionTicket {
                    ticket_lifetime: 5,
                    ticket_age_add: 6,
                    ticket_nonce: Seq::<u8>::empty(),
                    ticket: seq![9u8],
                    extensions: Seq::<Ext>::empty(),
                },
            ),
        ),
        parse_handshake(seq![4u8, 0, 0, 13, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode),
        parse_handshake(seq![4u8, 0, 0, 22, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 8, 0, 0x2a, 0, 4, 0, 0, 16, 0], 32) is Ok,
        parse_handshake(seq![4u8, 0, 0, 20, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 6, 0, 0x2b, 0, 2, 3, 4], 32)
            == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed),
{
    assert(parse_handshake(seq![8u8, 0, 0, 2, 0, 0], 32) == Res::<HsMsg>::Ok(HsMsg::EncryptedExtensions(Seq::<Ext>::empty()))) by (compute_only);
    assert(parse_handshake(seq![8u8, 0, 0, 6, 0, 4, 0, 0, 0, 0], 32)
        == Res::<HsMsg>::Ok(HsMsg::EncryptedExtensions(seq![Ext { etype: 0, data: Seq::<u8>::empty() }]))) by (compute_only);
    assert(parse_handshake(seq![8u8, 0, 0, 8, 0, 6, 0, 0x2b, 0, 2, 3, 4], 32) == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed))
        by (compute_only);
    assert(parse_handshake(seq![8u8, 0, 0, 7, 0, 5, 0, 0, 0, 1, 5], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![8u8, 0, 0, 3, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![11u8, 0, 0, 4, 0, 0, 0, 0], 32)
        == Res::<HsMsg>::Ok(HsMsg::Certificate(Certificate { context: Seq::<u8>::empty(), entries: Seq::<CertificateEntry>::empty() })))
        by (compute_only);
    assert(parse_handshake(seq![11u8, 0, 0, 12, 0, 0, 0, 8, 0, 0, 3, 1, 2, 3, 0, 0], 32)
        == Res::<HsMsg>::Ok(
        HsMsg::Certificate(
            Certificate {
                context: Seq::<u8>::empty(),
                entries: seq![CertificateEntry { cert_data: seq![1u8, 2, 3], extensions: Seq::<Ext>::empty() }],
            },
        ),
    )) by (compute_only);
    assert(parse_handshake(seq![11u8, 0, 0, 5, 1, 7, 0, 0, 0], 32)
        == Res::<HsMsg>::Ok(HsMsg::Certificate(Certificate { context: seq![7u8], entries: Seq::<CertificateEntry>::empty() }))) by (compute_only);
    assert(parse_handshake(seq![11u8, 0, 0, 9, 0, 0, 0, 5, 0, 0, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![11u8, 0, 0, 16, 0, 0, 0, 12, 0, 0, 3, 1, 2, 3, 0, 4, 0, 0, 0, 0], 32)
        == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed)) by (compute_only);
    assert(parse_handshake(seq![11u8, 0, 0, 16, 0, 0, 0, 12, 0, 0, 3, 1, 2, 3, 0, 4, 0, 18, 0, 0], 32) is Ok) by (compute_only);
    assert(parse_handshake(seq![13u8, 0, 0, 3, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![13u8, 0, 0, 11, 0, 0, 8, 0, 13, 0, 4, 0, 2, 4, 3], 32)
        == Res::<HsMsg>::Ok(
        HsMsg::CertificateRequest(
            CertificateRequest { context: Seq::<u8>::empty(), extensions: seq![Ext { etype: 13, data: seq![0u8, 2, 4, 3] }] },
        ),
    )) by (compute_only);
    assert(parse_handshake(seq![13u8, 0, 0, 7, 0, 0, 4, 0, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed))
        by (compute_only);
    assert(parse_handshake(seq![15u8, 0, 0, 6, 8, 7, 0, 2, 1, 2], 32)
        == Res::<HsMsg>::Ok(HsMsg::CertificateVerify(CertificateVerify { algorithm: 0x0807, signature: seq![1u8, 2] }))) by (compute_only);
    assert(parse_handshake(seq![15u8, 0, 0, 5, 8, 7, 0, 2, 1], 32) == Res::<HsMsg>::Err(ErrKind::Decode)) by (compute_only);
    assert(parse_handshake(seq![4u8, 0, 0, 14, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 0], 32)
        == Res::<HsMsg>::Ok(
        HsMsg::NewSessionTicket(
            NewSessionTicket {
                ticket_lifetime: 5,
                ticket_age_add: 6,
                ticket_nonce: Seq::<u8>::empty(),
                ticket: seq![9u8],
                extensions: Seq::<Ext>::empty(),
            },
        ),
    )) by (compute_only);
    assert(parse_handshake(seq![4u8, 0, 0, 13, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 0, 0], 32) == Res::<HsMsg>::Err(ErrKind::Decode))
        by (compute_only);
    assert(parse_handshake(seq![4u8, 0, 0, 22, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 8, 0, 0x2a, 0, 4, 0, 0, 16, 0], 32) is Ok)
        by (compute_only);
    assert(parse_handshake(seq![4u8, 0, 0, 20, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 1, 9, 0, 6, 0, 0x2b, 0, 2, 3, 4], 32)
        == Res::<HsMsg>::Err(ErrKind::ExtensionNotAllowed)) by (compute_only);
}

} // verus!
