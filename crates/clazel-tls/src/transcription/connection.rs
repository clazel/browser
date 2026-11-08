//! RFC 8446 §5 and §6 from the client's side as it receives and sends records: what
//! each record does, reassembly of handshake messages, closure, and key updates.
//!
//! Modelling choices:
//! - Records are read from a byte stream ([`receive_stream`]) one at a time; a partial
//!   record waits. The length check runs on the header, before the body has arrived,
//!   since a client need not wait for bytes it must reject.
//! - **Which alert order for a record.** Length first, since it is what the header
//!   shows. Then §5's change_cipher_spec rule, since "it is necessary to detect this
//!   condition prior to attempting to deprotect the record". Then the type.
//! - **change_cipher_spec inside a fragmented handshake message.** §5 says an
//!   implementation that receives this record "at any time after the first ClientHello
//!   ... and before the peer's Finished ... MUST simply drop it without further
//!   processing"; §5.1 says "if a handshake message is split over two or more records,
//!   there MUST NOT be any other records between them". The first is a receiver's
//!   rule, explicit about time; the second binds the sender and states no receiver
//!   action. This file's author dropped the record and kept the fragments, after
//!   seeing only the heading of an existing `docs/ERRATA.md` entry on the same subject.
//!   **The equivalence author changed that** (see `receive_record`): the record is
//!   fatal with `unexpected_message` inside a fragmented message, as the crate and
//!   the one `docs/ERRATA.md` entry now say, because this file already treats §5.1 as
//!   a receiver's rule for every other interleaved record type.
//! - An interleaved alert or application data record is `unexpected_message` (§5.1's
//!   rule, with no conflict) even if the alert is a closure or error one: the check
//!   comes before the alert is read.
//! - "without further processing" also means a dropped change_cipher_spec does not
//!   advance the read sequence number. §5.3's "incremented by one after reading or
//!   writing each record" is read as "each record protected under the key", since the
//!   number only feeds the nonce and the sender does not count such records either.
//! - A plaintext record of type alert or handshake when a receive key is engaged is
//!   `unexpected_message`: §5.1 "Once record protection has started, TLSPlaintext
//!   records are protected"; §6 "Like other messages, alert messages are encrypted as
//!   specified by the current connection state".
//! - A zero-length TLSPlaintext of type handshake is `unexpected_message`, as §5.4
//!   says of a TLSInnerPlaintext; §5.1 only says "MUST NOT send". Likewise a
//!   zero-length unprotected alert. A non-zero alert length other than 2 is
//!   `decode_error` (§5.1: "exactly one message"; §6: a length that is incorrect).
//! - **Alignment.** §5.1's check runs on the messages that end the key in use for
//!   reading, by the reader: ServerHello, the server's Finished and KeyUpdate. A
//!   HelloRetryRequest does not "immediately precede a key change", so the check does
//!   not cover it. The message's own failures are looked at first.
//! - Reads after a close_notify are skipped: "Any data received after a closure alert
//!   has been received MUST be ignored." A user_canceled changes nothing (changed by the
//!   equivalence author; see `receive_alert_content`). Writing is still possible: "This does not have
//!   any effect on its read side" is the same rule mirrored.
//! - A fatal alert from the peer ends the run with `PeerError`. Its forgetting of
//!   secrets (§6 "MUST forget") is not modelled, as a pure function has no memory.
//! - A record's sequence number at or past 2^64: §5.3 "MUST either rekey ... or
//!   terminate". A client can only do so for what it writes: [`send_application_data`]
//!   rekeys, as the "rekey" branch. A reader terminates. Reaching it is impossible in
//!   practice, and the model has it only so that no record uses an out-of-range nonce.
//! - The sender's choices of §5.1 and §5.4 (no padding, no fragmenting below 2^14, no
//!   coalescing, no dummy change_cipher_spec) are in `record`, and are what makes this
//!   file a function: any other choice would be equally conformant.
//! - §6.1 "Each party MUST send a 'close_notify' alert before closing its write side"
//!   is [`close_write`]. Transport closure itself is out of scope.

#[allow(unused_imports)]
use vstd::prelude::*;

use super::alerts::ClientError;
use super::record::TrafficState;
use super::state_machine::ClientHandshake;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::post_handshake::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;
#[cfg(verus_only)]
use super::record::*;
#[cfg(verus_only)]
use super::state_machine::*;

verus! {

/// §5.1: "When record protection has not yet been engaged, TLSPlaintext structures are
/// written directly onto the wire. Once record protection has started, TLSPlaintext
/// records are protected".
pub enum Protection {
    /// Not engaged.
    Unprotected,
    /// Engaged with this secret, its keys and its sequence number.
    Protected(TrafficState),
}

/// The connection as the record layer sees it.
pub struct Connection {
    /// Appendix A.1's state and what goes with it.
    pub handshake: ClientHandshake,
    /// A.1's K_recv.
    pub receive: Protection,
    /// A.1's K_send.
    pub send: Protection,
    /// §5.1: the start of a handshake message split over records.
    pub handshake_fragments: Seq<u8>,
    /// §6.1: "Any data received after a closure alert has been received MUST be
    /// ignored."
    pub read_closed: bool,
    /// §4.6.3: a KeyUpdate of ours is owed "prior to sending its next Application
    /// Data record".
    pub key_update_owed: bool,
}

/// What a record or a stream leaves behind.
pub struct Progress {
    /// The connection after it.
    pub connection: Connection,
    /// Application Data delivered, in order.
    pub application_data: Seq<u8>,
    /// Encoded records to write, in order.
    pub records_to_send: Seq<Seq<u8>>,
}

/// The result of receiving.
pub enum Receive {
    /// §6.2: an error detected here. `connection::alert_record` encodes what to send.
    Abort(ClientError),
    /// §6: an error alert from the peer: "MUST NOT allow any further data to be sent or
    /// received on the connection". The description is the field.
    PeerError(nat),
    /// Keep going.
    Continue(Progress),
}

/// The record that carries `data` of `content_type` as written now: a TLSPlaintext or a
/// TLSCiphertext, and the sender's state after it.
pub open spec fn send_one(p: Primitives, send: Protection, content_type: nat, legacy_record_version: nat, data: Seq<u8>) -> (Seq<u8>, Protection) {
    match send {
        Protection::Unprotected => (write_tls_plaintext(content_type, legacy_record_version, data), send),
        Protection::Protected(traffic) => (
            protect_record(p, traffic, content_type, data),
            // §5.3: "The appropriate sequence number is incremented by one after reading
            // or writing each record."
            Protection::Protected(TrafficState { sequence_number: traffic.sequence_number + 1, ..traffic }),
        ),
    }
}

/// `blocks`, one record each, and the sender's state after them.
pub open spec fn send_blocks(p: Primitives, send: Protection, content_type: nat, legacy_record_version: nat, blocks: Seq<Seq<u8>>) -> (Seq<Seq<u8>>, Protection)
    decreases blocks.len(),
{
    if blocks.len() == 0 {
        (seq![], send)
    } else {
        let (record, after) = send_one(p, send, content_type, legacy_record_version, blocks[0]);
        let (records, last) = send_blocks(p, after, content_type, legacy_record_version, blocks.subrange(1, blocks.len() as int));
        (seq![record] + records, last)
    }
}

/// §7.2: the next generation of a direction, with §7.3's keys and §5.3's sequence number
/// back at 0. A direction with no secret stays as it is, which cannot happen after a
/// Finished.
pub open spec fn updated_traffic(p: Primitives, protection: Protection) -> Protection {
    match protection {
        Protection::Unprotected => protection,
        Protection::Protected(traffic) =>
            Protection::Protected(traffic_state(p, next_application_traffic_secret(p, traffic.secret))),
    }
}

/// A.1's actions, in order, and the records they write.
pub open spec fn apply_actions(p: Primitives, connection: Connection, actions: Seq<Action>) -> (Connection, Seq<Seq<u8>>)
    decreases actions.len(),
{
    if actions.len() == 0 {
        (connection, seq![])
    } else {
        let tail = actions.subrange(1, actions.len() as int);
        match actions[0] {
            Action::SendHandshake(message, legacy_record_version) => {
                let (records, send) = send_blocks(p, connection.send, ct_handshake(), legacy_record_version, fragment_blocks(message));
                let (last, more) = apply_actions(p, Connection { send, ..connection }, tail);
                (last, records + more)
            },
            Action::SetReceiveSecret(secret) =>
                apply_actions(p, Connection { receive: Protection::Protected(traffic_state(p, secret)), ..connection }, tail),
            Action::SetSendSecret(secret) =>
                apply_actions(p, Connection { send: Protection::Protected(traffic_state(p, secret)), ..connection }, tail),
            Action::UpdateReceiveSecret =>
                apply_actions(p, Connection { receive: updated_traffic(p, connection.receive), ..connection }, tail),
            Action::RespondToKeyUpdate =>
                apply_actions(p, Connection { key_update_owed: true, ..connection }, tail),
        }
    }
}

/// §4.1.2: the connection in its first state after START, with the record of the first
/// ClientHello. `hello` is expected to meet `client_hello_conforms`.
pub open spec fn start_connection(p: Primitives, hello: ClientHello, x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>) -> (Connection, Seq<Seq<u8>>) {
    let connection = Connection {
        handshake: start_handshake(hello, x25519_private_key, retry_private_key),
        receive: Protection::Unprotected,
        send: Protection::Unprotected,
        handshake_fragments: seq![],
        read_closed: false,
        key_update_owed: false,
    };
    apply_actions(p, connection, seq![Action::SendHandshake(write_client_hello(hello), initial_client_hello_record_version())])
}

/// §4 and §5.1: "Handshake messages MAY be coalesced into a single TLSPlaintext record or
/// fragmented across several records": take whole messages off `buffer`, leaving the
/// remainder for the next record.
pub open spec fn process_handshake_bytes(p: Primitives, connection: Connection, buffer: Seq<u8>) -> Receive
    decreases buffer.len(),
{
    match read_handshake_header(buffer) {
        None => Receive::Continue(Progress {
            connection: Connection { handshake_fragments: buffer, ..connection },
            application_data: seq![],
            records_to_send: seq![],
        }),
        Some(header) =>
            if buffer.len() < 4 + header.length {
                Receive::Continue(Progress {
                    connection: Connection { handshake_fragments: buffer, ..connection },
                    application_data: seq![],
                    records_to_send: seq![],
                })
            } else {
                let raw = buffer.subrange(0, (4 + header.length) as int);
                let rest = buffer.subrange((4 + header.length) as int, buffer.len() as int);
                match receive_handshake_message(p, connection.handshake, raw) {
                    HandshakeStep::Abort(error) => Receive::Abort(error),
                    HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                        // §5.1: "Implementations MUST verify that all messages immediately
                        // preceding a key change align with a record boundary".
                        if receive_key_changes && rest.len() != 0 {
                            Receive::Abort(ClientError::KeyChangeNotAligned)
                        } else {
                            let (after_actions, sent) = apply_actions(p, Connection { handshake, ..connection }, actions);
                            match process_handshake_bytes(p, after_actions, rest) {
                                Receive::Continue(progress) => Receive::Continue(Progress {
                                    records_to_send: sent + progress.records_to_send,
                                    ..progress
                                }),
                                other => other,
                            }
                        },
                }
            },
    }
}

/// §5.1, §5.4: a fragment of a handshake record, plain or from a TLSInnerPlaintext.
pub open spec fn receive_handshake_content(p: Primitives, connection: Connection, content: Seq<u8>) -> Receive {
    // §5.4: "MUST NOT send Handshake and Alert records that have a zero-length
    // TLSInnerPlaintext.content".
    if content.len() == 0 {
        Receive::Abort(ClientError::ZeroLengthContent)
    } else {
        process_handshake_bytes(p, connection, connection.handshake_fragments + content)
    }
}

/// §5.1, §6: the content of an alert record.
pub open spec fn receive_alert_content(connection: Connection, content: Seq<u8>) -> Receive {
    if connection.handshake_fragments.len() != 0 {
        // §5.1: "Handshake messages MUST NOT be interleaved with other record types."
        Receive::Abort(ClientError::InterleavedRecord)
    } else if content.len() == 0 {
        // §5.4.
        Receive::Abort(ClientError::ZeroLengthContent)
    } else {
        match read_alert(content) {
            // §5.1, §6.
            None => Receive::Abort(ClientError::Malformed),
            Some((_level, description)) =>
                if description == ad_close_notify() {
                    // §6.1.
                    Receive::Continue(Progress {
                        connection: Connection { read_closed: true, ..connection },
                        application_data: seq![],
                        records_to_send: seq![],
                    })
                } else if description == ad_user_canceled() {
                    // Changed by the equivalence author (transcription_equivalence): this
                    // file closed the read side on user_canceled too. §6.1: user_canceled
                    // "notifies the recipient that the sender is canceling the handshake for
                    // some reason unrelated to a protocol failure" and "This alert SHOULD be
                    // followed by a 'close_notify'", which would be ignored if user_canceled
                    // had already ended the read side; "Any data received after a closure
                    // alert" is read as after the close_notify. So it changes nothing.
                    Receive::Continue(Progress { connection, application_data: seq![], records_to_send: seq![] })
                } else {
                    // §6: "Upon receiving an error alert, the TLS implementation SHOULD
                    // indicate an error to the application and MUST NOT allow any further
                    // data to be sent or received on the connection."
                    Receive::PeerError(description)
                },
        }
    }
}

/// §5: the content of a TLSCiphertext once deprotected, or a plaintext record's, by its
/// real type.
pub open spec fn receive_protected_content(p: Primitives, connection: Connection, content_type: nat, content: Seq<u8>) -> Receive {
    if content_type == ct_change_cipher_spec() {
        // §5: "or which receives a protected change_cipher_spec record".
        Receive::Abort(ClientError::ChangeCipherSpecProtected)
    } else if content_type == ct_alert() {
        receive_alert_content(connection, content)
    } else if content_type == ct_handshake() {
        receive_handshake_content(p, connection, content)
    } else if content_type == ct_application_data() {
        if connection.handshake_fragments.len() != 0 {
            // §5.1.
            Receive::Abort(ClientError::InterleavedRecord)
        } else if connection.handshake.state != ClientState::Connected {
            // §4.4.4: "Once a side has sent its Finished message and has received and
            // validated the Finished message from its peer, it may begin to send and
            // receive Application Data"; §6.2 "premature Application Data".
            Receive::Abort(ClientError::UnexpectedRecordType)
        } else {
            Receive::Continue(Progress { connection, application_data: content, records_to_send: seq![] })
        }
    } else {
        // §5: "receives an unexpected record type".
        Receive::Abort(ClientError::UnexpectedRecordType)
    }
}

/// §5.2: "plaintext of encrypted_record = AEAD-Decrypt(peer_write_key, nonce,
/// additional_data, AEADEncrypted)", and what follows it.
pub open spec fn receive_ciphertext(p: Primitives, connection: Connection, traffic: TrafficState,
    legacy_record_version: nat, encrypted_record: Seq<u8>) -> Receive
{
    if traffic.sequence_number > max_sequence_number() {
        // §5.3.
        Receive::Abort(ClientError::SequenceNumberWrap)
    } else {
        let additional = additional_data(ct_application_data(), legacy_record_version, encrypted_record.len());
        let nonce = per_record_nonce(traffic.iv, traffic.sequence_number);
        match (p.aead_decrypt)(traffic.key, nonce, additional, encrypted_record) {
            // §5.2: "If the decryption fails, the receiver MUST terminate the connection
            // with a 'bad_record_mac' alert."
            None => Receive::Abort(ClientError::DeprotectionFailed),
            Some(cleartext) =>
                // §5.4, §6.2 record_overflow.
                if cleartext.len() > max_inner_plaintext_length() {
                    Receive::Abort(ClientError::InnerPlaintextTooLong)
                } else {
                    match read_inner_plaintext(cleartext) {
                        // §5.4.
                        None => Receive::Abort(ClientError::NoContentType),
                        Some((content, content_type)) => {
                            // §5.3: "incremented by one after reading".
                            let after = Connection {
                                receive: Protection::Protected(TrafficState {
                                    sequence_number: traffic.sequence_number + 1,
                                    ..traffic
                                }),
                                ..connection
                            };
                            receive_protected_content(p, after, content_type, content)
                        },
                    }
                },
        }
    }
}

/// §5: "If a TLS implementation receives an unexpected record type"; §5.1, §5.2: which
/// length limit applies is what the record is being read as.
pub open spec fn record_length_failure(connection: Connection, header: RecordHeader) -> Option<ClientError> {
    match connection.receive {
        Protection::Protected(_) =>
            if header.content_type == ct_application_data() {
                if header.length > max_ciphertext_length() { Some(ClientError::CiphertextTooLong) } else { None }
            } else if header.length > max_plaintext_length() {
                Some(ClientError::PlaintextTooLong)
            } else {
                None
            },
        Protection::Unprotected =>
            if header.length > max_plaintext_length() { Some(ClientError::PlaintextTooLong) } else { None },
    }
}

/// §5: one record, by the rules of §5, §5.1, §5.2 and §5.4, given its header and exactly
/// its fragment.
pub open spec fn receive_record(p: Primitives, connection: Connection, header: RecordHeader, fragment: Seq<u8>) -> Receive {
    // §6.1: "Any data received after a closure alert has been received MUST be ignored."
    if connection.read_closed {
        Receive::Continue(Progress { connection, application_data: seq![], records_to_send: seq![] })
    } else if header.content_type == ct_change_cipher_spec() {
        // §5: "An implementation may receive an unencrypted record of type
        // change_cipher_spec consisting of the single byte value 0x01 at any time after the
        // first ClientHello message has been sent or received and before the peer's
        // Finished message has been received and MUST simply drop it without further
        // processing. ... An implementation which receives any other change_cipher_spec
        // value ... MUST abort the handshake with an 'unexpected_message' alert. If an
        // implementation detects a change_cipher_spec record received before the first
        // ClientHello message or after the peer's Finished message, it MUST be treated as
        // an unexpected record type".
        if connection.handshake.state == ClientState::Start || connection.handshake.state == ClientState::Connected {
            Receive::Abort(ClientError::UnexpectedRecordType)
        } else if fragment != seq![0x01u8] {
            Receive::Abort(ClientError::ChangeCipherSpecBadValue)
        } else if connection.handshake_fragments.len() != 0 {
            // Changed by the equivalence author (transcription_equivalence), resolving
            // docs/ERRATA.md "RFC 8446 §5 and §5.1: a compatibility CCS inside a
            // fragmented handshake message". §5.1: "Handshake messages MUST NOT be
            // interleaved with other record types. That is, if a handshake message is
            // split over two or more records, there MUST NOT be any other records
            // between them." This file already reads that sentence as a receiver's rule
            // for alert and application data records (`InterleavedRecord`); a
            // change_cipher_spec record is another record type, and Appendix D.4 puts the
            // server's at a message boundary ("immediately after its first handshake
            // message"), so §5's drop is read as applying at a boundary only.
            Receive::Abort(ClientError::InterleavedRecord)
        } else {
            Receive::Continue(Progress { connection, application_data: seq![], records_to_send: seq![] })
        }
    } else {
        match connection.receive {
            Protection::Unprotected =>
                if header.content_type == ct_alert() {
                    receive_alert_content(connection, fragment)
                } else if header.content_type == ct_handshake() {
                    receive_handshake_content(p, connection, fragment)
                } else {
                    // §5.1: "Application Data records MUST NOT be written to the wire
                    // unprotected". §5: "unexpected record type".
                    Receive::Abort(ClientError::UnexpectedRecordType)
                },
            Protection::Protected(traffic) =>
                if header.content_type == ct_application_data() {
                    // §5.2: "opaque_type ... is always set to the value 23".
                    receive_ciphertext(p, connection, traffic, header.legacy_record_version, fragment)
                } else {
                    Receive::Abort(ClientError::UnexpectedRecordType)
                },
        }
    }
}

/// §5: "Received data is verified, decrypted, reassembled, and then delivered". All whole
/// records of `stream`. The bytes of an incomplete last record are returned with it in the
/// second place of the pair.
pub open spec fn receive_stream(p: Primitives, connection: Connection, stream: Seq<u8>) -> (Receive, Seq<u8>)
    decreases stream.len(),
{
    match read_record_header(stream) {
        None => (Receive::Continue(Progress { connection, application_data: seq![], records_to_send: seq![] }), stream),
        Some(header) =>
            if !connection.read_closed && record_length_failure(connection, header) is Some {
                (Receive::Abort(record_length_failure(connection, header)->0), seq![])
            } else if stream.len() < 5 + header.length {
                (Receive::Continue(Progress { connection, application_data: seq![], records_to_send: seq![] }), stream)
            } else {
                let fragment = stream.subrange(5, (5 + header.length) as int);
                let rest = stream.subrange((5 + header.length) as int, stream.len() as int);
                match receive_record(p, connection, header, fragment) {
                    Receive::Continue(first) => {
                        let (outcome, leftover) = receive_stream(p, first.connection, rest);
                        match outcome {
                            Receive::Continue(second) => (Receive::Continue(Progress {
                                connection: second.connection,
                                application_data: first.application_data + second.application_data,
                                records_to_send: first.records_to_send + second.records_to_send,
                            }), leftover),
                            other => (other, leftover),
                        }
                    },
                    other => (other, rest),
                }
            },
    }
}

/// A.1's note: "clients may send alerts that derive from post-ServerHello messages in the
/// clear or with the early data keys. If clients need to send such alerts, they SHOULD
/// first rekey to the handshake keys if possible." From WAIT_EE to WAIT_FINISHED, K_send
/// has not been set, so the alert goes under the client's handshake keys, at sequence
/// number 0.
pub open spec fn protection_for_alert(p: Primitives, connection: Connection) -> Protection {
    match connection.handshake.state {
        ClientState::WaitEe | ClientState::WaitCertCr | ClientState::WaitCert
        | ClientState::WaitCv | ClientState::WaitFinished =>
            Protection::Protected(traffic_state(p, connection.handshake.client_handshake_traffic_secret)),
        _ => connection.send,
    }
}

/// §6.2: "Whenever an implementation encounters a fatal error condition, it SHOULD send an
/// appropriate fatal alert and MUST close the connection without sending or receiving any
/// additional data." §6: alert messages "are encrypted as specified by the current
/// connection state". The record for an alert, whose level comes from `write_alert`.
pub open spec fn alert_record(p: Primitives, connection: Connection, description: nat) -> Seq<u8> {
    send_one(p, protection_for_alert(p, connection), ct_alert(), other_record_version(), write_alert(description)).0
}

/// The record to send on detecting `error`.
pub open spec fn abort_record(p: Primitives, connection: Connection, error: ClientError) -> Seq<u8> {
    alert_record(p, connection, required_alert(error))
}

/// §6.1: "Each party MUST send a 'close_notify' alert before closing its write side of the
/// connection, unless it has already sent some error alert."
pub open spec fn close_write(p: Primitives, connection: Connection) -> Seq<u8> {
    alert_record(p, connection, ad_close_notify())
}

/// The outcome of a send.
pub enum SendResult {
    /// "premature Application Data": not in CONNECTED.
    NotConnected,
    /// The records to write, and the connection after them.
    Sent(Seq<Seq<u8>>, Connection),
}

/// §4.6.3: send a KeyUpdate. "Both sender and receiver MUST encrypt their KeyUpdate
/// messages with the old keys." "After sending a KeyUpdate message, the sender SHALL send
/// all its traffic using the next generation of keys".
pub open spec fn send_key_update(p: Primitives, connection: Connection, request_update: nat) -> (Seq<Seq<u8>>, Connection) {
    let (records, send) = send_blocks(p, connection.send, ct_handshake(), other_record_version(),
        fragment_blocks(write_key_update(request_update)));
    (records, Connection { send: updated_traffic(p, send), ..connection })
}

/// A.1, "Can send app data after here"; §4.6.3's owed KeyUpdate first ("prior to sending
/// its next Application Data record"); §5.3's "MUST either rekey" when the write sequence
/// number would run out.
pub open spec fn send_application_data(p: Primitives, connection: Connection, data: Seq<u8>) -> SendResult {
    if connection.handshake.state != ClientState::Connected {
        SendResult::NotConnected
    } else {
        // One record early, so that the KeyUpdate itself still has a number.
        let must_rekey = connection.key_update_owed || match connection.send {
            Protection::Protected(traffic) => traffic.sequence_number + fragment_blocks(data).len() > max_sequence_number(),
            Protection::Unprotected => false,
        };
        let (update_records, after_update) = if must_rekey {
            send_key_update(p, Connection { key_update_owed: false, ..connection }, update_not_requested())
        } else {
            (seq![], connection)
        };
        let (records, send) = send_blocks(p, after_update.send, ct_application_data(), other_record_version(), fragment_blocks(data));
        SendResult::Sent(update_records + records, Connection { send, ..after_update })
    }
}

} // verus!
