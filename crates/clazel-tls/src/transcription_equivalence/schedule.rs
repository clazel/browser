//! RFC 8446 §7.1 to §7.3 and §4.4.4: `schedule::spec` proven equal to the
//! clean-room `transcription::key_schedule` (and `authentication`'s
//! `finished_key`/`verify_data`), for every input:
//! [`theorem_schedule_equivalence`].
//!
//! How the two are compared:
//! - **Primitives.** `schedule::spec::Crypto`'s four fields are the
//!   transcription's `Primitives` fields of the same name ([`crypto_agrees`]).
//!   Nothing else of `Primitives` is used by either side here.
//! - **Messages.** `schedule::spec::derive_secret` takes the concatenated
//!   handshake encodings; the transcription takes the list of raw messages and
//!   the retry flag of §4.4.1. With the flag false they agree for every list
//!   whose concatenation is the crate's bytes. The retried case is
//!   `transcript::spec`'s, compared in [`super::transcript`].
//! - **Lengths.** The crate passes `Length` as `u16`; the transcription as
//!   `nat`. Every length either side uses (32, 12) fits.
//! - **What only one side has.** The PSK branches of §7.1 (binder_key,
//!   client_early_traffic_secret, early_exporter_master_secret) and the two
//!   exporter-related secrets (exporter_master_secret, resumption_master_secret)
//!   exist only in the transcription; the crate specifies no PSK, resumption or
//!   exporter (its header says so), so there is nothing to compare them with.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's `Crypto` is the transcription's `Primitives`, field by field.
pub open spec fn crypto_agrees(c: crate::schedule::spec::Crypto, p: crate::transcription::primitives::Primitives) -> bool {
    c.hash == p.hash && c.extract == p.hkdf_extract && c.expand == p.hkdf_expand && c.hmac == p.hmac
}

/// The transcription's label for each of the crate's.
pub open spec fn transcription_label(label: crate::schedule::spec::Label) -> Seq<u8> {
    match label {
        crate::schedule::spec::Label::Derived => crate::transcription::key_schedule::label_derived(),
        crate::schedule::spec::Label::ClientHandshake => crate::transcription::key_schedule::label_c_hs_traffic(),
        crate::schedule::spec::Label::ServerHandshake => crate::transcription::key_schedule::label_s_hs_traffic(),
        crate::schedule::spec::Label::ClientApplication => crate::transcription::key_schedule::label_c_ap_traffic(),
        crate::schedule::spec::Label::ServerApplication => crate::transcription::key_schedule::label_s_ap_traffic(),
        crate::schedule::spec::Label::Finished => crate::transcription::key_schedule::label_finished(),
        crate::schedule::spec::Label::Update => crate::transcription::key_schedule::label_traffic_upd(),
        crate::schedule::spec::Label::Key => crate::transcription::key_schedule::label_key(),
        crate::schedule::spec::Label::Iv => crate::transcription::key_schedule::label_iv(),
    }
}

/// §3.3: the two encoders of a number in network byte order are one function.
pub proof fn lemma_be_bytes(value: nat, width: nat)
    ensures crate::spec::be_bytes(value, width) == crate::transcription::presentation::encode_uint(value, width),
    decreases width,
{
    if width > 0 {
        lemma_be_bytes(value / 256, (width - 1) as nat);
    }
}

/// §3.4: the two encoders of a vector agree on every ceiling below 2^24 (no
/// vector of either side has a larger one).
pub proof fn lemma_write_vec(body: Seq<u8>, ceiling: nat)
    requires ceiling < 0x100_0000,
    ensures crate::spec::write_vec(body, ceiling) == crate::transcription::presentation::write_vector(body, ceiling),
{
    lemma_be_bytes(body.len(), crate::spec::len_width(ceiling));
}

/// The labels are the same bytes, and so is the `"tls13 "` prefix.
pub proof fn lemma_labels(label: crate::schedule::spec::Label)
    ensures
        crate::schedule::spec::label_bytes(label) == transcription_label(label),
        crate::schedule::spec::prefix() == crate::transcription::key_schedule::label_prefix(),
{
    assert(crate::schedule::spec::prefix() =~= crate::transcription::key_schedule::label_prefix());
    match label {
        crate::schedule::spec::Label::Derived =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::ClientHandshake =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::ServerHandshake =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::ClientApplication =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::ServerApplication =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::Finished =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::Update =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::Key =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
        crate::schedule::spec::Label::Iv =>
            assert(crate::schedule::spec::label_bytes(label) =~= transcription_label(label)),
    }
}

/// §7.1: "0" is the same 32 zero bytes on both sides.
pub proof fn lemma_zeros()
    ensures crate::schedule::spec::zeros() == crate::transcription::primitives::zero_value(),
{
    assert(crate::schedule::spec::zeros() =~= crate::transcription::primitives::zero_value());
}

/// §7.1 HkdfLabel: the same bytes for every label, context and length.
pub proof fn lemma_hkdf_label(label: Seq<u8>, context: Seq<u8>, length: u16)
    ensures
        crate::schedule::spec::hkdf_label(label, context, length)
            == crate::transcription::key_schedule::hkdf_label(length as nat, label, context),
{
    lemma_be_bytes(length as nat, 2);
    lemma_write_vec(crate::schedule::spec::prefix() + label, 255);
    lemma_write_vec(context, 255);
    lemma_labels(crate::schedule::spec::Label::Derived);
}

/// RFC 8446 §7.1 to §7.3 and §4.4.4, for every secret, context, message
/// list, length and label: HKDF-Expand-Label, Derive-Secret, the Early,
/// Handshake and Master Secrets, §7.2's next application traffic secret,
/// §7.3's key and IV, and §4.4.4's finished_key and verify_data are the same
/// values on both sides, whenever the primitives are the same functions.
pub proof fn theorem_schedule_equivalence(c: crate::schedule::spec::Crypto, p: crate::transcription::primitives::Primitives)
    requires crypto_agrees(c, p),
    ensures
        // §7.1 HKDF-Expand-Label.
        forall|secret: Seq<u8>, label: crate::schedule::spec::Label, context: Seq<u8>, length: u16|
            #[trigger] crate::schedule::spec::expand_label(c, secret, label, context, length)
                == crate::transcription::key_schedule::hkdf_expand_label(p, secret, transcription_label(label), context, length as nat),
        // §7.1 Derive-Secret, for any list of messages the crate's bytes concatenate.
        forall|secret: Seq<u8>, label: crate::schedule::spec::Label, messages: Seq<Seq<u8>>|
            #[trigger] crate::schedule::spec::derive_secret(c, secret, label, crate::transcription::presentation::concatenate(messages))
                == crate::transcription::key_schedule::derive_secret(p, secret, transcription_label(label), messages, false),
        // §7.1 diagram: Early Secret without PSK ("HKDF-Extract(0, 0)").
        crate::schedule::spec::early_secret(c)
            == crate::transcription::key_schedule::early_secret(p, crate::transcription::primitives::zero_value()),
        // §7.1 diagram: Handshake Secret.
        forall|early: Seq<u8>, dhe: Seq<u8>|
            #[trigger] crate::schedule::spec::handshake_secret(c, early, dhe)
                == crate::transcription::key_schedule::handshake_secret(p, early, dhe),
        // §7.1 diagram: Master Secret.
        forall|handshake: Seq<u8>|
            #[trigger] crate::schedule::spec::master_secret(c, handshake)
                == crate::transcription::key_schedule::master_secret(p, handshake),
        // §7.1: the four traffic secrets from their parent secret and transcript.
        forall|handshake: Seq<u8>, messages: Seq<Seq<u8>>|
            #[trigger] crate::schedule::spec::derive_secret(c, handshake, crate::schedule::spec::Label::ClientHandshake,
                crate::transcription::presentation::concatenate(messages))
                == crate::transcription::key_schedule::client_handshake_traffic_secret(p, handshake, messages, false),
        forall|handshake: Seq<u8>, messages: Seq<Seq<u8>>|
            #[trigger] crate::schedule::spec::derive_secret(c, handshake, crate::schedule::spec::Label::ServerHandshake,
                crate::transcription::presentation::concatenate(messages))
                == crate::transcription::key_schedule::server_handshake_traffic_secret(p, handshake, messages, false),
        forall|master: Seq<u8>, messages: Seq<Seq<u8>>|
            #[trigger] crate::schedule::spec::derive_secret(c, master, crate::schedule::spec::Label::ClientApplication,
                crate::transcription::presentation::concatenate(messages))
                == crate::transcription::key_schedule::client_application_traffic_secret_0(p, master, messages, false),
        forall|master: Seq<u8>, messages: Seq<Seq<u8>>|
            #[trigger] crate::schedule::spec::derive_secret(c, master, crate::schedule::spec::Label::ServerApplication,
                crate::transcription::presentation::concatenate(messages))
                == crate::transcription::key_schedule::server_application_traffic_secret_0(p, master, messages, false),
        // §7.2.
        forall|secret: Seq<u8>|
            #[trigger] crate::schedule::spec::next_traffic_secret(c, secret)
                == crate::transcription::key_schedule::next_application_traffic_secret(p, secret),
        // §7.3, with the suite's key_length 32 and iv_length 12.
        forall|secret: Seq<u8>|
            #[trigger] crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Key, seq![], 32)
                == crate::transcription::key_schedule::write_key(p, secret),
        forall|secret: Seq<u8>|
            #[trigger] crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Iv, seq![], 12)
                == crate::transcription::key_schedule::write_iv(p, secret),
        // §4.4.4 finished_key and verify_data.
        forall|base: Seq<u8>|
            #[trigger] crate::schedule::spec::expand_label(c, base, crate::schedule::spec::Label::Finished, seq![], 32)
                == crate::transcription::authentication::finished_key(p, base),
        forall|base: Seq<u8>, messages: Seq<Seq<u8>>|
            #[trigger] crate::schedule::spec::finished(c, base, crate::transcription::presentation::concatenate(messages))
                == crate::transcription::authentication::verify_data(p, base, messages, false),
{
    assert forall|secret: Seq<u8>, label: crate::schedule::spec::Label, context: Seq<u8>, length: u16|
        #[trigger] crate::schedule::spec::expand_label(c, secret, label, context, length)
            == crate::transcription::key_schedule::hkdf_expand_label(p, secret, transcription_label(label), context, length as nat)
    by {
        lemma_labels(label);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(label), context, length);
    }
    assert forall|secret: Seq<u8>, label: crate::schedule::spec::Label, messages: Seq<Seq<u8>>|
        #[trigger] crate::schedule::spec::derive_secret(c, secret, label, crate::transcription::presentation::concatenate(messages))
            == crate::transcription::key_schedule::derive_secret(p, secret, transcription_label(label), messages, false)
    by {
        lemma_labels(label);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(label),
            (c.hash)(crate::transcription::presentation::concatenate(messages)), 32);
    }
    lemma_zeros();
    lemma_labels(crate::schedule::spec::Label::Derived);
    lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Derived), (c.hash)(seq![]), 32);
    assert(crate::transcription::presentation::concatenate(seq![]) =~= Seq::<u8>::empty());
    assert forall|early: Seq<u8>, dhe: Seq<u8>|
        #[trigger] crate::schedule::spec::handshake_secret(c, early, dhe)
            == crate::transcription::key_schedule::handshake_secret(p, early, dhe)
    by {
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Derived), (c.hash)(seq![]), 32);
    }
    assert forall|handshake: Seq<u8>|
        #[trigger] crate::schedule::spec::master_secret(c, handshake)
            == crate::transcription::key_schedule::master_secret(p, handshake)
    by {
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Derived), (c.hash)(seq![]), 32);
    }
    assert forall|secret: Seq<u8>|
        #[trigger] crate::schedule::spec::next_traffic_secret(c, secret)
            == crate::transcription::key_schedule::next_application_traffic_secret(p, secret)
    by {
        lemma_labels(crate::schedule::spec::Label::Update);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Update), seq![], 32);
    }
    assert forall|secret: Seq<u8>|
        #[trigger] crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Key, seq![], 32)
            == crate::transcription::key_schedule::write_key(p, secret)
    by {
        lemma_labels(crate::schedule::spec::Label::Key);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Key), seq![], 32);
    }
    assert forall|secret: Seq<u8>|
        #[trigger] crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Iv, seq![], 12)
            == crate::transcription::key_schedule::write_iv(p, secret)
    by {
        lemma_labels(crate::schedule::spec::Label::Iv);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Iv), seq![], 12);
    }
    assert forall|base: Seq<u8>|
        #[trigger] crate::schedule::spec::expand_label(c, base, crate::schedule::spec::Label::Finished, seq![], 32)
            == crate::transcription::authentication::finished_key(p, base)
    by {
        lemma_labels(crate::schedule::spec::Label::Finished);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Finished), seq![], 32);
    }
    assert forall|base: Seq<u8>, messages: Seq<Seq<u8>>|
        #[trigger] crate::schedule::spec::finished(c, base, crate::transcription::presentation::concatenate(messages))
            == crate::transcription::authentication::verify_data(p, base, messages, false)
    by {
        lemma_labels(crate::schedule::spec::Label::Finished);
        lemma_hkdf_label(crate::schedule::spec::label_bytes(crate::schedule::spec::Label::Finished), seq![], 32);
    }
}

} // verus!
