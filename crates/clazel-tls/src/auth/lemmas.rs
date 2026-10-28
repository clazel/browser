//! Trace and effect properties of the initial authentication machine.
//! These are conditional on the supplied verification functions; they do not
//! assert that a production X.509/cryptography provider has been implemented.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// Recording preserves all authentication metadata and the transcript invariant.
pub proof fn lemma_record(c: crate::schedule::spec::Crypto, s: State,
    kind: crate::transcript::spec::Kind, body: Seq<u8>, phase: Phase)
    requires crate::transcript::spec::wf(s.transcript),
        s.transcript.phase == crate::transcript::spec::Phase::Handshake,
    ensures {
        let (next, action) = record(c, s, kind, body, phase);
        &&& crate::transcript::spec::wf(next.transcript)
        &&& next.transcript.phase == crate::transcript::spec::Phase::Handshake
        &&& next.config == s.config
        &&& next.key == s.key
        &&& next.requested == s.requested
        &&& next.chain_checked == s.chain_checked
        &&& next.signature_checked == s.signature_checked
        &&& next.finished_checked == s.finished_checked
        &&& next.client_sent == s.client_sent
        &&& next.application_hash == s.application_hash
        &&& (action is None || action is Fail)
        &&& (action is None ==> next.phase == phase)
        &&& (action is Fail ==> next.phase == Phase::Failed)
    },
{
    crate::transcript::lemmas::lemma_step_wf(c.hash, s.transcript, kind, body);
}

/// Every successful constructor establishes the authentication invariant.
pub proof fn lemma_start(config: Config, transcript: crate::transcript::spec::State)
    ensures match start(config, transcript) { Ok(s) => wf(s), Err(_) => true },
{
}

/// Finished processing emits only a fatal failure or the validated client flight.
pub proof fn lemma_finished(c: crate::schedule::spec::Crypto, s: State, received: Seq<u8>)
    requires wf(s), s.phase == Phase::Finished,
    ensures {
        let (next, action) = accept_finished(c, s, received);
        &&& wf(next)
        &&& (action is Fail || action is Send)
        &&& super::contract::send_safe(next, action)
    },
{
    if received == crate::schedule::spec::finished(c, s.config.server_secret, s.transcript.messages) {
        let checked = State { finished_checked: true, ..s };
        lemma_record(c, checked, crate::transcript::spec::Kind::Finished, received, Phase::SendFinished);
        let (s1, a1) = record(c, checked, crate::transcript::spec::Kind::Finished, received, Phase::SendFinished);
        if !(a1 is Fail) {
            let s1 = State { application_hash: (c.hash)(s1.transcript.messages), ..s1 };
            if s1.requested {
                lemma_record(c, s1, crate::transcript::spec::Kind::Certificate, empty_certificate(), Phase::SendFinished);
            }
            let (s2, a2) = if s1.requested {
                record(c, s1, crate::transcript::spec::Kind::Certificate, empty_certificate(), Phase::SendFinished)
            } else { (s1, Action::None) };
            if !(a2 is Fail) {
                let own = crate::schedule::spec::finished(c, s2.config.client_secret, s2.transcript.messages);
                lemma_record(c, s2, crate::transcript::spec::Kind::Finished, own, Phase::SendFinished);
            }
        }
    }
}

/// Parsed-message dispatch preserves the invariant and never delivers application data.
pub proof fn lemma_dispatch(c: crate::schedule::spec::Crypto, v: Verification, s: State, body: Seq<u8>, message: crate::spec::HsMsg)
    requires wf(s),
    ensures {
        let (next, action) = dispatch(c, v, s, body, message);
        &&& wf(next)
        &&& !(action is Deliver)
        &&& !(action is Ready)
        &&& super::contract::send_safe(next, action)
    },
{
    match message {
        crate::spec::HsMsg::EncryptedExtensions(es) => {
            if s.phase == Phase::EncryptedExtensions && extensions_offered(es, s.config.extensions) {
                lemma_record(c, s, crate::transcript::spec::Kind::EncryptedExtensions, body, Phase::CertificateOrRequest);
            }
        },
        crate::spec::HsMsg::CertificateRequest(request) => {
            if s.phase == Phase::CertificateOrRequest && request.context.len() == 0 && crate::spec::has_ext(request.extensions, 13) {
                lemma_record(c, State { requested: true, ..s }, crate::transcript::spec::Kind::CertificateRequest, body, Phase::Certificate);
            }
        },
        crate::spec::HsMsg::Certificate(certificate) => {
            if (s.phase == Phase::CertificateOrRequest || s.phase == Phase::Certificate) && certificate.entries.len() > 0 {
                match (v.chain)(s.config.host, s.config.now, body) {
                    Ok(key) => {
                        if key.len() <= MAX_KEY {
                            lemma_record(c, State { key, chain_checked: true, ..s }, crate::transcript::spec::Kind::Certificate, body, Phase::CertificateVerify);
                        }
                    },
                    Err(_) => {},
                }
            }
        },
        crate::spec::HsMsg::CertificateVerify(cv) => {
            let input = crate::transcript::spec::certificate_verify_input(true, (c.hash)(s.transcript.messages));
            if s.phase == Phase::CertificateVerify && signature_scheme(cv.algorithm) && member(s.config.signatures, cv.algorithm)
                && (v.signature)(s.key, cv.algorithm, input, cv.signature)
            {
                lemma_record(c, State { signature_checked: true, ..s }, crate::transcript::spec::Kind::CertificateVerify, body, Phase::Finished);
            }
        },
        crate::spec::HsMsg::Finished(received) => {
            if s.phase == Phase::Finished && received.len() == 32 { lemma_finished(c, s, received); }
        },
        _ => {},
    }
}

/// §4.4.2: a new chain-check flag comes from this host/time/body validation result.
pub proof fn theorem_certificate_binding(c: crate::schedule::spec::Crypto, v: Verification, s: State, body: Seq<u8>, empty: bool, offered: bool)
    requires wf(s), !s.chain_checked,
    ensures {
        let next = on_certificate(c, v, s, body, true, empty, offered).0;
        next.chain_checked ==> (v.chain)(s.config.host, s.config.now, body) == Ok(next.key)
    },
{
    if (s.phase == Phase::CertificateOrRequest || s.phase == Phase::Certificate) && !empty && offered {
        match (v.chain)(s.config.host, s.config.now, body) {
            Ok(key) => {
                if key.len() <= MAX_KEY {
                    lemma_record(c, State { key, chain_checked: true, ..s }, crate::transcript::spec::Kind::Certificate, body, Phase::CertificateVerify);
                }
            },
            Err(_) => {},
        }
    }
}

/// §4.4.3: the signature check binds the leaf key, offered scheme and server transcript context.
pub proof fn theorem_signature_binding(c: crate::schedule::spec::Crypto, v: Verification, s: State, body: Seq<u8>, algorithm: u16, signature: Seq<u8>)
    requires wf(s), !s.signature_checked,
    ensures {
        let next = on_verify(c, v, s, body, algorithm, signature).0;
        next.signature_checked ==> signature_scheme(algorithm) && member(s.config.signatures, algorithm)
            && (v.signature)(s.key, algorithm,
                crate::transcript::spec::certificate_verify_input(true, (c.hash)(s.transcript.messages)), signature)
    },
{
    let input = crate::transcript::spec::certificate_verify_input(true, (c.hash)(s.transcript.messages));
    if s.phase == Phase::CertificateVerify && signature_scheme(algorithm) && member(s.config.signatures, algorithm)
        && (v.signature)(s.key, algorithm, input, signature)
    {
        lemma_record(c, State { signature_checked: true, ..s }, crate::transcript::spec::Kind::CertificateVerify, body, Phase::Finished);
    }
}

/// §4.4.4: a new Finished-check flag matches the server secret and the pre-Finished transcript.
pub proof fn theorem_finished_binding(c: crate::schedule::spec::Crypto, s: State, received: Seq<u8>)
    requires wf(s), s.phase == Phase::Finished, !s.finished_checked,
    ensures accept_finished(c, s, received).0.finished_checked ==>
        received == crate::schedule::spec::finished(c, s.config.server_secret, s.transcript.messages),
{
}

/// One step preserves the authentication invariant and both effect gates.
pub proof fn lemma_step(c: crate::schedule::spec::Crypto, v: Verification, s: State, input: Input)
    requires wf(s),
    ensures {
        let (next, action) = step(c, v, s, input);
        &&& wf(next)
        &&& super::contract::delivery_safe(s, action)
        &&& super::contract::send_safe(next, action)
    },
{
    if s.phase != Phase::Failed && s.phase != Phase::Closed {
        match input {
            Input::Handshake(typ, body) => {
                if body.len() <= crate::transcript::spec::MAX_BODY {
                    match crate::spec::parse_handshake_body(typ, body, 32) {
                        crate::spec::Res::Ok(message) => lemma_dispatch(c, v, s, body, message),
                        crate::spec::Res::Err(_) => {},
                    }
                }
            },
            _ => {},
        }
    }
}

/// Arbitrary finite peer/I/O traces preserve the authentication invariant.
pub proof fn theorem_trace_invariant(c: crate::schedule::spec::Crypto, v: Verification, s: State, inputs: Seq<Input>)
    requires wf(s),
    ensures wf(run(c, v, s, inputs)),
    decreases inputs.len(),
{
    if inputs.len() > 0 {
        lemma_step(c, v, s, inputs[0]);
        theorem_trace_invariant(c, v, step(c, v, s, inputs[0]).0, inputs.skip(1));
    }
}

/// At every position of any trace, application delivery follows all checks and the send ack.
pub proof fn theorem_no_early_delivery(c: crate::schedule::spec::Crypto, v: Verification, s: State, prefix: Seq<Input>, input: Input)
    requires wf(s),
    ensures {
        let before = run(c, v, s, prefix);
        super::contract::delivery_safe(before, step(c, v, before, input).1)
    },
{
    theorem_trace_invariant(c, v, s, prefix);
    lemma_step(c, v, run(c, v, s, prefix), input);
}

/// A failed/closed connection cannot be revived by any subsequent input trace.
pub proof fn theorem_terminal(c: crate::schedule::spec::Crypto, v: Verification, s: State, inputs: Seq<Input>)
    requires s.phase == Phase::Failed || s.phase == Phase::Closed,
    ensures run(c, v, s, inputs) == s,
    decreases inputs.len(),
{
    if inputs.len() > 0 { theorem_terminal(c, v, s, inputs.skip(1)); }
}
} // verus!
