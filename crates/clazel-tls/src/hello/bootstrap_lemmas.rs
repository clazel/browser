//! Size and binding lemmas for bootstrap flights.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// A successful fixed-profile HRR retry always fits one TLSPlaintext record.
pub proof fn lemma_retry_flight_bound(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::client_spec::State, server: Seq<u8>, cookie: Seq<u8>,
    next: super::client_spec::State, flight: Seq<u8>)
    requires super::client_spec::wf(before),
        super::client_spec::retry(hash, before, server, cookie)
            == Ok(super::client_spec::Outcome::Retry(next, flight)),
    ensures next.config == before.config, next.transcript.retried,
        flight == crate::spec::write_handshake(1, super::client_spec::body(next.config, cookie)),
        flight.len() <= 4528, flight.len() < 65536,
{
    super::client_lemmas::lemma_retry_configuration(hash, before, server, cookie, next, flight);
    assert(super::client_spec::cookie_ok(cookie));
    assert(cookie.len() <= super::client_spec::MAX_COOKIE);
    super::client_lemmas::lemma_profile(next.config, cookie);
    reveal(crate::spec::write_handshake);
    crate::lemmas_pl::lemma_be_bytes_len(super::client_spec::body(next.config, cookie).len(), 3);
    reveal(crate::spec::write_u24);
    assert(flight.len() == 4 + super::client_spec::body(next.config, cookie).len());
    assert(flight.len() <= 4528);
}

/// A retry selected by the fixed-profile receive operation has a bounded CH2.
pub proof fn lemma_receive_retry_flight_bound(hash: spec_fn(Seq<u8>) -> Seq<u8>,
    before: super::client_spec::State, server: Seq<u8>,
    next: super::client_spec::State, flight: Seq<u8>)
    requires super::client_spec::wf(before),
        super::client_spec::receive(hash, before, server)
            == Ok(super::client_spec::Outcome::Retry(next, flight)),
    ensures next.config == before.config, next.transcript.retried,
        flight.len() <= 4528, flight.len() < 65536,
{
    reveal(super::client_spec::receive);
    match super::spec::validate(before.config.session_id, before.transcript.retried, server) {
        Err(_) => assert(false),
        Ok(super::spec::Selection::Share(_)) => assert(false),
        Ok(super::spec::Selection::Retry(cookie)) => {
            assert(super::client_spec::retry(hash, before, server, cookie)
                == Ok(super::client_spec::Outcome::Retry(next, flight)));
            lemma_retry_flight_bound(hash, before, server, cookie, next, flight);
        },
    }
}
} // verus!
