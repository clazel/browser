//! Verification parameters for the initial TLS authentication machine.
//! Production X.509 and signature implementations are not provided here.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Certificate and signature verification, joined to production providers later.
pub trait Verifier {
    /// Pure functions implemented by this validator for its configured trust store.
    spec fn functions(&self) -> super::spec::Verification;

    /// RFC 8446 §4.4.2: validate this chain for exactly this typed host and
    /// time; return its end-entity key or a typed certificate error.
    fn chain(&self, host: &crate::host::exec::Host, now: u64, certificate_body: &[u8]) -> (out: Result<Vec<u8>, super::spec::CertificateError>)
        ensures match out {
            Ok(key) => (self.functions().chain)(host@, now, certificate_body@) == Ok(key@),
            Err(error) => (self.functions().chain)(host@, now, certificate_body@) == Err(error),
        };

    /// RFC 8446 §4.4.3: verify this signature with the validated leaf key.
    fn signature(&self, key: &[u8], scheme: u16, input: &[u8], signature: &[u8]) -> (out: bool)
        ensures out == (self.functions().signature)(key@, scheme, input@, signature@);

    /// RFC 8446 §4.4.4: compare Finished values. The production join must
    /// use a timing-safe comparison; this functional contract does not prove timing.
    fn finished_equal(&self, received: &[u8], expected: &[u8]) -> (out: bool)
        requires received.len() == 32, expected.len() == 32,
        ensures out == (received@ == expected@);
}
} // verus!
