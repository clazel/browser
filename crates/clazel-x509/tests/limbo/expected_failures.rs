// Testcases whose verdict through `verify_server_chain` (accept-all links)
// is not limbo's, or that are not run, with the reason (conformance_limbo.rs).
// Checked in by hand. The test fails on any id that is missing, extra, or
// that now agrees with limbo. Where the reason is a profile rule, the
// refusal is deliberate and the rule is named; none of these is a known
// defect of the RFC 5280 6.1 code.

const NEEDS_CRL: &str = "needs CRL checking (Phase 8); the profile checks no revocation";
const NEEDS_SIGNATURE: &str = "needs signature verification (3.5f, P11)";
const NEEDS_MLDSA: &str = "needs ML-DSA signatures (RFC 9881; not in the 3.5b algorithm set): the chain is refused as an unsupported algorithm";
const NEEDS_CLIENT_VALIDATION: &str = "needs client-certificate path validation (3.5b); only server path validation exists";
const NO_PEER_NAME: &str = "SUCCESS without a DNS or IP peer name (a directoryName constraint case): verify_server_chain needs a reference identity, and a TLS server name is a DNS name or an IP address";
const PROFILE_CA_TARGET: &str = "browser profile refuses a CA certificate as the target (profile.rs, leaf/spec.rs: basicConstraints cA and keyCertSign without digitalSignature); limbo follows RFC 5280, which allows it";
const PROFILE_EKU_REQUIRED: &str = "browser profile requires extKeyUsage on the target (profile.rs (R), design Q7, BR 7.1.2.7.6); limbo's rfc5280 case follows RFC 5280 4.2.1.12, and its webpki::eku::ee-without-eku expects FAILURE";
const CA_RULE_AKI_SKI: &str = "an issuer-side certificate-profile rule (RFC 5280 4.2.1.1 / 4.2.1.2: a CA MUST include the extension); no RFC 5280 6.1 step reads the presence of authorityKeyIdentifier or subjectKeyIdentifier (names chain) and the profile adds no rule";
const CA_RULE_CRITICALITY: &str = "an issuer-side rule on an extension's criticality (RFC 5280 4.2.1.9, 4.2.1.10, 4.2.1.11: the CA MUST mark it critical); 6.1 processes the extension whatever its criticality, so the path is valid, and the profile adds no rule (nameConstraints and policyConstraints on an intermediate, basicConstraints on a trust anchor, which 6.1 takes as input)";
const CA_RULE_SERIAL: &str = "an issuer-side rule (RFC 5280 4.1.2.2: the serial number MUST be a positive integer); no 6.1 step reads it, and the profile adds no rule (whether both browsers refuse a zero serial is unconfirmed)";
const CABF_ROOT_PROFILE: &str = "a CA/Browser Forum rule on the content of a root certificate (BR 7.1.2.1.2 or 7.1.2.1.3); the trust anchor is an input to 6.1 and the profile does not audit it (Anchor construction checks only its role and key usage)";
const CABF_SAN_CRITICALITY: &str = "a CA/Browser Forum or RFC 5280 4.1.2.6 issuer-side rule on the criticality of subjectAltName given the subject (empty subject: critical; BR 7.1.2.7.12: otherwise not critical); the RFC 9525 match does not depend on it, and the profile adds no rule";
const CABF_LEAF_EKU: &str = "a CA/Browser Forum rule on a subscriber certificate's extKeyUsage that also contains serverAuth (BR 7.1.2.7.6 critical; 7.1.2.7.10 anyExtendedKeyUsage); the profile requires serverAuth and does not refuse the extra or critical forms (limbo: pedantic-webpki-eku)";
const CABF_CN: &str = "a CA/Browser Forum rule on the subject commonName (BR 7.1.4.3: it must copy a SAN entry); the peer name matches a subjectAltName entry, and the commonName is never read (RFC 9525), so the path is valid";
const CABF_AIA: &str = "a CA/Browser Forum rule on the content of authorityInfoAccess (a non-critical extension the decoders keep opaque; RFC 5280 6.1 does not read it)";
const LEAF_KEY_RULE: &str = "the profile has no rule on the target's key type or size (BR 6.1.5, limbo: pedantic-webpki-subscriber-key); the path verdict returns the key and a key the TLS stack cannot verify with fails at CertificateVerify; whether Chrome and Firefox refuse such a key is unconfirmed (accept only where both accept)";
const ROOT_RSA_BITS: &str = "BR 6.1.5 asks for an RSA modulus of a multiple of 8 bits and the real links accept this 2052-bit root (clazel-crypto/tests/chain_limbo.rs records that Chrome, Firefox and webpki accept it): a listed divergence, not a signature failure";

const EXPECTED_FAILURES: &[(&str, &str)] = &[
    ("crl::structure::crl-invalid-signature", NEEDS_CRL),
    ("crl::structure::crl-wrong-signing-key", NEEDS_CRL),
    ("crl::structure::crl-duplicate-revoked-serial", NEEDS_CRL),
    ("crl::structure::crl-unknown-critical-extension", NEEDS_CRL),
    ("crl::structure::entry-unknown-critical-extension", NEEDS_CRL),
    ("crl::structure::entry-unknown-noncritical-extension", NEEDS_CRL),
    ("crl::revoked-certificate-with-crl", NEEDS_CRL),
    ("crl::crlnumber-missing", NEEDS_CRL),
    ("crl::crlnumber-critical", NEEDS_CRL),
    ("crl::issuer-missing-crlsign", NEEDS_CRL),
    ("invalid::invalid-issuer-key", NEEDS_SIGNATURE),
    ("pathlen::validation-ignores-pathlen-in-leaf", PROFILE_CA_TARGET),
    ("rfc5280::aki::leaf-missing-aki", CA_RULE_AKI_SKI),
    ("rfc5280::aki::intermediate-missing-aki", CA_RULE_AKI_SKI),
    ("rfc5280::aki::cross-signed-root-missing-aki", CA_RULE_AKI_SKI),
    ("rfc5280::eku::ee-without-eku", PROFILE_EKU_REQUIRED),
    ("rfc5280::nc::permitted-dns-match-noncritical", CA_RULE_CRITICALITY),
    ("rfc5280::nc::permitted-dn-match", NO_PEER_NAME),
    ("rfc5280::nc::invalid-email-address", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-invalid-email-san", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-exact", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-domain", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-literal-asterisk-exact-match", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-literal-asterisk-rejects-user", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-literal-asterisk-rejects-subdomain", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-literal-double-asterisk", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-literal-double-asterisk-rejects-single", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::nc::nc-permits-email-literal-mid-asterisk", NEEDS_CLIENT_VALIDATION),
    ("rfc5280::pc::ica-noncritical-pc", CA_RULE_CRITICALITY),
    ("rfc5280::san::noncritical-with-empty-subject", CABF_SAN_CRITICALITY),
    ("rfc5280::serial::zero", CA_RULE_SERIAL),
    ("rfc5280::ski::root-missing-ski", CA_RULE_AKI_SKI),
    ("rfc5280::ski::intermediate-missing-ski", CA_RULE_AKI_SKI),
    ("rfc5280::root-non-critical-basic-constraints", CA_RULE_CRITICALITY),
    ("rfc5280::ca-as-leaf", PROFILE_CA_TARGET),
    ("rfc9881::ml-dsa-44", NEEDS_MLDSA),
    ("rfc9881::ml-dsa-65", NEEDS_MLDSA),
    ("rfc9881::ml-dsa-87", NEEDS_MLDSA),
    ("webpki::aki::root-with-aki-missing-keyidentifier", CABF_ROOT_PROFILE),
    ("webpki::aki::root-with-aki-authoritycertissuer", CABF_ROOT_PROFILE),
    ("webpki::aki::root-with-aki-authoritycertserialnumber", CABF_ROOT_PROFILE),
    ("webpki::aki::root-with-aki-all-fields", CABF_ROOT_PROFILE),
    ("webpki::aki::root-with-aki-ski-mismatch", CABF_ROOT_PROFILE),
    ("webpki::cn::ipv4-hex-mismatch", CABF_CN),
    ("webpki::cn::ipv4-leading-zeros-mismatch", CABF_CN),
    ("webpki::cn::ipv6-uppercase-mismatch", CABF_CN),
    ("webpki::cn::ipv6-uncompressed-mismatch", CABF_CN),
    ("webpki::cn::ipv6-non-rfc5952-mismatch", CABF_CN),
    ("webpki::cn::punycode-not-in-san", CABF_CN),
    ("webpki::cn::utf8-vs-punycode-mismatch", CABF_CN),
    ("webpki::cn::not-in-san", CABF_CN),
    ("webpki::cn::case-mismatch", CABF_CN),
    ("webpki::eku::ee-anyeku", CABF_LEAF_EKU),
    ("webpki::eku::ee-critical-eku", CABF_LEAF_EKU),
    ("webpki::eku::root-has-eku", CABF_ROOT_PROFILE),
    ("webpki::san::san-critical-with-nonempty-subject", CABF_SAN_CRITICALITY),
    ("webpki::explicit-curve", NEEDS_SIGNATURE),
    ("webpki::malformed-aia", CABF_AIA),
    ("webpki::forbidden-p192-root", NEEDS_SIGNATURE),
    ("webpki::forbidden-p192-leaf", LEAF_KEY_RULE),
    ("webpki::forbidden-dsa-leaf", LEAF_KEY_RULE),
    ("webpki::forbidden-weak-rsa-key-in-root", NEEDS_SIGNATURE),
    ("webpki::forbidden-weak-rsa-in-leaf", LEAF_KEY_RULE),
    ("webpki::forbidden-rsa-not-divisible-by-8-in-root", ROOT_RSA_BITS),
    ("webpki::forbidden-rsa-key-not-divisible-by-8-in-leaf", LEAF_KEY_RULE),
];
