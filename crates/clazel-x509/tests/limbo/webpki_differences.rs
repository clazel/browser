// Every reason says what our verdict rests on. "limbo refuses" or "limbo
// accepts" is the corpus's own expected result. The reasons were read from the
// verdict of each engine, not from either engine's documentation.
const DEPTH: &str = "limbo's max_chain_depth is passed to our engine only; limbo refuses";
const ANCHOR_OR_ISSUER: &str = "our decoding or checks refuse this root or intermediate, so no \
    issuer is found (UnknownIssuer); webpki accepts it; limbo refuses";
const CONSTRAINT_SYNTAX: &str =
    "we refuse a name constraint form we do not support (NameConstraintUnsupported); limbo refuses";
const LEAF: &str = "our leaf checks refuse the target, webpki does not check this; limbo refuses";
const LEAF_CONSTRAINTS: &str = "we refuse nameConstraints on the target (LeafNameConstraints); \
    limbo refuses";
const EXPIRED_ANCHOR: &str = "we check the trust anchor's validity (AnchorExpired), webpki does \
    not; limbo refuses";
const EKU_REQUIRED: &str = "the browser profile requires extKeyUsage on the target (see \
    expected_failures.rs); webpki accepts its absence";
const STAND_IN: &str = "only with the accept-all link: webpki refuses the key's algorithm, and \
    clazel-crypto's real links refuse it too (tests/chain_limbo.rs, BadSignature)";

/// Testcases where `rustls-webpki` and our path validation disagree: the id,
/// the engine that accepts, and why.
const WEBPKI_DIFFERENCES: &[(&str, &str, &str)] = &[
    ("pathlen::max-chain-depth-0-exhausted", "webpki", DEPTH),
    ("pathlen::max-chain-depth-1-exhausted", "webpki", DEPTH),
    ("rfc5280::aki::critical-aki", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::ski::critical-ski", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::unknown-critical-extension-root", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::root-missing-basic-constraints", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::root-inconsistent-ca-extensions", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::nc::permitted-empty-sequence-excluded-nonempty", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::nc::permitted-nonempty-excluded-empty-sequence", "webpki", ANCHOR_OR_ISSUER),
    ("webpki::nc::intermediate-permitted-excluded-subtrees-both-empty-sequences", "webpki", ANCHOR_OR_ISSUER),
    ("rfc5280::nc::invalid-dnsname-leading-period", "webpki", CONSTRAINT_SYNTAX),
    ("webpki::nc::intermediate-permitted-excluded-subtrees-both-null", "webpki", CONSTRAINT_SYNTAX),
    ("rfc5280::nc::not-allowed-in-ee-critical", "webpki", LEAF),
    ("rfc5280::san::underscore-dns", "webpki", LEAF),
    ("rfc5280::leaf-ku-keycertsign", "webpki", LEAF),
    ("webpki::san::public-suffix-multi-label-wildcard-san", "webpki", LEAF),
    ("webpki::san::public-suffix-private-namespace-wildcard-san", "webpki", LEAF),
    ("rfc5280::nc::not-allowed-in-ee-noncritical", "webpki", LEAF_CONSTRAINTS),
    ("rfc5280::validity::expired-root", "webpki", EXPIRED_ANCHOR),
    ("rfc5280::eku::ee-without-eku", "webpki", EKU_REQUIRED),
    ("webpki::eku::ee-without-eku", "webpki", EKU_REQUIRED),
    ("webpki::explicit-curve", "clazel", STAND_IN),
    ("webpki::forbidden-p192-root", "clazel", STAND_IN),
];
