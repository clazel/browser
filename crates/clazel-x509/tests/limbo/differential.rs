// A differential of path validation against `rustls-webpki`
// (docs/phases/phase-3.md item 3.5b).
//
// Every `SERVER` testcase of the x509-limbo corpus that names a DNS or IP
// peer runs through both engines, with the same chain, trust anchors,
// time and peer name, and the two verdicts are compared.
//
// - **Signatures are not compared.** Both engines get a stand-in that accepts
//   every signature (`AcceptAll` here, `AnySignature` for webpki), so this
//   compares chain building, the certificate checks and name matching.
//   `rustls-webpki` is built without a cryptography provider.
// - Webpki's own limits apply on its side; the corpus's `max_chain_depth` is
//   passed to ours only.
// - Every difference is listed by id with a reason in
//   `tests/limbo/webpki_differences.rs`. The test fails if a difference is not
//   listed, or if a listed testcase no longer differs, and the counts are
//   pinned in `COUNTS`. The 11 corpus testcases not compared are the 10
//   `CLIENT` ones and one `SERVER` one with no DNS or IP peer name.

// `WEBPKI_DIFFERENCES`: (testcase id, which engine accepts, reason), by hand.
include!("webpki_differences.rs");

/// Testcases compared, accepted by both, refused by both.
const COUNTS: (usize, usize, usize) = (9791, 970, 8799);

/// Accepts every signature of one key and signature algorithm.
#[derive(Debug)]
struct AnySignature(WebpkiAlgorithm, WebpkiAlgorithm);

impl SignatureVerificationAlgorithm for AnySignature {
    fn verify_signature(&self, _: &[u8], _: &[u8], _: &[u8]) -> Result<(), InvalidSignature> {
        Ok(())
    }

    fn public_key_alg_id(&self) -> WebpkiAlgorithm {
        self.0
    }

    fn signature_alg_id(&self) -> WebpkiAlgorithm {
        self.1
    }
}

/// Every key and signature algorithm pair webpki can name.
static ALGORITHMS: &[&dyn SignatureVerificationAlgorithm] = &[
    &AnySignature(alg_id::ECDSA_P256, alg_id::ECDSA_SHA256),
    &AnySignature(alg_id::ECDSA_P256, alg_id::ECDSA_SHA384),
    &AnySignature(alg_id::ECDSA_P256, alg_id::ECDSA_SHA512),
    &AnySignature(alg_id::ECDSA_P384, alg_id::ECDSA_SHA256),
    &AnySignature(alg_id::ECDSA_P384, alg_id::ECDSA_SHA384),
    &AnySignature(alg_id::ECDSA_P384, alg_id::ECDSA_SHA512),
    &AnySignature(alg_id::ECDSA_P521, alg_id::ECDSA_SHA256),
    &AnySignature(alg_id::ECDSA_P521, alg_id::ECDSA_SHA384),
    &AnySignature(alg_id::ECDSA_P521, alg_id::ECDSA_SHA512),
    &AnySignature(alg_id::RSA_ENCRYPTION, alg_id::RSA_PKCS1_SHA256),
    &AnySignature(alg_id::RSA_ENCRYPTION, alg_id::RSA_PKCS1_SHA384),
    &AnySignature(alg_id::RSA_ENCRYPTION, alg_id::RSA_PKCS1_SHA512),
    &AnySignature(alg_id::RSA_ENCRYPTION, alg_id::RSA_PSS_SHA256),
    &AnySignature(alg_id::RSA_ENCRYPTION, alg_id::RSA_PSS_SHA384),
    &AnySignature(alg_id::RSA_ENCRYPTION, alg_id::RSA_PSS_SHA512),
    &AnySignature(alg_id::ED25519, alg_id::ED25519),
    &AnySignature(alg_id::ED448, alg_id::ED448),
];

/// Our verdict.
fn ours(case: &Case, now: u64) -> Option<bool> {
    let ip;
    let reference = match case.peer {
        ("DNS", name) => ReferenceIdentity::Dns(name.as_bytes()),
        ("IP", text) => {
            ip = match text.parse::<IpAddr>().ok()? {
                IpAddr::V4(a) => a.octets().to_vec(),
                IpAddr::V6(a) => a.octets().to_vec(),
            };
            ReferenceIdentity::Ip(&ip)
        }
        _ => return None,
    };
    let anchors: Vec<Anchor<'_>> = case
        .trusted
        .iter()
        .filter_map(|&i| cert(i).and_then(|der| anchor_from_root(der, None)))
        .collect();
    let presented: Option<Vec<&[u8]>> = std::iter::once(case.leaf)
        .chain(case.intermediates.iter().copied())
        .map(cert)
        .collect();
    let environment = Environment {
        link: &AcceptAll,
        revoked: &NotRevoked,
        max_intermediates: case.max_chain_depth.map_or(DEFAULT_MAX_INTERMEDIATES, |d| {
            usize::try_from(d).unwrap_or(DEFAULT_MAX_INTERMEDIATES)
        }),
    };
    Some(verify_server_chain(&environment, &anchors, &presented?, reference, now).is_ok())
}

/// Webpki's verdict, and its error when it refuses.
fn theirs(case: &Case, now: u64) -> Option<Result<(), String>> {
    let name = ServerName::try_from(case.peer.1).ok();
    let leaf = CertificateDer::from(cert(case.leaf)?);
    let roots: Vec<CertificateDer<'_>> = case
        .trusted
        .iter()
        .filter_map(|&i| cert(i).map(CertificateDer::from))
        .collect();
    let anchors: Vec<TrustAnchor<'_>> = roots
        .iter()
        .filter_map(|der| anchor_from_trusted_cert(der).ok())
        .collect();
    let intermediates: Option<Vec<CertificateDer<'_>>> = case
        .intermediates
        .iter()
        .map(|&i| cert(i).map(CertificateDer::from))
        .collect();
    let intermediates = intermediates?;
    let verdict = (|| {
        let end_entity = EndEntityCert::try_from(&leaf).map_err(|e| format!("{e:?}"))?;
        end_entity
            .verify_for_usage(
                ALGORITHMS,
                &anchors,
                &intermediates,
                UnixTime::since_unix_epoch(Duration::from_secs(now)),
                KeyUsage::server_auth(),
                None,
                None,
            )
            .map_err(|e| format!("{e:?}"))?;
        let name = name.as_ref().ok_or("peer name does not parse")?;
        end_entity
            .verify_is_valid_for_subject_name(name)
            .map_err(|e| format!("{e:?}"))
    })();
    Some(verdict)
}

/// Which engine accepted a testcase the other refused.
fn accepted_by(ours_accepts: bool) -> &'static str {
    if ours_accepts { "clazel" } else { "webpki" }
}

#[test]
#[cfg_attr(miri, ignore)]
fn path_validation_agrees_with_webpki_or_the_difference_is_listed() {
    let mut problems: Vec<String> = Vec::new();
    let (mut compared, mut agree_accept, mut agree_refuse) = (0usize, 0usize, 0usize);
    let mut differing: Vec<&'static str> = Vec::new();
    for case in CASES.iter().filter(|c| c.kind == "SERVER") {
        let Some(now) = case_time(case) else { continue };
        let (Some(ours), Some(theirs)) = (ours(case, now), theirs(case, now)) else {
            continue;
        };
        compared = compared.saturating_add(1);
        match (ours, theirs.is_ok()) {
            (true, true) => agree_accept = agree_accept.saturating_add(1),
            (false, false) => agree_refuse = agree_refuse.saturating_add(1),
            (mine, _) => {
                differing.push(case.id);
                match WEBPKI_DIFFERENCES.iter().find(|d| d.0 == case.id) {
                    Some(listed) if listed.1 == accepted_by(mine) => {}
                    Some(listed) => problems.push(format!(
                        "{}: listed as accepted by {}, but {} accepts it",
                        case.id,
                        listed.1,
                        accepted_by(mine)
                    )),
                    None => problems.push(format!(
                        "{}: not listed: accepted by {}, limbo {}, webpki {:?}",
                        case.id,
                        accepted_by(mine),
                        case.expected,
                        theirs.err()
                    )),
                }
            }
        }
    }
    for (id, _, _) in WEBPKI_DIFFERENCES {
        if !differing.contains(id) {
            problems.push(format!("{id}: listed, but the engines now agree"));
        }
    }
    println!(
        "{compared} compared: {agree_accept} accepted by both, {agree_refuse} refused by both, {} differ",
        differing.len()
    );
    let agreed = agree_accept.saturating_add(agree_refuse);
    println!(
        "clazel-conformance: suite=\"rustls-webpki differential (x509-limbo, accept-all signatures)\" pass={agreed} xfail={} fail={} total={compared}",
        differing.len().saturating_sub(problems.len()),
        problems.len()
    );
    if (compared, agree_accept, agree_refuse) != COUNTS {
        problems.push(format!(
            "counts changed: ({compared}, {agree_accept}, {agree_refuse}), pinned {COUNTS:?}"
        ));
    }
    assert!(
        problems.is_empty(),
        "{} problems:\n{}",
        problems.len(),
        problems.join("\n")
    );
}
