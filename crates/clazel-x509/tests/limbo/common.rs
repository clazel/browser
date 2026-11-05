// The corpus, as both limbo suites read it: the testcase index, the
// certificates, and the stand-ins that keep signatures and revocation out of
// the verdict. `include!`d, because integration tests are separate crates.

/// One testcase of the index.
struct Case {
    id: &'static str,
    kind: &'static str,
    expected: &'static str,
    peer: (&'static str, &'static str),
    peer_names: &'static [(&'static str, &'static str)],
    time: &'static str,
    features: &'static [&'static str],
    importance: &'static str,
    max_chain_depth: Option<u32>,
    key_usage: &'static [&'static str],
    extended_key_usage: &'static [&'static str],
    trusted: &'static [usize],
    intermediates: &'static [usize],
    leaf: usize,
}

// `TESTCASE_COUNT`, `CERT_SPANS` and `CASES`, generated from the vendored file.
include!("../generated/x509_limbo.rs");

static CERTS: &[u8] = include_bytes!("../generated/x509_limbo_certs.bin");

fn cert(index: usize) -> Option<&'static [u8]> {
    let &(offset, length) = CERT_SPANS.get(index)?;
    let start = usize::try_from(offset).ok()?;
    let end = start.checked_add(usize::try_from(length).ok()?)?;
    CERTS.get(start..end)
}

/// `YYYY-MM-DDTHH:MM:SS+00:00` (all of limbo's times are UTC).
fn parse_time(text: &str) -> Option<CertificateTime> {
    let body = text.strip_suffix("+00:00")?;
    let (date, clock) = body.split_once('T')?;
    let mut d = date.split('-');
    let mut c = clock.split(':');
    let time = CertificateTime {
        year: d.next()?.parse().ok()?,
        month: d.next()?.parse().ok()?,
        day: d.next()?.parse().ok()?,
        hour: c.next()?.parse().ok()?,
        minute: c.next()?.parse().ok()?,
        // Fractional seconds (`...:00.005`) are truncated, as RFC 5280 time
        // has whole-second precision.
        second: c.next()?.split('.').next()?.parse().ok()?,
    };
    (d.next().is_none() && c.next().is_none()).then_some(time)
}

/// Accepts every signature: the stand-in for `clazel-crypto`'s real link
/// verifier (see the module docs).
struct AcceptAll;

impl LinkVerifier for AcceptAll {
    fn verify(&self, _: &[u8], _: &AlgorithmIdentifier<'_>, _: &[u8], _: &[u8]) -> bool {
        true
    }
}

/// Nothing is revoked (the production oracle; CRLs are Phase 8).
struct NotRevoked;

impl RevocationOracle for NotRevoked {
    fn is_revoked(&self, _: &PathCert<'_>) -> bool {
        false
    }
}

/// Production `max_intermediates`, used when the testcase gives no
/// `max_chain_depth`.
const DEFAULT_MAX_INTERMEDIATES: usize = 6;

/// Unix seconds of a UTC time (proleptic Gregorian, days from civil).
fn unix_seconds(t: &CertificateTime) -> Option<u64> {
    let (m, d) = (i64::from(t.month), i64::from(t.day));
    let y = i64::from(t.year).checked_sub(i64::from(m <= 2))?;
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400);
    let mp = m.checked_add(9)?.checked_rem(12)?;
    let doy = mp
        .checked_mul(153)?
        .checked_add(2)?
        .checked_div(5)?
        .checked_add(d)?
        .checked_sub(1)?;
    let doe = yoe
        .checked_mul(365)?
        .checked_add(yoe / 4)?
        .checked_sub(yoe / 100)?
        .checked_add(doy)?;
    let days = era
        .checked_mul(146_097)?
        .checked_add(doe)?
        .checked_sub(719_468)?;
    let clock = i64::from(t.hour)
        .checked_mul(3600)?
        .checked_add(i64::from(t.minute).checked_mul(60)?)?
        .checked_add(i64::from(t.second))?;
    u64::try_from(days.checked_mul(86_400)?.checked_add(clock)?).ok()
}

/// The testcase's validation time as Unix seconds. Limbo leaves the time out
/// of some testcases (`time` is empty): the leaf is then judged at its own
/// notBefore, which its validity includes. A leaf that does not decode gives
/// 0: the chain is refused whatever the time.
fn case_time(case: &Case) -> Option<u64> {
    if case.time.is_empty() {
        let decoded = cert(case.leaf)
            .and_then(parse_certificate)
            .and_then(|e| parse_tbs_certificate(e.tbs_certificate_der));
        return match decoded {
            Some(tbs) => unix_seconds(&tbs.not_before),
            None => Some(0),
        };
    }
    unix_seconds(&parse_time(case.time)?)
}
