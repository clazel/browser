//! Safe executable RFC 9525 matching routines.

/// A reference identifier has an explicit DNS or binary IP type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReferenceIdentity<'a> {
    /// Canonical ASCII DNS name supplied by the URL layer.
    Dns(&'a [u8]),
    /// Four-octet IPv4 or sixteen-octet IPv6 address.
    Ip(&'a [u8]),
}

/// A typed identifier already extracted from subjectAltName.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PresentedIdentity<'a> {
    /// X.509 dNSName value.
    Dns(&'a [u8]),
    /// X.509 iPAddress value.
    Ip(&'a [u8]),
}

fn is_dns_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'-'
}

fn valid_dns_name(name: &[u8]) -> bool {
    if name.is_empty() || name.len() > 253 {
        return false;
    }
    let mut label_len = 0_usize;
    let mut label_first = None;
    let mut label_last = None;
    for byte in name.iter().copied() {
        if byte == b'.' {
            if label_len == 0 || label_len > 63
                || label_first.is_some_and(|c: u8| !c.is_ascii_alphanumeric())
                || label_last.is_some_and(|c: u8| !c.is_ascii_alphanumeric())
            {
                return false;
            }
            label_len = 0;
            label_first = None;
            label_last = None;
        } else if is_dns_byte(byte) {
            label_first = label_first.or(Some(byte));
            label_last = Some(byte);
            let Some(next_len) = label_len.checked_add(1) else { return false; };
            label_len = next_len;
        } else {
            return false;
        }
    }
    label_len > 0 && label_len <= 63
        && label_first.is_some_and(|c| c.is_ascii_alphanumeric())
        && label_last.is_some_and(|c| c.is_ascii_alphanumeric())
}

fn ascii_equal(left: &[u8], right: &[u8]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right.iter()).all(|(a, b)| a.eq_ignore_ascii_case(b))
}

/// RFC 9525 §6.3: compare DNS labels with ASCII case folding. A presented
/// wildcard is accepted only when `*` is its complete leftmost label and
/// appears nowhere else. It matches exactly one reference label.
pub fn dns_id_matches(reference: &[u8], presented: &[u8]) -> bool {
    if !valid_dns_name(reference) {
        return false;
    }
    if valid_dns_name(presented) {
        return ascii_equal(reference, presented);
    }
    let Some(suffix) = presented.strip_prefix(b"*.") else {
        return false;
    };
    if !valid_dns_name(suffix) || suffix.contains(&b'*') {
        return false;
    }
    let Some(dot) = reference.iter().position(|byte| *byte == b'.') else {
        return false;
    };
    let Some(leftmost) = reference.get(..dot) else { return false; };
    let Some(suffix_start) = dot.checked_add(1) else { return false; };
    let Some(ref_suffix) = reference.get(suffix_start..) else { return false; };
    !leftmost.is_empty() && ascii_equal(ref_suffix, suffix)
}

/// RFC 9525 §6.4: compare IP-ID values octet for octet, rejecting malformed
/// SAN encodings. A DNS-ID can never serve as the presented IP identifier.
pub fn ip_id_matches(reference: &[u8], presented: &[u8]) -> bool {
    (reference.len() == 4 || reference.len() == 16)
        && presented.len() == reference.len()
        && reference == presented
}

/// RFC 9525 §6.2 dispatches matching by identifier type.
pub fn service_identity_matches(
    reference: ReferenceIdentity<'_>,
    presented: PresentedIdentity<'_>,
) -> bool {
    match (reference, presented) {
        (ReferenceIdentity::Dns(reference), PresentedIdentity::Dns(presented)) => {
            dns_id_matches(reference, presented)
        }
        (ReferenceIdentity::Ip(reference), PresentedIdentity::Ip(presented)) => {
            ip_id_matches(reference, presented)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::{PresentedIdentity, ReferenceIdentity, dns_id_matches, ip_id_matches, service_identity_matches};

    #[test]
    fn rfc9525_dns_case_and_wildcard_examples() {
        assert!(dns_id_matches(b"www.bigcompany.example", b"WWW.BigCompany.Example"));
        assert!(dns_id_matches(b"www.bigcompany.example", b"*.bigcompany.example"));
        assert!(!dns_id_matches(b"a.b.bigcompany.example", b"*.bigcompany.example"));
        assert!(!dns_id_matches(b"bigcompany.example", b"*.bigcompany.example"));
    }

    #[test]
    fn malformed_wildcards_and_names_are_rejected() {
        assert!(!dns_id_matches(b"www.example.test", b"w*.example.test"));
        assert!(!dns_id_matches(b"www.example.test", b"*.*.example.test"));
        assert!(!dns_id_matches(b"www.example.test", b"a.*.example.test"));
        assert!(!dns_id_matches(b"www.example.test", b"*.example.test."));
        assert!(!dns_id_matches(b"www..example.test", b"www..example.test"));
    }

    #[test]
    fn ip_ids_are_binary_and_exact() {
        let v4 = [192, 0, 2, 107];
        assert!(ip_id_matches(&v4, &v4));
        assert!(!ip_id_matches(&v4, &[192, 0, 2, 108]));
        assert!(!ip_id_matches(&v4, b"192.0.2.107"));
        let v6 = [0x20, 0x01, 0x0d, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5];
        assert!(ip_id_matches(&v6, &v6));
        assert!(!ip_id_matches(&v6[..15], &v6[..15]));
    }

    #[test]
    fn dns_and_ip_identifiers_never_cross_match() {
        assert!(!service_identity_matches(
            ReferenceIdentity::Dns(b"192.0.2.107"), PresentedIdentity::Ip(&[192, 0, 2, 107]),
        ));
        assert!(!service_identity_matches(
            ReferenceIdentity::Ip(&[192, 0, 2, 107]), PresentedIdentity::Dns(b"192.0.2.107"),
        ));
    }
}
