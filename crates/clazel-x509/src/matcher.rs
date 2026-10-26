//! Safe executable RFC 9525 matching routines.

pub use super::exec::{PresentedIdentity, ReferenceIdentity};

/// RFC 9525 §6.3: compare DNS labels with ASCII case folding. A presented
/// wildcard is accepted only when `*` is its complete leftmost label and
/// appears nowhere else. It matches exactly one reference label.
pub fn dns_id_matches(reference: &[u8], presented: &[u8]) -> bool {
    super::exec::dns_id_matches_exec(reference, presented)
}

/// RFC 9525 §6.4: compare IP-ID values octet for octet, rejecting malformed
/// SAN encodings. A DNS-ID can never serve as the presented IP identifier.
pub fn ip_id_matches(reference: &[u8], presented: &[u8]) -> bool {
    super::exec::ip_id_matches_exec(reference, presented)
}

/// RFC 9525 §6.2 dispatches matching by identifier type.
pub fn service_identity_matches(
    reference: ReferenceIdentity<'_>,
    presented: PresentedIdentity<'_>,
) -> bool {
    super::exec::service_identity_matches_exec(reference, presented)
}

#[cfg(test)]
mod tests {
    use super::{
        PresentedIdentity, ReferenceIdentity, dns_id_matches, ip_id_matches,
        service_identity_matches,
    };

    #[test]
    fn rfc9525_dns_case_and_wildcard_examples() {
        assert!(dns_id_matches(
            b"www.bigcompany.example",
            b"WWW.BigCompany.Example"
        ));
        assert!(dns_id_matches(
            b"www.bigcompany.example",
            b"*.bigcompany.example"
        ));
        assert!(!dns_id_matches(
            b"a.b.bigcompany.example",
            b"*.bigcompany.example"
        ));
        assert!(!dns_id_matches(
            b"bigcompany.example",
            b"*.bigcompany.example"
        ));
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
            ReferenceIdentity::Dns(b"192.0.2.107"),
            PresentedIdentity::Ip(&[192, 0, 2, 107]),
        ));
        assert!(!service_identity_matches(
            ReferenceIdentity::Ip(&[192, 0, 2, 107]),
            PresentedIdentity::Dns(b"192.0.2.107"),
        ));
    }
}
