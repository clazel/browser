//! The root table against a second record of the same list.
//!
//! `xtask/src/roots.rs` derives `ROOTS` from NSS's `certdata.txt`, and
//! `tests/trust_store.rs` re-reads that file with a separate scanner. Both
//! start from that one file. `webpki-root-certs` is generated from the CCADB's
//! Mozilla report instead, by code that is not ours, so this catches a root
//! that `certdata.txt`'s trust bits and Mozilla's published list disagree on,
//! or that both our readers mistake the same way. The whole DER encodings are
//! compared, not names or fingerprints.
//!
//! No difference is expected at the pinned versions. The two sources publish
//! on their own schedules, so an update of either can bring one: update both
//! together (`data/nss-<commit>/SOURCE.md`), and list here, with its reason,
//! any root they still disagree on.

use clazel_x509::roots::ROOTS;
use std::collections::BTreeSet;

#[test]
fn the_table_equals_the_ccadb_report() {
    let ours: BTreeSet<&[u8]> = ROOTS.iter().map(|root| root.der).collect();
    let theirs: BTreeSet<&[u8]> = webpki_root_certs::TLS_SERVER_ROOT_CERTS
        .iter()
        .map(|cert| cert.as_ref())
        .collect();
    assert_eq!(ours.len(), ROOTS.len(), "a root is listed twice");

    let only_ours: Vec<&str> = ROOTS
        .iter()
        .filter(|root| !theirs.contains(root.der))
        .map(|root| root.label)
        .collect();
    let only_theirs = theirs.difference(&ours).count();
    let agreeing = ours.intersection(&theirs).count();
    let differing = only_ours.len().saturating_add(only_theirs);
    println!(
        "clazel-conformance: suite=\"Mozilla roots against webpki-root-certs (CCADB), whole DER\" pass={agreeing} xfail=0 fail={differing} total={}",
        agreeing.saturating_add(differing)
    );
    assert!(
        only_ours.is_empty(),
        "not in the CCADB report: {only_ours:?}"
    );
    assert_eq!(only_theirs, 0, "in the CCADB report, not in the table");
}
