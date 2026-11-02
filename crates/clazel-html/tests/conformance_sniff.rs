//! Encoding sniffing conformance (docs/phases/phase-4.md item 4.2).
//!
//! The proofs show `sniff::exec::sniff` equals `sniff/spec.rs`. This file
//! checks it against the outside world:
//!
//! 1. Every case of html5lib-tests `encoding/*.dat` (`tests/data/
//!    html5lib-encoding/`): sniffing the input with no transport encoding
//!    gives the expected encoding (html5lib-tests states no confidence).
//!    One unit per case. The `scripted/` case needs a script and is not
//!    run; it is reported as a count, not a pass. Seven cases are expected
//!    failures, listed in [`XFAIL`] with the reason.
//! 2. A differential test of the labels the sniffer reads against
//!    `encoding_rs`'s `Encoding::for_label` (Firefox's label resolution):
//!    every label of the standard, upper-cased and with spaces, and random
//!    near-miss strings, each placed in `<meta charset=...>`, in
//!    `<meta http-equiv="Content-Type" content="text/html; charset=...">`,
//!    in an XML declaration, and given as the transport encoding. The
//!    expected encoding applies the standard's own rules to `for_label`'s
//!    answer: UTF-16BE/LE become UTF-8 (and x-user-defined windows-1252)
//!    in a `<meta>`, UTF-16BE/LE become UTF-8 in an XML declaration, and no
//!    answer leaves the default, windows-1252.

use clazel_encoding::labels::exec::{get_an_encoding, name};
use clazel_encoding::labels::spec::Encoding;
use clazel_html::sniff::exec::sniff;
use clazel_html::sniff::spec::Confidence;

/// One converted html5lib case.
struct Case {
    file: &'static str,
    line: usize,
    encoding: &'static str,
    data: &'static [u8],
}

include!("generated/html5lib_encoding.rs");

/// Expected failures: (file, line of `#data`, reason).
///
/// Each puts its `<meta charset>` after a comment of 2048 to 8193 bytes,
/// beyond the first 1024 bytes the prescan reads (the end condition the
/// standard encourages, and this implementation's modelling choice). A
/// browser finds that `<meta>` while parsing and restarts with its encoding
/// (§13.2.3.4 "change the encoding", `sniff::exec::change_the_encoding`),
/// which needs the tree builder's `<meta>` rule; the document pipeline
/// (Phase 4 item 4.13) runs sniff and that restart together, and these
/// cases move to it then. Sniffing alone rightly gives windows-1252.
const XFAIL: &[(&str, usize, &str)] = &[
    (
        "tests1.dat",
        313,
        "meta after 2048 bytes: found by the parser's restart, not the 1024-byte prescan",
    ),
    (
        "tests1.dat",
        319,
        "meta after 2049 bytes: found by the parser's restart, not the 1024-byte prescan",
    ),
    (
        "tests1.dat",
        325,
        "meta after 4096 bytes: found by the parser's restart, not the 1024-byte prescan",
    ),
    (
        "tests1.dat",
        331,
        "meta after 4097 bytes: found by the parser's restart, not the 1024-byte prescan",
    ),
    (
        "tests1.dat",
        337,
        "meta after 8192 bytes: found by the parser's restart, not the 1024-byte prescan",
    ),
    (
        "tests1.dat",
        343,
        "meta after 8193 bytes: found by the parser's restart, not the 1024-byte prescan",
    ),
    (
        "tests1.dat",
        349,
        "meta after a long multi-script comment: found by the parser's restart, not the 1024-byte prescan",
    ),
];

fn label(s: &[u8]) -> Option<Encoding> {
    let cps: Vec<u32> = s.iter().map(|b| u32::from(*b)).collect();
    get_an_encoding(&cps)
}

fn show(e: Encoding) -> String {
    String::from_utf8_lossy(&name(e)).into_owned()
}

#[test]
fn html5lib_encoding() {
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut failures = Vec::new();
    for case in ENCODING {
        let expected = label(case.encoding.as_bytes());
        let (got, confidence) = sniff(case.data, None);
        // A byte order mark gives confidence certain, anything else
        // tentative (no transport encoding here).
        let bom = clazel_encoding::hooks::decode::bom_sniff(case.data).is_some();
        let confidence_ok = confidence
            == if bom {
                Confidence::Certain
            } else {
                Confidence::Tentative
            };
        let listed = XFAIL
            .iter()
            .find(|(f, l, _)| *f == case.file && *l == case.line);
        match (Some(got) == expected && confidence_ok, listed) {
            (true, None) => pass = pass.saturating_add(1),
            (false, Some(_)) => xfail = xfail.saturating_add(1),
            (true, Some((_, _, why))) => failures.push(format!(
                "{}:{}: listed as an expected failure ({why}) but passes; remove it from XFAIL",
                case.file, case.line
            )),
            (false, None) => failures.push(format!(
                "{}:{}: expected {}, got {} ({confidence:?})",
                case.file,
                case.line,
                case.encoding,
                show(got)
            )),
        }
    }
    println!(
        "clazel-conformance: suite=\"html5lib-tests encoding/\" pass={pass} xfail={xfail} fail={} total={}",
        failures.len(),
        ENCODING.len()
    );
    assert_eq!(
        xfail,
        XFAIL.len(),
        "every listed expected failure must occur"
    );
    println!("scripted cases not run: {SCRIPTED_NOT_RUN}");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Deterministic SplitMix64, so a failure reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ z.wrapping_shr(30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ z.wrapping_shr(27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ z.wrapping_shr(31)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(u64::MAX);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
}

/// `encoding_rs`'s encoding as ours.
fn ours_for(e: &'static encoding_rs::Encoding) -> Option<Encoding> {
    label(e.name().as_bytes())
}

/// The encoding a `<meta>` naming `l` must give.
fn expected_meta(l: &[u8]) -> Encoding {
    match encoding_rs::Encoding::for_label(l).and_then(ours_for) {
        Some(Encoding::Utf16Be | Encoding::Utf16Le) => Encoding::Utf8,
        Some(Encoding::XUserDefined) => Encoding::Windows1252,
        Some(e) => e,
        None => Encoding::Windows1252,
    }
}

/// The encoding an XML declaration naming `l` must give.
fn expected_xml(l: &[u8]) -> Encoding {
    match encoding_rs::Encoding::for_label(l).and_then(ours_for) {
        Some(Encoding::Utf16Be | Encoding::Utf16Le) => Encoding::Utf8,
        Some(e) => e,
        None => Encoding::Windows1252,
    }
}

#[test]
fn differential_for_label() {
    // Every label of the standard, from the generated table.
    let mut labels: Vec<Vec<u8>> = Vec::new();
    for n in 0..40u8 {
        let e = clazel_encoding::labels::exec::from_number(n);
        labels.push(name(e));
    }
    for raw in [
        &b"utf-8"[..],
        b"UTF8",
        b"latin1",
        b"ISO-8859-1",
        b"iso8859-2",
        b"euc-jp",
        b"shift_jis",
        b"x-sjis",
        b"gb2312",
        b"big5",
        b"koi8-u",
        b"csisolatin9",
        b"x-user-defined",
        b"utf-16",
        b"utf-16be",
        b"unicodefffe",
        b"replacement",
        b"iso-2022-kr",
        b"hz-gb-2312",
        b"windows-1252",
        b"ascii",
        b"us-ascii",
        b"tis-620",
        b"dos-874",
        b"mac",
        b"x-mac-ukrainian",
        b"logical",
        b"visual",
    ] {
        labels.push(raw.to_vec());
        labels.push(raw.to_ascii_uppercase());
        let mut spaced = b" ".to_vec();
        spaced.extend_from_slice(raw);
        spaced.push(b'\t');
        labels.push(spaced);
    }
    let mut rng = Rng(0x0004_0201);
    let count = if cfg!(miri) { 30 } else { 3000 };
    let alphabet = b"abcdefgiklmnorstuwxyABCIJKSUX0123456789-_.: \t";
    for _ in 0..count {
        let base = labels
            .get(rng.below(labels.len()))
            .cloned()
            .unwrap_or_default();
        let mut l = base;
        for _ in 0..rng.below(3) {
            let c = *alphabet.get(rng.below(alphabet.len())).unwrap_or(&b'x');
            let at = rng.below(l.len().saturating_add(1));
            l.insert(at.min(l.len()), c);
        }
        labels.push(l);
    }
    let mut total = 0usize;
    let mut failures = Vec::new();
    // Miri checks every other label (all of them took 101 s there): it
    // looks for undefined behaviour in the paths they exercise, and the
    // normal test job checks every label.
    let stride = if cfg!(miri) { 2 } else { 1 };
    for l in labels.iter().step_by(stride) {
        // A label with a quote, `>` or `;` would end the attribute early,
        // and one with bytes up to 0x20 is not an XML encoding; keep the
        // shapes simple.
        if l.iter()
            .any(|b| matches!(b, b'"' | b'\'' | b'>' | b';' | b'<'))
        {
            continue;
        }
        let mut meta = b"<meta charset=\"".to_vec();
        meta.extend_from_slice(l);
        meta.extend_from_slice(b"\">");
        let mut pragma =
            b"<meta http-equiv=\"Content-Type\" content=\"text/html; charset=".to_vec();
        pragma.extend_from_slice(l);
        pragma.extend_from_slice(b"\">");
        let mut xml = b"<?xml version=\"1.0\" encoding=\"".to_vec();
        xml.extend_from_slice(l);
        xml.extend_from_slice(b"\"?>");
        let trimmed: Vec<u8> = l
            .iter()
            .copied()
            .filter(|b| !matches!(b, b' ' | b'\t'))
            .collect();
        let pragma_expected = if l.iter().any(|b| matches!(b, b' ' | b'\t')) {
            // The content value ends at the first space; the label is cut.
            let first: Vec<u8> = l
                .iter()
                .copied()
                .skip_while(|b| matches!(b, b' ' | b'\t'))
                .take_while(|b| !matches!(b, b' ' | b'\t'))
                .collect();
            expected_meta(&first)
        } else {
            expected_meta(l)
        };
        let xml_expected = if l.iter().any(|b| *b <= 0x20) || trimmed.is_empty() {
            Encoding::Windows1252
        } else {
            expected_xml(l)
        };
        let checks = [
            ("meta charset", sniff(&meta, None).0, expected_meta(l)),
            ("meta pragma", sniff(&pragma, None).0, pragma_expected),
            ("xml declaration", sniff(&xml, None).0, xml_expected),
        ];
        for (what, got, want) in checks {
            total = total.saturating_add(1);
            if got != want && failures.len() < 20 {
                failures.push(format!(
                    "{what} {:?}: ours {}, encoding_rs {}",
                    String::from_utf8_lossy(l),
                    show(got),
                    show(want)
                ));
            } else if got != want {
                failures.push(String::new());
            }
        }
        // Transport: "get an encoding" of the charset parameter, as is.
        total = total.saturating_add(1);
        let transport = label(l);
        let want = encoding_rs::Encoding::for_label(l).and_then(ours_for);
        if transport != want {
            failures.push(format!(
                "transport {:?}: ours {transport:?}, encoding_rs {want:?}",
                String::from_utf8_lossy(l)
            ));
        }
    }
    let fail = failures.len();
    if !cfg!(miri) {
        println!(
            "clazel-conformance: suite=\"encoding_rs for_label through the sniffer\" pass={} xfail=0 fail={fail} total={total}",
            total.saturating_sub(fail)
        );
    }
    failures.retain(|f| !f.is_empty());
    assert!(fail == 0, "{}", failures.join("\n"));
}
