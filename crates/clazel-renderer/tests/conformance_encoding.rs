//! The document pipeline's encoding (docs/phases/phase-4.md item 4.13)
//! against html5lib-tests `encoding/*.dat`.
//!
//! `clazel-html`'s `tests/conformance_sniff.rs` runs these cases through
//! the encoding sniffing algorithm alone, which reads at most the first
//! 1024 bytes, and lists seven as expected failures: their `<meta>` comes
//! later, and a browser finds it while parsing and restarts (§13.2.3.4
//! "change the encoding"). Here every case goes through the whole
//! pipeline's HTML path, `clazel_renderer::pipeline::parse_html`: sniff,
//! decode, parse with `clazel-treebuilder`'s driver, and on the parser's
//! `ChangeEncoding`, change the encoding and parse again. One unit per
//! case: the encoding of the parse that built the document is the expected
//! one. A case whose encoding has no decoder here (`euc-jp`, item 4.4)
//! cannot be parsed; its unit is that the pipeline settles on that
//! encoding (and the page shows the "not supported" notice, as item 4.0(b)
//! requires), which is what html5lib-tests checks. The `scripted/` case
//! needs a script and is not run; it is reported as a count, not a pass.
//!
//! Under Miri every 11th case runs and no summary line is printed (the
//! counts are the plain run's), as `clazel-html`'s tokenizer suite does.
//!
//! The cases are `clazel-html`'s generated table, read from that crate's
//! directory: this crate depends on `clazel-html`, so a change there
//! re-runs this test (docs/VERIFICATION.md, "Local and CI runs").

use clazel_encoding::labels::exec::{get_an_encoding, name};
use clazel_encoding::labels::spec::Encoding;
use clazel_renderer::pipeline::{NotParsed, parse_html};

/// One converted html5lib case.
struct Case {
    file: &'static str,
    line: usize,
    encoding: &'static str,
    data: &'static [u8],
}

include!("../../clazel-html/tests/generated/html5lib_encoding.rs");

fn label(s: &[u8]) -> Option<Encoding> {
    let cps: Vec<u32> = s.iter().map(|b| u32::from(*b)).collect();
    get_an_encoding(&cps)
}

fn show(e: Encoding) -> String {
    String::from_utf8_lossy(&name(e)).into_owned()
}

/// The document URL the cases are parsed at.
fn url() -> Vec<u32> {
    "http://a.test/".chars().map(u32::from).collect()
}

#[test]
fn html5lib_encoding_through_the_pipeline() {
    let mut pass = 0usize;
    let mut restarted = 0usize;
    let mut failures = Vec::new();
    let stride = if cfg!(miri) { 11 } else { 1 };
    for case in ENCODING.iter().step_by(stride) {
        let expected = label(case.encoding.as_bytes());
        let got = match parse_html(case.data, None, &url()) {
            Ok(parsed) => {
                if parsed.restarted {
                    restarted = restarted.saturating_add(1);
                }
                parsed.encoding
            }
            Err(NotParsed::Unsupported(e)) => e,
        };
        if Some(got) == expected {
            pass = pass.saturating_add(1);
        } else {
            failures.push(format!(
                "{}:{}: expected {}, got {}",
                case.file,
                case.line,
                case.encoding,
                show(got)
            ));
        }
    }
    if !cfg!(miri) {
        println!(
            "clazel-conformance: suite=\"html5lib-tests encoding/ through the pipeline\" pass={pass} xfail=0 fail={} total={}",
            failures.len(),
            ENCODING.len()
        );
    }
    println!("parsed twice (change the encoding): {restarted}");
    println!("scripted cases not run: {SCRIPTED_NOT_RUN}");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // The seven cases the sniffer alone cannot pass are found by the
    // restart, so at least that many parse twice.
    assert!(cfg!(miri) || restarted >= 7, "only {restarted} restarts");
}
