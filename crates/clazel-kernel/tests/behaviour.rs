//! Hand-written checks of the exec kernel's rules that the official suites
//! do not reach (malformed frames, ids that name nothing, opaque origins,
//! the storage quota, public-suffix hosts, bad navigations). These are not
//! conformance tests: they cite no official suite, print no
//! `clazel-conformance:` line, and the proofs (`exec::step`) are what say
//! the kernel does these things for every input.

mod support;

use clazel_kernel::exec::fetch::NetOutcomeRecord;
use clazel_kernel::exec::records::EventRecord;

use clazel_ipc::message::codec::Msg;
use support::{Kernel, Out};

/// Answer every `Fetch` among `out` as a shell with no network would: the
/// kernel's stand-in fetch makes the delivered bytes (none) the document's
/// script. The outputs, with each `Fetch` replaced by what answering it gave.
fn settled(kernel: &mut Kernel, out: Vec<Out>) -> Vec<Out> {
    let mut all = Vec::new();
    for o in out {
        match o {
            Out::Fetch(tab, url) => {
                let outcome = NetOutcomeRecord {
                    url,
                    net: Vec::new(),
                };
                all.extend(kernel.event(&EventRecord::Fetched { tab, outcome }));
            }
            other => all.push(other),
        }
    }
    all
}

/// Open a tab; the id of its renderer.
fn open(kernel: &mut Kernel, url: &str) -> u64 {
    let (id, _) = kernel.open_tab(url, "");
    assert!(id.is_some(), "{url} spawned no renderer");
    id.unwrap_or(0)
}

fn cookie_string(out: &[Out], id: u64) -> Option<&[u8]> {
    match out {
        [Out::To(to, Msg::CookieValue { cookie_string })] if *to == id => {
            Some(cookie_string.as_slice())
        }
        _ => None,
    }
}

#[test]
fn a_frame_that_does_not_decode_kills_the_sender() {
    let mut kernel = Kernel::new();
    let id = open(&mut kernel, "https://example.test/");
    let out = kernel.event(&clazel_kernel::exec::records::EventRecord::FromRenderer {
        id,
        bytes: vec![0xFF, 0xFF, 0xFF],
    });
    assert_eq!(out, vec![Out::Kill(id)]);
    // The record is gone: the id now names nothing, so nothing is answered.
    assert!(kernel.send(id, &Msg::CookieGet).is_empty());
}

#[test]
fn a_message_only_the_kernel_may_send_kills_the_sender() {
    let mut kernel = Kernel::new();
    let id = open(&mut kernel, "https://example.test/");
    let out = kernel.send(
        id,
        &Msg::CookieValue {
            cookie_string: b"a=b".to_vec(),
        },
    );
    assert_eq!(out, vec![Out::Kill(id)]);
}

#[test]
fn an_id_that_names_no_renderer_is_ignored() {
    let mut kernel = Kernel::new();
    assert!(kernel.send(7, &Msg::CookieGet).is_empty());
    let id = open(&mut kernel, "https://example.test/");
    assert!(
        kernel
            .send(id.saturating_add(1), &Msg::CookieGet)
            .is_empty()
    );
}

#[test]
fn local_storage_of_an_opaque_origin_is_a_security_error() {
    let mut kernel = Kernel::new();
    let id = open(&mut kernel, "data:text/plain,hi");
    let out = kernel.send(id, &Msg::StorageLength);
    assert_eq!(out, vec![Out::To(id, Msg::Error { code: 1 })]);
}

#[test]
fn storage_is_per_origin() {
    let mut kernel = Kernel::new();
    let a = open(&mut kernel, "https://example.test/");
    let b = open(&mut kernel, "https://other.test/");
    assert!(
        kernel
            .send(
                a,
                &Msg::StorageSetItem {
                    key: b"k".to_vec(),
                    value: b"v".to_vec()
                }
            )
            .is_empty()
    );
    let own = kernel.send(a, &Msg::StorageGetItem { key: b"k".to_vec() });
    assert_eq!(
        own,
        vec![Out::To(
            a,
            Msg::StorageValue {
                value: Some(b"v".to_vec())
            }
        )]
    );
    let other = kernel.send(b, &Msg::StorageGetItem { key: b"k".to_vec() });
    assert_eq!(other, vec![Out::To(b, Msg::StorageValue { value: None })]);
}

#[test]
#[cfg_attr(miri, ignore)]
fn the_storage_quota_is_per_origin() {
    // Megabyte strings: Miri would spend its time in the UTF-8 validator.
    let mut kernel = Kernel::new();
    let a = open(&mut kernel, "https://example.test/");
    let b = open(&mut kernel, "https://other.test/");
    let big = vec![b'x'; 1_000_000];
    for i in 0..5u8 {
        let out = kernel.send(
            a,
            &Msg::StorageSetItem {
                key: vec![b'k', b'0'.saturating_add(i)],
                value: big.clone(),
            },
        );
        assert!(out.is_empty(), "the first five megabytes fit");
    }
    let out = kernel.send(
        a,
        &Msg::StorageSetItem {
            key: b"k9".to_vec(),
            value: big.clone(),
        },
    );
    assert_eq!(out, vec![Out::To(a, Msg::Error { code: 2 })]);
    // Another origin has its own quota.
    let out = kernel.send(
        b,
        &Msg::StorageSetItem {
            key: b"k".to_vec(),
            value: big,
        },
    );
    assert!(out.is_empty());
}

#[test]
fn a_document_on_a_public_suffix_host_gets_no_cookies() {
    let mut kernel = Kernel::new();
    kernel.event(&clazel_kernel::exec::records::EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = open(&mut kernel, "https://github.io/");
    assert!(
        kernel
            .send(
                id,
                &Msg::CookieSet {
                    cookie_string: b"a=b".to_vec()
                }
            )
            .is_empty()
    );
    let out = kernel.send(id, &Msg::CookieGet);
    assert_eq!(cookie_string(&out, id), Some(&b""[..]));
}

#[test]
fn a_navigation_to_a_url_that_does_not_parse_is_an_error() {
    let mut kernel = Kernel::new();
    let id = open(&mut kernel, "https://example.test/");
    let out = kernel.send(
        id,
        &Msg::Navigate {
            url: b"http://".to_vec(),
        },
    );
    assert_eq!(out, vec![Out::To(id, Msg::Error { code: 3 })]);
    // A relative URL resolves against the committed URL, same origin: the
    // renderer stays and gets a new Commit with no script.
    let out = kernel.send(
        id,
        &Msg::Navigate {
            url: b"/b".to_vec(),
        },
    );
    assert_eq!(
        out,
        vec![Out::Fetch(
            id,
            support::code_points("https://example.test/b")
        )]
    );
    let out = settled(&mut kernel, out);
    assert_eq!(
        out,
        vec![Out::To(
            id,
            Msg::Commit {
                url: b"https://example.test/b".to_vec(),
                script: Vec::new()
            }
        )]
    );
}

#[test]
fn a_script_that_is_not_utf8_cannot_be_sent() {
    // The user's script is text; a `Commit` that cannot be encoded is
    // replaced by the encode error, so the tab is still opened.
    let mut kernel = Kernel::new();
    let out = kernel.event(&clazel_kernel::exec::records::EventRecord::OpenTab {
        url: support::code_points("https://example.test/"),
        script: vec![0xFF],
    });
    assert_eq!(out.len(), 2);
    assert!(matches!(out.first(), Some(Out::Spawn(_))));
    assert!(matches!(
        out.get(1),
        Some(Out::To(_, Msg::Error { code: 4 }))
    ));
}

#[test]
fn a_relative_navigate_is_resolved_by_the_real_parser() {
    // Dot segments, query and fragment are the parser's, and the committed
    // URL is its serialization (host lower-cased, default port dropped).
    let mut kernel = Kernel::new();
    let id = open(&mut kernel, "HTTPS://Example.TEST:443/a/b/c");
    let out = kernel.send(
        id,
        &Msg::Navigate {
            url: b"../d/./e?x=1#y".to_vec(),
        },
    );
    let out = settled(&mut kernel, out);
    assert_eq!(
        out,
        vec![Out::To(
            id,
            Msg::Commit {
                url: b"https://example.test/a/d/e?x=1#y".to_vec(),
                script: Vec::new()
            }
        )]
    );
    // An absolute URL on another origin replaces the renderer.
    let out = kernel.send(
        id,
        &Msg::Navigate {
            url: b"//other.test/z".to_vec(),
        },
    );
    let out = settled(&mut kernel, out);
    assert!(matches!(
        out.as_slice(),
        [Out::Kill(old), Out::Spawn(new), Out::To(to, Msg::Commit { .. })]
            if *old == id && new == to && *new != id
    ));
}

#[test]
fn the_cookie_path_is_the_path_of_the_parsed_committed_url() {
    let mut kernel = Kernel::new();
    kernel.event(&clazel_kernel::exec::records::EventRecord::Tick {
        time: 13_000_000_000,
    });
    // The default path of `/dir/page` is `/dir`, from the URL's path and not
    // its query (`?/other/x`).
    let a = open(&mut kernel, "https://example.test/dir/page?/other/x");
    assert!(
        kernel
            .send(
                a,
                &Msg::CookieSet {
                    cookie_string: b"a=b".to_vec()
                }
            )
            .is_empty()
    );
    let in_dir = open(&mut kernel, "https://example.test/dir/other");
    let out = kernel.send(in_dir, &Msg::CookieGet);
    assert_eq!(cookie_string(&out, in_dir), Some(&b"a=b"[..]));
    let elsewhere = open(&mut kernel, "https://example.test/else/where");
    let out = kernel.send(elsewhere, &Msg::CookieGet);
    assert_eq!(cookie_string(&out, elsewhere), Some(&b""[..]));
}
