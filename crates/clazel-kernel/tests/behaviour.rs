//! Hand-written checks of the exec kernel's rules that the official suites
//! do not reach (malformed frames, ids that name nothing, opaque origins,
//! the storage quota, public-suffix hosts, bad navigations). These are not
//! conformance tests: they cite no official suite, print no
//! `clazel-conformance:` line, and the proofs (`exec::step`) are what say
//! the kernel does these things for every input.

mod support;

use clazel_fetch::transducer::types::InputBuf;
use clazel_kernel::exec::records::EventRecord;

use clazel_ipc::message::codec::Msg;
use support::{Kernel, Out};

/// Answer the network outputs among `out` as a server with an empty page
/// would: `Connected` for a `Connect`, a whole response for a `Send`, nothing
/// for a `Close`. The outputs for renderers, in order, with those that
/// answering gave after them (the document's script is the empty body).
fn settled(kernel: &mut Kernel, out: Vec<Out>) -> Vec<Out> {
    let response = b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n".to_vec();
    let mut all = Vec::new();
    let mut queue: std::collections::VecDeque<Out> = out.into();
    while let Some(o) = queue.pop_front() {
        let answer = match o {
            Out::Connect(conn, ..) => Some((conn, InputBuf::Connected)),
            Out::Send(conn, _) => Some((conn, InputBuf::Bytes(response.clone()))),
            Out::Close(_) => None,
            other => {
                all.push(other);
                None
            }
        };
        if let Some((conn, input)) = answer {
            queue.extend(kernel.event(&EventRecord::Net { conn, input }));
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
    let id = open(&mut kernel, "http://example.test/");
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
        vec![Out::Connect(0, b"example.test".to_vec(), 80, false)]
    );
    let out = settled(&mut kernel, out);
    assert_eq!(out, vec![Out::Commit(id, page("http://example.test/b"))]);
}

/// The document a server with an empty page and no `Content-Type` commits.
fn page(url: &str) -> support::Doc {
    support::Doc {
        url: url.as_bytes().to_vec(),
        content_type: Vec::new(),
        kind: 0,
        body: Vec::new(),
    }
}

#[test]
fn a_script_is_committed_as_its_bytes() {
    // Item 4.12: a user script is a document of kind 1 whose body is the
    // script's bytes, so it need not be UTF-8 (the renderer reads it).
    let mut kernel = Kernel::new();
    let out = kernel.event(&clazel_kernel::exec::records::EventRecord::OpenTab {
        url: support::code_points("https://example.test/"),
        script: Some(vec![0xFF]),
    });
    assert_eq!(
        out,
        vec![
            Out::Spawn(0),
            Out::Commit(
                0,
                support::Doc {
                    url: b"https://example.test/".to_vec(),
                    content_type: Vec::new(),
                    kind: 1,
                    body: vec![0xFF],
                }
            )
        ]
    );
}

#[test]
fn a_relative_navigate_is_resolved_by_the_real_parser() {
    // Dot segments, query and fragment are the parser's, and the committed
    // URL is its serialization (host lower-cased, default port dropped).
    let mut kernel = Kernel::new();
    let id = open(&mut kernel, "HTTP://Example.TEST:80/a/b/c");
    let out = kernel.send(
        id,
        &Msg::Navigate {
            url: b"../d/./e?x=1#y".to_vec(),
        },
    );
    let out = settled(&mut kernel, out);
    assert_eq!(
        out,
        vec![Out::Commit(id, page("http://example.test/a/d/e?x=1#y"))]
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
        [Out::Kill(old), Out::Spawn(new), Out::Commit(to, _)]
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
