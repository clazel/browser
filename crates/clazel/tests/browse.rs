//! `clazel browse` (phase-4.md item 4.15) driven against an in-process
//! server, through real renderer processes.
//!
//! What this covers: opening a tab is a fetch through the kernel; the real
//! renderer parses the page (item 4.13) and its title, text and numbered
//! links are printed under the kernel's committed URL; a link number
//! follows a link the renderer found, and `g`, `b` and `r` navigate the
//! tab; a failed fetch is printed with its URL; a renderer's title cannot
//! forge the address line (its control characters are replaced; that test
//! uses a stub renderer, a shell script, to send a hostile `Display`).

mod support;

#[path = "../cli/browse.rs"]
mod browse;

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener};
use std::process::Command;

use clazel::Host;
use clazel_ipc::message::codec::{Msg, encode_framed};

/// A server on loopback that answers every connection with a small HTML
/// page, and closes it.
fn serve() -> SocketAddr {
    let dead = SocketAddr::from(([127, 0, 0, 1], 9));
    let Ok(listener) = TcpListener::bind("127.0.0.1:0") else {
        return dead;
    };
    let addr = listener.local_addr().unwrap_or(dead);
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            std::thread::spawn(move || {
                let mut request = [0u8; 4096];
                let _ = stream.read(&mut request);
                let body = "<title>A page</title><p>Hello <a href=\"/two\">two</a></p>";
                let page = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                    body.len()
                );
                let _ = stream.write_all(page.as_bytes());
            });
        }
    });
    addr
}

/// A host whose renderers are `command(id)` and whose connections all go to
/// the in-process server.
fn host(command: impl FnMut(u64) -> Command + 'static) -> Host {
    let mut host = Host::new(command);
    host.route = Some(serve());
    host
}

/// Run `browse` on `url` with these command lines; what it printed.
fn run(host: &mut Host, url: &str, commands: &[&str]) -> String {
    let input = commands.join("\n");
    let mut out = Vec::new();
    let result = browse::browse(host, url, input.as_bytes(), &mut out, 40);
    assert!(result.is_ok(), "{result:?}");
    String::from_utf8_lossy(&out).into_owned()
}

/// The lines of the `n`-th page `out` printed (counting from 0), from its
/// address line on: what follows the `n`-th rule.
fn page(out: &str, n: usize) -> Vec<&str> {
    let rule = format!("{}\n", "-".repeat(40));
    out.split(rule.as_str())
        .nth(n.saturating_add(1))
        .map(|p| p.lines().collect())
        .unwrap_or_default()
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn browsing_is_a_fetch_and_every_page_is_under_the_kernels_url() {
    let renderer = support::binary("clazel-renderer");
    let mut host = host(move |_| Command::new(&renderer));
    let out = run(
        &mut host,
        "http://a.test/",
        &["1", "b", "r", "g https://a.test/", "q"],
    );
    // The first page: a rule of the width, the kernel's URL, then the
    // page's title, its text with the link's number, and the link resolved
    // against the document's URL.
    assert!(
        out.starts_with(&format!("{}\nURL: http://a.test/\n", "-".repeat(40))),
        "{out}"
    );
    let first = page(&out, 0);
    assert_eq!(first.get(1), Some(&"A page"), "{out}");
    assert!(first.contains(&"Hello two[1]"), "{out}");
    assert!(out.contains("Links:\n[1] http://a.test/two\n"), "{out}");
    // `1` follows the link, `b` comes back, then `r` reloads it.
    assert_eq!(
        page(&out, 1).first(),
        Some(&"URL: http://a.test/two"),
        "{out}"
    );
    assert_eq!(page(&out, 2).first(), Some(&"URL: http://a.test/"), "{out}");
    assert_eq!(page(&out, 3).first(), Some(&"URL: http://a.test/"), "{out}");
    // `https:` is not fetched until TLS (3.5): a fetch failure, with its URL.
    assert!(out.contains("fetch failed: https://a.test/"), "{out}");
    assert_eq!(
        out.matches(&format!("{}\nURL: ", "-".repeat(40))).count(),
        4,
        "{out}"
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn a_link_is_followed_and_a_title_cannot_forge_the_address_line() {
    // Renderer 0 is a stub that, once its document is committed, displays a
    // title that tries to redraw the terminal's address line, and one link
    // to another origin. Every other renderer is the real one.
    let display = Msg::Display {
        title: b"\x1b[1A\x1b[2KURL: https://bank.test/".to_vec(),
        text: b"line one\nline two".to_vec(),
        links: vec![b"http://b.test/landing".to_vec()],
    };
    let octal: String = encode_framed(&display)
        .unwrap_or_default()
        .iter()
        .map(|b| format!("\\{b:03o}"))
        .collect();
    let stub = format!("head -c 4 > /dev/null; sleep 0.3; printf '{octal}'; exec cat > /dev/null");
    let renderer = support::binary("clazel-renderer");
    let mut host = host(move |id| {
        if id == 0 {
            let mut c = Command::new("/bin/sh");
            c.arg("-c").arg(&stub);
            c
        } else {
            Command::new(&renderer)
        }
    });
    let out = run(&mut host, "http://a.test/", &["1", "b", "q"]);
    let first = page(&out, 0);
    assert_eq!(first.first(), Some(&"URL: http://a.test/"), "{out}");
    // The title's escape characters are replaced; the address line is the
    // kernel's, on its own line.
    assert!(!out.contains('\u{1b}'), "{out:?}");
    assert!(
        first.get(1).is_some_and(|t| t.starts_with('\u{FFFD}')),
        "{out}"
    );
    assert!(out.contains("line one\nline two"), "{out}");
    assert!(out.contains("Links:\n[1] http://b.test/landing"), "{out}");
    // `1` follows the link (another origin: a new renderer), `b` comes back.
    assert_eq!(
        page(&out, 1).first(),
        Some(&"URL: http://b.test/landing"),
        "{out}"
    );
    assert_eq!(page(&out, 2).first(), Some(&"URL: http://a.test/"), "{out}");
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes")]
fn a_url_the_kernel_refuses_opens_no_tab() {
    let renderer = support::binary("clazel-renderer");
    let mut host = host(move |_| Command::new(&renderer));
    let out = run(&mut host, "not a url", &["q"]);
    assert_eq!(out, "cannot open not a url\n");
}
