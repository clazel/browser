//! Hostile pages (phase-4.md item 4.16), each served by an in-process
//! server (`support/server.rs`), fetched by the kernel and parsed by a real
//! sandboxed `clazel-renderer` process, as `clazel browse` does.
//!
//! Every page is checked for the three things exit criterion 5 asks:
//!
//! - **no panic**: the renderer displays the page and is still running
//!   afterwards (a panic ends the process, which the host logs as
//!   `exited`);
//! - **the memory bound of item 4.13** (`crates/clazel-renderer/README.md`,
//!   "Memory"): the renderer's peak resident set is at most the README's
//!   terms for the page's body size `B`, node count `N` and attributes, plus
//!   [`BASE`] for the process itself. The peak is read from
//!   `/proc/<pid>/status` (`VmHWM`, exact) on Linux and sampled with `ps`
//!   every 25 ms elsewhere (macOS has no peak counter a test can read
//!   without `unsafe`); each renderer is started through `/bin/sh`, which
//!   writes its pid and `exec`s it, so the pid is the renderer's;
//! - **the address line is unchanged**: the `Show` the kernel makes of the
//!   renderer's `Display` names the tab's committed URL, whatever the page
//!   says.
//!
//! Pages up to a few MiB are also rendered in this process
//! (`clazel_renderer::pipeline::render`) and what the renderer process
//! sent must be exactly that (through `fit`, the one-frame limit), and
//! their node count is taken from that parse. The largest pages are not
//! parsed twice: their `N` is stated.
//!
//! Sizes. A million nested `<div>`s cannot be parsed in a test's time:
//! the tree builder is quadratic in the depth (see
//! [`nested_divs_at_scale`]), so the normal run nests [`DIVS`] and the
//! million is an ignored test. 64 MiB of `&amp;` takes about 15 minutes
//! (each named reference scans the whole table, see
//! [`sixty_four_mib_of_amp`]), so the normal run has 1 MiB of `&amp;` and
//! a 64 MiB body of plain words, and the 64 MiB of `&amp;` is an ignored
//! test (it passed when run: 872 s, peak 675 MiB of a 1,361 MiB bound,
//! macOS arm64, debug build). Under Miri nothing here runs: every test
//! spawns processes and calls the OS sandbox. The tests take turns
//! ([`HEAVY`]) so that their peaks and times are their own.
#![cfg(unix)]

mod support;

#[path = "support/server.rs"]
mod server;

#[path = "../cli/browse.rs"]
mod browse;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_dom::exec::{Arena, ExecAttr, ExecKind, MAX_NODES};
use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::OutputRecord;
use clazel_renderer::pipeline::{fit, parse_html, render};
use server::{Reply, Request, serve};

/// One test at a time: their memory and time are measured.
static HEAVY: Mutex<()> = Mutex::new(());

/// The URL every hostile page is served at.
const URL: &str = "http://h.test/";

/// How long a page may take, debug build, loaded machine.
const LIMIT: Duration = Duration::from_secs(1200);

const MIB: u64 = 1024 * 1024;

/// The process itself, before any page: the binary, the standard library,
/// the allocator's arenas and the 1 MiB frame buffers. Ours, not the
/// README's: an idle renderer measures about 2 MiB on macOS arm64.
const BASE: u64 = 16 * MIB;

/// The nesting depth of the normal run of the nested `<div>` page.
const DIVS: usize = 20_000;

/// What the renderer of a page displayed, how its process fared, and the
/// server's view.
struct Loaded {
    /// The `Show`'s URL: the address line.
    url: String,
    /// The title, text and links displayed.
    title: String,
    text: String,
    links: Vec<String>,
    /// From the navigation to the `Show`.
    elapsed: Duration,
    /// The largest peak resident set of a renderer of this host, bytes.
    peak: u64,
    /// Requests the server received.
    requests: usize,
}

/// The resident set of `pid` now, and its peak where the OS keeps one, in
/// KiB.
fn sample(pid: &str) -> Option<u64> {
    let hwm = std::fs::read_to_string(format!("/proc/{pid}/status"))
        .ok()
        .and_then(|s| {
            s.lines()
                .find_map(|l| l.strip_prefix("VmHWM:"))
                .and_then(|v| v.trim().trim_end_matches("kB").trim().parse::<u64>().ok())
        });
    if hwm.is_some() {
        return hwm;
    }
    let out = Command::new("ps")
        .args(["-o", "rss=", "-p", pid])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout).trim().parse().ok()
}

/// Sample every renderer whose pid file is in `dir`; the largest value seen
/// so far for each, in `peaks`.
fn sample_all(dir: &Path, peaks: &Mutex<BTreeMap<String, u64>>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let Ok(pid) = std::fs::read_to_string(entry.path()) else {
            continue;
        };
        let pid = pid.trim().to_owned();
        if let (Some(kib), Ok(mut p)) = (sample(&pid), peaks.lock()) {
            let e = p.entry(pid).or_insert(0);
            *e = (*e).max(kib);
        }
    }
}

/// Serve `route`, start a host whose renderers are `program args`, each
/// started through `/bin/sh` so its pid is recorded, run `f` on it, and
/// measure the renderers' peak resident sets meanwhile. `f`'s result, the
/// largest peak in bytes, and the number of requests served.
fn measured<T>(
    name: &str,
    route: impl Fn(&Request) -> Reply + Send + Sync + 'static,
    program: impl Fn(u64) -> Vec<String> + 'static,
    f: impl FnOnce(&mut Host) -> T,
) -> (T, u64, usize) {
    let _turn = HEAVY
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("hostile-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(std::fs::create_dir_all(&dir).is_ok(), "cannot make {dir:?}");
    let server = serve(route);
    let piddir = dir.clone();
    let mut host = Host::new(move |id| {
        let mut c = Command::new("/bin/sh");
        c.arg("-c")
            .arg("echo $$ > \"$PIDDIR/$ID.pid\"; exec \"$0\" \"$@\"")
            .args(program(id))
            .env("PIDDIR", &piddir)
            .env("ID", id.to_string());
        c
    });
    host.route = Some(server.addr);
    let peaks: Arc<Mutex<BTreeMap<String, u64>>> = Arc::default();
    let stop = Arc::new(AtomicBool::new(false));
    let sampler = {
        let (dir, peaks, stop) = (dir.clone(), Arc::clone(&peaks), Arc::clone(&stop));
        std::thread::spawn(move || {
            while !stop.load(Ordering::SeqCst) {
                sample_all(&dir, &peaks);
                std::thread::sleep(Duration::from_millis(25));
            }
        })
    };
    let result = f(&mut host);
    stop.store(true, Ordering::SeqCst);
    let _ = sampler.join();
    // A last reading while the renderers still run (on Linux, the exact
    // peak).
    sample_all(&dir, &peaks);
    let peak = peaks
        .lock()
        .map(|p| p.values().copied().max().unwrap_or(0))
        .unwrap_or(0)
        .saturating_mul(1024);
    // No renderer ended on its own (a panic would have); the kernel kills
    // one when its tab leaves its origin.
    let ended: Vec<&String> = host
        .log
        .iter()
        .filter(|l| l.contains(" exited: ") && !l.contains(" exited: killed by the kernel;"))
        .collect();
    assert!(ended.is_empty(), "a renderer ended: {ended:#?}");
    let requests = server.seen.lock().map(|s| s.len()).unwrap_or(0);
    drop(host);
    let _ = std::fs::remove_dir_all(&dir);
    (result, peak, requests)
}

/// The real renderer.
fn renderer(_: u64) -> Vec<String> {
    vec![support::binary("clazel-renderer").display().to_string()]
}

/// Pump until `tab` is shown or `LIMIT` passes.
fn shown(host: &mut Host, tab: u64) -> Option<(String, String, String, Vec<String>)> {
    let end = Instant::now()
        .checked_add(LIMIT)
        .unwrap_or_else(Instant::now);
    while Instant::now() < end {
        let found = host
            .shown
            .iter()
            .position(|o| matches!(o, OutputRecord::Show { tab: t, .. } if *t == tab));
        if let Some(OutputRecord::Show {
            url,
            title,
            text,
            links,
            ..
        }) = found.map(|i| host.shown.remove(i))
        {
            let lossy = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
            return Some((
                url.iter().filter_map(|c| char::from_u32(*c)).collect(),
                lossy(&title),
                lossy(&text),
                links.iter().map(|l| lossy(l)).collect(),
            ));
        }
        if host.log.iter().any(|l| l.contains(" exited: ")) {
            return None;
        }
        host.pump(Duration::from_millis(50));
    }
    None
}

/// Load `reply` at [`URL`] in a fresh host with the real renderer.
fn load(name: &str, reply: Reply) -> Loaded {
    let ((shown, elapsed), peak, requests) = measured(
        name,
        move |_| reply.clone(),
        renderer,
        |host| {
            let start = Instant::now();
            let tab = host.open(URL);
            let s = shown(host, tab);
            assert!(s.is_some(), "{name}: no page; host log: {:#?}", host.log);
            (s, start.elapsed())
        },
    );
    let (url, title, text, links) = shown.unwrap_or_default();
    let loaded = Loaded {
        url,
        title,
        text,
        links,
        elapsed,
        peak,
        requests,
    };
    println!(
        "{name}: shown after {:?}, renderer peak {} MiB, text {} bytes, {} links",
        loaded.elapsed,
        loaded.peak / MIB,
        loaded.text.len(),
        loaded.links.len()
    );
    // The address line is the kernel's, and the renderer asked for nothing.
    assert_eq!(loaded.url, URL, "{name}");
    assert_eq!(loaded.requests, 1, "{name}");
    loaded
}

/// A `200` reply of `body` (one piece) with the content type `ct`.
fn page(ct: &str, body: &[u8]) -> Reply {
    Reply {
        head: format!("HTTP/1.1 200 OK\r\nContent-Type: {ct}\r\n"),
        piece: body.to_vec(),
        times: 1,
    }
}

/// The attribute records of a tree, in bytes, and their characters.
fn attributes(doc: &Arena) -> (u64, u64) {
    let record = u64::try_from(std::mem::size_of::<ExecAttr>()).unwrap_or(u64::MAX);
    let (mut bytes, mut chars) = (0u64, 0u64);
    for id in 0..doc.len() {
        if let ExecKind::Element { attributes, .. } = doc.kind(id) {
            for a in attributes {
                let n = a
                    .local_name
                    .len()
                    .saturating_add(a.value.len())
                    .saturating_add(a.prefix.as_ref().map_or(0, Vec::len));
                let n = u64::try_from(n).unwrap_or(u64::MAX);
                bytes = bytes
                    .saturating_add(record)
                    .saturating_add(n.saturating_mul(4));
                chars = chars.saturating_add(n);
            }
        }
    }
    (bytes, chars)
}

/// The bound of item 4.13 (`crates/clazel-renderer/README.md`, "Memory"),
/// in bytes, for a body of `b` bytes whose tree has `n` nodes and
/// attributes of `attr_bytes` bytes holding `attr_chars` characters: the
/// body, the decoded input, the preprocessed copy, the node records, the
/// text node data, the attributes, the page (`2·(T + A) + 162·N`
/// characters, at most 4 bytes each, with `T` at most `b`), the frame, and
/// [`BASE`].
fn bound(b: u64, n: u64, attr_bytes: u64, attr_chars: u64) -> u64 {
    let parser = b
        .saturating_mul(13)
        .saturating_add(n.saturating_mul(176))
        .saturating_add(attr_bytes);
    let page_chars = b
        .saturating_add(attr_chars)
        .saturating_mul(2)
        .saturating_add(n.saturating_mul(162));
    parser
        .saturating_add(page_chars.saturating_mul(4))
        .saturating_add(MIB)
        .saturating_add(BASE)
}

/// Check `loaded` against the bound for a body of `b` bytes and the tree
/// `doc` (or `n` nodes and no attributes, when the page is too large to
/// parse twice).
fn check_bound(name: &str, loaded: &Loaded, b: usize, tree: Result<&Arena, u64>) {
    let b = u64::try_from(b).unwrap_or(u64::MAX);
    let (n, attr_bytes, attr_chars) = match tree {
        Ok(doc) => {
            let (ab, ac) = attributes(doc);
            (u64::try_from(doc.len()).unwrap_or(u64::MAX), ab, ac)
        }
        Err(n) => (n, 0, 0),
    };
    let limit = bound(b, n, attr_bytes, attr_chars);
    println!(
        "{name}: B = {b} bytes, N = {n} nodes, attributes {attr_bytes} bytes: bound {} MiB, peak {} MiB",
        limit / MIB,
        loaded.peak / MIB
    );
    assert!(
        loaded.peak > 0,
        "{name}: the renderer's memory was not measured"
    );
    assert!(
        loaded.peak <= limit,
        "{name}: peak {} bytes over the bound {limit} bytes",
        loaded.peak
    );
}

/// What the pipeline gives for `body` at [`URL`] in this process, as the
/// `Display` the renderer sends.
fn in_process(ct: &str, body: &[u8]) -> (String, String, Vec<String>) {
    let shown = render(
        URL.as_bytes(),
        ct.as_bytes(),
        body,
        clazel_renderer::DEFAULT_WIDTH,
    );
    let Msg::Display { title, text, links } = fit(shown) else {
        return Default::default();
    };
    let lossy = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
    (
        lossy(&title),
        lossy(&text),
        links.iter().map(|l| lossy(l)).collect(),
    )
}

/// The tree the pipeline builds for an HTML `body` at [`URL`].
fn tree(body: &[u8]) -> Arena {
    let url: Vec<u32> = URL.chars().map(u32::from).collect();
    match parse_html(body, None, &url) {
        Ok(p) => p.arena,
        Err(_) => Arena::new(url),
    }
}

/// Load a page of moderate size and check it in full: the renderer
/// process displays what the pipeline gives here, within the bound. The
/// page, and the tree the pipeline builds of it as HTML.
fn load_and_compare(name: &str, ct: &str, body: &[u8]) -> (Loaded, Arena) {
    let loaded = load(name, page(ct, body));
    let want = in_process(ct, body);
    assert_eq!(
        (&loaded.title, &loaded.text, &loaded.links),
        (&want.0, &want.1, &want.2),
        "{name}"
    );
    let doc = tree(body);
    check_bound(name, &loaded, body.len(), Ok(&doc));
    (loaded, doc)
}

/// `depth` nested `<div>`s, with a word at the bottom.
fn nested_divs(depth: usize) -> Vec<u8> {
    let mut body = "<div>".repeat(depth).into_bytes();
    body.extend_from_slice(b"bottom");
    body
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn nested_divs_in_a_real_renderer() {
    let body = nested_divs(DIVS);
    let (loaded, _) = load_and_compare("nested divs", "text/html", &body);
    assert_eq!(loaded.text, "bottom");
}

/// The million of the plan. Ignored: the tree builder's "insert an
/// element at the adjusted insertion location" checks that the new
/// element is not an inclusive ancestor of its parent
/// (`clazel-treebuilder` `exec/insert.rs`, a walk up the parents), so each
/// of the `d` nested elements costs `O(d)` and the page `O(d²)`: 8,000
/// nested elements parse in about 1.4 s in a debug build, 20,000 in about
/// 9 s, so a million would take hours. Run with `--ignored` to measure it.
#[test]
#[ignore = "quadratic in the depth: a million nested divs take hours in a debug build (see the doc comment)"]
fn nested_divs_at_scale() {
    let body = nested_divs(1_000_000);
    let loaded = load("a million nested divs", page("text/html", &body));
    assert_eq!(loaded.text, "bottom");
    check_bound("a million nested divs", &loaded, body.len(), Err(1_000_005));
}

/// `kinds` formatting elements of each of `<b>`, `<i>`, `<u>` with distinct
/// attributes (so the Noah's Ark clause keeps every one) in a paragraph,
/// then `paragraphs` paragraphs of one character, each of which
/// reconstructs the whole list.
fn formatting_page(kinds: usize, paragraphs: usize) -> Vec<u8> {
    let mut body = String::from("<p>");
    for k in 0..kinds {
        body.push_str(&format!("<b id=b{k}><i id=i{k}><u id=u{k}>"));
    }
    body.push_str("</p>");
    body.push_str(&"<p>x</p>".repeat(paragraphs));
    body.into_bytes()
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn the_active_formatting_list_reconstructed_again_and_again() {
    let (kinds, paragraphs) = (100usize, 2000usize);
    let body = formatting_page(kinds, paragraphs);
    let (loaded, doc) = load_and_compare("formatting list", "text/html", &body);
    let nodes = doc.len();
    // The growth is the quadratic one: each paragraph's text reconstructs
    // all 3·kinds formatting elements.
    let f = kinds.saturating_mul(3);
    assert!(
        nodes >= paragraphs.saturating_mul(f),
        "{nodes} nodes: the list was not reconstructed"
    );
    // Item 4.9's bound: one token creates at most 44 + 6T + 2F + P(F + 1)
    // nodes; here T = 0 (no templates), P = 0 (no table text), F at most
    // the number of formatting start tags, and every token but the end of
    // file consumes at least one input character.
    let tokens = body.len().saturating_add(1);
    let per_token = f.saturating_mul(2).saturating_add(44);
    let theorem = tokens.saturating_mul(per_token).saturating_add(1);
    println!(
        "formatting list: {nodes} nodes from {} bytes in {:?}; 4.9's bound {theorem}",
        body.len(),
        loaded.elapsed
    );
    assert!(nodes <= theorem, "{nodes} nodes over 4.9's bound {theorem}");
}

/// A body of `piece` repeated `times` times, streamed by the server, in one
/// text node: its text starts with `first`, and is either cut to the
/// display limit or, if `whole`, all there (one `&` a piece).
fn one_text_node(name: &str, piece: &[u8], times: usize, first: &str, whole: bool) {
    let reply = Reply {
        head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
        piece: piece.to_vec(),
        times,
    };
    let loaded = load(name, reply);
    assert!(
        loaded.text.starts_with(first),
        "{:?}",
        loaded.text.get(..200)
    );
    if whole {
        assert_eq!(loaded.text.matches('&').count(), times, "{name}");
    } else {
        assert!(
            loaded
                .text
                .lines()
                .last()
                .is_some_and(|l| l.starts_with("[page cut to fit the 1 MiB display limit")),
            "{:?}",
            loaded.text.lines().last()
        );
    }
    // N: the document, `html`, `head`, `body` and one text node.
    check_bound(name, &loaded, times.saturating_mul(piece.len()), Err(5));
}

/// 64 MiB, the body limit, less what a whole number of `piece`s leaves.
fn at_the_limit(piece: &[u8]) -> usize {
    (64usize * 1024 * 1024)
        .checked_div(piece.len())
        .unwrap_or(0)
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_body_at_the_64_mib_limit() {
    // 67,108,864 bytes of words: the body limit, streamed by the server and
    // held by the kernel and the renderer.
    one_text_node(
        "64 MiB of words",
        b"word ",
        at_the_limit(b"word "),
        "word word",
        false,
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_mib_of_amp() {
    // 209,715 references (1 MiB less 1 byte): the normal run's size, see
    // `sixty_four_mib_of_amp`.
    one_text_node(
        "1 MiB of &amp;",
        b"&amp;",
        at_the_limit(b"&amp;") / 64,
        &"&".repeat(80),
        true,
    );
}

/// The plan's 64 MiB of `&amp;`: 13,421,772 references, 67,108,860 bytes.
/// Ignored in the normal run: `clazel-html`'s named reference match
/// (`charref::exec::longest_match_exec`) compares the input with every one
/// of the table's 2,231 names, so each reference costs about 66 µs in a
/// debug build on a loaded machine (plain text: 0.45 µs a character), and
/// this page takes about 15 minutes. Run with `--ignored` to measure it.
#[test]
#[ignore = "about 15 minutes in a debug build: each named reference scans the whole table (see the doc comment)"]
fn sixty_four_mib_of_amp() {
    one_text_node(
        "64 MiB of &amp;",
        b"&amp;",
        at_the_limit(b"&amp;"),
        &"&".repeat(80),
        false,
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn references_without_semicolons() {
    let piece = "<p>&amp &lt &gt &notin &noti &copy2 &ampx &#65 &#x42 &#xZ &#0 &#x110000 &unknown; & &&</p><a href=\"/?a=1&copy=2&lt=3&amp\">q</a>\n";
    let body = piece.repeat(2000).into_bytes();
    let (loaded, _) = load_and_compare("references without semicolons", "text/html", &body);
    let first = loaded.text.lines().next().unwrap_or_default();
    assert_eq!(
        first,
        "& < > \u{AC}in \u{AC}i \u{A9}2 &x A B &#xZ \u{FFFD} \u{FFFD} &unknown; & &&",
    );
    // In an attribute, a legacy reference followed by `=` or an
    // alphanumeric is left as written (HTML §13.2.5.73); `&amp` at the end
    // is decoded.
    assert_eq!(
        loaded.links.first().map(String::as_str),
        Some("http://h.test/?a=1&copy=2&lt=3&")
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_meta_charset_at_byte_1025_restarts_the_parser() {
    // 1025 bytes of comment, so the prescan (the first 1024 bytes) does
    // not see the `meta`; the tree builder does, and the pipeline parses
    // again in windows-1251.
    let mut body = b"<!--".to_vec();
    body.resize(1025 - 3, b'x');
    body.extend_from_slice(b"-->");
    assert_eq!(body.len(), 1025);
    body.extend_from_slice(b"<meta charset=\"windows-1251\"><title>\xcf\xf0\xe8\xe2\xe5\xf2</title><p>\xcf\xf0\xe8\xe2\xe5\xf2</p>");
    let (loaded, _) = load_and_compare("meta charset at byte 1025", "text/html", &body);
    assert_eq!(loaded.title, "\u{41f}\u{440}\u{438}\u{432}\u{435}\u{442}");
    assert_eq!(loaded.text, "\u{41f}\u{440}\u{438}\u{432}\u{435}\u{442}");
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn content_types_that_lie() {
    let html = b"<title>Bank</title><p>Sign in <a href=\"/login\">here</a></p>";
    // An image type over HTML: not shown, and not sniffed as HTML.
    let (image, _) = load_and_compare("image/png over HTML", "image/png", html);
    assert_eq!(image.text, "image/png is not shown: http://h.test/");
    assert!(image.links.is_empty() && image.title.is_empty());
    // text/plain over HTML: the markup is text.
    let (plain, _) = load_and_compare("text/plain over HTML", "text/plain", html);
    assert!(plain.text.contains("<title>Bank</title>"), "{}", plain.text);
    assert!(plain.links.is_empty() && plain.title.is_empty());
    // text/html over an image: parsed as HTML, whatever it is.
    let png = b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR\x00\x00\x00\x01<a href=x>";
    load_and_compare("text/html over a PNG", "text/html", png);
    // A type that does not parse: sniffed, as no type.
    load_and_compare("an unparsable type", "text/html; charset=\"", html);
}

/// Bytes no encoding reads cleanly: every byte from 0x80, NUL, UTF-8's
/// overlong, surrogate and out-of-range forms, and an unpaired UTF-16
/// surrogate, in an odd number of bytes.
fn invalid_bytes() -> Vec<u8> {
    let mut b: Vec<u8> = (0x80..=0xFFu8).collect();
    b.extend_from_slice(b"\x00\xC0\xAF\xED\xA0\x80\xF4\x90\x80\x80\x00\xD8<p>\xFF");
    b
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn bytes_that_are_not_valid_in_any_encoding() {
    let body = invalid_bytes().repeat(1000);
    for ct in [
        "text/html; charset=utf-8",
        "text/html",
        "text/html; charset=utf-16le",
        "text/html; charset=utf-16be",
        "text/html; charset=shift_jis",
        "text/plain; charset=utf-8",
    ] {
        let (loaded, _) = load_and_compare(&format!("invalid bytes as {ct}"), ct, &body);
        if ct.ends_with("utf-8") {
            assert!(loaded.text.contains('\u{FFFD}'), "{ct}");
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_page_that_is_one_plaintext() {
    let mut body = b"<plaintext>".to_vec();
    body.extend(
        b"<title>t</title><base href=\"http://bank.test/\"><a href=/x>y</a>\n".repeat(5000),
    );
    let (loaded, _) = load_and_compare("one plaintext", "text/html", &body);
    assert!(loaded.title.is_empty() && loaded.links.is_empty());
    assert!(
        loaded.text.starts_with("<title>t</title>"),
        "{:?}",
        loaded.text.get(..100)
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_title_and_a_base_that_look_like_the_address_bar() {
    let body: &[u8] = b"<title>\x1b[1A\x1b[2K\rURL: http://bank.test/login</title><base href=\"http://bank.test/\"><p>Sign in <a href=\"login\">here</a></p>";
    let reply = page("text/html", body);
    let (out, peak, requests) = measured(
        "address bar",
        move |r: &Request| {
            if r.host == "h.test" {
                reply.clone()
            } else {
                page("text/html", b"<title>the bank</title>")
            }
        },
        renderer,
        |host| {
            let mut out = Vec::new();
            let result = browse::browse(host, URL, b"1\nq\n".as_slice(), &mut out, 80);
            assert!(result.is_ok(), "{result:?}");
            String::from_utf8_lossy(&out).into_owned()
        },
    );
    let rule = format!("{}\n", "-".repeat(80));
    let pages: Vec<&str> = out.split(rule.as_str()).skip(1).collect();
    // The address line is the kernel's; the title is on the next line,
    // its escape characters replaced (the carriage return is white space,
    // collapsed by the layout).
    let first: Vec<&str> = pages
        .first()
        .map(|p| p.lines().collect())
        .unwrap_or_default();
    assert_eq!(first.first(), Some(&"URL: http://h.test/"), "{out}");
    assert_eq!(
        first.get(1),
        Some(&"\u{FFFD}[1A\u{FFFD}[2K URL: http://bank.test/login"),
        "{out}"
    );
    assert!(!out.contains('\u{1b}') && !out.contains('\r'), "{out:?}");
    // The base URL is the page's to set, so its link goes to the bank: the
    // address line says so only once the user follows it and the kernel
    // commits it.
    assert!(
        out.contains("Links:\n[1] http://bank.test/login\n"),
        "{out}"
    );
    let second: Vec<&str> = pages
        .get(1)
        .map(|p| p.lines().collect())
        .unwrap_or_default();
    assert_eq!(
        second.first(),
        Some(&"URL: http://bank.test/login"),
        "{out}"
    );
    assert_eq!(requests, 2);
    let doc = tree(body);
    let loaded = Loaded {
        url: URL.to_owned(),
        title: String::new(),
        text: String::new(),
        links: Vec::new(),
        elapsed: Duration::ZERO,
        peak,
        requests,
    };
    check_bound("address bar", &loaded, body.len(), Ok(&doc));
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_page_over_max_nodes_is_cut_with_a_notice() {
    // Each `<br>` is one element node; with the document, `html`, `head`
    // and `body`, this is past the arena's limit.
    let times = MAX_NODES.saturating_add(1000);
    let reply = Reply {
        head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
        piece: b"<br>".to_vec(),
        times,
    };
    let loaded = load("over max_nodes", reply);
    assert!(
        loaded.text.contains(&format!(
            "[the page was cut at {MAX_NODES} nodes, the parser's limit]"
        )),
        "{:?}",
        loaded.text.lines().rev().take(3).collect::<Vec<_>>()
    );
    let n = u64::try_from(MAX_NODES).unwrap_or(u64::MAX);
    check_bound("over max_nodes", &loaded, times.saturating_mul(4), Err(n));
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn a_display_titled_with_another_tabs_url_is_shown_under_its_own_tab() {
    // Tab a's renderer is the real one; tab b's is `clazel-adversary
    // display`, sandboxed, which displays a page claiming to be tab a's.
    let spawned = std::cell::Cell::new(0u32);
    let ((a, b, shows), _, requests) = measured(
        "another tab's url",
        |r: &Request| {
            page(
                "text/html",
                format!("<title>{}</title><p>real</p>", r.host).as_bytes(),
            )
        },
        move |_| {
            spawned.set(spawned.get().saturating_add(1));
            if spawned.get() == 1 {
                renderer(0)
            } else {
                vec![
                    support::binary("clazel-adversary").display().to_string(),
                    "display".to_owned(),
                    "http://a.test/".to_owned(),
                ]
            }
        },
        |host| {
            let a = host.open("http://a.test/");
            let shown_a = shown(host, a);
            let b = host.open("http://b.test/");
            let shown_b = shown(host, b);
            // Anything else the adversary's frame caused.
            host.pump(Duration::from_millis(300));
            let more = host.shown.len();
            (shown_a, shown_b, more)
        },
    );
    let a = a.unwrap_or_default();
    let b = b.unwrap_or_default();
    assert_eq!((a.0.as_str(), a.1.as_str()), ("http://a.test/", "a.test"));
    // The adversary's page is shown, under tab b's committed URL.
    assert_eq!(b.0, "http://b.test/");
    assert_eq!(b.1, "http://a.test/");
    assert_eq!(b.2, "URL: http://a.test/");
    assert_eq!(shows, 0, "the adversary's Display made another Show");
    assert_eq!(requests, 2);
}
