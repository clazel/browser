//! `clazel-adversary`: a renderer that misbehaves, for the tests of phase-2.md
//! item 2.16. Like the real renderer its first act is to enter the sandbox.
//!
//! - `clazel-adversary hostile SEED`: send one hostile frame
//!   (`clazel_renderer::hostile`) on the socket that is its standard input
//!   and output, then wait to be killed. It prints the seed and what it sent
//!   to standard error, which the host shell reports when the renderer is
//!   gone, so a failure names the seed that reproduces it.
//! - `clazel-adversary escape ATTEMPT TARGET`: make one escape attempt
//!   (`clazel_renderer::escape`) and print `DENIED ...` (exit 0) or
//!   `ESCAPED ...` (exit 3). On Linux a forbidden call ends the process with
//!   `SIGSYS` before anything is printed.
//! - `clazel-adversary control ATTEMPT TARGET`: the same attempt without the
//!   sandbox, which the tests use to show that the target is reachable, so
//!   that a denial is the sandbox's.
//! - `clazel-adversary display TITLE [TEXT [LINK]]`: wait for its document
//!   to be committed, then send a `Display` whose title is TITLE, whose text
//!   is TEXT (without one, `URL: TITLE`) and whose only link is LINK (without
//!   one, TITLE), then wait to be killed or for the socket to close. With a
//!   URL as TITLE it is phase-4.md item 4.16's renderer that tries to show
//!   its page under another tab's address; with escape characters in TITLE
//!   it is the renderer of `clazel`'s `browse` test that tries to redraw the
//!   address line.
//! - `clazel-adversary idle`: not sandboxed; block until its standard input
//!   closes. The `ptrace-attach` test starts one as the sibling to attach to
//!   (a plain binary of this build, which the OS lets a same-user process
//!   attach to, unlike a platform binary such as `/bin/sleep` on macOS).
//!
//! Exit codes: 71 a sandbox layer failed (as for the real renderer), 64
//! usage, 70 the socket failed.

use std::io::{self, Read, Write};
use std::process::ExitCode;

use clazel_ipc::message::codec::{Msg, encode_framed};
use clazel_renderer::{escape, hostile, next_document, sandbox};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str);
    if mode != Some("control") && mode != Some("idle") {
        // First act, before anything else is read or done: fail closed.
        if let Err(failure) = sandbox::enter() {
            eprintln!("FAILED-CLOSED {failure}");
            return ExitCode::from(71);
        }
    }
    match (mode, args.get(2), args.get(3)) {
        (Some("idle"), None, None) => {
            let mut sink = Vec::new();
            let _ = io::Read::read_to_end(&mut io::stdin().lock(), &mut sink);
            ExitCode::SUCCESS
        }
        (Some("display"), Some(title), text) => display_mode(
            title,
            text.map(String::as_str),
            args.get(4).map(String::as_str),
        ),
        (Some("hostile"), Some(seed), None) => match seed.parse::<u64>() {
            Ok(seed) => hostile_mode(seed),
            Err(_) => usage(),
        },
        (Some("escape" | "control"), Some(name), Some(target)) => {
            match escape::Attempt::parse(name) {
                Some(attempt) => match escape::try_it(attempt, target) {
                    Ok(done) => {
                        println!("ESCAPED {name}: {done}");
                        ExitCode::from(3)
                    }
                    Err(e) => {
                        println!("DENIED {name}: {e}");
                        ExitCode::SUCCESS
                    }
                },
                None => usage(),
            }
        }
        _ => usage(),
    }
}

fn hostile_mode(seed: u64) -> ExitCode {
    let h = hostile::generate(seed);
    let head: Vec<String> = h
        .bytes
        .iter()
        .take(16)
        .map(|b| format!("{b:02x}"))
        .collect();
    eprintln!(
        "hostile: seed={seed} kind={:?} bytes={} head={}",
        h.kind,
        h.bytes.len(),
        head.join("")
    );
    match hostile::attack(&h, &mut io::stdin().lock(), &mut io::stdout().lock()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("hostile: socket: {e}");
            ExitCode::from(70)
        }
    }
}

/// After the first committed document, a `Display` with this `title`; its
/// text is `text`, or `URL: title` without one, and its one link is `link`,
/// or `title` without one.
fn display_mode(title: &str, text: Option<&str>, link: Option<&str>) -> ExitCode {
    let (mut input, mut output) = (io::stdin().lock(), io::stdout().lock());
    match next_document(&mut input) {
        Ok(Some(_)) => {}
        Ok(None) => return ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("display: {e}");
            return ExitCode::from(70);
        }
    }
    let display = Msg::Display {
        title: title.as_bytes().to_vec(),
        text: text
            .map_or_else(|| format!("URL: {title}"), str::to_owned)
            .into_bytes(),
        links: vec![link.unwrap_or(title).as_bytes().to_vec()],
    };
    let sent = encode_framed(&display).is_some_and(|frame| {
        output
            .write_all(&frame)
            .and_then(|()| output.flush())
            .is_ok()
    });
    eprintln!("display: sent a Display titled {title:?}: {sent}");
    let mut sink = Vec::new();
    let _ = input.read_to_end(&mut sink);
    ExitCode::SUCCESS
}

fn usage() -> ExitCode {
    eprintln!(
        "usage: clazel-adversary hostile SEED | display TITLE [TEXT [LINK]] | escape|control ATTEMPT TARGET | idle"
    );
    ExitCode::from(64)
}
