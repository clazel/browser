//! `clazel browse URL` (phase-4.md item 4.15): a text-mode browser in the
//! style of Lynx, as a loop over the host shell's public functions. Outside
//! the line-counted shell in `src/`.
//!
//! It opens a tab at the URL (a fetch, item 4.12), then repeats: wait for
//! what the tab's renderer displays (a `Show`), print it, read a command.
//!
//! - A `Show` prints as a rule, the address line `URL: <the kernel's URL>`
//!   (the `Show`'s `url`, which the kernel takes from its own state, never
//!   from the message), the title, the text, and `Links:` with each number
//!   and URL. Control characters in what the renderer sent are replaced by
//!   U+FFFD (the text keeps its line breaks), so a page cannot use terminal
//!   escape sequences to redraw the address line: this loop has no terminal
//!   library (CLAUDE.md rule 8) and prints plain lines.
//! - A fetch that fails (an `Error` to the tab's renderer, item 3.7, which
//!   the host logs) prints `fetch failed: <URL>`.
//! - Commands, one per line: a number follows that link (`navigate_tab`, the
//!   user's own action, which is why the host and not the renderer sends
//!   it); `g URL` navigates; `b` goes back along this loop's list of the
//!   URLs the tab committed; `r` reloads; `q` (or the end of the input)
//!   quits.
//!
//! The width is `$COLUMNS`, or 80. It sets the rule and wraps the title,
//! the address line and the links; the text is printed as the renderer laid
//! it out (item 4.14 lays it out in the renderer).

use std::io::{self, BufRead, Write};
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_kernel::exec::records::OutputRecord;

/// How long to wait for a page before saying so.
const PAGE_WAIT: Duration = Duration::from_secs(30);

/// What a tab showed: the address line, the title, the text and the links.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Page {
    /// The kernel's committed URL for the tab.
    pub url: String,
    /// The title the renderer displayed.
    pub title: String,
    /// The text it displayed.
    pub text: String,
    /// The links it displayed, absolute URLs.
    pub links: Vec<String>,
}

/// What waiting for a tab gave.
enum Outcome {
    /// The tab showed a page.
    Shown(Page),
    /// The navigation failed (`Error` to the tab's renderer).
    Failed,
    /// The tab has no renderer any more.
    Gone,
    /// Nothing happened within [`PAGE_WAIT`].
    Silent,
}

/// `s` with every control character but those in `keep` replaced by
/// U+FFFD.
fn clean(s: &str, keep: &[char]) -> String {
    s.chars()
        .map(|c| {
            if c.is_control() && !keep.contains(&c) {
                '\u{FFFD}'
            } else {
                c
            }
        })
        .collect()
}

/// A renderer's octets as text, with no control character but the kept
/// ones.
fn text(b: &[u8], keep: &[char]) -> String {
    clean(&String::from_utf8_lossy(b), keep)
}

/// `line` in pieces of at most `width` characters.
fn wrap(line: &str, width: usize) -> Vec<String> {
    let chars: Vec<char> = line.chars().collect();
    let pieces: Vec<String> = chars
        .chunks(width.max(1))
        .map(|c| c.iter().collect())
        .collect();
    if pieces.is_empty() {
        vec![String::new()]
    } else {
        pieces
    }
}

/// The renderer of `tab` in the host's kernel state, if it has one.
fn renderer_of(host: &Host, tab: u64) -> Option<u64> {
    host.state
        .renderers
        .iter()
        .find(|r| r.tab == tab)
        .map(|r| r.id)
}

/// Pump the host until `tab` shows a page, its navigation fails or it has no
/// renderer; the host's log is read from line `seen` on.
fn wait(host: &mut Host, tab: u64, seen: &mut usize) -> Outcome {
    let end = Instant::now()
        .checked_add(PAGE_WAIT)
        .unwrap_or_else(Instant::now);
    loop {
        let found = host
            .shown
            .iter()
            .position(|o| matches!(o, OutputRecord::Show { tab: t, .. } if *t == tab));
        if let Some(OutputRecord::Show {
            url,
            title,
            text: body,
            links,
            ..
        }) = found.map(|i| host.shown.remove(i))
        {
            let url: String = url.iter().filter_map(|c| char::from_u32(*c)).collect();
            return Outcome::Shown(Page {
                url: clean(&url, &[]),
                title: text(&title, &[]),
                text: text(&body, &['\n']),
                links: links.iter().map(|l| text(l, &[])).collect(),
            });
        }
        let Some(id) = renderer_of(host, tab) else {
            return Outcome::Gone;
        };
        let failed = host.log.iter().skip(*seen).any(|l| {
            l.starts_with(&format!("renderer {id} <- Error {{ code: "))
                && (l.contains("code: 5 }") || l.contains("code: 3 }"))
        });
        *seen = host.log.len();
        if failed {
            return Outcome::Failed;
        }
        if Instant::now() >= end {
            return Outcome::Silent;
        }
        host.pump(Duration::from_millis(50));
    }
}

/// Print a page.
fn print<W: Write>(out: &mut W, page: &Page, width: usize) -> io::Result<()> {
    writeln!(out, "{}", "-".repeat(width.max(1)))?;
    for line in wrap(&format!("URL: {}", page.url), width) {
        writeln!(out, "{line}")?;
    }
    for line in wrap(&page.title, width) {
        writeln!(out, "{line}")?;
    }
    writeln!(out)?;
    writeln!(out, "{}", page.text)?;
    writeln!(out, "Links:")?;
    for (n, link) in page.links.iter().enumerate() {
        for line in wrap(&format!("[{}] {link}", n.saturating_add(1)), width) {
            writeln!(out, "{line}")?;
        }
    }
    Ok(())
}

/// The loop, over any input and output: open a tab at `url` in `host`, and
/// browse it with the commands read from `input`. Returns when the user
/// quits, the input ends, or the tab is gone.
pub fn browse<R: BufRead, W: Write>(
    host: &mut Host,
    url: &str,
    input: R,
    out: &mut W,
    width: usize,
) -> io::Result<()> {
    let tab = host.open(url);
    if renderer_of(host, tab).is_none() {
        writeln!(out, "cannot open {url}")?;
        return Ok(());
    }
    let mut seen = 0usize;
    // The URLs this tab committed, the current one last: `b` walks it back.
    let mut history: Vec<String> = Vec::new();
    let mut going_back = false;
    let mut current: Option<Page> = None;
    let mut target = url.to_owned();
    let mut lines = input.lines();
    loop {
        match wait(host, tab, &mut seen) {
            Outcome::Shown(page) => {
                print(out, &page, width)?;
                if !going_back && history.last() != Some(&page.url) {
                    history.push(page.url.clone());
                }
                current = Some(page);
            }
            Outcome::Failed => writeln!(out, "fetch failed: {target}")?,
            Outcome::Gone => {
                writeln!(out, "the tab is gone")?;
                return Ok(());
            }
            Outcome::Silent => writeln!(out, "no page from {target} yet")?,
        }
        going_back = false;
        // Read commands until one navigates.
        loop {
            write!(out, "> ")?;
            out.flush()?;
            let Some(line) = lines.next().transpose()? else {
                return Ok(());
            };
            let line = line.trim();
            let links = current.as_ref().map_or(&[][..], |p| p.links.as_slice());
            let next = if line == "q" {
                return Ok(());
            } else if line == "r" {
                current.as_ref().map(|p| p.url.clone())
            } else if line == "b" {
                if history.len() > 1 {
                    history.pop();
                    going_back = true;
                }
                match (going_back, history.last()) {
                    (true, Some(u)) => Some(u.clone()),
                    _ => {
                        writeln!(out, "no earlier page")?;
                        None
                    }
                }
            } else if let Some(u) = line.strip_prefix("g ") {
                Some(u.trim().to_owned())
            } else if let Ok(n) = line.parse::<usize>() {
                let link = n.checked_sub(1).and_then(|i| links.get(i)).cloned();
                if link.is_none() {
                    writeln!(out, "no link {n}")?;
                }
                link
            } else {
                writeln!(out, "commands: a link number, g URL, b, r, q")?;
                None
            };
            if let Some(u) = next {
                target = u;
                host.navigate_tab(tab, &target);
                break;
            }
        }
    }
}
