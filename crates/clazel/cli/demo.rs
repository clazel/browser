//! The exit demo (phase-2.md item 2.16): two tabs on different cookie roots
//! each set a cookie and a `localStorage` item and read both back, then a
//! third tab on a subdomain of the first reads the first's `Domain` cookie.
//! Every request and reply is printed by the host as it happens; this file
//! reads the results from what the host logged and says what they show.

use std::process::ExitCode;
use std::time::Duration;

use clazel::Host;

const LIMIT: Duration = Duration::from_secs(60);

/// a.test: a `localStorage` item and a cookie with `Domain=a.test`.
const A: &str = "document.cookie = 'session=alpha; Domain=a.test; Path=/'; document.cookie; \
    localStorage.setItem('owner', 'alpha'); localStorage.getItem('owner');";
/// b.test: the same names, other values.
const B: &str = "document.cookie = 'session=beta; Path=/'; document.cookie; \
    localStorage.setItem('owner', 'beta'); localStorage.getItem('owner');";
/// x.a.test: reads without writing.
const X: &str = "document.cookie; localStorage.getItem('owner');";

/// What renderer `id` was answered, in order: `"text"` or `null`.
fn answers(host: &Host, id: u64) -> Vec<String> {
    let prefix = format!("renderer {id} <- result ");
    host.log
        .iter()
        .filter_map(|l| l.strip_prefix(&prefix).map(str::to_owned))
        .collect()
}

/// Open a tab, returning its renderer id.
fn open(host: &mut Host, url: &str, script: &str) -> u64 {
    let id = host.state.next_id;
    host.open_tab(url, script);
    id
}

pub fn run(mut host: Host) -> ExitCode {
    println!("== Clazel exit demo: one kernel, one sandboxed renderer process per tab ==");
    println!("-- tabs https://a.test/ and https://b.test/ open together");
    let a = open(&mut host, "https://a.test/", A);
    let b = open(&mut host, "https://b.test/", B);
    let ended = host.run(LIMIT);
    println!("-- a third tab opens https://x.a.test/, after the first two are done");
    let x = open(&mut host, "https://x.a.test/", X);
    let ended = host.run(LIMIT) && ended;

    let q = |s: &str| format!("{s:?}");
    let (got_a, got_b, got_x) = (answers(&host, a), answers(&host, b), answers(&host, x));
    println!("-- results (document.cookie, then localStorage.getItem(\"owner\"))");
    println!("a.test   {}", got_a.join("   "));
    println!("b.test   {}", got_b.join("   "));
    println!("x.a.test {}", got_x.join("   "));

    let ok_a = got_a == [q("session=alpha"), q("alpha")];
    let ok_b = got_b == [q("session=beta"), q("beta")];
    let ok_x = got_x == [q("session=alpha"), "null".to_owned()];
    let no_leak =
        !got_a.iter().any(|r| r.contains("beta")) && !got_b.iter().any(|r| r.contains("alpha"));
    if ended && ok_a && ok_b && ok_x && no_leak {
        println!("NEITHER of the first two tabs saw the other's cookies or storage:");
        println!(
            "  a.test saw only session=alpha and owner=alpha; b.test saw only session=beta and owner=beta."
        );
        println!(
            "x.a.test read a.test's Domain=a.test cookie (session=alpha) but not its localStorage:"
        );
        println!(
            "  the cookie boundary is the cookie root (registrable domain), the storage boundary the origin."
        );
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "DEMO FAILED: a.test {ok_a}, b.test {ok_b}, x.a.test {ok_x}, no leak {no_leak}, renderers ended {ended}"
        );
        ExitCode::FAILURE
    }
}
