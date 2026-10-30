//! `clazel demo` as a real process (phase-2.md item 2.16): it starts the
//! kernel and a sandboxed renderer process per tab, and its output must say
//! plainly what each tab saw and that the first two did not see each other's
//! cookies.

mod support;

use std::process::Command;

use support::binary;

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn the_demo_shows_that_neither_tab_sees_the_others_cookies() {
    let out = Command::new(env!("CARGO_BIN_EXE_clazel"))
        .arg("demo")
        .env("CLAZEL_RENDERER", binary("clazel-renderer"))
        .output();
    assert!(out.is_ok(), "cannot run the demo: {out:?}");
    let Ok(out) = out else { return };
    let (status, stdout, stderr) = (
        out.status,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    );
    assert!(status.success(), "{status}\n{stdout}\n{stderr}");
    // The host's log of frames goes to standard error (item 4.15), the
    // demo's own statements to standard output: read both.
    let stdout = format!("{stdout}\n{stderr}");
    for want in [
        // Each tab's own cookie and storage item, set and read back.
        "renderer 0 -> document.cookie = \"session=alpha; Domain=a.test; Path=/\"",
        "renderer 0 <- result \"session=alpha\"",
        "renderer 1 -> document.cookie = \"session=beta; Path=/\"",
        "renderer 1 <- result \"session=beta\"",
        "renderer 0 <- result \"alpha\"",
        "renderer 1 <- result \"beta\"",
        // The third tab, on a subdomain of the first's cookie root.
        "renderer 2 <- commit \"https://x.a.test/\"",
        "renderer 2 <- result \"session=alpha\"",
        "renderer 2 <- result null",
        // The plain statement.
        "NEITHER of the first two tabs saw the other's cookies or storage",
        "x.a.test read a.test's Domain=a.test cookie (session=alpha)",
    ] {
        assert!(stdout.contains(want), "missing {want:?} in:\n{stdout}");
    }
    // And no tab was ever given the other's value.
    for (id, other) in [(0, "beta"), (1, "alpha")] {
        let prefix = format!("renderer {id} <- ");
        assert!(
            !stdout
                .lines()
                .any(|l| l.starts_with(&prefix) && l.contains(other)),
            "renderer {id} was sent {other}:\n{stdout}"
        );
    }
}
