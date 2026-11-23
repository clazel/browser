//! Hand-written checks of item 7.16's popups (`OpenTab` from a renderer) and
//! of the refusal of `javascript:` URLs, through the exec kernel
//! (`step_real`). These cite no official suite; `theorem_popup_needs_input`
//! and `theorem_no_javascript_url` are what say the kernel does these things
//! for every input.

mod support;

use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::EventRecord;
use support::{Kernel, Out, code_points};

const T0: u64 = 13_000_000_000;

fn open(k: &mut Kernel, url: &str) -> u64 {
    let (id, _) = k.open_tab(url, "");
    assert!(id.is_some(), "{url} spawned no renderer");
    id.unwrap_or(0)
}

fn popup(url: &str) -> Msg {
    Msg::OpenTab {
        url: url.as_bytes().to_vec(),
    }
}

/// The user's input of `kind` (0 a click, 1 a scroll, 2 a key) on `tab`.
fn input(k: &mut Kernel, tab: u64, kind: u64) -> Vec<Out> {
    k.event(&EventRecord::Input {
        tab,
        kind,
        x: 1,
        y: 2,
        negative: false,
        delta: 0,
        key: 0,
    })
}

fn tick(k: &mut Kernel, n: u64) {
    for i in 0..n {
        k.event(&EventRecord::Tick {
            time: T0.saturating_add(i),
        });
    }
}

/// Whether a popup's outputs opened a tab: the spawn of renderer `id`.
fn opened(out: &[Out], id: u64) -> bool {
    out.contains(&Out::Spawn(id))
}

#[test]
fn a_popup_without_an_input_opens_nothing() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    let out = k.send(a, &popup("http://example.test/b"));
    assert_eq!(out, vec![]);
    // Nor does another tab's input give it one.
    let b = open(&mut k, "http://other.test/");
    input(&mut k, b, 0);
    assert_eq!(k.send(a, &popup("http://example.test/b")), vec![]);
}

#[test]
fn a_click_lets_the_renderer_open_one_tab() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    assert_eq!(input(&mut k, a, 0).len(), 1);
    let out = k.send(a, &popup("http://example.test/b"));
    assert!(opened(&out, 1), "{out:?}");
    // The activation is spent: a second popup is refused.
    assert_eq!(k.send(a, &popup("http://example.test/c")), vec![]);
    // A new input gives another.
    input(&mut k, a, 0);
    let out = k.send(a, &popup("http://example.test/c"));
    assert!(opened(&out, 2), "{out:?}");
}

#[test]
fn a_key_activates_and_a_scroll_does_not() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    input(&mut k, a, 1);
    assert_eq!(k.send(a, &popup("http://example.test/b")), vec![]);
    input(&mut k, a, 2);
    let out = k.send(a, &popup("http://example.test/b"));
    assert!(opened(&out, 1), "{out:?}");
}

#[test]
fn the_activation_is_the_senders_not_another_tabs() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    let b = open(&mut k, "http://example.test/b");
    input(&mut k, a, 0);
    assert_eq!(k.send(b, &popup("http://example.test/c")), vec![]);
    let out = k.send(a, &popup("http://example.test/c"));
    assert!(opened(&out, 2), "{out:?}");
}

#[test]
fn the_activation_lasts_a_window_of_ticks() {
    // 999 ticks after the input the window is still open; the 1000th ends it.
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    input(&mut k, a, 0);
    tick(&mut k, 999);
    let out = k.send(a, &popup("http://example.test/b"));
    assert!(opened(&out, 1), "{out:?}");

    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    input(&mut k, a, 0);
    tick(&mut k, 1000);
    assert_eq!(k.send(a, &popup("http://example.test/b")), vec![]);
}

#[test]
fn a_popup_url_is_resolved_against_the_senders_url() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/dir/a");
    input(&mut k, a, 0);
    let out = k.send(a, &popup("b"));
    assert!(opened(&out, 1), "{out:?}");
    // The new tab fetches the resolved URL from its host.
    assert!(
        out.iter()
            .any(|o| matches!(o, Out::Connect(_, host, _, _) if host == b"example.test")),
        "{out:?}"
    );
}

#[test]
fn a_popup_to_a_javascript_url_opens_nothing_and_spends_the_activation() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    input(&mut k, a, 0);
    let out = k.send(a, &popup("javascript:alert(1)"));
    assert!(!out.iter().any(|o| matches!(o, Out::Spawn(_))), "{out:?}");
    // Spent: even a good URL now needs a new input.
    assert_eq!(k.send(a, &popup("http://example.test/b")), vec![]);
}

#[test]
fn an_uncommitted_renderer_that_sends_a_popup_is_killed() {
    let mut k = Kernel::new();
    k.event(&EventRecord::OpenTab {
        url: code_points("http://example.test/"),
        script: None,
    });
    let out = k.send(0, &popup("http://example.test/b"));
    assert_eq!(out, vec![Out::Kill(0), Out::Close(0)]);
}

#[test]
fn the_user_cannot_type_a_javascript_url() {
    let mut k = Kernel::new();
    for url in [
        "javascript:alert(1)",
        "JavaScript:alert(1)",
        " javascript:alert(1)",
        "\tjava\nscript:alert(1)",
    ] {
        let out = k.event(&EventRecord::OpenTab {
            url: code_points(url),
            script: None,
        });
        assert_eq!(out, vec![], "{url:?}");
        let (id, out) = k.open_tab(url, "");
        assert_eq!((id, out), (None, vec![]), "{url:?}");
    }
    // The first real tab is still id 0: the refused ones took no id.
    let (id, _) = k.open_tab("http://example.test/", "");
    assert_eq!(id, Some(0));
}

#[test]
fn a_renderer_cannot_navigate_to_a_javascript_url() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    let out = k.send(
        a,
        &Msg::Navigate {
            url: b"javascript:alert(1)".to_vec(),
        },
    );
    // An error to the sender, and no fetch.
    assert!(
        out.iter().all(|o| !matches!(o, Out::Connect(..))),
        "{out:?}"
    );
    assert!(
        out.iter()
            .any(|o| matches!(o, Out::To(id, Msg::Error { .. }) if *id == a)),
        "{out:?}"
    );
}
