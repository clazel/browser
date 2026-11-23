//! Hand-written checks of item 7.16's URL updates (`UpdateUrl`, which is
//! `history.pushState` and `history.replaceState`), through the exec kernel
//! (`step_real`). These cite no official suite; `theorem_url_update_same_origin`
//! and `theorem_address_bar_integrity` are what say the kernel does these
//! things for every input.

mod support;

use clazel_ipc::message::codec::Msg;
use support::{Kernel, Out, code_points};

fn open(k: &mut Kernel, url: &str) -> u64 {
    let (id, _) = k.open_tab(url, "");
    assert!(id.is_some(), "{url} spawned no renderer");
    id.unwrap_or(0)
}

fn update(url: &str, replace: bool) -> Msg {
    Msg::UpdateUrl {
        replace,
        url: url.as_bytes().to_vec(),
    }
}

/// The URL the kernel shows for `id`'s tab: the URL of the `Show` its
/// `Display` gives.
fn shown(k: &mut Kernel, id: u64) -> Option<Vec<u32>> {
    let out = k.send(
        id,
        &Msg::Display {
            title: Vec::new(),
            text: Vec::new(),
            links: Vec::new(),
        },
    );
    match out.as_slice() {
        [Out::Show(_, url, _, _, _)] => Some(url.clone()),
        _ => None,
    }
}

#[test]
fn a_same_origin_push_state_changes_the_address_line() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/a");
    let out = k.send(id, &update("http://example.test/b?x#y", false));
    assert_eq!(out, vec![]);
    assert_eq!(
        shown(&mut k, id),
        Some(code_points("http://example.test/b?x#y"))
    );
}

#[test]
fn replace_state_does_what_push_state_does_to_the_address_line() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/a");
    assert_eq!(k.send(id, &update("http://example.test/c", true)), vec![]);
    assert_eq!(
        shown(&mut k, id),
        Some(code_points("http://example.test/c"))
    );
    // A second update replaces the first.
    assert_eq!(k.send(id, &update("http://example.test/d", false)), vec![]);
    assert_eq!(
        shown(&mut k, id),
        Some(code_points("http://example.test/d"))
    );
}

#[test]
fn a_relative_url_resolves_against_the_committed_url() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/dir/a");
    assert_eq!(k.send(id, &update("b#f", false)), vec![]);
    assert_eq!(
        shown(&mut k, id),
        Some(code_points("http://example.test/dir/b#f"))
    );
}

#[test]
fn a_cross_origin_url_changes_nothing() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/a");
    for other in [
        "https://example.test/a",
        "http://example.test:8080/a",
        "http://bank.test/",
        "data:text/html,x",
    ] {
        assert_eq!(k.send(id, &update(other, false)), vec![], "{other}");
        assert_eq!(
            shown(&mut k, id),
            Some(code_points("http://example.test/a")),
            "{other}"
        );
    }
}

#[test]
fn an_empty_or_unparsable_url_changes_nothing() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/a");
    for url in ["", "http://[::1"] {
        assert_eq!(k.send(id, &update(url, false)), vec![], "{url:?}");
        assert_eq!(
            shown(&mut k, id),
            Some(code_points("http://example.test/a")),
            "{url:?}"
        );
    }
}

#[test]
fn an_opaque_origin_document_cannot_update_the_address_line() {
    let mut k = Kernel::new();
    let id = open(&mut k, "data:text/html,a");
    assert_eq!(k.send(id, &update("data:text/html,a#f", false)), vec![]);
    assert_eq!(shown(&mut k, id), Some(code_points("data:text/html,a")));
}

#[test]
fn an_uncommitted_renderer_that_updates_its_url_is_killed() {
    let mut k = Kernel::new();
    k.event(&clazel_kernel::exec::records::EventRecord::OpenTab {
        url: code_points("http://example.test/"),
        script: None,
    });
    let out = k.send(0, &update("http://example.test/b", false));
    assert_eq!(out, vec![Out::Kill(0), Out::Close(0)]);
}

#[test]
fn an_update_from_another_tab_does_not_change_this_tab() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    let b = open(&mut k, "http://example.test/b");
    assert_eq!(k.send(b, &update("http://example.test/c", false)), vec![]);
    assert_eq!(shown(&mut k, a), Some(code_points("http://example.test/a")));
    assert_eq!(shown(&mut k, b), Some(code_points("http://example.test/c")));
}
