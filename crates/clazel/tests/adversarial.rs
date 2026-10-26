//! Hostile renderers against the real kernel host (phase-2.md item 2.16).
//!
//! The kernel kills a renderer on its first frame it cannot decode, so a
//! renderer that "sends random frames for a fixed time" is many short-lived
//! ones: here 96 sandboxed `clazel-adversary` processes, each sending one
//! frame generated from its own seed (truncated, oversized, non-shortest
//! CBOR, CBOR outside the profile, invalid UTF-8, random bytes, a mutation of
//! a valid message, a kernel-only message), among 16 well-behaved sandboxed
//! `clazel-renderer` processes running a cookie and `localStorage` script,
//! all at once, against one kernel.
//!
//! Checked: the host and kernel never panic (this test would fail); every
//! hostile renderer ends the way its kind says (killed by the kernel, refused
//! for its length, or closed inside a frame) and the kernel forgets it; the
//! kernel sends a hostile renderer nothing but its `Commit`; and the log of
//! each well-behaved renderer is exactly what it is when the same 16 run
//! alone, so nothing a hostile renderer did reached another renderer.
//!
//! The seed is printed. To reproduce a failure, run with `CLAZEL_SEED=<seed>`.
//! Each hostile renderer's own seed, kind and first bytes are in the host's
//! `exited` line for it (its standard error).

mod support;

use std::collections::BTreeMap;
use std::process::Command;
use std::time::Duration;

use clazel::Host;
use clazel_renderer::hostile::{Kind, generate};
use support::binary;

const LONG: Duration = Duration::from_secs(120);
const DEFAULT_SEED: u64 = 0x2026_1023;
/// Tabs opened, and which are well behaved: those whose id is a multiple of 7.
const TABS: u64 = 112;
const GOOD_EVERY: u64 = 7;

fn base_seed() -> u64 {
    std::env::var("CLAZEL_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_SEED)
}

/// The script of well-behaved tab `k`: a cookie and a storage item of its own.
fn good_script(k: u64) -> String {
    format!(
        "cookie-set mark=g{k}; Path=/\ncookie-get\nstorage-set mark g{k}\nstorage-get mark\nstorage-length"
    )
}

fn good_url(k: u64) -> String {
    format!("https://good{k}.test/")
}

/// The lines the host logged for renderer `id`, with the id taken out.
fn lines_of(host: &Host, id: u64) -> Vec<String> {
    let prefix = format!("renderer {id} ");
    host.log
        .iter()
        .filter_map(|l| l.strip_prefix(&prefix).map(str::to_owned))
        .collect()
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn hostile_renderers_are_killed_and_well_behaved_ones_are_unaffected() {
    let seed = base_seed();
    let (renderer, adversary) = (binary("clazel-renderer"), binary("clazel-adversary"));
    let seed_of = move |id: u64| seed.wrapping_add(id);
    println!("hostile frames: base seed {seed} (CLAZEL_SEED={seed} reproduces this run)");

    // The baseline: the well-behaved tabs alone.
    let r = renderer.clone();
    let mut alone = Host::new(move |_| Command::new(&r));
    let goods = TABS.div_ceil(GOOD_EVERY);
    for k in 0..goods {
        alone.open_tab(&good_url(k), &good_script(k));
    }
    assert!(alone.run(LONG), "{:#?}", alone.log);
    let baseline: Vec<Vec<String>> = (0..goods).map(|k| lines_of(&alone, k)).collect();
    assert!(
        baseline
            .iter()
            .all(|l| l.iter().any(|x| x.contains("result \"g"))),
        "the well-behaved renderers did not run (a sandbox layer refused?): {:#?}",
        alone.log
    );

    // The same tabs among hostile ones.
    let mut host = Host::new(move |id| {
        if id % GOOD_EVERY == 0 {
            Command::new(&renderer)
        } else {
            let mut c = Command::new(&adversary);
            c.args(["hostile", &seed_of(id).to_string()]);
            c
        }
    });
    for id in 0..TABS {
        if id % GOOD_EVERY == 0 {
            let k = id / GOOD_EVERY;
            host.open_tab(&good_url(k), &good_script(k));
        } else {
            host.open_tab(&format!("https://evil{id}.test/"), "");
        }
    }
    assert!(host.run(LONG), "renderers still alive: {:#?}", host.log);

    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for id in 0..TABS {
        let lines = lines_of(&host, id);
        if id % GOOD_EVERY == 0 {
            let k = usize::try_from(id / GOOD_EVERY).unwrap_or(usize::MAX);
            assert_eq!(
                Some(&lines),
                baseline.get(k),
                "well-behaved tab {k} (renderer {id}) differs from running alone"
            );
            continue;
        }
        let kind = generate(seed_of(id)).kind;
        let n = kinds.entry(format!("{kind:?}")).or_default();
        *n = n.saturating_add(1);
        // Only the Commit was ever sent to it.
        let sent: Vec<&String> = lines.iter().filter(|l| l.starts_with("<- ")).collect();
        assert!(
            matches!(sent.as_slice(), [only] if only.starts_with("<- commit ")),
            "renderer {id} ({kind:?}, seed {}) was sent more than its Commit: {lines:#?}",
            seed_of(id)
        );
        let ends: Vec<&String> = lines.iter().filter(|l| l.starts_with("exited: ")).collect();
        assert!(
            matches!(ends.as_slice(), [end] if end.contains(kind.host_says())
                && end.contains(&format!("hostile: seed={} kind={kind:?}", seed_of(id)))),
            "renderer {id} ({kind:?}, seed {}) did not end with {:?}: {lines:#?}",
            seed_of(id),
            kind.host_says()
        );
    }
    println!("hostile frames by kind: {kinds:?}");
    assert_eq!(
        kinds.len(),
        Kind::ALL.len(),
        "not every kind was sent: {kinds:?}"
    );

    // The kernel forgot every renderer: a navigation of any of them spawns
    // nothing (it would, if the kernel still had the tab).
    assert_eq!(host.live(), 0);
    for id in 0..TABS {
        host.navigate_tab(id, "http://after.test/");
        assert_eq!(host.live(), 0, "the kernel still has renderer {id}");
    }
}
