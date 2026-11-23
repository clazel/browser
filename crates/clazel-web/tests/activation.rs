//! DOM §2.9† "dispatch"'s activation behavior: which node is the
//! activation target, the order of legacy-pre-activation behavior, the
//! listeners, and activation (or legacy-canceled-activation) behavior, on
//! trees built by hand. The expectations are written from the standard's
//! steps (`dispatch` steps for "isActivationEvent", "activationTarget" and
//! the two places they are used), not from the implementation.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_web::events::{
    AddOptions, Event, EventInit, EventPhase, Host, Invocation, ListenerId, Listeners, TargetId,
    dispatch,
};

fn u(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// `document > html > body > div(2) > div(3)`, node ids 1 to 4.
fn tree() -> Arena {
    let mut arena = Arena::new(Vec::new());
    let mut parent = 0;
    for name in ["html", "body", "div", "div"] {
        let e = arena.create(ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: u(name),
            attributes: Vec::<ExecAttr>::new(),
            template_contents: None,
            form_owner: None,
        });
        let Some(e) = e else {
            unreachable!("node limit")
        };
        arena.append(parent, e);
        parent = e;
    }
    arena
}

const BODY: usize = 2;
const OUTER: usize = 3;
const INNER: usize = 4;

struct H {
    /// The nodes that have activation behavior.
    activators: Vec<usize>,
    log: Vec<String>,
}

impl Host for H {
    fn invoke(&mut self, call: Invocation<'_>) {
        self.log.push(format!("listener {}", call.listener.0));
    }

    fn has_activation_behavior(&mut self, node: usize) -> bool {
        self.activators.contains(&node)
    }

    fn legacy_pre_activation_behavior(&mut self, node: usize) {
        self.log.push(format!("pre {node}"));
    }

    fn legacy_canceled_activation_behavior(&mut self, node: usize) {
        self.log.push(format!("canceled {node}"));
    }

    fn activation_behavior(&mut self, node: usize, event: &Event, _listeners: &mut Listeners) {
        // "Unset event's dispatch flag, stop propagation flag, and stop
        // immediate propagation flag" come before the activation behavior.
        assert!(!event.is_dispatching());
        assert_eq!(event.event_phase(), EventPhase::None);
        assert_eq!(event.current_target(), None);
        self.log.push(format!("activate {node}"));
    }
}

fn click(bubbles: bool, mouse: bool, type_: &str) -> Event {
    let mut e = Event::new_trusted(
        &u(type_),
        EventInit {
            bubbles,
            cancelable: true,
            composed: true,
        },
        0.0,
    );
    e.set_mouse_event(mouse);
    e
}

/// Dispatches at `target` with listeners 1 (capture on the body), 2 (at the
/// target), and `cancel`, which makes listener 2 cancel; returns the log.
fn run(activators: &[usize], target: usize, mut event: Event, cancel: bool) -> (Vec<String>, bool) {
    let arena = tree();
    let mut listeners = Listeners::new();
    listeners.add_event_listener(
        &arena,
        TargetId::Node(BODY),
        &u("click"),
        ListenerId(1),
        AddOptions {
            capture: true,
            ..AddOptions::default()
        },
    );
    listeners.add_event_listener(
        &arena,
        TargetId::Node(target),
        &u("click"),
        ListenerId(2),
        AddOptions::default(),
    );
    struct Cancel<'a>(&'a mut H, bool);
    impl Host for Cancel<'_> {
        fn invoke(&mut self, call: Invocation<'_>) {
            if self.1 && call.listener == ListenerId(2) {
                call.event.prevent_default();
            }
            self.0.invoke(call);
        }

        fn has_activation_behavior(&mut self, node: usize) -> bool {
            self.0.has_activation_behavior(node)
        }

        fn legacy_pre_activation_behavior(&mut self, node: usize) {
            self.0.legacy_pre_activation_behavior(node);
        }

        fn legacy_canceled_activation_behavior(&mut self, node: usize) {
            self.0.legacy_canceled_activation_behavior(node);
        }

        fn activation_behavior(&mut self, node: usize, e: &Event, l: &mut Listeners) {
            self.0.activation_behavior(node, e, l);
        }
    }
    let mut h = H {
        activators: activators.to_vec(),
        log: Vec::new(),
    };
    let result = {
        let mut host = Cancel(&mut h, cancel);
        dispatch(
            &arena,
            &mut listeners,
            TargetId::Node(target),
            &mut event,
            &mut host,
        )
    };
    (h.log, result.unwrap_or(false))
}

#[test]
fn the_target_with_activation_behavior_runs_it_after_the_listeners() {
    // "If activationTarget is non-null and activationTarget has
    // legacy-pre-activation behavior, then run" it before the capture pass;
    // "If event's canceled flag is unset, then run activationTarget's
    // activation behavior with event" after.
    let (log, ok) = run(&[INNER], INNER, click(true, true, "click"), false);
    assert!(ok);
    assert_eq!(log, ["pre 4", "listener 1", "listener 2", "activate 4"]);
}

#[test]
fn a_canceled_event_runs_the_legacy_canceled_activation_behavior_instead() {
    let (log, ok) = run(&[INNER], INNER, click(true, true, "click"), true);
    assert!(!ok);
    assert_eq!(log, ["pre 4", "listener 1", "listener 2", "canceled 4"]);
}

#[test]
fn the_nearest_ancestor_is_the_target_of_a_bubbling_click() {
    // "If isActivationEvent is true, event's bubbles attribute is true,
    // activationTarget is null, and parent has activation behavior, then set
    // activationTarget to parent": the first one met going up.
    let (log, _) = run(&[OUTER, BODY], INNER, click(true, true, "click"), false);
    assert_eq!(log, ["pre 3", "listener 1", "listener 2", "activate 3"]);
}

#[test]
fn the_target_itself_comes_before_its_ancestors() {
    let (log, _) = run(&[OUTER, INNER], INNER, click(true, true, "click"), false);
    assert_eq!(log.last().map(String::as_str), Some("activate 4"));
}

#[test]
fn a_click_that_does_not_bubble_has_no_ancestors_activation_target() {
    let (log, _) = run(&[OUTER], INNER, click(false, true, "click"), false);
    assert_eq!(log, ["listener 1", "listener 2"]);
}

#[test]
fn only_a_mouse_event_named_click_is_an_activation_event() {
    // "Let isActivationEvent be true, if event is a MouseEvent object and
    // event's type attribute is "click"".
    let (not_mouse, _) = run(&[INNER], INNER, click(true, false, "click"), false);
    assert_eq!(not_mouse, ["listener 1", "listener 2"]);
    let (other, _) = run(&[INNER], INNER, click(true, true, "mousedown"), false);
    assert!(other.iter().all(|l| !l.starts_with("activate")));
}

#[test]
fn a_target_without_the_behavior_and_no_ancestor_with_it_does_nothing() {
    let (log, ok) = run(&[], INNER, click(true, true, "click"), false);
    assert!(ok);
    assert_eq!(log, ["listener 1", "listener 2"]);
}
