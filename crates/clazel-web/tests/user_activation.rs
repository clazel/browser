//! HTML §6.4† user activation: the state of a window and what triggers it,
//! written from the standard's definitions ("has transient activation",
//! "has sticky activation", "consume user activation").

use clazel_web::user_activation::{
    TRANSIENT_ACTIVATION_DURATION_MS, UserActivation, is_activation_triggering,
};

#[test]
fn a_new_window_has_no_activation() {
    let w = UserActivation::new();
    assert!(!w.has_transient(0.0));
    assert!(!w.has_transient(1e9));
    assert!(!w.has_sticky());
    assert!(!w.has_history_action(10.0));
    assert!(!w.is_active(5.0));
    assert!(!w.has_been_active());
}

#[test]
fn transient_activation_lasts_the_duration_and_sticky_stays() {
    let mut w = UserActivation::new();
    w.notify(100.0);
    assert!(w.has_transient(100.0));
    assert!(w.has_transient(100.0 + TRANSIENT_ACTIVATION_DURATION_MS - 0.001));
    // "greater than or equal to last activation timestamp, and less than
    // last activation timestamp plus the transient activation duration"
    assert!(!w.has_transient(100.0 + TRANSIENT_ACTIVATION_DURATION_MS));
    // The clock never runs backwards, but the definition says "greater than
    // or equal": a time before the activation is not transient.
    assert!(!w.has_transient(99.0));
    assert!(w.has_sticky());
    assert!(w.has_been_active());
    assert!(w.is_active(101.0));
}

#[test]
fn consuming_takes_the_transient_activation_and_not_the_sticky() {
    let mut w = UserActivation::new();
    assert!(!w.consume(0.0), "nothing to consume");
    w.notify(10.0);
    assert!(w.consume(11.0));
    assert!(!w.has_transient(11.0));
    assert!(!w.consume(11.0));
    assert!(w.has_sticky());
    // A new activation after that is transient again.
    w.notify(20.0);
    assert!(w.has_transient(21.0));
}

#[test]
fn history_action_activation_is_consumed_apart() {
    let mut w = UserActivation::new();
    w.notify(10.0);
    assert!(w.consume(11.0));
    assert!(w.has_history_action(12.0));
    assert!(w.consume_history_action(12.0));
    assert!(!w.has_history_action(12.0));
    assert!(!w.consume_history_action(12.0));
}

#[test]
fn activation_triggering_input_events() {
    // "keydown, provided the key is neither the Esc key nor a shortcut key
    // reserved by the user agent; mousedown".
    assert!(is_activation_triggering("mousedown", None));
    assert!(is_activation_triggering("keydown", Some("a")));
    assert!(is_activation_triggering("keydown", Some("Enter")));
    assert!(!is_activation_triggering("keydown", Some("Escape")));
    assert!(!is_activation_triggering("keyup", Some("a")));
    assert!(!is_activation_triggering("mouseup", None));
    assert!(!is_activation_triggering("click", None));
    assert!(!is_activation_triggering("wheel", None));
}
