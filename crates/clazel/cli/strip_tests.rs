//! The unit tests of `strip.rs`, kept apart so that the integration tests that
//! include `strip.rs` by path (`tests/browse_window.rs`) carry no dead test code.

use crate::strip::{
    BACK_DISABLED, BACK_ENABLED, BACKGROUND, Contents, FIELD, back_button, blend, on_back_button,
    render,
};

/// DejaVu Serif, vendored for `clazel-font`'s tests.
fn font() -> Option<Vec<u8>> {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
    );
    std::fs::read(path).ok()
}

fn dark(pixels: &[u32]) -> usize {
    pixels.iter().filter(|&&p| p & 0xFF < 0x60).count()
}

#[test]
fn blending_is_coverage_over_the_background() {
    assert_eq!(blend(0, 0x00FF_FFFF, 255), 0);
    assert_eq!(blend(0, 0x00FF_FFFF, 0), 0x00FF_FFFF);
    assert_eq!(blend(0, 0x00FF_FFFF, 128), 0x007F_7F7F);
    assert_eq!(blend(0x00FF_0000, 0x0000_00FF, 255), 0x00FF_0000);
}

#[test]
fn a_url_draws_dark_pixels_only_inside_the_field() {
    let font = font();
    assert!(font.is_some(), "the vendored DejaVu Serif is missing");
    let what = Contents {
        text: "http://example.com/",
        editing: false,
        committed: true,
        can_go_back: false,
    };
    let px = render(font.as_deref(), 400, 36, 1.0, &what);
    assert_eq!(px.len(), 14_400);
    // The corners are the strip's background, the field is white where no
    // glyph is, and the text made dark pixels.
    assert_eq!(px.first().copied(), Some(BACKGROUND));
    assert!(px.contains(&FIELD));
    let n = dark(&px);
    assert!(n > 50, "only {n} dark pixels");
    // Nothing dark outside the field (x 39 to 391, y 7 to 29).
    for (i, p) in px.iter().enumerate() {
        let (x, y) = (i % 400, i / 400);
        if *p & 0xFF < 0x60 {
            assert!(
                (39..391).contains(&x) && (7..29).contains(&y),
                "dark at {x},{y}"
            );
        }
    }
    // More text, more ink; no font, no ink.
    let longer = Contents {
        text: "http://example.com/a/longer/path",
        ..what.clone()
    };
    assert!(dark(&render(font.as_deref(), 400, 36, 1.0, &longer)) > n);
    assert_eq!(dark(&render(None, 400, 36, 1.0, &what)), 0);
}

#[test]
fn editing_shows_a_caret_and_keeps_long_text_in_view() {
    let font = font();
    let editing = Contents {
        text: "",
        editing: true,
        committed: true,
        can_go_back: false,
    };
    // An empty field while editing still has its caret.
    assert!(dark(&render(font.as_deref(), 200, 36, 1.0, &editing)) > 0);
    let long = "x".repeat(400);
    let shown = Contents {
        text: &long,
        editing: false,
        committed: true,
        can_go_back: false,
    };
    let typed = Contents {
        text: &long,
        editing: true,
        committed: true,
        can_go_back: false,
    };
    // Both fill the field with ink, and stay inside it.
    for what in [&shown, &typed] {
        let px = render(font.as_deref(), 200, 36, 1.0, what);
        assert!(dark(&px) > 100);
        assert!(
            px.iter()
                .enumerate()
                .all(|(i, p)| p & 0xFF >= 0x60 || (39..191).contains(&(i % 200)))
        );
    }
}

#[test]
fn a_retina_strip_is_twice_the_size() {
    let font = font();
    let what = Contents {
        text: "clazel",
        editing: false,
        committed: true,
        can_go_back: false,
    };
    let one = dark(&render(font.as_deref(), 300, 36, 1.0, &what));
    let two = dark(&render(font.as_deref(), 600, 72, 2.0, &what));
    assert!(two > one * 3, "{one} then {two}");
}

#[test]
fn the_back_button_is_dark_only_when_there_is_somewhere_to_go() {
    let off = Contents {
        text: "",
        editing: false,
        committed: true,
        can_go_back: false,
    };
    let on = Contents {
        can_go_back: true,
        ..off.clone()
    };
    // At scale 1 in a 36 pixel strip: a 24 pixel square, 8 from the left.
    assert_eq!(back_button(36, 1.0), (8, 6, 32, 30));
    assert_eq!(back_button(72, 2.0), (16, 12, 64, 60));
    for (what, colour, other) in [
        (&off, BACK_DISABLED, BACK_ENABLED),
        (&on, BACK_ENABLED, BACK_DISABLED),
    ] {
        // No font: the chevron needs none.
        let px = render(None, 400, 36, 1.0, what);
        let at: Vec<(i64, i64)> = px
            .iter()
            .enumerate()
            .filter(|(_, p)| **p == colour)
            .map(|(i, _)| ((i % 400) as i64, (i / 400) as i64))
            .collect();
        assert!(at.len() > 10, "{} chevron pixels", at.len());
        // Every chevron pixel is on the button, and none is in the other colour.
        assert!(at.iter().all(|&(x, y)| on_back_button(x, y, 36, 1.0)));
        assert!(!px.contains(&other));
        // Its point is left of its ends: the leftmost pixel is on the middle row.
        let left = at.iter().map(|&(x, _)| x).min();
        assert!(at.iter().any(|&(x, y)| Some(x) == left && y == 18));
    }
}

#[test]
fn a_click_is_on_the_back_button_only_inside_its_square() {
    assert!(on_back_button(8, 6, 36, 1.0));
    assert!(on_back_button(31, 29, 36, 1.0));
    for (x, y) in [(7, 18), (32, 18), (20, 5), (20, 30), (-1, -1), (200, 18)] {
        assert!(!on_back_button(x, y, 36, 1.0), "{x},{y}");
    }
    // A strip too short for a button has none to click.
    assert!(!on_back_button(8, 6, 4, 1.0));
}
