//! The unit tests of `strip.rs`, kept apart so that the integration tests that
//! include `strip.rs` by path (`tests/browse_window.rs`) carry no dead test code.

use crate::strip::{BACKGROUND, Contents, FIELD, blend, render};

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
    };
    let px = render(font.as_deref(), 400, 36, 1.0, &what);
    assert_eq!(px.len(), 14_400);
    // The corners are the strip's background, the field is white where no
    // glyph is, and the text made dark pixels.
    assert_eq!(px.first().copied(), Some(BACKGROUND));
    assert!(px.contains(&FIELD));
    let n = dark(&px);
    assert!(n > 50, "only {n} dark pixels");
    // Nothing dark outside the field (x 9 to 391, y 7 to 29).
    for (i, p) in px.iter().enumerate() {
        let (x, y) = (i % 400, i / 400);
        if *p & 0xFF < 0x60 {
            assert!(
                (9..391).contains(&x) && (7..29).contains(&y),
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
    };
    // An empty field while editing still has its caret.
    assert!(dark(&render(font.as_deref(), 200, 36, 1.0, &editing)) > 0);
    let long = "x".repeat(400);
    let shown = Contents {
        text: &long,
        editing: false,
        committed: true,
    };
    let typed = Contents {
        text: &long,
        editing: true,
        committed: true,
    };
    // Both fill the field with ink, and stay inside it.
    for what in [&shown, &typed] {
        let px = render(font.as_deref(), 200, 36, 1.0, what);
        assert!(dark(&px) > 100);
        assert!(
            px.iter()
                .enumerate()
                .all(|(i, p)| p & 0xFF >= 0x60 || (9..191).contains(&(i % 200)))
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
    };
    let one = dark(&render(font.as_deref(), 300, 36, 1.0, &what));
    let two = dark(&render(font.as_deref(), 600, 72, 2.0, &what));
    assert!(two > one * 3, "{one} then {two}");
}
