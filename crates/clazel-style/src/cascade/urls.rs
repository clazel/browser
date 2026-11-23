//! `url()` in `background-image`, made absolute (item 6.11, decision 6.0(c)'s U2).
//!
//! CSS Values 4 §4.5 "Resource Locators: the `<url>` type": "relative URLs are resolved
//! to be absolute ... a relative URL ... is relative to the URL of the style sheet in which
//! it appears" (for a `style` attribute or a `style` element, the style sheet's base URL is
//! the document's, CSSOM §6.2 "the style sheet's location": null for a `style` element,
//! whose URLs are then relative to the document's base URL). The basic URL parser is URL
//! §4.4, through `clazel-url`.
//!
//! Modelling choices:
//!
//! - **At the cascade's input**, not at computed-value time: a computed style does not know
//!   which sheet its declaration came from, so a declaration's `url()` is made absolute
//!   when its sheet's rules are read ([`resolve`], called by `prepare`).
//! - **A failure leaves the URL as written**, which no fetch can then resolve: the layer
//!   keeps its place (CSS Backgrounds 3 §2.1†: "a value of none still creates a layer") and
//!   its image never loads. So does a missing base (the caller has not given the sheet's
//!   URL): an absolute URL still parses, a relative one stays relative.
//! - **Only `background-image`** is rewritten (this item's); `cursor`'s `url()` is not read.

use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;

use super::rules::Longhands;
use crate::values::Specified;
use crate::values::component::Component;
use crate::values::longhand::Longhand;

/// The base URL `url` (a code point string) parses to, if it parses.
pub fn base(url: Option<&[u32]>) -> Option<ParsedUrl> {
    let url = url?;
    if url.iter().any(|&c| char::from_u32(c).is_none()) {
        return None;
    }
    basic_url_parser(url, None)
}

/// URL §4.4: `url` parsed against `base` and serialized (without the fragment excluded:
/// "exclude fragment" false), or `None` on failure.
fn absolute(url: &[u32], base: Option<&ParsedUrl>) -> Option<Vec<u32>> {
    if url.iter().any(|&c| char::from_u32(c).is_none()) {
        return None;
    }
    Some(basic_url_parser(url, base)?.serialize(false))
}

/// Every `background-image` `url()` in `declarations` made absolute against `base`.
pub fn resolve(declarations: &mut [Longhands], base: Option<&ParsedUrl>) {
    for l in declarations {
        for d in &mut l.set {
            if d.property != Longhand::BackgroundImage {
                continue;
            }
            if let Specified::Value(v) = &mut d.value {
                for c in v {
                    if let Component::Url(u) = c
                        && let Some(a) = absolute(u, base)
                    {
                        *u = a;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::values::{Declared, Specified};

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn one(url: &str) -> Vec<Longhands> {
        vec![Longhands {
            set: vec![Declared {
                property: Longhand::BackgroundImage,
                value: Specified::Value(vec![Component::Url(u(url))]),
            }],
            important: false,
        }]
    }

    fn url_of(l: &[Longhands]) -> String {
        match l.first().and_then(|x| x.set.first()).map(|d| &d.value) {
            Some(Specified::Value(v)) => match v.first() {
                Some(Component::Url(u)) => u.iter().filter_map(|&c| char::from_u32(c)).collect(),
                _ => String::new(),
            },
            _ => String::new(),
        }
    }

    #[test]
    fn relative_to_the_sheet() {
        let b = base(Some(&u("https://example.com/css/site.css")));
        let mut l = one("../img/bg.png");
        resolve(&mut l, b.as_ref());
        assert_eq!(url_of(&l), "https://example.com/img/bg.png");
    }

    #[test]
    fn absolute_stays_and_missing_base_keeps_relative() {
        let mut l = one("https://other.test/a.gif");
        resolve(&mut l, None);
        assert_eq!(url_of(&l), "https://other.test/a.gif");
        let mut l = one("a.gif");
        resolve(&mut l, None);
        assert_eq!(url_of(&l), "a.gif");
    }
}
