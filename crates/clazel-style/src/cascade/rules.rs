//! Style rules made ready for the cascade: each rule's selector list parsed once by
//! `clazel-selectors` and its declarations read once into longhands, so that matching an
//! element is a selector match and nothing else.
//!
//! CSS Cascade 4 §5 "Filtering": "In order to find the declared values, implementations must
//! first identify all declarations that apply to each element. A declaration applies to an
//! element if: It belongs to a style sheet that currently applies to this document. It is
//! not qualified by a conditional rule with a false condition. It belongs to a style rule
//! whose selector matches the element. ... It is syntactically valid: the declaration's
//! property is a known property name, and the declaration's value matches the syntax for
//! that property." The first two are `sources::Sources::rules_for`'s; the last two are
//! here.
//!
//! A style rule's specificity, for a selector list, is Selectors 4 §17†'s: "If the selector
//! is a selector list, this number is calculated for each selector in the list. For a given
//! matching process against the list, the specificity in effect is that of the most
//! specific selector in the list that matches." `clazel-selectors` matches a whole list
//! ([`clazel_selectors::exec_match::matches`]); to match one complex selector of it, the
//! list of that one selector alone is appended to the parsed arrays as their last list
//! (which is the list `matches` reads), matched, and removed. Every list the parser builds
//! must pass its proven check ([`clazel_selectors::exec_check::check`]); each such
//! one-selector list is checked once, when the rule is prepared, and a rule where one fails
//! falls back to the whole list and its greatest specificity.

use clazel_css::parser::contract::MAX_PARSER_INPUT;
use clazel_dom::exec::Arena;
use clazel_selectors::exec_check::check;
use clazel_selectors::exec_match::matches;
use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_specificity::{ExecSpecificity, complex_specificity_of};
use clazel_selectors::exec_types::{ExecRange, ExecSelectors};

use super::logical;
use super::sort::Specificity;
use crate::sources::Declaration;
use crate::values::{self, Declared};

/// A declaration of a rule, read into the longhands it sets.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Longhands {
    /// The longhands and their values, in the declaration's order.
    pub set: Vec<Declared>,
    /// Its `!important` flag.
    pub important: bool,
}

/// The longhands each valid declaration of `declarations` sets, in order; invalid and
/// unknown declarations are dropped (§5: "It is syntactically valid"). `quirks` turns on
/// the Quirks Mode Standard's value quirks, which apply to author style sheets of a document
/// in quirks mode (`values::parse`'s flag).
pub fn read_declarations(declarations: &[Declaration], quirks: bool) -> Vec<Longhands> {
    let mut out = Vec::new();
    for d in declarations {
        let set = match values::property(&d.name) {
            Some(p) => values::parse_items(p, d.value.src(), quirks),
            None => logical::parse(&d.name, d.value.src()),
        };
        if let Some(set) = set {
            out.push(Longhands {
                set,
                important: d.important,
            });
        }
    }
    out
}

/// A rule's selectors, parsed.
#[derive(Debug)]
pub struct Selectors {
    /// The parse, whose last list is the rule's selector list.
    parsed: ExecSelectors,
    /// That list's range of complex selectors and its index.
    list: ExecRange,
    list_index: usize,
    /// The specificity of each complex selector of the list, in order.
    specificities: Vec<Specificity>,
    /// True if every complex selector of the list can be matched alone (see the module's
    /// documentation).
    one_by_one: bool,
}

fn specificity(s: ExecSpecificity) -> Specificity {
    Specificity {
        a: s.a,
        b: s.b,
        c: s.c,
    }
}

impl Selectors {
    /// "Parse a selector" (Selectors 4 §21.1†, `clazel-selectors`) on a rule's prelude;
    /// `None` if it is invalid, which drops the rule (CSS Syntax 3 §9†: "If the prelude
    /// fails to parse as a selector list, the style rule is invalid").
    pub fn parse(text: &[u32]) -> Option<Selectors> {
        if text.len() > MAX_PARSER_INPUT {
            return None;
        }
        let mut parsed = parse_selector(text)?;
        let list_index = parsed.lists.len().checked_sub(1)?;
        let list = *parsed.lists.get(list_index)?;
        if list.lo > list.hi || list.hi > parsed.complexes.len() {
            return None;
        }
        let mut specificities = Vec::new();
        let mut one_by_one = true;
        for ci in list.lo..list.hi {
            specificities.push(specificity(complex_specificity_of(&parsed, list_index, ci)));
            parsed.lists.push(ExecRange {
                lo: ci,
                hi: ci.saturating_add(1),
            });
            one_by_one &= check(&parsed);
            parsed.lists.pop();
        }
        Some(Selectors {
            parsed,
            list,
            list_index,
            specificities,
            one_by_one,
        })
    }

    /// The specificity in effect when the list is matched against element `x`, or `None`
    /// if it does not match. `x` must be a node of `arena`, which must be one the tree
    /// builder made (`clazel-selectors`' precondition: a well-formed document).
    pub fn match_element(&mut self, arena: &Arena, x: usize) -> Option<Specificity> {
        if x >= arena.len() || !matches(arena, &self.parsed, x) {
            return None;
        }
        let greatest = self.specificities.iter().copied().max();
        if self.specificities.len() <= 1 || !self.one_by_one {
            return greatest;
        }
        let mut best: Option<Specificity> = None;
        for (k, ci) in (self.list.lo..self.list.hi).enumerate() {
            let s = self.specificities.get(k).copied().unwrap_or_default();
            if best.is_some_and(|b| b >= s) {
                continue;
            }
            self.parsed.lists.push(ExecRange {
                lo: ci,
                hi: ci.saturating_add(1),
            });
            let hit = matches(arena, &self.parsed, x);
            self.parsed.lists.pop();
            if hit {
                best = Some(s);
            }
        }
        // The list matched, so one of its selectors did.
        best.or(greatest)
    }

    /// The index of the rule's list in the parse (for tests).
    pub fn list_index(&self) -> usize {
        self.list_index
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clazel_dom::exec::{ExecAttr, ExecKind};

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn element(arena: &mut Arena, parent: usize, name: &str, attrs: &[(&str, &str)]) -> usize {
        let id = arena
            .create(ExecKind::Element {
                namespace: Some(clazel_dom::spec::Namespace::Html),
                prefix: None,
                local_name: u(name),
                attributes: attrs
                    .iter()
                    .map(|(k, v)| ExecAttr {
                        namespace: None,
                        prefix: None,
                        local_name: u(k),
                        value: u(v),
                    })
                    .collect(),
                template_contents: None,
                form_owner: None,
            })
            .unwrap_or(0);
        arena.append(parent, id);
        id
    }

    #[test]
    fn most_specific_matching_selector() {
        let mut arena = Arena::new(u("about:blank"));
        let html = element(&mut arena, 0, "html", &[]);
        let p = element(&mut arena, html, "p", &[("id", "x"), ("class", "c")]);
        let q = element(&mut arena, html, "q", &[("class", "c")]);
        let mut s = Selectors::parse(&u("p, .c, #x")).unwrap_or_else(|| unreachable!());
        assert_eq!(s.list_index(), 0);
        let sp = |a, b, c| Some(Specificity { a, b, c });
        assert_eq!(s.match_element(&arena, p), sp(1, 0, 0));
        assert_eq!(s.match_element(&arena, q), sp(0, 1, 0));
        assert_eq!(s.match_element(&arena, html), None);
        let mut t = Selectors::parse(&u(":is(p, #x) q, q")).unwrap_or_else(|| unreachable!());
        assert_eq!(t.match_element(&arena, q), sp(0, 0, 1));
        assert!(Selectors::parse(&u("p:unknown")).is_none());
    }

    #[test]
    fn declarations_to_longhands() {
        let sheet = crate::sources::StyleSheet::parse(&u(
            "p { margin: 1px 2px; color: red !important; bogus: 1; width: calc(1px); \
             margin-block-start: 3px; height: 4 }",
        ));
        let rule = sheet.rules.first().map(|r| r.declarations.clone());
        let out = read_declarations(&rule.clone().unwrap_or_default(), false);
        let counts: Vec<(usize, bool)> = out.iter().map(|l| (l.set.len(), l.important)).collect();
        assert_eq!(counts, vec![(4, false), (1, true), (1, false)]);
        // The unitless length quirk, in quirks mode only.
        let quirky = read_declarations(&rule.unwrap_or_default(), true);
        assert_eq!(quirky.len(), 4);
    }
}
