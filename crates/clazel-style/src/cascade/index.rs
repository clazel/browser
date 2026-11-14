//! The rule index: which style rules may match an element, found without trying every rule.
//!
//! Matching every rule against every element costs rules × elements selector matches
//! (5.5's work bound: rules × elements × depth × compounds), which for item 5.26's CSS
//! bomb, 10,000 rules `.cN span` over 100,000 `div`s each holding a `span`, is 10^9
//! matches. The index brings that down to the rules that can match each element: each rule
//! is filed under, for each complex selector of its list, two keys, and an element looks
//! only in the buckets its own keys and its ancestors' keys select. The rules found are
//! then matched exactly as before, in the same order, so the cascade's result is unchanged.
//!
//! # Keys
//!
//! A [`Key`] is an ID, a class or a type (local name), ASCII-lowercased. A complex
//! selector's keys ([`super::rules::Selectors::index_keys`]) are:
//!
//! - its **subject key**: of the simple selectors directly in its last compound selector,
//!   the first ID selector's name, else the first class selector's, else the first type
//!   selector's, else none;
//! - its **ancestor key**: of the simple selectors directly in each compound selector that
//!   has a descendant (` `) or child (`>`) combinator to its right, the first ID, else
//!   the first class, else the first type, else none.
//!
//! An element's keys ([`element_keys`]) are its `id` attribute's value, each word of its
//! `class` attribute (split at the white space Selectors uses: tab, line feed, form feed,
//! carriage return, space), and its local name, each ASCII-lowercased.
//!
//! # The invariant
//!
//! **Every rule that matches an element is a candidate for it**: if a complex selector of
//! a rule's list matches element `x`, then its subject key is none or one of `x`'s keys,
//! and its ancestor key is none or one of the keys of an element ancestor of `x`. So the
//! rule is in a bucket `x` looks in ([`RuleIndex::candidates`]). Why, from Selectors 4
//! (`clazel_selectors::spec`):
//!
//! - §21.3: a complex selector matches `x` only if its last compound matches `x`, so each
//!   simple selector directly in it does. An ID selector matches only an element whose `id`
//!   equals its name (ASCII case-insensitively in quirks mode, §7), a class selector only
//!   one with its name as a word of `class` (likewise, §6.6), a type selector only one
//!   whose local name is its name (lowercased, for an HTML element, §5.1). In each case the
//!   two lowercased are equal, which is what the keys compare.
//! - A compound with a descendant or child combinator to its right matches an element
//!   ancestor of the element the compound to its right matched (§16.1, §16.2). That element
//!   is `x`, or an ancestor of `x`, or a sibling of one of these (§16.3, §16.4), and in
//!   each case its ancestors are ancestors of `x`. So that compound matches an ancestor of
//!   `x`, and its key is one of that ancestor's keys.
//!
//! Selectors inside `:is()`, `:where()` and `:not()` give no key (a rule with only those in
//! its subject is filed under no subject key, and found for every element); the existing
//! subject test ([`super::rules::Selectors::may_match`]) still skips it where it can.
//!
//! This invariant is argued here, not proven, and the lookup has no Kani harness (each one
//! tried stopped at a local cap; `proofs.rs` lists them). Both are tested: the cascade with
//! the index is required to equal the cascade without it ([`super::cascade_unindexed`]) on
//! the crate's golden and conformance documents and on random rule sets.

use std::collections::BTreeMap;

use clazel_dom::exec::{ExecAttr, ExecKind};

/// An ID, a class or a type, ASCII-lowercased.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Key {
    /// An ID.
    Id(Vec<u32>),
    /// A class.
    Class(Vec<u32>),
    /// A type: a local name.
    Type(Vec<u32>),
}

/// `s` ASCII-lowercased.
pub fn lower(s: &[u32]) -> Vec<u32> {
    s.iter()
        .map(|&c| {
            if (0x41..=0x5A).contains(&c) {
                c.saturating_add(0x20)
            } else {
                c
            }
        })
        .collect()
}

/// Selectors 4's white space (`clazel_selectors::spec::is_selector_whitespace`).
fn is_whitespace(c: u32) -> bool {
    matches!(c, 0x20 | 0x09 | 0x0A | 0x0C | 0x0D)
}

/// The value of the first attribute with no namespace named `name` (Selectors'
/// `get_attribute`, which ID and class selectors read).
fn attribute<'a>(attributes: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attributes
        .iter()
        .find(|a| {
            a.namespace.is_none() && a.local_name.iter().copied().eq(name.chars().map(u32::from))
        })
        .map(|a| a.value.as_slice())
}

/// An element's keys (see the module's documentation); none for a node that is not an
/// element.
pub fn element_keys(kind: &ExecKind) -> Vec<Key> {
    let ExecKind::Element {
        local_name,
        attributes,
        ..
    } = kind
    else {
        return Vec::new();
    };
    let mut keys = vec![Key::Type(lower(local_name))];
    if let Some(id) = attribute(attributes, "id") {
        keys.push(Key::Id(lower(id)));
    }
    if let Some(class) = attribute(attributes, "class") {
        for word in class.split(|&c| is_whitespace(c)) {
            if !word.is_empty() {
                keys.push(Key::Class(lower(word)));
            }
        }
    }
    keys
}

/// Rules filed by subject key and ancestor key: entries (subject key, ancestor key, rule
/// number) sorted, no key before any key, each once.
#[derive(Debug, Clone)]
pub struct RuleIndex<K> {
    entries: Vec<(Option<K>, Option<K>, usize)>,
}

/// A set of ancestor keys the index looks in.
pub trait KeySet<K> {
    /// Whether `k` is in the set.
    fn has(&self, k: &K) -> bool;
    /// How many keys it lists (at least the distinct ones).
    fn count(&self) -> usize;
    /// Call `f` on each key it lists.
    fn each(&self, f: &mut dyn FnMut(&K));
}

impl<K: PartialEq> KeySet<K> for [K] {
    fn has(&self, k: &K) -> bool {
        self.contains(k)
    }

    fn count(&self) -> usize {
        self.len()
    }

    fn each(&self, f: &mut dyn FnMut(&K)) {
        self.iter().for_each(f);
    }
}

/// The keys of an element's ancestors: a multiset, so that leaving an element removes
/// exactly the keys entering it added. Every count is positive.
#[derive(Debug, Clone)]
pub struct Ancestors<K> {
    counts: BTreeMap<K, u32>,
}

impl<K: Ord> Default for Ancestors<K> {
    fn default() -> Self {
        Ancestors {
            counts: BTreeMap::new(),
        }
    }
}

impl<K: Ord + Clone> Ancestors<K> {
    /// Add `keys` (one element's).
    pub fn push(&mut self, keys: &[K]) {
        for k in keys {
            let c = self.counts.entry(k.clone()).or_insert(0);
            *c = c.saturating_add(1);
        }
    }

    /// Remove `keys`, which [`Ancestors::push`] added.
    pub fn pop(&mut self, keys: &[K]) {
        for k in keys {
            if let Some(c) = self.counts.get_mut(k) {
                *c = c.saturating_sub(1);
                if *c == 0 {
                    self.counts.remove(k);
                }
            }
        }
    }

    /// Whether `k` is a key of some ancestor.
    pub fn contains(&self, k: &K) -> bool {
        self.counts.contains_key(k)
    }

    /// How many distinct keys.
    pub fn len(&self) -> usize {
        self.counts.len()
    }

    /// Whether there is none.
    pub fn is_empty(&self) -> bool {
        self.counts.is_empty()
    }

    /// The distinct keys.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.counts.keys()
    }
}

impl<K: Ord + Clone> KeySet<K> for Ancestors<K> {
    fn has(&self, k: &K) -> bool {
        self.contains(k)
    }

    fn count(&self) -> usize {
        self.len()
    }

    fn each(&self, f: &mut dyn FnMut(&K)) {
        self.keys().for_each(f);
    }
}

impl<K: Ord + Clone> RuleIndex<K> {
    /// The index of `entries`: rule number, subject key, ancestor key; a rule may have
    /// several entries (one per complex selector of its list).
    pub fn new(entries: impl IntoIterator<Item = (usize, Option<K>, Option<K>)>) -> Self {
        let mut entries: Vec<(Option<K>, Option<K>, usize)> = entries
            .into_iter()
            .map(|(rule, subject, ancestor)| (subject, ancestor, rule))
            .collect();
        entries.sort_unstable();
        entries.dedup();
        RuleIndex { entries }
    }

    /// The rules filed under subject key `subject` (or none) whose ancestor key is none or
    /// in `ancestors`, appended to `out`. It walks the shorter of the subject's entries
    /// with an ancestor key and `ancestors`' keys, finding each by binary search.
    fn bucket_into<A: KeySet<K> + ?Sized>(
        &self,
        subject: &Option<K>,
        ancestors: &A,
        out: &mut Vec<usize>,
    ) {
        let lo = self.entries.partition_point(|e| e.0 < *subject);
        let hi = self.entries.partition_point(|e| e.0 <= *subject);
        let bucket = self.entries.get(lo..hi).unwrap_or_default();
        // No ancestor key sorts first.
        let split = bucket.partition_point(|e| e.1.is_none());
        let (any, keyed) = bucket.split_at(split.min(bucket.len()));
        out.extend(any.iter().map(|e| e.2));
        if keyed.len() <= ancestors.count() {
            for e in keyed {
                if e.1.as_ref().is_some_and(|a| ancestors.has(a)) {
                    out.push(e.2);
                }
            }
        } else {
            ancestors.each(&mut |a| {
                let from = keyed.partition_point(|e| e.1.as_ref() < Some(a));
                let to = keyed.partition_point(|e| e.1.as_ref() <= Some(a));
                if let Some(found) = keyed.get(from..to) {
                    out.extend(found.iter().map(|e| e.2));
                }
            });
        }
    }

    /// The candidates for an element whose keys are `keys` and whose ancestors' keys are
    /// `ancestors`: every rule with an entry whose subject key is none or in `keys` and
    /// whose ancestor key is none or in `ancestors`, each once, in increasing order.
    pub fn candidates<A: KeySet<K> + ?Sized>(&self, keys: &[K], ancestors: &A) -> Vec<usize> {
        let mut out = Vec::new();
        self.bucket_into(&None, ancestors, &mut out);
        for (i, k) in keys.iter().enumerate() {
            // A key listed twice selects the same entries once.
            if keys.get(..i).is_some_and(|before| before.contains(k)) {
                continue;
            }
            self.bucket_into(&Some(k.clone()), ancestors, &mut out);
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidates_by_subject_and_ancestor() {
        // Rule 0: subject 1, no ancestor; rule 1: subject 1, ancestor 7; rule 2: no
        // subject, ancestor 8; rule 3: subject 2 and (another complex) no subject.
        let index = RuleIndex::new([
            (0, Some(1u8), None),
            (1, Some(1), Some(7)),
            (2, None, Some(8)),
            (3, Some(2), None),
            (3, None, None),
        ]);
        let mut anc = Ancestors::default();
        assert_eq!(index.candidates(&[1, 1], &anc), vec![0, 3]);
        anc.push(&[7, 9]);
        assert_eq!(index.candidates(&[1], &anc), vec![0, 1, 3]);
        anc.push(&[8, 7]);
        assert_eq!(index.candidates(&[5], &anc), vec![2, 3]);
        anc.pop(&[8, 7]);
        assert!(anc.contains(&7) && !anc.contains(&8));
        assert_eq!(index.candidates(&[5], &anc), vec![3]);
        anc.pop(&[7, 9]);
        assert!(anc.is_empty());
    }

    #[test]
    fn element_keys_split_class_at_selector_white_space() {
        let u = |s: &str| s.chars().map(u32::from).collect::<Vec<u32>>();
        let attr = |n: &str, v: &str| ExecAttr {
            namespace: None,
            prefix: None,
            local_name: u(n),
            value: u(v),
        };
        let kind = ExecKind::Element {
            namespace: Some(clazel_dom::spec::Namespace::Html),
            prefix: None,
            local_name: u("DIV"),
            attributes: vec![
                attr("id", "Main"),
                attr("class", " a\tB\u{c}c\u{a0}d  "),
                attr("class", "ignored"),
            ],
            template_contents: None,
            form_owner: None,
        };
        assert_eq!(
            element_keys(&kind),
            vec![
                Key::Type(u("div")),
                Key::Id(u("main")),
                Key::Class(u("a")),
                Key::Class(u("b")),
                // U+00A0 is not Selectors' white space.
                Key::Class(u("c\u{a0}d")),
            ]
        );
    }
}
