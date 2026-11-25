//! `Attr`, `NamedNodeMap` and `DOMStringMap` (DOM §4.9†, HTML §3.2.6.6†) over
//! the arena's attribute lists.
//!
//! <https://dom.spec.whatwg.org/#interface-attr>
//!
//! Modelling choices:
//! - **An `Attr` is not an arena node.** `clazel-dom`'s attributes are
//!   records of their element's list, not nodes, so an `Attr` is a platform
//!   object ([`Object::Attr`]) naming its element (`owner`) while it is in
//!   one: it reads its value from the element, so a change through
//!   `setAttribute` shows in an `Attr` made before it. One element and one
//!   attribute (namespace and local name) have one `Attr` object
//!   (`Page::attr_index`), so `el.attributes[0] === el.getAttributeNode(n)`.
//!   When the attribute is removed or replaced the `Attr` keeps its last
//!   value and has no owner. The `Node` members of an `Attr` that make
//!   sense (`nodeType`, `nodeName`, `nodeValue`, `textContent`,
//!   `ownerDocument`, `parentNode`, `isConnected`) are answered in
//!   `node.rs`; the others throw a `TypeError` ("not a node").
//! - **Namespaces:** only the six of Infra §8 exist in the arena, so
//!   `setAttributeNS`, `createAttributeNS` and their kin throw
//!   `NotSupportedError` for another namespace.
//! - **`DOMStringMap`** is complete as Rust functions ([`Page::dataset_names`]
//!   and its siblings, HTML §3.2.6.6† "dataset"), and `dataset` returns the
//!   platform object. `dataset.foo` itself needs the named-property hooks of
//!   a legacy platform object, which `clazel-js`'s VM does not call yet, so a
//!   script cannot reach the properties; the item moves with the engine's
//!   exotic dispatch (`clazel-webidl`'s README).

use clazel_dom::exec::{Arena, ExecAttr};
use clazel_dom::spec::Namespace;
use clazel_js::{Result, Scope};
use clazel_webidl::convert::DomString;
use clazel_webidl::exception::DomErrorName;
use clazel_webidl::generated::bindings::{AttrImpl, DOMStringMapImpl, NamedNodeMapImpl};
use clazel_webidl::platform::ObjectKey;

use super::fragment::{copy_attr, copy_ns};
use super::node::{
    attributes_of_element, element_of, is_html_element_node, namespace_from_uri,
    namespace_uri_points, valid_attribute_local_name, valid_qualified_name,
};
use super::{Object, Page, dom_error, page, points_to_units, type_error, units_to_points};

/// An `Attr`'s state.
pub(crate) struct AttrState {
    /// The element whose attribute list holds it, if it is in one.
    pub(crate) owner: Option<usize>,
    /// Its namespace, prefix and local name; its value while it has no owner.
    pub(crate) attr: ExecAttr,
}

impl core::fmt::Debug for AttrState {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AttrState")
            .field("owner", &self.owner)
            .field("local_name", &self.attr.local_name)
            .finish_non_exhaustive()
    }
}

pub(crate) fn namespace_code(ns: Option<&Namespace>) -> u8 {
    match ns {
        None => 0,
        Some(Namespace::Html) => 1,
        Some(Namespace::MathMl) => 2,
        Some(Namespace::Svg) => 3,
        Some(Namespace::XLink) => 4,
        Some(Namespace::Xml) => 5,
        Some(Namespace::Xmlns) => 6,
    }
}

fn same_name(a: &ExecAttr, ns: Option<&Namespace>, local: &[u32]) -> bool {
    namespace_code(a.namespace.as_ref()) == namespace_code(ns) && a.local_name == local
}

/// The index of the attribute with namespace `ns` and local name `local`.
pub(crate) fn find_attribute(
    arena: &Arena,
    e: usize,
    ns: Option<&Namespace>,
    local: &[u32],
) -> Option<usize> {
    attributes_of_element(arena, e)
        .iter()
        .position(|a| same_name(a, ns, local))
}

impl Page {
    /// The `Attr` object of attribute `i` of element `e`, made if there is
    /// none.
    pub(crate) fn attr_object(&mut self, e: usize, i: usize) -> Option<ObjectKey> {
        let a = copy_attr(attributes_of_element(&self.arena, e).get(i)?);
        let k = (
            e,
            namespace_code(a.namespace.as_ref()),
            a.local_name.clone(),
        );
        if let Some(&key) = self.attr_index.get(&k) {
            return Some(key);
        }
        let key = self.add_object(Object::Attr(AttrState {
            owner: Some(e),
            attr: a,
        }));
        self.attr_index.insert(k, key);
        Some(key)
    }

    /// Attribute `i` of `e` is about to leave its list: its `Attr` object, if
    /// any, keeps the value and loses the owner.
    pub(crate) fn detach_attr_object(&mut self, e: usize, i: usize) {
        let Some(a) = attributes_of_element(&self.arena, e).get(i) else {
            return;
        };
        let k = (
            e,
            namespace_code(a.namespace.as_ref()),
            a.local_name.clone(),
        );
        let value = a.value.clone();
        if let Some(key) = self.attr_index.remove(&k)
            && let Some(Object::Attr(s)) = self.object_mut(key)
        {
            s.owner = None;
            s.attr.value = value;
        }
    }

    /// The attribute of `e` that `Attr` object `key` is, now: `None` if it
    /// has no owner.
    fn attr_current(&self, key: ObjectKey) -> Option<(&AttrState, Option<usize>)> {
        let Some(Object::Attr(s)) = self.object(key) else {
            return None;
        };
        let idx = s.owner.and_then(|e| {
            find_attribute(
                &self.arena,
                e,
                s.attr.namespace.as_ref(),
                &s.attr.local_name,
            )
        });
        Some((s, idx))
    }

    /// An `Attr`'s value now.
    pub(crate) fn attr_value(&self, key: ObjectKey) -> Option<Vec<u32>> {
        let (s, idx) = self.attr_current(key)?;
        Some(match (s.owner, idx) {
            (Some(e), Some(i)) => attributes_of_element(&self.arena, e)
                .get(i)
                .map_or_else(|| s.attr.value.clone(), |a| a.value.clone()),
            _ => s.attr.value.clone(),
        })
    }

    /// An `Attr`'s qualified name.
    pub(crate) fn attr_qualified_name(&self, key: ObjectKey) -> Option<Vec<u32>> {
        let Some(Object::Attr(s)) = self.object(key) else {
            return None;
        };
        Some(match &s.attr.prefix {
            Some(p) => {
                let mut q = p.clone();
                q.push(u32::from(':'));
                q.extend_from_slice(&s.attr.local_name);
                q
            }
            None => s.attr.local_name.clone(),
        })
    }

    /// A new `Attr` object with no owner.
    pub(crate) fn new_attr(&mut self, attr: ExecAttr) -> ObjectKey {
        self.add_object(Object::Attr(AttrState { owner: None, attr }))
    }

    // ---- HTML §3.2.6.6† dataset -------------------------------------------

    /// HTML §3.2.6.6† "the names of the supported property names": "for each
    /// content attribute on the element whose first five characters are the
    /// string "data-" and whose remaining characters (if any) do not include
    /// any ASCII upper alphas, in the order that those attributes are listed
    /// in the element's attribute list, add a name to the list, which is the
    /// attribute's name with the first five characters removed and every
    /// U+002D HYPHEN-MINUS character (-) followed by an ASCII lower alpha
    /// removed, and the ASCII lower alpha converted to ASCII upper case".
    #[must_use]
    pub fn dataset_names(&self, e: usize) -> Vec<Vec<u32>> {
        attributes_of_element(&self.arena, e)
            .iter()
            .filter(|a| a.namespace.is_none())
            .filter_map(|a| data_name_to_property(&a.local_name))
            .collect()
    }

    /// The value of the dataset property `name` of `e`, if it has one:
    /// HTML §3.2.6.6† "to determine the value of a named property name for
    /// a DOMStringMap: return the value of the attribute whose name gives
    /// name".
    #[must_use]
    pub fn dataset_get(&self, e: usize, name: &[u32]) -> Option<Vec<u32>> {
        attributes_of_element(&self.arena, e)
            .iter()
            .find(|a| {
                a.namespace.is_none()
                    && data_name_to_property(&a.local_name).as_deref() == Some(name)
            })
            .map(|a| a.value.clone())
    }

    /// HTML §3.2.6.6† "to set the value of a new or existing named property
    /// name to value": "1. Let name be the property name. 2. If name
    /// contains a U+002D HYPHEN-MINUS character (-) followed by an ASCII
    /// lower alpha, then throw a SyntaxError. 3. For each ASCII upper alpha
    /// in name, insert a U+002D HYPHEN-MINUS character (-) before the
    /// character and replace the character with the same character
    /// converted to ASCII lowercase. 4. Insert the string data- at the
    /// front of name. 5. If name does not match the XML Name production,
    /// throw an InvalidCharacterError. 6. Set an attribute value for the
    /// element using name and value."
    ///
    /// # Errors
    /// The name of the `DOMException` the standard throws.
    pub fn dataset_set(
        &mut self,
        e: usize,
        name: &[u32],
        value: Vec<u32>,
    ) -> core::result::Result<(), DomErrorName> {
        let attr = property_to_data_name(name)?;
        super::node::set_attribute_value(self, e, &attr, value);
        Ok(())
    }

    /// HTML §3.2.6.6† "to delete an existing named property name": "Remove
    /// an attribute by name given name (as converted) and the element".
    pub fn dataset_delete(&mut self, e: usize, name: &[u32]) {
        if let Ok(attr) = property_to_data_name(name) {
            super::node::remove_attribute_named(self, e, &attr);
        }
    }
}

/// The dataset property of attribute `name`, or `None` if it has none.
fn data_name_to_property(name: &[u32]) -> Option<Vec<u32>> {
    let prefix: Vec<u32> = "data-".chars().map(u32::from).collect();
    let rest = name.strip_prefix(prefix.as_slice())?;
    if rest.iter().any(|&c| (0x41..=0x5A).contains(&c)) {
        return None;
    }
    let mut out = Vec::with_capacity(rest.len());
    let mut i = 0;
    while let Some(&c) = rest.get(i) {
        if c == u32::from('-')
            && let Some(&n) = rest.get(i.saturating_add(1))
            && (0x61..=0x7A).contains(&n)
        {
            out.push(n & !0x20);
            i = i.saturating_add(2);
        } else {
            out.push(c);
            i = i.saturating_add(1);
        }
    }
    Some(out)
}

/// The attribute name of dataset property `name`, or the error.
fn property_to_data_name(name: &[u32]) -> core::result::Result<Vec<u32>, DomErrorName> {
    for (i, &c) in name.iter().enumerate() {
        if c == u32::from('-')
            && let Some(&n) = name.get(i.saturating_add(1))
            && (0x61..=0x7A).contains(&n)
        {
            return Err(DomErrorName::SyntaxError);
        }
    }
    let mut out: Vec<u32> = "data-".chars().map(u32::from).collect();
    for &c in name {
        if (0x41..=0x5A).contains(&c) {
            out.push(u32::from('-'));
            out.push(c | 0x20);
        } else {
            out.push(c);
        }
    }
    if !valid_attribute_local_name(&out) || out.contains(&u32::from(':')) {
        return Err(DomErrorName::InvalidCharacterError);
    }
    Ok(out)
}

fn attr_key_state(scope: &mut Scope<'_>, this: ObjectKey) -> Result<()> {
    if matches!(page(scope)?.object(this), Some(Object::Attr(_))) {
        Ok(())
    } else {
        Err(type_error(scope, "not an Attr"))
    }
}

impl AttrImpl for Page {
    /// DOM §4.9.2† `namespaceURI`.
    fn namespace_uri<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        attr_key_state(scope, this)?;
        Ok(match page(scope)?.object(this) {
            Some(Object::Attr(s)) => s
                .attr
                .namespace
                .as_ref()
                .map(|n| points_to_units(&namespace_uri_points(n))),
            _ => None,
        })
    }

    fn prefix<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<DomString>> {
        attr_key_state(scope, this)?;
        Ok(match page(scope)?.object(this) {
            Some(Object::Attr(s)) => s.attr.prefix.as_deref().map(points_to_units),
            _ => None,
        })
    }

    fn local_name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        attr_key_state(scope, this)?;
        Ok(match page(scope)?.object(this) {
            Some(Object::Attr(s)) => points_to_units(&s.attr.local_name),
            _ => Vec::new(),
        })
    }

    /// DOM §4.9.2† `name`: "this's qualified name".
    fn name<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        attr_key_state(scope, this)?;
        Ok(page(scope)?
            .attr_qualified_name(this)
            .map(|q| points_to_units(&q))
            .unwrap_or_default())
    }

    fn value<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        attr_key_state(scope, this)?;
        Ok(page(scope)?
            .attr_value(this)
            .map(|v| points_to_units(&v))
            .unwrap_or_default())
    }

    /// DOM §4.9.2† `value` setter: "Set an existing attribute value with
    /// this and the given value": "1. If attribute's element is null, then
    /// set attribute's value to value. 2. Otherwise, change attribute to
    /// value."
    fn set_value<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: DomString) -> Result<()> {
        attr_key_state(scope, this)?;
        let value = units_to_points(&value);
        let p = page(scope)?;
        let target = p.attr_current(this).map(|(s, idx)| (s.owner, idx));
        match target {
            Some((Some(e), Some(i))) => p.attr_change(e, i, value),
            _ => {
                if let Some(Object::Attr(s)) = p.object_mut(this) {
                    s.attr.value = value;
                }
            }
        }
        Ok(())
    }

    fn owner_element<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        attr_key_state(scope, this)?;
        let p = page(scope)?;
        Ok(match p.attr_current(this) {
            Some((s, Some(_))) => s.owner.map(Page::node_key),
            _ => None,
        })
    }

    fn specified<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        attr_key_state(scope, this)?;
        Ok(true)
    }
}

fn map_element(scope: &mut Scope<'_>, this: ObjectKey) -> Result<usize> {
    match page(scope)?.object(this) {
        Some(Object::NamedNodeMap(e)) => Ok(*e),
        _ => Err(type_error(scope, "not a NamedNodeMap")),
    }
}

/// DOM §4.9† "get an attribute by name": in an HTML element of an HTML
/// document the name is lowercased first.
pub(crate) fn by_name(arena: &Arena, e: usize, name: &[u32]) -> Option<usize> {
    let name: Vec<u32> = if is_html_element_node(arena, e) {
        name.iter()
            .map(|&c| {
                if (0x41..=0x5A).contains(&c) {
                    c | 0x20
                } else {
                    c
                }
            })
            .collect()
    } else {
        name.to_vec()
    };
    attributes_of_element(arena, e).iter().position(|a| {
        let mut q = a.prefix.clone().map_or_else(Vec::new, |mut p| {
            p.push(u32::from(':'));
            p
        });
        q.extend_from_slice(&a.local_name);
        q == name
    })
}

fn ns_from_option(
    scope: &mut Scope<'_>,
    namespace: &Option<DomString>,
) -> Result<Option<Namespace>> {
    match namespace {
        None => Ok(None),
        Some(n) if n.is_empty() => Ok(None),
        Some(n) => match namespace_from_uri(&units_to_points(n)) {
            Some(ns) => Ok(Some(ns)),
            None => Err(dom_error(
                scope,
                DomErrorName::NotSupportedError,
                "only the HTML, MathML, SVG, XLink, XML and XMLNS namespaces are implemented",
            )),
        },
    }
}

/// The attribute of `e` named `name` in namespace `namespace`, as the NS
/// methods find it: a namespace that no attribute can have finds nothing.
pub(crate) fn by_name_ns(
    arena: &Arena,
    e: usize,
    namespace: &Option<DomString>,
    local: &[u32],
) -> Option<usize> {
    let ns = match namespace {
        None => None,
        Some(n) if n.is_empty() => None,
        Some(n) => Some(namespace_from_uri(&units_to_points(n))?),
    };
    find_attribute(arena, e, ns.as_ref(), local)
}

/// DOM §4.9† "set an attribute": "1. If attr's element is neither null nor
/// element, throw an InUseAttributeError. 2. Let oldAttr be the result of
/// getting an attribute given attr's namespace, attr's local name, and
/// element. 3. If oldAttr is attr, return attr. 4. If oldAttr is non-null,
/// then replace oldAttr with attr. 5. Otherwise, append attr to element. 6.
/// Return oldAttr."
fn set_attribute_node(
    scope: &mut Scope<'_>,
    e: usize,
    attr: ObjectKey,
) -> Result<Option<ObjectKey>> {
    attr_key_state(scope, attr)?;
    let p = page(scope)?;
    let (owner, idx) = match p.attr_current(attr) {
        Some((s, idx)) => (s.owner, idx),
        None => (None, None),
    };
    let in_use = matches!((owner, idx), (Some(o), Some(_)) if o != e);
    if in_use {
        return Err(dom_error(
            scope,
            DomErrorName::InUseAttributeError,
            "the attribute is in use by another element",
        ));
    }
    let p = page(scope)?;
    if matches!((owner, idx), (Some(o), Some(_)) if o == e) {
        return Ok(Some(attr));
    }
    let (new, ns_local) = match p.object(attr) {
        Some(Object::Attr(s)) => {
            let a = copy_attr(&s.attr);
            let ns = a.namespace.as_ref().map(copy_ns);
            let local = a.local_name.clone();
            (a, (ns, local))
        }
        _ => return Err(type_error(scope, "not an Attr")),
    };
    let existing = find_attribute(&p.arena, e, ns_local.0.as_ref(), &ns_local.1);
    let old = match existing {
        Some(i) => {
            let old = p.attr_object(e, i);
            p.attr_replace(e, i, new);
            old
        }
        None => {
            p.attr_append(e, new);
            None
        }
    };
    // The new Attr object is now the attribute.
    if let Some(Object::Attr(s)) = p.object_mut(attr) {
        s.owner = Some(e);
    }
    p.attr_index
        .insert((e, namespace_code(ns_local.0.as_ref()), ns_local.1), attr);
    Ok(old)
}

impl NamedNodeMapImpl for Page {
    fn length<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        let e = map_element(scope, this)?;
        Ok(u32::try_from(attributes_of_element(&page(scope)?.arena, e).len()).unwrap_or(u32::MAX))
    }

    fn item<'s>(scope: &mut Scope<'s>, this: ObjectKey, index: u32) -> Result<Option<ObjectKey>> {
        let e = map_element(scope, this)?;
        let Ok(i) = usize::try_from(index) else {
            return Ok(None);
        };
        Ok(page(scope)?.attr_object(e, i))
    }

    fn get_named_item<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<Option<ObjectKey>> {
        let e = map_element(scope, this)?;
        let p = page(scope)?;
        match by_name(&p.arena, e, &units_to_points(&qualified_name)) {
            Some(i) => Ok(p.attr_object(e, i)),
            None => Ok(None),
        }
    }

    fn get_named_item_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<Option<ObjectKey>> {
        let e = map_element(scope, this)?;
        let p = page(scope)?;
        match by_name_ns(&p.arena, e, &namespace, &units_to_points(&local_name)) {
            Some(i) => Ok(p.attr_object(e, i)),
            None => Ok(None),
        }
    }

    fn set_named_item<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        attr: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        let e = map_element(scope, this)?;
        set_attribute_node(scope, e, attr)
    }

    fn set_named_item_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        attr: ObjectKey,
    ) -> Result<Option<ObjectKey>> {
        let e = map_element(scope, this)?;
        set_attribute_node(scope, e, attr)
    }

    /// DOM §4.9.1† `removeNamedItem(qualifiedName)`: "1. Let attr be the
    /// result of removing an attribute given qualifiedName and element. 2.
    /// If attr is null, then throw a NotFoundError. 3. Return attr."
    fn remove_named_item<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        qualified_name: DomString,
    ) -> Result<ObjectKey> {
        let e = map_element(scope, this)?;
        let p = page(scope)?;
        let found = by_name(&p.arena, e, &units_to_points(&qualified_name));
        remove_found(scope, e, found)
    }

    fn remove_named_item_ns<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        namespace: Option<DomString>,
        local_name: DomString,
    ) -> Result<ObjectKey> {
        let e = map_element(scope, this)?;
        let p = page(scope)?;
        let found = by_name_ns(&p.arena, e, &namespace, &units_to_points(&local_name));
        remove_found(scope, e, found)
    }
}

fn remove_found(scope: &mut Scope<'_>, e: usize, found: Option<usize>) -> Result<ObjectKey> {
    let Some(i) = found else {
        return Err(dom_error(
            scope,
            DomErrorName::NotFoundError,
            "no such attribute",
        ));
    };
    let p = page(scope)?;
    let Some(key) = p.attr_object(e, i) else {
        return Err(dom_error(
            scope,
            DomErrorName::NotFoundError,
            "no such attribute",
        ));
    };
    p.attr_remove(e, i);
    Ok(key)
}

impl DOMStringMapImpl for Page {}

// ---------------------------------------------------------------------------
// The Element and Document members that make and use Attr objects

/// `Element.attributes` (DOM §4.9†: "a NamedNodeMap object whose associated
/// element is this").
pub(crate) fn attributes_map(scope: &mut Scope<'_>, this: ObjectKey) -> Result<ObjectKey> {
    let e = element_of(scope, this)?;
    Ok(page(scope)?.add_object(Object::NamedNodeMap(e)))
}

/// `Element.dataset`.
pub(crate) fn dataset_object(scope: &mut Scope<'_>, this: ObjectKey) -> Result<ObjectKey> {
    let e = element_of(scope, this)?;
    Ok(page(scope)?.add_object(Object::DataSet(e)))
}

/// `getAttributeNode(qualifiedName)`.
pub(crate) fn get_attribute_node(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    name: &[u16],
) -> Result<Option<ObjectKey>> {
    let e = element_of(scope, this)?;
    let p = page(scope)?;
    match by_name(&p.arena, e, &units_to_points(name)) {
        Some(i) => Ok(p.attr_object(e, i)),
        None => Ok(None),
    }
}

/// `getAttributeNodeNS(namespace, localName)`.
pub(crate) fn get_attribute_node_ns(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    namespace: &Option<DomString>,
    local: &[u16],
) -> Result<Option<ObjectKey>> {
    let e = element_of(scope, this)?;
    let p = page(scope)?;
    match by_name_ns(&p.arena, e, namespace, &units_to_points(local)) {
        Some(i) => Ok(p.attr_object(e, i)),
        None => Ok(None),
    }
}

/// `setAttributeNode(attr)` and `setAttributeNodeNS(attr)`.
pub(crate) fn set_attribute_node_of(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    attr: ObjectKey,
) -> Result<Option<ObjectKey>> {
    let e = element_of(scope, this)?;
    set_attribute_node(scope, e, attr)
}

/// DOM §4.9† `removeAttributeNode(attr)`: "1. If this's attribute list does
/// not contain attr, then throw a NotFoundError. 2. Remove attr. 3. Return
/// attr."
pub(crate) fn remove_attribute_node(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    attr: ObjectKey,
) -> Result<ObjectKey> {
    let e = element_of(scope, this)?;
    attr_key_state(scope, attr)?;
    let p = page(scope)?;
    let idx = match p.attr_current(attr) {
        Some((s, Some(i))) if s.owner == Some(e) => Some(i),
        _ => None,
    };
    let Some(i) = idx else {
        return Err(dom_error(
            scope,
            DomErrorName::NotFoundError,
            "the attribute is not on this element",
        ));
    };
    page(scope)?.attr_remove(e, i);
    Ok(attr)
}

/// The namespace, prefix and local name "validate and extract" returns.
pub(crate) type Extracted = (Option<Namespace>, Option<Vec<u32>>, Vec<u32>);

/// DOM §4.9† "validate and extract" a namespace and qualified name: the
/// namespace, prefix and local name, or the `DOMException` name.
pub(crate) fn validate_and_extract(
    scope: &mut Scope<'_>,
    namespace: &Option<DomString>,
    qualified: &[u16],
) -> Result<Extracted> {
    let q = units_to_points(qualified);
    // 1. "If namespace is the empty string, then set it to null."
    let empty_ns = matches!(namespace, Some(n) if n.is_empty());
    let uri = if empty_ns { &None } else { namespace };
    // 2. "Validate qualifiedName."
    if !valid_qualified_name(&q) {
        return Err(dom_error(
            scope,
            DomErrorName::InvalidCharacterError,
            "not a valid qualified name",
        ));
    }
    // 3. to 4.
    let (prefix, local) = match q.iter().position(|&c| c == u32::from(':')) {
        Some(i) => (
            Some(q.get(..i).unwrap_or(&[]).to_vec()),
            q.get(i.saturating_add(1)..).unwrap_or(&[]).to_vec(),
        ),
        None => (None, q.clone()),
    };
    let ns_points = uri.as_ref().map(|n| units_to_points(n));
    let is = |v: &[u32], s: &str| v.iter().copied().eq(s.chars().map(u32::from));
    let ns_is = |s: &str| ns_points.as_deref().is_some_and(|n| is(n, s));
    let err = |scope: &mut Scope<'_>| {
        dom_error(
            scope,
            DomErrorName::NamespaceError,
            "the prefix does not match the namespace",
        )
    };
    // 5. "If prefix is non-null and namespace is null, then throw."
    if prefix.is_some() && ns_points.is_none() {
        return Err(err(scope));
    }
    // 6. "If prefix is "xml" and namespace is not the XML namespace, throw."
    if prefix.as_deref().is_some_and(|p| is(p, "xml"))
        && !ns_is("http://www.w3.org/XML/1998/namespace")
    {
        return Err(err(scope));
    }
    // 7. "If either qualifiedName or prefix is "xmlns" and namespace is not
    // the XMLNS namespace, then throw."
    if (is(&q, "xmlns") || prefix.as_deref().is_some_and(|p| is(p, "xmlns")))
        && !ns_is("http://www.w3.org/2000/xmlns/")
    {
        return Err(err(scope));
    }
    // 8. "If namespace is the XMLNS namespace and neither qualifiedName nor
    // prefix is "xmlns", then throw a NamespaceError."
    if ns_is("http://www.w3.org/2000/xmlns/")
        && !is(&q, "xmlns")
        && !prefix.as_deref().is_some_and(|p| is(p, "xmlns"))
    {
        return Err(err(scope));
    }
    let ns = ns_from_option(scope, uri)?;
    Ok((ns, prefix, local))
}

impl Page {
    /// The element a `DOMStringMap` object (`dataset`) is for.
    #[must_use]
    pub fn dataset_element(&self, key: ObjectKey) -> Option<usize> {
        match self.object(key) {
            Some(Object::DataSet(e)) => Some(*e),
            _ => None,
        }
    }
}
