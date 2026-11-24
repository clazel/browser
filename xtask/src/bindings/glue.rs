//! Writing the binding glue (`crates/clazel-webidl/src/generated/bindings.rs`)
//! from the resolved model (phase-7.md item 7.12): for each interface the
//! browser exposes ([`EXPOSED`]),
//!
//! - a trait, `<Interface>Impl`, with one method per attribute getter and
//!   setter, operation, constructor and stringifier, whose arguments and
//!   results are IDL values in Rust (`crates/clazel-webidl/src/convert.rs`
//!   lists the representation). The platform (`clazel-web`) implements it;
//!   every method has a default that throws a `NotSupportedError`
//!   `DOMException` naming the member, so what is not implemented says so.
//! - a native function per member (the "glue"), which checks `this`
//!   (WebIDL §3.7.5†, §3.7.6†), checks the argument count, converts the
//!   arguments (§3.2†), resolves overloads (§3.6†), calls the trait method,
//!   and converts the result;
//! - the code that makes the interface object, the interface prototype
//!   object, the constants, attributes and operations (§3.7†), with
//!   `[LegacyUnforgeable]`, `[Replaceable]`, `[SameObject]`, `[PutForwards]`
//!   and `[Reflect]`.
//!
//! Event handler IDL attributes (`on*`, of type `EventHandler`,
//! `OnErrorEventHandler` or `OnBeforeUnloadEventHandler`: HTML §8.1.8.1†)
//! have no trait method: their getter and setter call the platform's
//! `event_handler_get` and `event_handler_set` with the event type's name (the
//! attribute's name without `on`), as `[Reflect]` ones call `reflect_get`.
//!
//! Dictionaries, enumerations and unions that those members use become Rust
//! types with their conversion functions (§3.2.18†, §3.2.19†, §3.2.24†).
//!
//! What is left out, and why, is listed in the generated file's header: a
//! member whose types the bindings cannot convert yet (`Promise`, `record`,
//! buffer types, `bigint`, `symbol`, interfaces not exposed),
//! `[SecureContext]` members (the browser has no secure
//! contexts yet), special operations without a name (indexed and named
//! properties need exotic objects), and `iterable`, `maplike` and `setlike`
//! (Symbol.iterator).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use super::model::{
    Argument, ExtAttr, ExtValue, Member, MemberKind, OpKind, Operation, Simple, Ty, TyKind, Value,
};
use super::resolve::{Interface, Model};

/// The interfaces the bindings expose to script: those `clazel-web`
/// implements (phase-7.md items 7.13 and 7.15), with every ancestor. In this
/// order they are installed, parents first.
pub const EXPOSED: &[&str] = &[
    "EventTarget",
    "AbortSignal",
    "AbortController",
    "Event",
    "CustomEvent",
    "Node",
    "Document",
    "DocumentType",
    "DocumentFragment",
    "CharacterData",
    "Text",
    "Comment",
    "ProcessingInstruction",
    "Element",
    "Attr",
    "NamedNodeMap",
    "HTMLElement",
    "HTMLUnknownElement",
    "HTMLHtmlElement",
    "HTMLHeadElement",
    "HTMLTitleElement",
    "HTMLBodyElement",
    "HTMLDivElement",
    "HTMLSpanElement",
    "HTMLParagraphElement",
    "HTMLAnchorElement",
    "NodeList",
    "HTMLCollection",
    "DOMTokenList",
    "DOMStringMap",
    "MutationObserver",
    "MutationRecord",
    "AbstractRange",
    "NodeRange",
    "Range",
    "Window",
    "Location",
    "History",
    "Navigator",
    "UIEvent",
    "MouseEvent",
    "WheelEvent",
    "KeyboardEvent",
    "FocusEvent",
    "InputEvent",
    "UserActivation",
];

/// The typedefs that are event handlers (HTML §8.1.8.1†), whose attributes
/// go through the platform's `event_handler_get` and `event_handler_set`.
const EVENT_HANDLERS: &[&str] = &[
    "EventHandler",
    "OnErrorEventHandler",
    "OnBeforeUnloadEventHandler",
];

/// Rust's reserved words, which a name gets `_` after.
const KEYWORDS: &[&str] = &[
    "as", "async", "await", "box", "break", "const", "continue", "crate", "dyn", "else", "enum",
    "extern", "false", "final", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod",
    "move", "mut", "override", "priv", "pub", "ref", "return", "self", "Self", "static", "struct",
    "super", "trait", "true", "try", "type", "typeof", "unsafe", "unsized", "use", "virtual",
    "where", "while", "yield", "macro", "abstract", "become", "do",
];

/// `camelCase` or `PascalCase` as `snake_case`, keeping acronyms together
/// (`innerHTML` is `inner_html`, `URL` is `url`).
pub fn snake(name: &str) -> String {
    let chars: Vec<char> = name.chars().collect();
    let mut out = String::new();
    for (i, c) in chars.iter().enumerate() {
        if c.is_ascii_uppercase() {
            let prev = i.checked_sub(1).and_then(|j| chars.get(j)).copied();
            let next = chars.get(i.saturating_add(1)).copied();
            let boundary = match prev {
                Some(p) if p.is_ascii_lowercase() || p.is_ascii_digit() => true,
                Some(p) if p.is_ascii_uppercase() => next.is_some_and(|n| n.is_ascii_lowercase()),
                _ => false,
            };
            if boundary && !out.ends_with('_') {
                out.push('_');
            }
            out.push(c.to_ascii_lowercase());
        } else if *c == '-' || *c == ' ' {
            out.push('_');
        } else {
            out.push(*c);
        }
    }
    if KEYWORDS.contains(&out.as_str()) {
        out.push('_');
    }
    out
}

/// A name as a Rust type or variant name: `PascalCase` from words split at
/// `-`, `_` and spaces; the empty string is `Empty`.
fn pascal(name: &str) -> String {
    if name.is_empty() {
        return "Empty".to_owned();
    }
    let mut out = String::new();
    let mut up = true;
    for c in name.chars() {
        if c == '-' || c == '_' || c == ' ' || c == '/' || c == '.' {
            up = true;
            continue;
        }
        if up {
            out.push(c.to_ascii_uppercase());
            up = false;
        } else {
            out.push(c);
        }
    }
    if out.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        out.insert(0, 'V');
    }
    out
}

fn has(ext: &[ExtAttr], name: &str) -> bool {
    ext.iter().any(|a| a.name == name)
}

fn ident(ext: &[ExtAttr], name: &str) -> Option<String> {
    ext.iter()
        .find(|a| a.name == name)
        .and_then(|a| match &a.value {
            ExtValue::Ident(s) => Some(s.clone()),
            _ => None,
        })
}

fn q(s: &str) -> String {
    format!("{s:?}")
}

/// What a named type is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NamedKind {
    Interface,
    CallbackInterface,
    Dictionary,
    Enum,
    CallbackFunction,
}

/// A member left out, and why.
struct Skip {
    what: String,
    why: String,
}

struct Gen<'m> {
    m: &'m Model,
    exposed: BTreeSet<String>,
    dicts: BTreeSet<String>,
    enums: BTreeSet<String>,
    /// The enumerations converted from ECMAScript values (not only to).
    enums_read: BTreeSet<String>,
    unions: BTreeMap<String, (Vec<Ty>, bool)>,
    skipped: Vec<Skip>,
    dropped_dict_members: Vec<Skip>,
}

impl<'m> Gen<'m> {
    fn interface(&self, name: &str) -> Option<&'m Interface> {
        self.m.interfaces.iter().find(|i| i.name == name)
    }

    fn named_kind(&self, name: &str) -> Option<NamedKind> {
        if let Some(i) = self.interface(name) {
            return Some(if i.callback {
                NamedKind::CallbackInterface
            } else {
                NamedKind::Interface
            });
        }
        if self.m.dictionaries.iter().any(|d| d.name == name) {
            return Some(NamedKind::Dictionary);
        }
        if self.m.enums.iter().any(|e| e.name == name) {
            return Some(NamedKind::Enum);
        }
        if self.m.callbacks.iter().any(|c| c.name == name)
            || name == "Function"
            || name == "VoidFunction"
        {
            return Some(NamedKind::CallbackFunction);
        }
        None
    }

    /// The type with typedefs expanded and the external names the bindings
    /// know mapped: `DOMHighResTimeStamp` is `double` (High Resolution Time
    /// §4†), `CSSOMString` is `DOMString` (CSSOM's choice for an
    /// implementation), and `WindowProxy` is the `Window` it proxies (HTML
    /// §7.2.3†; there is one browsing context, so no navigation swaps it).
    fn resolve(&self, ty: &Ty) -> Ty {
        let mut t = ty.clone();
        for _ in 0..16 {
            let TyKind::Named(n) = &t.kind else {
                break;
            };
            let mapped = match n.as_str() {
                "DOMHighResTimeStamp" => Some(TyKind::Simple(Simple::UnrestrictedDouble)),
                "CSSOMString" => Some(TyKind::Simple(Simple::DomString)),
                "WindowProxy" => Some(TyKind::Named("Window".to_owned())),
                _ => None,
            };
            if let Some(k) = mapped {
                t.kind = k;
                continue;
            }
            let Some(td) = self.m.typedefs.iter().find(|d| &d.name == n) else {
                break;
            };
            if EVENT_HANDLERS.contains(&n.as_str()) {
                break;
            }
            let nullable = t.nullable || td.ty.nullable;
            let mut ext = t.ext.clone();
            ext.extend(td.ty.ext.iter().cloned());
            t = Ty {
                kind: td.ty.kind.clone(),
                nullable,
                ext,
            };
        }
        // A union left with one member (Trusted Types dropped) is that member.
        if let TyKind::Union(ms) = &t.kind {
            let (flat, nullable) = self.flatten(ms);
            if let [only] = flat.as_slice() {
                let mut ext = t.ext.clone();
                ext.extend(only.ext.iter().cloned());
                return Ty {
                    kind: only.kind.clone(),
                    nullable: t.nullable || nullable || only.nullable,
                    ext,
                };
            }
        }
        t
    }

    /// The flattened member types of a union (§2.13.?): unions inside are
    /// opened; the result says whether any member was nullable. Trusted
    /// Types' types are dropped: no value of them can exist here.
    fn flatten(&self, members: &[Ty]) -> (Vec<Ty>, bool) {
        let mut out = Vec::new();
        let mut nullable = false;
        for m in members {
            let m = self.resolve(m);
            nullable |= m.nullable;
            match &m.kind {
                TyKind::Union(inner) => {
                    let (o, n) = self.flatten(inner);
                    nullable |= n;
                    out.extend(o);
                }
                TyKind::Named(n) if n.starts_with("Trusted") => {}
                _ => out.push(Ty {
                    nullable: false,
                    ..m
                }),
            }
        }
        (out, nullable)
    }

    /// Why a type cannot be converted, or `None`.
    fn unsupported(&self, ty: &Ty) -> Option<String> {
        let t = self.resolve(ty);
        match &t.kind {
            TyKind::Simple(Simple::Bigint | Simple::Symbol) => Some("bigint or symbol".into()),
            TyKind::Simple(_) => None,
            TyKind::Buffer(b) => Some(format!("buffer type {b}")),
            TyKind::Promise(_) => Some("Promise".into()),
            TyKind::Record(..) => Some("record".into()),
            TyKind::ObservableArray(_) => Some("ObservableArray".into()),
            TyKind::Sequence(inner) | TyKind::FrozenArray(inner) => {
                if self.needs_lt(inner) {
                    return Some("a sequence of objects".into());
                }
                self.unsupported(inner)
            }
            TyKind::Union(members) => {
                let (flat, _) = self.flatten(members);
                if flat.is_empty() {
                    return Some("a union of Trusted Types only".into());
                }
                for f in &flat {
                    if matches!(f.kind, TyKind::Simple(Simple::Undefined)) {
                        return Some("a union with undefined".into());
                    }
                    if let Some(why) = self.unsupported(f) {
                        return Some(why);
                    }
                }
                None
            }
            TyKind::Named(n) => {
                if EVENT_HANDLERS.contains(&n.as_str()) {
                    return None;
                }
                match self.named_kind(n) {
                    Some(NamedKind::Interface) if self.exposed.contains(n) => None,
                    Some(NamedKind::Interface) => Some(format!("interface {n} is not exposed")),
                    Some(_) => None,
                    None => Some(format!("{n} is not in the vendored IDL")),
                }
            }
        }
    }

    /// Whether the Rust type borrows the scope (holds a `Local`).
    fn needs_lt(&self, ty: &Ty) -> bool {
        let t = self.resolve(ty);
        match &t.kind {
            TyKind::Simple(Simple::Any | Simple::Object) => true,
            TyKind::Simple(_) | TyKind::Buffer(_) => false,
            TyKind::Sequence(i)
            | TyKind::FrozenArray(i)
            | TyKind::ObservableArray(i)
            | TyKind::Promise(i) => self.needs_lt(i),
            TyKind::Record(_, v) => self.needs_lt(v),
            TyKind::Union(ms) => self.flatten(ms).0.iter().any(|m| self.needs_lt(m)),
            TyKind::Named(n) => match self.named_kind(n) {
                Some(NamedKind::CallbackFunction | NamedKind::CallbackInterface) => true,
                Some(NamedKind::Dictionary) => self
                    .dict_members(n)
                    .iter()
                    .any(|(_, m)| self.needs_lt(&m.ty)),
                _ => false,
            },
        }
    }

    /// A dictionary's members with its ancestors', least derived first, each
    /// dictionary's members in lexicographic order (§3.2.18† step 3 and 4),
    /// with the dictionary each comes from. Members whose type cannot be
    /// converted are dropped (and listed).
    fn dict_members(&self, name: &str) -> Vec<(String, super::model::DictMember)> {
        let mut chain = Vec::new();
        let mut cur = Some(name.to_owned());
        while let Some(c) = cur {
            let Some(d) = self.m.dictionaries.iter().find(|d| d.name == c) else {
                break;
            };
            chain.push(d);
            cur = d.parent.clone();
            if chain.len() > 32 {
                break;
            }
        }
        chain.reverse();
        let mut out = Vec::new();
        for d in chain {
            let mut ms: Vec<_> = d.members.iter().collect();
            ms.sort_by(|a, b| a.name.cmp(&b.name));
            for m in ms {
                if self.unsupported(&m.ty).is_none() && !has(&m.ext, "SecureContext") {
                    out.push((d.name.clone(), m.clone()));
                }
            }
        }
        out
    }

    fn union_name(&self, flat: &[Ty]) -> String {
        flat.iter()
            .map(|t| self.type_label(t))
            .collect::<Vec<_>>()
            .join("Or")
    }

    fn type_label(&self, t: &Ty) -> String {
        let t = self.resolve(t);
        let base = match &t.kind {
            TyKind::Simple(s) => pascal(&simple_label(*s)),
            TyKind::Named(n) => n.clone(),
            TyKind::Sequence(i) => format!("{}Sequence", self.type_label(i)),
            TyKind::FrozenArray(i) => format!("{}FrozenArray", self.type_label(i)),
            TyKind::Union(ms) => self.union_name(&self.flatten(ms).0),
            _ => "Other".to_owned(),
        };
        if t.nullable {
            format!("Nullable{base}")
        } else {
            base
        }
    }

    /// The Rust type of an IDL type, given and returned.
    fn rty(&mut self, ty: &Ty) -> String {
        let t = self.resolve(ty);
        let base = match &t.kind {
            TyKind::Simple(s) => match s {
                Simple::Any | Simple::Object => "Local<'s>".to_owned(),
                Simple::Undefined => "()".to_owned(),
                Simple::Boolean => "bool".to_owned(),
                Simple::Byte => "i8".to_owned(),
                Simple::Octet => "u8".to_owned(),
                Simple::Short => "i16".to_owned(),
                Simple::UnsignedShort => "u16".to_owned(),
                Simple::Long => "i32".to_owned(),
                Simple::UnsignedLong => "u32".to_owned(),
                Simple::LongLong => "i64".to_owned(),
                Simple::UnsignedLongLong => "u64".to_owned(),
                Simple::Float | Simple::UnrestrictedFloat => "f32".to_owned(),
                Simple::Double | Simple::UnrestrictedDouble => "f64".to_owned(),
                Simple::ByteString => "Vec<u8>".to_owned(),
                Simple::DomString => "DomString".to_owned(),
                Simple::UsvString => "String".to_owned(),
                Simple::Bigint | Simple::Symbol => "()".to_owned(),
            },
            TyKind::Named(n) => match self.named_kind(n) {
                Some(NamedKind::Interface) => "ObjectKey".to_owned(),
                Some(NamedKind::CallbackInterface | NamedKind::CallbackFunction) => {
                    "Local<'s>".to_owned()
                }
                Some(NamedKind::Enum) => {
                    self.enums.insert(n.clone());
                    n.clone()
                }
                Some(NamedKind::Dictionary) => {
                    self.dicts.insert(n.clone());
                    if self.needs_lt(&t) {
                        format!("{n}<'s>")
                    } else {
                        n.clone()
                    }
                }
                None => "()".to_owned(),
            },
            TyKind::Sequence(i) | TyKind::FrozenArray(i) => format!("Vec<{}>", self.rty(i)),
            TyKind::Union(ms) => {
                let (flat, nullable) = self.flatten(ms);
                let name = self.union_name(&flat);
                for f in &flat {
                    let _ = self.rty(f);
                }
                let lt = self.needs_lt(&t);
                self.unions.insert(name.clone(), (flat, nullable));
                let base = if lt { format!("{name}<'s>") } else { name };
                return if nullable || t.nullable {
                    format!("Option<{base}>")
                } else {
                    base
                };
            }
            _ => "()".to_owned(),
        };
        if t.nullable {
            format!("Option<{base}>")
        } else {
            base
        }
    }

    /// Rust code converting the ECMAScript value `v` (a `Local<'s>`) to the
    /// IDL type: an expression of type `self.rty(ty)`, using `scope` and `?`.
    fn conv(&mut self, ty: &Ty, v: &str) -> String {
        let t = self.resolve(ty);
        let is_union = matches!(t.kind, TyKind::Union(_));
        let union_nullable = match &t.kind {
            TyKind::Union(ms) => self.flatten(ms).1,
            _ => false,
        };
        if t.nullable || union_nullable {
            let inner = Ty {
                nullable: false,
                ..t.clone()
            };
            let c = if is_union {
                self.conv_union(&inner, v)
            } else {
                self.conv(&inner, v)
            };
            // §3.2.? nullable types: "Otherwise, if V is undefined or null,
            // then return the IDL nullable type T? value null."
            return format!("if convert::is_nullish(scope, {v}) {{ None }} else {{ Some({c}) }}");
        }
        let legacy_null = has(&t.ext, "LegacyNullToEmptyString");
        let flags = format!(
            "IntegerFlags {{ enforce_range: {}, clamp: {} }}",
            has(&t.ext, "EnforceRange"),
            has(&t.ext, "Clamp")
        );
        match &t.kind {
            TyKind::Simple(s) => match s {
                Simple::Any => v.to_owned(),
                Simple::Undefined | Simple::Bigint | Simple::Symbol => "()".to_owned(),
                Simple::Object => format!("convert::object(scope, {v})?"),
                Simple::Boolean => format!("convert::boolean(scope, {v})"),
                Simple::Byte => format!("convert::byte(scope, {v}, {flags})?"),
                Simple::Octet => format!("convert::octet(scope, {v}, {flags})?"),
                Simple::Short => format!("convert::short(scope, {v}, {flags})?"),
                Simple::UnsignedShort => format!("convert::unsigned_short(scope, {v}, {flags})?"),
                Simple::Long => format!("convert::long(scope, {v}, {flags})?"),
                Simple::UnsignedLong => format!("convert::unsigned_long(scope, {v}, {flags})?"),
                Simple::LongLong => format!("convert::long_long(scope, {v}, {flags})?"),
                Simple::UnsignedLongLong => {
                    format!("convert::unsigned_long_long(scope, {v}, {flags})?")
                }
                Simple::Float => format!("convert::float(scope, {v}, false)?"),
                Simple::UnrestrictedFloat => format!("convert::float(scope, {v}, true)?"),
                Simple::Double => format!("convert::double(scope, {v}, false)?"),
                Simple::UnrestrictedDouble => format!("convert::double(scope, {v}, true)?"),
                Simple::ByteString => format!("convert::byte_string(scope, {v})?"),
                Simple::DomString => format!("convert::dom_string(scope, {v}, {legacy_null})?"),
                Simple::UsvString => format!("convert::usv_string(scope, {v})?"),
            },
            TyKind::Named(n) => match self.named_kind(n) {
                Some(NamedKind::Interface) => {
                    format!("convert::interface::<P>(scope, {v}, InterfaceId::{n})?")
                }
                Some(NamedKind::CallbackInterface) => {
                    format!("convert::callback_interface(scope, {v})?")
                }
                Some(NamedKind::CallbackFunction) => {
                    format!("convert::callback_function(scope, {v})?")
                }
                Some(NamedKind::Enum) => {
                    self.enums.insert(n.clone());
                    self.enums_read.insert(n.clone());
                    format!("enum_{}(scope, {v})?", snake(n))
                }
                Some(NamedKind::Dictionary) => {
                    self.dicts.insert(n.clone());
                    format!("dict_{}::<P>(scope, {v})?", snake(n))
                }
                None => "()".to_owned(),
            },
            TyKind::Sequence(i) | TyKind::FrozenArray(i) => {
                let inner = self.conv(i, "item");
                format!(
                    "convert::sequence(scope, {v}, |scope, item| {{ let x = {inner}; Ok(x) }})?"
                )
            }
            TyKind::Union(_) => self.conv_union(&t, v),
            _ => "()".to_owned(),
        }
    }

    fn conv_union(&mut self, t: &Ty, v: &str) -> String {
        let _ = self.rty(t);
        let TyKind::Union(ms) = &t.kind else {
            return "()".into();
        };
        let (flat, _) = self.flatten(ms);
        format!("union_{}::<P>(scope, {v})?", snake(&self.union_name(&flat)))
    }

    /// Rust code converting the IDL value `x` (of `self.rty(ty)`) to an
    /// ECMAScript value: an expression of type `Local<'s>`.
    fn js_value(&mut self, ty: &Ty, x: &str) -> String {
        let t = self.resolve(ty);
        let union_nullable = match &t.kind {
            TyKind::Union(ms) => self.flatten(ms).1,
            _ => false,
        };
        if t.nullable || union_nullable {
            let inner = Ty {
                nullable: false,
                ..t.clone()
            };
            let c = self.js_value(&inner, "x");
            return format!("match {x} {{ Some(x) => {c}, None => scope.null() }}");
        }
        match &t.kind {
            TyKind::Simple(s) => match s {
                Simple::Any | Simple::Object => x.to_owned(),
                Simple::Undefined | Simple::Bigint | Simple::Symbol => {
                    "scope.undefined()".to_owned()
                }
                Simple::Boolean => format!("scope.boolean({x})"),
                Simple::Byte
                | Simple::Octet
                | Simple::Short
                | Simple::UnsignedShort
                | Simple::Long
                | Simple::UnsignedLong
                | Simple::Float
                | Simple::UnrestrictedFloat => {
                    format!("scope.number(f64::from({x}))")
                }
                Simple::LongLong | Simple::UnsignedLongLong => format!("scope.number({x} as f64)"),
                Simple::Double | Simple::UnrestrictedDouble => format!("scope.number({x})"),
                Simple::ByteString => format!("convert::from_byte_string(scope, &{x})"),
                Simple::DomString => format!("convert::from_dom_string(scope, &{x})"),
                Simple::UsvString => format!("convert::from_usv_string(scope, &{x})"),
            },
            TyKind::Named(n) => match self.named_kind(n) {
                Some(NamedKind::Interface) => format!("convert::from_interface::<P>(scope, {x})?"),
                Some(NamedKind::Enum) => format!("scope.string({x}.as_str())"),
                _ => x.to_owned(),
            },
            TyKind::Sequence(i) | TyKind::FrozenArray(i) => {
                let c = self.js_value(i, "x");
                format!(
                    "{{ let mut items = Vec::new(); for x in {x} {{ let v = {c}; items.push(v); }} convert::from_sequence(scope, &items)? }}"
                )
            }
            TyKind::Union(ms) => {
                let (flat, _) = self.flatten(ms);
                let name = self.union_name(&flat);
                let mut arms = String::new();
                for f in &flat {
                    let c = self.js_value(f, "x");
                    let _ = write!(arms, "{name}::{}(x) => {c}, ", self.type_label(f));
                }
                format!("match {x} {{ {arms}}}")
            }
            _ => "scope.undefined()".to_owned(),
        }
    }

    /// The Rust value of a default (§2.5.? "default value"), of
    /// `self.rty(ty)`.
    fn default_value(&mut self, ty: &Ty, v: &Value) -> String {
        let t = self.resolve(ty);
        if matches!(t.kind, TyKind::Simple(Simple::Any)) {
            return match v {
                Value::Null => "scope.null()".into(),
                Value::Undefined => "scope.undefined()".into(),
                other => literal_js(other),
            };
        }
        if matches!(v, Value::Null) {
            return "None".into();
        }
        if let TyKind::Union(ms) = &t.kind {
            // A union's default is the value of the member type it fits.
            let (flat, nullable) = self.flatten(ms);
            let name = self.union_name(&flat);
            let fits = |g: &Gen<'_>, f: &Ty| {
                let f = g.resolve(f);
                match (&f.kind, v) {
                    (TyKind::Simple(Simple::Boolean), Value::Bool(_)) => true,
                    (
                        TyKind::Simple(s),
                        Value::Integer(_)
                        | Value::Decimal(_)
                        | Value::Infinity
                        | Value::NegInfinity
                        | Value::NaN,
                    ) => !matches!(
                        s,
                        Simple::Boolean
                            | Simple::Any
                            | Simple::Object
                            | Simple::Undefined
                            | Simple::ByteString
                            | Simple::DomString
                            | Simple::UsvString
                            | Simple::Bigint
                            | Simple::Symbol
                    ),
                    (
                        TyKind::Simple(Simple::DomString | Simple::UsvString | Simple::ByteString),
                        Value::Str(_),
                    ) => true,
                    (TyKind::Named(n), Value::Str(_)) => g.named_kind(n) == Some(NamedKind::Enum),
                    (TyKind::Named(n), Value::EmptyDictionary) => {
                        g.named_kind(n) == Some(NamedKind::Dictionary)
                    }
                    (TyKind::Sequence(_) | TyKind::FrozenArray(_), Value::EmptySequence) => true,
                    _ => false,
                }
            };
            let member = flat.iter().find(|f| fits(self, f)).cloned();
            let Some(member) = member else {
                return "Default::default()".into();
            };
            let inner = self.default_value(&member, v);
            let s = format!("{name}::{}({inner})", self.type_label(&member));
            return if nullable || t.nullable {
                format!("Some({s})")
            } else {
                s
            };
        }
        let wrap = |s: String, t: &Ty| if t.nullable { format!("Some({s})") } else { s };
        let s = match (&t.kind, v) {
            (_, Value::Bool(b)) => b.to_string(),
            (
                TyKind::Simple(
                    Simple::Float
                    | Simple::UnrestrictedFloat
                    | Simple::Double
                    | Simple::UnrestrictedDouble,
                ),
                Value::Integer(n),
            ) => {
                format!("{n}.0")
            }
            (_, Value::Integer(n)) => n.to_string(),
            (_, Value::Decimal(d)) => d.clone(),
            (TyKind::Simple(Simple::Float | Simple::UnrestrictedFloat), Value::Infinity) => {
                "f32::INFINITY".into()
            }
            (TyKind::Simple(Simple::Float | Simple::UnrestrictedFloat), Value::NegInfinity) => {
                "f32::NEG_INFINITY".into()
            }
            (TyKind::Simple(Simple::Float | Simple::UnrestrictedFloat), Value::NaN) => {
                "f32::NAN".into()
            }
            (_, Value::Infinity) => "f64::INFINITY".into(),
            (_, Value::NegInfinity) => "f64::NEG_INFINITY".into(),
            (_, Value::NaN) => "f64::NAN".into(),
            (TyKind::Simple(Simple::UsvString), Value::Str(s)) => format!("String::from({})", q(s)),
            (TyKind::Simple(Simple::ByteString), Value::Str(s)) => {
                format!("{}.as_bytes().to_vec()", q(s))
            }
            (TyKind::Named(n), Value::Str(s)) if self.named_kind(n) == Some(NamedKind::Enum) => {
                format!("{n}::{}", pascal(s))
            }
            (_, Value::Str(s)) => format!("{}.encode_utf16().collect::<DomString>()", q(s)),
            (_, Value::EmptySequence) => "Vec::new()".into(),
            (TyKind::Named(n), Value::EmptyDictionary) => {
                self.dicts.insert(n.clone());
                format!(
                    "{{ let u = scope.undefined(); dict_{}::<P>(scope, u)? }}",
                    snake(n)
                )
            }
            (_, Value::Undefined) => "scope.undefined()".into(),
            _ => "Default::default()".into(),
        };
        wrap(s, &t)
    }

    /// The categories of a type for overload resolution
    /// (`crate::overload::TypeSet`), as Rust code.
    fn type_set(&self, ty: &Ty) -> String {
        let t = self.resolve(ty);
        let (members, mut nullable) = match &t.kind {
            TyKind::Union(ms) => self.flatten(ms),
            _ => (
                vec![Ty {
                    nullable: false,
                    ..t.clone()
                }],
                false,
            ),
        };
        nullable |= t.nullable;
        let mut interfaces = Vec::new();
        let mut flags: BTreeSet<&str> = BTreeSet::new();
        for m in &members {
            let m = self.resolve(m);
            if m.nullable {
                nullable = true;
            }
            match &m.kind {
                TyKind::Simple(s) => match s {
                    Simple::Any => {
                        flags.insert("any");
                    }
                    Simple::Undefined => {
                        flags.insert("undefined");
                    }
                    Simple::Boolean => {
                        flags.insert("boolean");
                    }
                    Simple::Object => {
                        flags.insert("object");
                    }
                    Simple::ByteString | Simple::DomString | Simple::UsvString => {
                        flags.insert("string");
                    }
                    Simple::Bigint | Simple::Symbol => {}
                    _ => {
                        flags.insert("numeric");
                    }
                },
                TyKind::Named(n) => match self.named_kind(n) {
                    Some(NamedKind::Interface) => interfaces.push(format!("InterfaceId::{n}")),
                    Some(NamedKind::CallbackInterface) => {
                        flags.insert("callback_interface");
                    }
                    Some(NamedKind::CallbackFunction) => {
                        flags.insert("callback_function");
                    }
                    Some(NamedKind::Dictionary) => {
                        flags.insert("dictionary");
                    }
                    Some(NamedKind::Enum) => {
                        flags.insert("string");
                    }
                    None => {}
                },
                TyKind::Sequence(_) | TyKind::FrozenArray(_) => {
                    flags.insert("sequence");
                }
                _ => {}
            }
        }
        let mut s = format!(
            "TypeSet {{ interfaces: &[{}], nullable: {nullable}",
            interfaces.join(", ")
        );
        for f in flags {
            let _ = write!(s, ", {f}: true");
        }
        s.push_str(", ..EMPTY_SET }");
        s
    }
}

fn simple_label(s: Simple) -> String {
    match s {
        Simple::Any => "any",
        Simple::Undefined => "undefined",
        Simple::Boolean => "boolean",
        Simple::Byte => "byte",
        Simple::Octet => "octet",
        Simple::Bigint => "bigint",
        Simple::Object => "object",
        Simple::Symbol => "symbol",
        Simple::Short => "short",
        Simple::UnsignedShort => "unsigned short",
        Simple::Long => "long",
        Simple::UnsignedLong => "unsigned long",
        Simple::LongLong => "long long",
        Simple::UnsignedLongLong => "unsigned long long",
        Simple::Float => "float",
        Simple::UnrestrictedFloat => "unrestricted float",
        Simple::Double => "double",
        Simple::UnrestrictedDouble => "unrestricted double",
        Simple::ByteString => "ByteString",
        Simple::DomString => "DOMString",
        Simple::UsvString => "USVString",
    }
    .to_owned()
}

/// An IDL type as written, for doc comments.
fn idl(t: &Ty) -> String {
    let base = match &t.kind {
        TyKind::Simple(s) => simple_label(*s),
        TyKind::Buffer(b) | TyKind::Named(b) => b.clone(),
        TyKind::Sequence(i) => format!("sequence<{}>", idl(i)),
        TyKind::FrozenArray(i) => format!("FrozenArray<{}>", idl(i)),
        TyKind::ObservableArray(i) => format!("ObservableArray<{}>", idl(i)),
        TyKind::Promise(i) => format!("Promise<{}>", idl(i)),
        TyKind::Record(k, v) => format!("record<{}, {}>", idl(k), idl(v)),
        TyKind::Union(ms) => format!("({})", ms.iter().map(idl).collect::<Vec<_>>().join(" or ")),
    };
    if t.nullable { format!("{base}?") } else { base }
}

fn idl_args(args: &[Argument]) -> String {
    args.iter()
        .map(|a| {
            let mut s = String::new();
            if a.optional {
                s.push_str("optional ");
            }
            s.push_str(&idl(&a.ty));
            if a.variadic {
                s.push_str("...");
            }
            s.push(' ');
            s.push_str(&a.name);
            s
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// An attribute as the bindings make it.
struct Attr {
    name: String,
    ty: Ty,
    readonly: bool,
    is_static: bool,
    stringifier: bool,
    ext: Vec<ExtAttr>,
    /// The trait method names.
    getter: String,
    setter: String,
}

/// An operation (all its overloads) as the bindings make it.
struct Op {
    name: String,
    is_static: bool,
    unforgeable: bool,
    overloads: Vec<(Operation, Vec<ExtAttr>, String)>,
}

/// The members of one interface the bindings make.
struct Members {
    consts: Vec<(String, Value)>,
    attrs: Vec<Attr>,
    ops: Vec<Op>,
    ctors: Vec<Vec<Argument>>,
    html_constructor: bool,
    /// An anonymous `stringifier;`.
    stringifier: bool,
}

fn literal_js(v: &Value) -> String {
    match v {
        Value::Bool(b) => format!("scope.boolean({b})"),
        Value::Integer(n) => format!("scope.number({n}.0)"),
        Value::Decimal(d) => format!("scope.number({d})"),
        Value::Infinity => "scope.number(f64::INFINITY)".into(),
        Value::NegInfinity => "scope.number(f64::NEG_INFINITY)".into(),
        Value::NaN => "scope.number(f64::NAN)".into(),
        _ => "scope.undefined()".into(),
    }
}

/// The interface's members, filtered; skips are recorded.
fn members(g: &mut Gen<'_>, i: &Interface) -> Members {
    let mut out = Members {
        consts: Vec::new(),
        attrs: Vec::new(),
        ops: Vec::new(),
        ctors: Vec::new(),
        html_constructor: false,
        stringifier: false,
    };
    let mut used: BTreeSet<String> = BTreeSet::new();
    let skip = |g: &mut Gen<'_>, what: String, why: String| g.skipped.push(Skip { what, why });
    for m in &i.members {
        let Member { ext, kind, .. } = m;
        if has(ext, "SecureContext") {
            let what = match kind {
                MemberKind::Attribute(a) => a.name.clone(),
                MemberKind::Operation(o) => o.name.clone().unwrap_or_default(),
                _ => "member".into(),
            };
            skip(
                g,
                format!("{}.{what}", i.name),
                "[SecureContext] (no secure contexts yet)".into(),
            );
            continue;
        }
        if let Some(e) = ext.iter().find(|a| a.name == "Exposed") {
            let window = match &e.value {
                ExtValue::Ident(s) => s == "Window" || s == "*",
                ExtValue::IdentList(l) => l.iter().any(|s| s == "Window"),
                ExtValue::Wildcard => true,
                _ => true,
            };
            if !window {
                continue;
            }
        }
        match kind {
            MemberKind::Const(c) => out.consts.push((c.name.clone(), c.value.clone())),
            MemberKind::Attribute(a) => {
                if let Some(why) = g.unsupported(&a.ty) {
                    skip(g, format!("{}.{}", i.name, a.name), why);
                    continue;
                }
                let base = snake(&a.name);
                let getter = if used.contains(&base) {
                    format!("{base}_attribute")
                } else {
                    base.clone()
                };
                used.insert(getter.clone());
                let setter = format!("set_{base}");
                used.insert(setter.clone());
                out.attrs.push(Attr {
                    name: a.name.clone(),
                    ty: a.ty.clone(),
                    readonly: a.readonly,
                    is_static: a.is_static,
                    stringifier: a.stringifier,
                    ext: ext.clone(),
                    getter,
                    setter,
                });
            }
            MemberKind::Operation(o) => {
                if o.kind == OpKind::Stringifier && o.name.is_none() {
                    out.stringifier = true;
                    continue;
                }
                let Some(name) = o.name.clone() else {
                    skip(
                        g,
                        format!("{} (anonymous {:?})", i.name, o.kind),
                        "indexed and named properties need exotic objects".into(),
                    );
                    continue;
                };
                let bad = std::iter::once(&o.ret)
                    .chain(o.args.iter().map(|a| &a.ty))
                    .find_map(|t| g.unsupported(t));
                let ret = g.resolve(&o.ret);
                let dict_ret = matches!(&ret.kind, TyKind::Named(n) if g.named_kind(n) == Some(NamedKind::Dictionary));
                // A long operation's arguments go in a struct (see `is_long`),
                // which cannot borrow the scope.
                let borrows = is_long(o, o.kind == OpKind::Static)
                    && o.args.iter().any(|a| g.needs_lt(&a.ty));
                let too_long = borrows.then(|| {
                    "more than 7 parameters, and an argument that borrows the scope".to_owned()
                });
                if let Some(why) = bad
                    .or_else(|| dict_ret.then(|| "returns a dictionary".to_owned()))
                    .or(too_long)
                {
                    skip(g, format!("{}.{name}", i.name), why);
                    continue;
                }
                let is_static = o.kind == OpKind::Static;
                let unforgeable = has(ext, "LegacyUnforgeable") || has(&i.ext, "LegacyUnforgeable");
                match out
                    .ops
                    .iter_mut()
                    .find(|x| x.name == name && x.is_static == is_static)
                {
                    Some(op) => op.overloads.push((o.clone(), ext.clone(), String::new())),
                    None => out.ops.push(Op {
                        name,
                        is_static,
                        unforgeable,
                        overloads: vec![(o.clone(), ext.clone(), String::new())],
                    }),
                }
            }
            MemberKind::Constructor(args) => {
                if has(ext, "HTMLConstructor") {
                    out.html_constructor = true;
                    continue;
                }
                if let Some(why) = args.iter().find_map(|a| g.unsupported(&a.ty)) {
                    skip(g, format!("{} constructor", i.name), why);
                    continue;
                }
                out.ctors.push(args.clone());
            }
            MemberKind::Iterable(_) => skip(
                g,
                format!("{} iterable", i.name),
                "needs Symbol.iterator".into(),
            ),
            MemberKind::Collection(_) => skip(
                g,
                format!("{} maplike/setlike", i.name),
                "needs Symbol.iterator".into(),
            ),
        }
    }
    for op in &mut out.ops {
        let base = snake(&op.name);
        let base = if used.contains(&base) {
            format!("{base}_operation")
        } else {
            base
        };
        let n = op.overloads.len();
        for (k, ov) in op.overloads.iter_mut().enumerate() {
            ov.2 = if n > 1 {
                format!("{base}_{k}")
            } else {
                base.clone()
            };
            used.insert(ov.2.clone());
        }
    }
    out
}

fn unforgeable_attr(i: &Interface, a: &Attr) -> bool {
    has(&a.ext, "LegacyUnforgeable") || has(&i.ext, "LegacyUnforgeable")
}

/// The `[Reflect]` content attribute name of a `DOMString` or `boolean`
/// attribute (HTML §2.6.1† "reflect"): the identifier given, or the IDL
/// attribute's name in ASCII lowercase.
fn reflect(g: &Gen<'_>, a: &Attr) -> Option<(String, bool)> {
    if !has(&a.ext, "Reflect") {
        return None;
    }
    let t = g.resolve(&a.ty);
    let boolean = match t.kind {
        TyKind::Simple(Simple::DomString) if !t.nullable => false,
        TyKind::Simple(Simple::Boolean) if !t.nullable => true,
        _ => return None,
    };
    let name = ident(&a.ext, "Reflect").unwrap_or_else(|| a.name.to_ascii_lowercase());
    Some((name, boolean))
}

/// The event type of an event handler IDL attribute (HTML §8.1.8.1†: an
/// event handler IDL attribute is named for its event handler, `on` and the
/// event type): the attribute's name without `on`.
fn event_handler(a: &Attr) -> Option<String> {
    match &a.ty.kind {
        TyKind::Named(n) if EVENT_HANDLERS.contains(&n.as_str()) && !a.is_static => {
            a.name.strip_prefix("on").map(str::to_owned)
        }
        _ => None,
    }
}

/// Whether the trait method of `o` would have more than 7 parameters
/// (`scope`, `this` unless static, and the arguments): clippy's
/// `too_many_arguments`, which the workspace keeps. The arguments of such an
/// operation go in one struct, [`args_struct`], with a field for each.
fn is_long(o: &Operation, is_static: bool) -> bool {
    o.args.len().saturating_add(if is_static { 1 } else { 2 }) > 7
}

/// The name of the struct holding a long operation's arguments.
fn args_struct(iface: &str, o: &Operation) -> String {
    format!("{iface}{}Args", pascal(o.name.as_deref().unwrap_or("")))
}

/// The Rust type of an argument, for a trait method.
fn arg_type(g: &mut Gen<'_>, a: &Argument) -> String {
    let t = g.rty(&a.ty);
    if a.variadic {
        format!("Vec<{t}>")
    } else if a.optional && a.default.is_none() {
        format!("Option<{t}>")
    } else {
        t
    }
}

/// The struct of a long operation's arguments, as Rust source.
fn args_struct_def(g: &mut Gen<'_>, iface: &str, o: &Operation) -> String {
    let name = args_struct(iface, o);
    let mut s = format!(
        "/// The arguments of `{iface}.{}`, more than a method may have.\n#[derive(Debug, Clone)]\npub struct {name} {{\n",
        o.name.as_deref().unwrap_or("")
    );
    for a in &o.args {
        let t = arg_type(g, a);
        let _ = writeln!(s, "    /// `{}`\n    pub {}: {t},", a.name, snake(&a.name));
    }
    s.push_str("}\n\n");
    s
}

/// The Rust parameters of an argument list, for a trait method.
fn params(g: &mut Gen<'_>, args: &[Argument]) -> String {
    let mut s = String::new();
    for a in args {
        let t = g.rty(&a.ty);
        let t = if a.variadic {
            format!("Vec<{t}>")
        } else if a.optional && a.default.is_none() {
            format!("Option<{t}>")
        } else {
            t
        };
        let _ = write!(s, ", _{}: {t}", snake(&a.name).trim_end_matches('_'));
    }
    s
}

/// Rust statements converting the arguments of `args` (WebIDL §3.6†, steps
/// 15 and 16: "If argument is optional and V is undefined: if it has a
/// default value, the default; otherwise the special value missing", a
/// variadic argument the rest of the values) into `a0`, `a1`, ...
fn convert_args(g: &mut Gen<'_>, args: &[Argument]) -> (String, String) {
    let mut code = String::new();
    let mut names = Vec::new();
    for (k, a) in args.iter().enumerate() {
        let n = format!("a{k}");
        if a.variadic {
            let c = g.conv(&a.ty, "v");
            let _ = writeln!(
                code,
                "    let mut {n} = Vec::new();\n    for i in {k}..args.len() {{ let v = args.get(i); {n}.push({c}); }}"
            );
        } else if a.optional {
            let c = g.conv(&a.ty, "v");
            let missing = match &a.default {
                Some(d) => g.default_value(&a.ty, d),
                None => "None".to_owned(),
            };
            let present = if a.default.is_some() {
                c
            } else {
                format!("Some({c})")
            };
            let _ = writeln!(
                code,
                "    let v = args.get({k});\n    let {n} = if scope.kind(v) == ValueKind::Undefined {{ {missing} }} else {{ {present} }};"
            );
        } else {
            let c = g.conv(&a.ty, "v");
            let _ = writeln!(code, "    let v = args.get({k});\n    let {n} = {c};");
        }
        names.push(n);
    }
    let call = names.iter().map(|n| format!(", {n}")).collect::<String>();
    (code, call)
}

fn required(args: &[Argument]) -> usize {
    args.iter()
        .take_while(|a| !a.optional && !a.variadic)
        .count()
}

/// Emits `bindings.rs`.
pub fn emit(m: &Model, header: &str) -> String {
    let mut g = Gen {
        m,
        exposed: EXPOSED.iter().map(|s| (*s).to_owned()).collect(),
        dicts: BTreeSet::new(),
        enums: BTreeSet::new(),
        enums_read: BTreeSet::new(),
        unions: BTreeMap::new(),
        skipped: Vec::new(),
        dropped_dict_members: Vec::new(),
    };
    let mut interfaces: Vec<&Interface> = Vec::new();
    for name in EXPOSED {
        if let Some(i) = g.interface(name) {
            interfaces.push(i);
        }
    }
    let all: Vec<(&Interface, Members)> = interfaces
        .iter()
        .map(|i| {
            let ms = members(&mut g, i);
            (*i, ms)
        })
        .collect();

    let mut o = Out::default();
    for (i, ms) in &all {
        emit_interface(&mut g, i, ms, &mut o);
    }
    let Out {
        traits,
        glue,
        install,
        unforgeables,
    } = o;

    // Types: resolved after the members, which register what they use;
    // dictionaries can pull in more dictionaries, enums and unions.
    let mut types = String::new();
    let mut done_dicts: BTreeSet<String> = BTreeSet::new();
    let mut done_unions: BTreeSet<String> = BTreeSet::new();
    loop {
        let next_dict = g.dicts.iter().find(|d| !done_dicts.contains(*d)).cloned();
        if let Some(d) = next_dict {
            done_dicts.insert(d.clone());
            emit_dictionary(&mut g, &d, &mut types);
            continue;
        }
        let next_union = g.unions.keys().find(|u| !done_unions.contains(*u)).cloned();
        if let Some(u) = next_union {
            done_unions.insert(u.clone());
            emit_union(&mut g, &u, &mut types);
            continue;
        }
        break;
    }
    for e in g.enums.clone() {
        emit_enum(&g, &e, &mut types);
    }

    let mut out = String::new();
    out.push_str("//! The generated WebIDL bindings (phase-7.md item 7.12): for each interface the\n//! browser exposes, the trait its platform implements, the native functions that\n//! convert between ECMAScript and IDL values and call it, and the code that makes\n//! its interface object and prototype. `xtask/src/bindings/glue.rs` says how.\n//!\n");
    for l in header.lines() {
        let _ = writeln!(out, "{}", l.trim_end());
    }
    out.push_str("//\n// Left out, and why (each member here has no property; see glue.rs):\n");
    for s in &g.skipped {
        let _ = writeln!(out, "// - {}: {}", s.what, s.why);
    }
    if !g.dropped_dict_members.is_empty() {
        out.push_str("//\n// Dictionary members not read (their types cannot be converted yet):\n");
        for s in &g.dropped_dict_members {
            let _ = writeln!(out, "// - {}: {}", s.what, s.why);
        }
    }
    out.push_str("\nuse clazel_js::{Args, Key, Local, Result, Scope, ValueKind};\n\nuse crate::convert::{self, DomString, IntegerFlags};\nuse crate::install;\nuse crate::overload::{self, Arg, Overload, TypeSet};\nuse crate::platform::{self, ObjectKey, Platform};\n\n");
    out.push_str("/// A [`TypeSet`] with nothing in it.\nconst EMPTY_SET: TypeSet = TypeSet { interfaces: &[], nullable: false, dictionary: false, callback_function: false, callback_interface: false, sequence: false, object: false, boolean: false, numeric: false, string: false, any: false, undefined: false };\n\n");
    // InterfaceId.
    out.push_str("/// The interfaces the bindings expose, in the order they are installed\n/// (parents first).\n#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]\npub enum InterfaceId {\n");
    for (i, _) in &all {
        let _ = writeln!(out, "    /// `{}`.\n    {},", i.name, i.name);
    }
    out.push_str("}\n\nimpl InterfaceId {\n    /// Every interface, parents first.\n    pub const ALL: &'static [InterfaceId] = &[\n");
    for (i, _) in &all {
        let _ = writeln!(out, "        InterfaceId::{},", i.name);
    }
    out.push_str("    ];\n\n    /// The interface's identifier.\n    #[must_use]\n    pub fn name(self) -> &'static str {\n        match self {\n");
    for (i, _) in &all {
        let _ = writeln!(
            out,
            "            InterfaceId::{} => {},",
            i.name,
            q(&i.name)
        );
    }
    out.push_str("        }\n    }\n\n    /// The interface it inherits from.\n    #[must_use]\n    pub fn parent(self) -> Option<InterfaceId> {\n        match self {\n");
    for (i, _) in &all {
        let p = i
            .parent
            .as_ref()
            .map_or_else(|| "None".to_owned(), |p| format!("Some(InterfaceId::{p})"));
        let _ = writeln!(out, "            InterfaceId::{} => {p},", i.name);
    }
    out.push_str("        }\n    }\n\n    /// Whether this interface is `other` or inherits from it (WebIDL §2.2†\n    /// \"inherited interfaces\").\n    #[must_use]\n    pub fn inherits(self, other: InterfaceId) -> bool {\n        let mut cur = Some(self);\n        for _ in 0..InterfaceId::ALL.len() {\n            match cur {\n                Some(c) if c == other => return true,\n                Some(c) => cur = c.parent(),\n                None => return false,\n            }\n        }\n        false\n    }\n\n    /// The interface named `name`.\n    #[must_use]\n    pub fn from_name(name: &str) -> Option<InterfaceId> {\n        InterfaceId::ALL.iter().copied().find(|i| i.name() == name)\n    }\n}\n\n");
    out.push_str(&types);
    out.push_str(&traits);
    out.push_str("/// Every interface's trait: what a platform implements to be given to\n/// [`install`].\npub trait AllInterfaces: Platform");
    for (i, _) in &all {
        let _ = write!(out, "\n    + {}Impl", i.name);
    }
    out.push_str("\n{\n}\n\nimpl<T: Platform");
    for (i, _) in &all {
        let _ = write!(out, "\n    + {}Impl", i.name);
    }
    out.push_str("> AllInterfaces for T {}\n\n");
    out.push_str(&glue);
    out.push_str("/// Defines the `[LegacyUnforgeable]` attributes and operations of\n/// `interface` and its ancestors on a new wrapper (WebIDL §3.7.? \"define the\n/// unforgeable regular operations\" and \"... attributes\", called when the\n/// platform object's wrapper is made).\n///\n/// # Errors\n/// What `clazel-js` returns.\npub fn define_unforgeables<P: AllInterfaces>(scope: &mut Scope<'_>, interface: InterfaceId, object: Local<'_>) -> Result<()> {\n    let mut cur = Some(interface);\n    while let Some(i) = cur {\n        match i {\n");
    out.push_str(&unforgeables);
    out.push_str(
        "            _ => {}\n        }\n        cur = i.parent();\n    }\n    Ok(())\n}\n\n",
    );
    out.push_str("/// Installs every exposed interface in the realm (WebIDL §3.7†: an\n/// interface object for each, exposed on the global object, with its\n/// prototype), `DOMException` (`crate::exception`), and makes the global\n/// object the `Window`: its prototype becomes `Window.prototype`, and\n/// `Window`'s members are its own properties ([Global], §3.7.?).\n///\n/// # Errors\n/// What `clazel-js` returns.\npub fn install<P: AllInterfaces>(scope: &mut Scope<'_>, realm: &clazel_js::Realm) -> Result<()> {\n    let global = scope.global(realm)?;\n    let handle = scope.persist(global);\n    scope.host_mut::<P>()?.bindings().global = Some(handle);\n    crate::exception::install::<P>(scope, global)?;\n");
    out.push_str(&install);
    out.push_str("    let window = platform::prototype::<P>(scope, InterfaceId::Window)?;\n    scope.set_prototype_of(global, window)?;\n    define_unforgeables::<P>(scope, InterfaceId::Window, global)?;\n    Ok(())\n}\n");
    out
}

/// The parts of the file, filled one interface at a time.
#[derive(Default)]
struct Out {
    traits: String,
    glue: String,
    install: String,
    unforgeables: String,
}

fn emit_interface(g: &mut Gen<'_>, i: &Interface, ms: &Members, o: &mut Out) {
    let traits = &mut o.traits;
    let glue = &mut o.glue;
    let unforgeables = &mut o.unforgeables;
    let mut member_install = String::new();
    let install = &mut member_install;
    let name = &i.name;
    let sn = snake(name);
    let global = has(&i.ext, "Global");
    // The trait.
    let _ = writeln!(
        traits,
        "/// What the platform implements for `interface {name}{}`. Each method's\n/// default throws a `NotSupportedError`.\npub trait {name}Impl: Platform {{",
        i.parent
            .as_ref()
            .map(|p| format!(" : {p}"))
            .unwrap_or_default()
    );
    let unimpl = |what: &str| format!("Err(platform::not_implemented::<Self>(scope, {}))", q(what));
    for a in &ms.attrs {
        if reflect(g, a).is_some() || event_handler(a).is_some() {
            continue;
        }
        let rt = g.rty(&a.ty);
        let this = if a.is_static {
            String::new()
        } else {
            ", _this: ObjectKey".to_owned()
        };
        let what = format!("{name}.{}", a.name);
        let _ = writeln!(
            traits,
            "    /// The getter of `{}attribute {} {}`.\n    fn {}<'s>(scope: &mut Scope<'s>{this}) -> Result<{rt}> {{\n        {}\n    }}",
            if a.readonly { "readonly " } else { "" },
            idl(&a.ty),
            a.name,
            a.getter,
            unimpl(&what)
        );
        if !a.readonly {
            let _ = writeln!(
                traits,
                "    /// The setter of `attribute {} {}`.\n    fn {}<'s>(scope: &mut Scope<'s>{this}, _value: {rt}) -> Result<()> {{\n        {}\n    }}",
                idl(&a.ty),
                a.name,
                a.setter,
                unimpl(&what)
            );
        }
    }
    for op in &ms.ops {
        for (o, _, method) in &op.overloads {
            let rt = g.rty(&o.ret);
            let ps = if is_long(o, op.is_static) {
                let def = args_struct_def(g, name, o);
                glue.push_str(&def);
                format!(", _args: {}", args_struct(name, o))
            } else {
                params(g, &o.args)
            };
            let this = if op.is_static {
                String::new()
            } else {
                ", _this: ObjectKey".to_owned()
            };
            let _ = writeln!(
                traits,
                "    /// `{}{} {}({})`.\n    fn {method}<'s>(scope: &mut Scope<'s>{this}{ps}) -> Result<{rt}> {{\n        {}\n    }}",
                if op.is_static { "static " } else { "" },
                idl(&o.ret),
                op.name,
                idl_args(&o.args),
                unimpl(&format!("{name}.{}", op.name))
            );
        }
    }
    for (k, args) in ms.ctors.iter().enumerate() {
        let ps = params(g, args);
        let method = if ms.ctors.len() > 1 {
            format!("constructor_{k}")
        } else {
            "constructor".to_owned()
        };
        let _ = writeln!(
            traits,
            "    /// `constructor({})`: the new platform object.\n    fn {method}<'s>(scope: &mut Scope<'s>{ps}) -> Result<ObjectKey> {{\n        {}\n    }}",
            idl_args(args),
            unimpl(&format!("new {name}"))
        );
    }
    if ms.stringifier {
        let _ = writeln!(
            traits,
            "    /// `stringifier;`: the string the object converts to.\n    fn stringify<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {{\n        {}\n    }}",
            unimpl(&format!("{name}.toString"))
        );
    }
    traits.push_str("}\n\n");

    // The glue.
    // Constructor.
    let ctor_fn = format!("ctor_{sn}");
    let _ = writeln!(
        glue,
        "/// The interface object of `{name}`: [[Call]] and [[Construct]] (WebIDL §3.7.1†).\nfn {ctor_fn}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{"
    );
    if ms.ctors.is_empty() || ms.html_constructor {
        // §3.7.1† step "If I was not declared with a constructor operation,
        // then throw a TypeError." [HTMLConstructor] (HTML §3.2.3†) throws
        // too: there are no custom elements, so step 1 ("If NewTarget is
        // the active function object, then throw a TypeError") or the
        // missing definition always applies.
        let _ = writeln!(
            glue,
            "    let _ = args;\n    let _: core::marker::PhantomData<P> = core::marker::PhantomData;\n    Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Illegal constructor\"))\n}}\n"
        );
    } else {
        let _ = writeln!(
            glue,
            "    // §3.7.1† step 1: \"If NewTarget is undefined, then throw a TypeError.\"\n    let Some(new_target) = args.new_target() else {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Constructor {name} requires 'new'\"));\n    }};"
        );
        if ms.ctors.len() == 1 {
            let args0 = ms.ctors.first().cloned().unwrap_or_default();
            let (code, call) = convert_args(g, &args0);
            let req = required(&args0);
            if req > 0 {
                let _ = writeln!(
                    glue,
                    "    if {} {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Failed to construct '{name}': {req} argument(s) required\"));\n    }}",
                    too_few(req)
                );
            }
            let _ = writeln!(
                glue,
                "{code}    let key = <P as {name}Impl>::constructor(scope{call})?;"
            );
        } else {
            let _ = writeln!(
                glue,
                "    let values: Vec<Local<'s>> = (0..args.len()).map(|i| args.get(i)).collect();\n    let key = match overload::resolve::<P>(scope, &CTOR_{}, &values)? {{",
                sn.to_uppercase()
            );
            for (k, a) in ms.ctors.iter().enumerate() {
                let (code, call) = convert_args(g, a);
                let _ = writeln!(
                    glue,
                    "        {k} => {{\n{code}            <P as {name}Impl>::constructor_{k}(scope{call})?\n        }}"
                );
            }
            let _ = writeln!(
                glue,
                "        _ => return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"no overload\")),\n    }};"
            );
            let mut sets = String::new();
            for a in &ms.ctors {
                let _ = write!(
                    sets,
                    "Overload {{ args: &[{}] }}, ",
                    a.iter()
                        .map(|x| format!(
                            "Arg {{ types: {}, optional: {}, variadic: {} }}",
                            g.type_set(&x.ty),
                            x.optional,
                            x.variadic
                        ))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            let _ = writeln!(
                glue,
                "/// The overloads of `{name}`'s constructor.\nstatic CTOR_{}: [Overload; {}] = [{sets}];",
                sn.to_uppercase(),
                ms.ctors.len()
            );
        }
        let _ = writeln!(
            glue,
            "    // \"internally create a new object implementing the interface\" with\n    // the prototype from NewTarget (§3.7.1†, §3.8.1†).\n    let fallback = platform::prototype::<P>(scope, InterfaceId::{name})?;\n    let proto = scope.get_prototype_from_constructor(new_target, fallback)?;\n    let interface = scope.host_mut::<P>()?.interface_of(key).unwrap_or(InterfaceId::{name});\n    platform::wrap_with_prototype::<P>(scope, key, interface, proto)\n}}\n"
        );
    }

    // Attributes.
    for a in &ms.attrs {
        let gname = format!("get_{sn}_{}", snake(&a.name));
        let this = if a.is_static {
            String::new()
        } else {
            format!(
                "    let this = platform::this_object::<P>(scope, args, InterfaceId::{name})?;\n"
            )
        };
        let same = has(&a.ext, "SameObject");
        let key = format!("{name}.{}", a.name);
        let _ = writeln!(
            glue,
            "/// The getter of `{name}.{}` (WebIDL §3.7.5.1†).\nfn {gname}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n{this}",
            a.name
        );
        if !a.is_static {
            glue.push_str("    let _ = &this;\n");
        } else {
            glue.push_str("    let _ = args;\n");
        }
        if same {
            let _ = writeln!(
                glue,
                "    if let Some(v) = platform::same_object::<P>(scope, this, {})? {{\n        return Ok(v);\n    }}",
                q(&key)
            );
        }
        if let Some(event) = event_handler(a) {
            // HTML §8.1.8.1†: the getter returns "the result of getting the
            // current value of the event handler" of that name: null if it
            // has none.
            let _ = writeln!(
                glue,
                "    let r = P::event_handler_get(scope, this, {})?;\n    Ok(match r {{ Some(x) => x, None => scope.null() }})\n}}\n",
                q(&event)
            );
        } else if let Some((content, boolean)) = reflect(g, a) {
            // HTML §2.6.1† "reflect": the getter is the content attribute's
            // value, or the empty string; for a boolean, whether it is there.
            if boolean {
                let _ = writeln!(
                    glue,
                    "    let v = P::reflect_get(scope, this, {})?;\n    Ok(scope.boolean(v.is_some()))\n}}\n",
                    q(&content)
                );
            } else {
                let _ = writeln!(
                    glue,
                    "    let v = P::reflect_get(scope, this, {})?.unwrap_or_default();\n    Ok(scope.string_utf16(&v))\n}}\n",
                    q(&content)
                );
            }
        } else {
            let call = if a.is_static {
                format!("<P as {name}Impl>::{}(scope)?", a.getter)
            } else {
                format!("<P as {name}Impl>::{}(scope, this)?", a.getter)
            };
            let c = g.js_value(&a.ty, "r");
            let _ = writeln!(glue, "    let r = {call};\n    let v = {c};");
            if same {
                let _ = writeln!(
                    glue,
                    "    platform::keep_same_object::<P>(scope, this, {}, v)?;",
                    q(&key)
                );
            }
            glue.push_str("    Ok(v)\n}\n\n");
        }
        // Setter.
        let sname = format!("set_{sn}_{}", snake(&a.name));
        let mut setter = None;
        if !a.readonly {
            let _ = writeln!(
                glue,
                "/// The setter of `{name}.{}` (WebIDL §3.7.5.2†).\nfn {sname}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n{this}    // \"If no arguments were passed, then throw a TypeError.\"\n    if args.is_empty() {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"1 argument required\"));\n    }}",
                a.name
            );
            if let Some(event) = event_handler(a) {
                let _ = writeln!(
                    glue,
                    "    let value = convert::event_handler(scope, args.get(0));\n    P::event_handler_set(scope, this, {}, value)?;",
                    q(&event)
                );
            } else if let Some((content, boolean)) = reflect(g, a) {
                if boolean {
                    let _ = writeln!(
                        glue,
                        "    let v = convert::boolean(scope, args.get(0));\n    let value = if v {{ Some(DomString::new()) }} else {{ None }};\n    P::reflect_set(scope, this, {}, value)?;",
                        q(&content)
                    );
                } else {
                    let c = g.conv(&a.ty, "args.get(0)");
                    let _ = writeln!(
                        glue,
                        "    let value = {c};\n    P::reflect_set(scope, this, {}, Some(value))?;",
                        q(&content)
                    );
                }
            } else {
                let c = g.conv(&a.ty, "v");
                let call = if a.is_static {
                    format!("<P as {name}Impl>::{}(scope, value)?", a.setter)
                } else {
                    format!("<P as {name}Impl>::{}(scope, this, value)?", a.setter)
                };
                let _ = writeln!(
                    glue,
                    "    let v = args.get(0);\n    let value = {c};\n    {call};"
                );
            }
            glue.push_str("    Ok(scope.undefined())\n}\n\n");
            setter = Some(format!("Some(Box::new({sname}::<P>))"));
        } else if let Some(fwd) = ident(&a.ext, "PutForwards") {
            let _ = writeln!(
                glue,
                "/// The setter of `[PutForwards={fwd}] {name}.{}` (WebIDL §3.7.5.2†).\nfn {sname}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n{this}    let _ = this;\n    if args.is_empty() {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"1 argument required\"));\n    }}\n    install::put_forwards(scope, args, {}, {})\n}}\n",
                a.name,
                q(&a.name),
                q(&fwd)
            );
            setter = Some(format!("Some(Box::new({sname}::<P>))"));
        } else if has(&a.ext, "Replaceable") {
            let _ = writeln!(
                glue,
                "/// The setter of `[Replaceable] {name}.{}` (WebIDL §3.7.5.2†).\nfn {sname}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n{this}    let _ = this;\n    if args.is_empty() {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"1 argument required\"));\n    }}\n    install::replace(scope, args, {})\n}}\n",
                a.name,
                q(&a.name)
            );
            setter = Some(format!("Some(Box::new({sname}::<P>))"));
        } else if has(&a.ext, "LegacyLenientSetter") {
            let _ = writeln!(
                glue,
                "/// The setter of `[LegacyLenientSetter] {name}.{}`: does nothing (WebIDL §3.7.5.2†).\nfn {sname}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n    let _ = args;\n    Ok(scope.undefined())\n}}\n",
                a.name
            );
            setter = Some(format!("Some(Box::new({sname}::<P>))"));
        }
        let setter = setter.unwrap_or_else(|| "None".to_owned());
        let unforgeable = unforgeable_attr(i, a);
        let line = format!(
            "install::attribute(scope, {{target}}, {}, {gname}::<P>, {setter}, {unforgeable})?;",
            q(&a.name)
        );
        if unforgeable && !a.is_static {
            let entry = format!(
                "                {};\n",
                line.replace("{target}", "object").trim_end_matches(';')
            );
            push_unforgeable(unforgeables, name, &entry);
        } else {
            let target = if a.is_static {
                "ctor"
            } else if global {
                "global"
            } else {
                "proto"
            };
            let _ = writeln!(install, "    {}", line.replace("{target}", target));
        }
        if a.stringifier {
            // §3.7.? stringifier: "the [[Value]] is a function that ... returns
            // the result of the attribute's getter steps".
            let target = if global { "global" } else { "proto" };
            let l = format!(
                "install::operation(scope, {{target}}, \"toString\", 0, {gname}::<P>, {unforgeable})?;"
            );
            if unforgeable {
                let entry = format!(
                    "                {};\n",
                    l.replace("{target}", "object").trim_end_matches(';')
                );
                push_unforgeable(unforgeables, name, &entry);
            } else {
                let _ = writeln!(install, "    {}", l.replace("{target}", target));
            }
        }
    }
    if ms.stringifier {
        let f = format!("op_{sn}_to_string");
        let _ = writeln!(
            glue,
            "/// `{name}`'s `stringifier;` as `toString` (WebIDL §3.7.?).\nfn {f}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n    let this = platform::this_object::<P>(scope, args, InterfaceId::{name})?;\n    let s = <P as {name}Impl>::stringify(scope, this)?;\n    Ok(scope.string_utf16(&s))\n}}\n"
        );
        let target = if global { "global" } else { "proto" };
        let _ = writeln!(
            install,
            "    install::operation(scope, {target}, \"toString\", 0, {f}::<P>, false)?;"
        );
    }

    // Operations.
    for op in &ms.ops {
        let f = format!(
            "op_{sn}_{}{}",
            if op.is_static { "static_" } else { "" },
            snake(&op.name)
        );
        let len = op
            .overloads
            .iter()
            .map(|(o, _, _)| required(&o.args))
            .min()
            .unwrap_or(0);
        let this = if op.is_static {
            String::new()
        } else {
            format!(
                "    let this = platform::this_object::<P>(scope, args, InterfaceId::{name})?;\n"
            )
        };
        let _ = writeln!(
            glue,
            "/// The operation `{name}.{}` (WebIDL §3.7.6†).\nfn {f}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, args: &Args<'s>) -> Result<Local<'s>> {{\n{this}",
            op.name
        );
        let call_one = |g: &mut Gen<'_>, o: &Operation, method: &str, indent: &str| -> String {
            let (code, mut call) = convert_args(g, &o.args);
            if is_long(o, op.is_static) {
                let fields = o
                    .args
                    .iter()
                    .enumerate()
                    .map(|(k, a)| format!("{}: a{k}", snake(&a.name)))
                    .collect::<Vec<_>>()
                    .join(", ");
                call = format!(", {} {{ {fields} }}", args_struct(name, o));
            }
            let this_arg = if op.is_static {
                String::new()
            } else {
                ", this".to_owned()
            };
            let ret = g.resolve(&o.ret);
            let mut s = String::new();
            for l in code.lines() {
                let _ = writeln!(s, "{indent}{l}");
            }
            if matches!(ret.kind, TyKind::Simple(Simple::Undefined)) {
                let _ = writeln!(
                    s,
                    "{indent}    <P as {name}Impl>::{method}(scope{this_arg}{call})?;\n{indent}    Ok(scope.undefined())"
                );
            } else {
                let c = g.js_value(&o.ret, "r");
                let _ = writeln!(
                    s,
                    "{indent}    let r = <P as {name}Impl>::{method}(scope{this_arg}{call})?;\n{indent}    let v = {c};\n{indent}    Ok(v)"
                );
            }
            s
        };
        if let [(o, _, method)] = op.overloads.as_slice() {
            let req = required(&o.args);
            if req > 0 {
                let _ = writeln!(
                    glue,
                    "    if {} {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Failed to execute '{}' on '{name}': {req} argument(s) required\"));\n    }}",
                    too_few(req),
                    op.name
                );
            }
            let body = call_one(g, o, method, "");
            glue.push_str(&body);
            glue.push_str("}\n\n");
        } else {
            let st = format!(
                "OVERLOADS_{}_{}",
                sn.to_uppercase(),
                snake(&op.name).to_uppercase()
            );
            let _ = writeln!(
                glue,
                "    let values: Vec<Local<'s>> = (0..args.len()).map(|i| args.get(i)).collect();\n    match overload::resolve::<P>(scope, &{st}, &values)? {{"
            );
            for (k, (o, _, method)) in op.overloads.iter().enumerate() {
                let body = call_one(g, o, method, "    ");
                let _ = writeln!(glue, "        {k} => {{\n{body}        }}");
            }
            glue.push_str("        _ => Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"no overload\")),\n    }\n}\n\n");
            let mut sets = String::new();
            for (o, _, _) in &op.overloads {
                let _ = write!(
                    sets,
                    "Overload {{ args: &[{}] }}, ",
                    o.args
                        .iter()
                        .map(|x| format!(
                            "Arg {{ types: {}, optional: {}, variadic: {} }}",
                            g.type_set(&x.ty),
                            x.optional,
                            x.variadic
                        ))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            let _ = writeln!(
                glue,
                "/// The overloads of `{name}.{}`.\nstatic {st}: [Overload; {}] = [{sets}];\n",
                op.name,
                op.overloads.len()
            );
        }
        let target = if op.is_static {
            "ctor"
        } else if global {
            "global"
        } else {
            "proto"
        };
        let line = format!(
            "install::operation(scope, {{target}}, {}, {len}, {f}::<P>, {})?;",
            q(&op.name),
            op.unforgeable
        );
        if op.unforgeable && !op.is_static {
            let entry = format!(
                "                {};\n",
                line.replace("{target}", "object").trim_end_matches(';')
            );
            push_unforgeable(unforgeables, name, &entry);
        } else {
            let _ = writeln!(install, "    {}", line.replace("{target}", target));
        }
    }

    // Install: prepended (interface object and prototype first).
    let len = ms.ctors.iter().map(|a| required(a)).min().unwrap_or(0);
    let parent = match &i.parent {
        Some(p) => format!(
            "    let parent_ctor = scope.host_mut::<P>()?.bindings().interface_objects.get(&InterfaceId::{p}).cloned();\n    let parent_ctor = match parent_ctor {{ Some(h) => Some(scope.local(&h)?), None => None }};\n    let parent_proto = Some(platform::prototype::<P>(scope, InterfaceId::{p})?);\n"
        ),
        None => "    let parent_ctor: Option<Local<'_>> = None;\n    let parent_proto: Option<Local<'_>> = None;\n".to_owned(),
    };
    let mut head = format!(
        "    // `interface {name}` (WebIDL §3.7.1† interface object, §3.7.3† interface\n    // prototype object).\n    {{\n{parent}    let ctor = install::interface_object(scope, {}, {len}, parent_ctor, {ctor_fn}::<P>)?;\n    let proto = scope.new_object()?;\n    if let Some(pp) = parent_proto {{\n        scope.set_prototype_of(proto, pp)?;\n    }}\n    install::link(scope, ctor, proto)?;\n    let h = scope.persist(proto);\n    scope.host_mut::<P>()?.bindings().prototypes.insert(InterfaceId::{name}, h);\n    let h = scope.persist(ctor);\n    scope.host_mut::<P>()?.bindings().interface_objects.insert(InterfaceId::{name}, h);\n    let _ = (&ctor, &proto, &global);\n",
        q(name)
    );
    for (c, v) in &ms.consts {
        let _ = writeln!(
            head,
            "    let c = {};\n    install::constant(scope, &[ctor, proto], {}, c)?;",
            literal_js(v),
            q(c)
        );
    }
    let body = std::mem::take(install);
    for l in body.lines() {
        let _ = writeln!(head, "    {l}");
    }
    let _ = writeln!(
        head,
        "    install::expose(scope, global, {}, ctor)?;\n    }}",
        q(name)
    );
    o.install.push_str(&head);
}

fn push_unforgeable(buf: &mut String, iface: &str, entry: &str) {
    let marker = format!("            InterfaceId::{iface} => {{\n");
    if let Some(pos) = buf.find(&marker) {
        buf.insert_str(pos.saturating_add(marker.len()), entry);
    } else {
        buf.push_str(&marker);
        buf.push_str(entry);
        buf.push_str("            }\n");
    }
}

fn emit_enum(g: &Gen<'_>, name: &str, out: &mut String) {
    let Some(e) = g.m.enums.iter().find(|e| e.name == name) else {
        return;
    };
    let _ = writeln!(
        out,
        "/// `enum {name}` (WebIDL §3.2.19†).\n#[derive(Clone, Copy, Debug, PartialEq, Eq)]\npub enum {name} {{"
    );
    for v in &e.values {
        let _ = writeln!(out, "    /// {}.\n    {},", q(v), pascal(v));
    }
    let _ = writeln!(
        out,
        "}}\n\nimpl {name} {{\n    /// The value as the IDL spells it.\n    #[must_use]\n    pub fn as_str(self) -> &'static str {{\n        match self {{"
    );
    for v in &e.values {
        let _ = writeln!(out, "            {name}::{} => {},", pascal(v), q(v));
    }
    let _ = writeln!(out, "        }}\n    }}\n}}\n");
    if !g.enums_read.contains(name) {
        return;
    }
    let _ = writeln!(
        out,
        "/// §3.2.19† enumeration: \"Let S be the result of calling ? ToString(V). If\n/// S is not one of E's enumeration values, then throw a TypeError.\"\nfn enum_{}(scope: &mut Scope<'_>, v: Local<'_>) -> Result<{name}> {{\n    let s = convert::dom_string(scope, v, false)?;",
        snake(name)
    );
    for val in &e.values {
        let _ = writeln!(
            out,
            "    if {}.encode_utf16().eq(s.iter().copied()) {{\n        return Ok({name}::{});\n    }}",
            q(val),
            pascal(val)
        );
    }
    let _ = writeln!(
        out,
        "    Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Value is not a valid {name}\"))\n}}\n"
    );
}

fn emit_dictionary(g: &mut Gen<'_>, name: &str, out: &mut String) {
    let Some(d) = g.m.dictionaries.iter().find(|d| d.name == name) else {
        return;
    };
    // Record members dropped for their types.
    let mut cur = Some(d.name.clone());
    while let Some(c) = cur {
        let Some(dd) = g.m.dictionaries.iter().find(|x| x.name == c) else {
            break;
        };
        for m in &dd.members {
            if let Some(why) = g.unsupported(&m.ty) {
                let what = format!("{}.{}", dd.name, m.name);
                if !g.dropped_dict_members.iter().any(|s| s.what == what) {
                    g.dropped_dict_members.push(Skip { what, why });
                }
            }
        }
        cur = dd.parent.clone();
    }
    let members = g.dict_members(name);
    let lt = members.iter().any(|(_, m)| g.needs_lt(&m.ty));
    let generics = if lt { "<'s>" } else { "" };
    let _ = writeln!(
        out,
        "/// `dictionary {name}`{} (WebIDL §3.2.18†), with its ancestors' members.\n#[derive(Clone, Debug)]\npub struct {name}{generics} {{",
        d.parent
            .as_ref()
            .map(|p| format!(" : {p}"))
            .unwrap_or_default()
    );
    let mut fields = Vec::new();
    for (_, m) in &members {
        let t = g.rty(&m.ty);
        let t = if m.default.is_some() || m.required {
            t
        } else {
            format!("Option<{t}>")
        };
        let _ = writeln!(
            out,
            "    /// `{}{} {}{}`.\n    pub {}: {t},",
            if m.required { "required " } else { "" },
            idl(&m.ty),
            m.name,
            if m.default.is_some() { " = ..." } else { "" },
            snake(&m.name)
        );
        fields.push(snake(&m.name));
    }
    if members.is_empty() {
        let _ = writeln!(
            out,
            "    /// Nothing the bindings can read.\n    pub empty: (),"
        );
    }
    out.push_str("}\n\n");
    let _ = writeln!(
        out,
        "/// ES to `{name}` (WebIDL §3.2.18†):\n/// 1. If Type(V) is not Undefined, Null or Object, then throw a TypeError.\n/// 3. For each dictionary dictionary in dictionaries (least derived first),\n///    each member in lexicographic order: if V is undefined or null, let\n///    esMemberValue be undefined, otherwise ? Get(V, key). If it is not\n///    undefined, convert it; else if the member has a default value, use it;\n///    else if the member is required, throw a TypeError.\nfn dict_{}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, v: Local<'s>) -> Result<{name}{generics}> {{\n    let _: core::marker::PhantomData<P> = core::marker::PhantomData;\n    let nullish = convert::is_nullish(scope, v);\n    if !nullish && !convert::is_object(scope, v) {{\n        return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Value is not a {name} dictionary\"));\n    }}",
        snake(name)
    );
    for (_, m) in &members {
        let f = snake(&m.name);
        let c = g.conv(&m.ty, "m");
        let missing = if let Some(dv) = &m.default {
            g.default_value(&m.ty, dv)
        } else if m.required {
            format!(
                "return Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"{name}.{} is required\"))",
                m.name
            )
        } else {
            "None".to_owned()
        };
        let present = if m.default.is_some() || m.required {
            c
        } else {
            format!("Some({c})")
        };
        let _ = writeln!(
            out,
            "    let m = if nullish {{ scope.undefined() }} else {{ scope.get(v, Key::Str({})) ? }};\n    let {f} = if scope.kind(m) == ValueKind::Undefined {{ {missing} }} else {{ {present} }};",
            q(&m.name)
        );
    }
    if members.is_empty() {
        let _ = writeln!(out, "    Ok({name} {{ empty: () }})\n}}\n");
    } else {
        let _ = writeln!(out, "    Ok({name} {{ {} }})\n}}\n", fields.join(", "));
    }
}

fn emit_union(g: &mut Gen<'_>, name: &str, out: &mut String) {
    let Some((flat, _)) = g.unions.get(name).cloned() else {
        return;
    };
    let lt = flat.iter().any(|t| g.needs_lt(t));
    let generics = if lt { "<'s>" } else { "" };
    let _ = writeln!(
        out,
        "/// The union `({})` (WebIDL §2.13.?, flattened).\n#[derive(Clone, Debug)]\npub enum {name}{generics} {{",
        flat.iter().map(idl).collect::<Vec<_>>().join(" or ")
    );
    for t in &flat {
        let rt = g.rty(t);
        let _ = writeln!(out, "    /// `{}`.\n    {}({rt}),", idl(t), g.type_label(t));
    }
    out.push_str("}\n\n");
    let resolved: Vec<Ty> = flat.iter().map(|t| g.resolve(t)).collect();
    let find = |pred: &dyn Fn(&Ty) -> bool| resolved.iter().find(|t| pred(t)).cloned();
    let kind_of = |t: &Ty| match &t.kind {
        TyKind::Named(n) => g.named_kind(n),
        _ => None,
    };
    let dict = find(&|t| kind_of(t) == Some(NamedKind::Dictionary));
    let interfaces: Vec<Ty> = resolved
        .iter()
        .filter(|t| kind_of(t) == Some(NamedKind::Interface))
        .cloned()
        .collect();
    let object = find(&|t| matches!(t.kind, TyKind::Simple(Simple::Object)));
    let callback_fn = find(&|t| kind_of(t) == Some(NamedKind::CallbackFunction));
    let callback_iface = find(&|t| kind_of(t) == Some(NamedKind::CallbackInterface));
    let sequence = find(&|t| matches!(t.kind, TyKind::Sequence(_) | TyKind::FrozenArray(_)));
    let boolean = find(&|t| matches!(t.kind, TyKind::Simple(Simple::Boolean)));
    let numeric = find(
        &|t| matches!(t.kind, TyKind::Simple(s) if !matches!(s, Simple::Boolean | Simple::Any | Simple::Object | Simple::Undefined | Simple::ByteString | Simple::DomString | Simple::UsvString | Simple::Bigint | Simple::Symbol)),
    );
    let string = find(&|t| {
        matches!(
            t.kind,
            TyKind::Simple(Simple::ByteString | Simple::DomString | Simple::UsvString)
        ) || kind_of(t) == Some(NamedKind::Enum)
    });
    let any = find(&|t| matches!(t.kind, TyKind::Simple(Simple::Any)));
    let _ = writeln!(
        out,
        "/// ES to the union (WebIDL §3.2.24†), in the standard's order of steps.\nfn union_{}<'s, P: AllInterfaces>(scope: &mut Scope<'s>, v: Local<'s>) -> Result<{name}{generics}> {{\n    let _: core::marker::PhantomData<P> = core::marker::PhantomData;\n    let is_object = convert::is_object(scope, v);\n    let _ = is_object;",
        snake(name)
    );
    let arm = |g: &mut Gen<'_>, t: &Ty| -> String {
        let c = g.conv(t, "v");
        format!("return Ok({name}::{}({c}));", g.type_label(t))
    };
    if let Some(t) = &dict {
        let a = arm(g, t);
        let _ = writeln!(
            out,
            "    // Step 4: null or undefined, and a dictionary type.\n    if convert::is_nullish(scope, v) {{\n        {a}\n    }}"
        );
    }
    if !interfaces.is_empty() {
        out.push_str("    // Step 5: a platform object.\n");
        for t in &interfaces {
            let TyKind::Named(n) = &t.kind else { continue };
            let label = g.type_label(t);
            let _ = writeln!(
                out,
                "    if is_object && let Some(k) = platform::implements::<P>(scope, v, InterfaceId::{n})? {{\n        return Ok({name}::{label}(k));\n    }}"
            );
        }
    }
    if let Some(t) = &callback_fn {
        let a = arm(g, t);
        let _ = writeln!(
            out,
            "    // Step 10: callable.\n    if scope.is_callable(v) {{\n        {a}\n    }}"
        );
    }
    let mut obj_arms = String::new();
    if let Some(t) = &sequence {
        let a = arm(g, t);
        let _ = writeln!(
            obj_arms,
            "        if scope.is_array(v)? {{\n            {a}\n        }}"
        );
    }
    // Step 11.3: a dictionary or callback interface type; 11.4: object.
    if let Some(t) = dict
        .as_ref()
        .or(callback_iface.as_ref())
        .or(object.as_ref())
    {
        let a = arm(g, t);
        let _ = writeln!(obj_arms, "        {a}");
    }
    if !obj_arms.is_empty() {
        let _ = writeln!(
            out,
            "    // Step 11: an object.\n    if is_object {{\n{obj_arms}    }}"
        );
    }
    if let Some(t) = &boolean {
        let a = arm(g, t);
        let _ = writeln!(
            out,
            "    // Step 12: a Boolean.\n    if scope.kind(v) == ValueKind::Boolean {{\n        {a}\n    }}"
        );
    }
    if let Some(t) = &numeric {
        let a = arm(g, t);
        let _ = writeln!(
            out,
            "    // Step 13: a Number.\n    if scope.kind(v) == ValueKind::Number {{\n        {a}\n    }}"
        );
    }
    // Steps 15, 16 and 18: a string type, else a numeric type, else boolean.
    if let Some(t) = string
        .as_ref()
        .or(numeric.as_ref())
        .or(boolean.as_ref())
        .or(any.as_ref())
    {
        let a = arm(g, t);
        let a = a.trim_start_matches("return ").trim_end_matches(';');
        let _ = writeln!(out, "    {a}");
        out.push_str("}\n\n");
    } else {
        let _ = writeln!(
            out,
            "    // Step 19.\n    Err(scope.throw_error(clazel_js::ErrorKind::TypeError, \"Value is not of any of the union's types\"))\n}}\n"
        );
    }
}

/// The check that fewer than `req` arguments were passed.
fn too_few(req: usize) -> String {
    if req == 1 {
        "args.is_empty()".to_owned()
    } else {
        format!("args.len() < {req}")
    }
}
