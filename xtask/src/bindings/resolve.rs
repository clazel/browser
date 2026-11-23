//! Resolution: merge the definitions of every file into one model.
//!
//! WebIDL §2.5 (the semantics of partials and `includes`), as far as the
//! model needs:
//! - **Partial interfaces, dictionaries and namespaces** (WebIDL §2.2
//!   "Interfaces", "Dictionaries", "Namespaces"): the members of each
//!   `partial` are appended to its target. A target defined nowhere is an
//!   error.
//! - **`includes`** (WebIDL §2.2 "Interface mixins", "Includes
//!   statements"): `A includes M;` appends the members of mixin `M` (its own
//!   and those of its partials) to `A`, each marked with the mixin's name.
//!
//! Modelling choices:
//! - Files are read in the order given (sorted by name by the caller), the
//!   definitions of a file in source order. An interface's members are its
//!   own, then those of its partials in the order the partials appear, then
//!   those of the mixins in the order the `includes` statements appear.
//! - Extended attributes `Exposed` and `SecureContext` written on a partial
//!   interface or a mixin (or a partial of one) apply to the members it
//!   adds (WebIDL §3.3.1 `[Exposed]` and HTML's `[SecureContext]` on partials
//!   and mixins), so each such member gets a copy unless it has its own.
//!   No other extended attribute of a partial or mixin is passed on, and
//!   the extended attributes of a partial are not merged into its target's.
//! - Every definition is in one namespace: an interface, namespace,
//!   dictionary, enum, typedef, callback or mixin name is defined once.
//! - A reference to a name no file defines is an error unless it is listed
//!   in [`EXTERNAL`], the types the vendored files refer to and other
//!   standards define (each with the standard that does).
//! - Interfaces, dictionaries, enums and the rest are sorted by name in the
//!   output, so lookups can bisect and a reordering of the input files
//!   changes nothing.

use std::collections::{BTreeMap, BTreeSet};

use super::model::{
    Argument, Attribute, Const, Definition, DictMember, ExtAttr, ExtValue, Iterable, Member,
    MemberKind, Operation, Ty, TyKind,
};

/// Names the vendored IDL refers to and defines nowhere in it, sorted, each
/// with the standard that defines it (its IDL is not vendored; see `SOURCE.md`
/// of `tests/data/webref-idl/`). The generated model records them as external
/// and gives them no definition. A reference to any other undefined name is an
/// error.
pub const EXTERNAL: &[(&str, &str)] = &[
    ("ARIAMixin", "WAI-ARIA (an interface mixin)"),
    ("Blob", "File API"),
    ("BufferSource", "WebIDL"),
    ("CSSMarginDescriptors", "CSS Paged Media"),
    (
        "CSSOMString",
        "CSSOM (an implementation-defined string type: DOMString or USVString)",
    ),
    ("DOMException", "WebIDL"),
    ("DOMHighResTimeStamp", "High Resolution Time"),
    ("DOMMatrix", "Geometry Interfaces"),
    ("DOMMatrix2DInit", "Geometry Interfaces"),
    ("DOMPointInit", "Geometry Interfaces"),
    ("File", "File API"),
    ("FileList", "File API"),
    ("Function", "WebIDL"),
    ("GPUCanvasContext", "WebGPU"),
    ("MathMLElement", "MathML Core"),
    ("MediaSource", "Media Source Extensions"),
    ("MediaStream", "Media Capture and Streams"),
    ("PerformanceEntry", "Performance Timeline"),
    ("QuotaExceededError", "WebIDL"),
    ("ReadableStream", "Streams"),
    ("ReferrerPolicy", "Referrer Policy"),
    ("SVGElement", "SVG 2"),
    ("SVGImageElement", "SVG 2"),
    ("SVGScriptElement", "SVG 2"),
    ("ServiceWorker", "Service Workers"),
    ("TrustedHTML", "Trusted Types"),
    ("TrustedHTMLParserOptions", "Trusted Types"),
    ("TrustedScript", "Trusted Types"),
    ("TrustedScriptURL", "Trusted Types"),
    ("TrustedType", "Trusted Types"),
    ("VideoFrame", "WebCodecs"),
    ("ViewTransition", "CSS View Transitions"),
    ("VoidFunction", "WebIDL"),
    ("WebGL2RenderingContext", "WebGL"),
    ("WebGLRenderingContext", "WebGL"),
    (
        "WindowProxy",
        "HTML (WindowProxy is defined in prose, not in `html.idl`)",
    ),
    ("WritableStream", "Streams"),
];

/// The extended attributes a partial interface or a mixin passes on to the
/// members it adds.
const PASSED_ON: &[&str] = &["Exposed", "SecureContext"];

/// A resolved interface.
#[derive(Debug, Clone, PartialEq)]
pub struct Interface {
    /// Its name.
    pub name: String,
    /// What it inherits from.
    pub parent: Option<String>,
    /// `callback interface`.
    pub callback: bool,
    /// Its own extended attributes.
    pub ext: Vec<ExtAttr>,
    /// The mixins it includes, in order.
    pub includes: Vec<String>,
    /// Members: own, partials', then mixins'.
    pub members: Vec<Member>,
}

/// A resolved namespace.
#[derive(Debug, Clone, PartialEq)]
pub struct Namespace {
    /// Its name.
    pub name: String,
    /// Its extended attributes.
    pub ext: Vec<ExtAttr>,
    /// Members: own, then partials'.
    pub members: Vec<Member>,
}

/// A resolved dictionary.
#[derive(Debug, Clone, PartialEq)]
pub struct Dictionary {
    /// Its name.
    pub name: String,
    /// What it inherits from.
    pub parent: Option<String>,
    /// Its extended attributes.
    pub ext: Vec<ExtAttr>,
    /// Members: own, then partials'.
    pub members: Vec<DictMember>,
}

/// An enum.
#[derive(Debug, Clone, PartialEq)]
pub struct Enum {
    /// Its name.
    pub name: String,
    /// Its extended attributes.
    pub ext: Vec<ExtAttr>,
    /// Its values.
    pub values: Vec<String>,
}

/// A typedef.
#[derive(Debug, Clone, PartialEq)]
pub struct Typedef {
    /// Its name.
    pub name: String,
    /// Its extended attributes.
    pub ext: Vec<ExtAttr>,
    /// The type it names.
    pub ty: Ty,
}

/// A callback function type.
#[derive(Debug, Clone, PartialEq)]
pub struct Callback {
    /// Its name.
    pub name: String,
    /// Its extended attributes.
    pub ext: Vec<ExtAttr>,
    /// Its return type.
    pub ret: Ty,
    /// Its arguments.
    pub args: Vec<Argument>,
}

/// The resolved model of all the files.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Model {
    /// Interfaces and callback interfaces, sorted by name.
    pub interfaces: Vec<Interface>,
    /// Namespaces, sorted by name.
    pub namespaces: Vec<Namespace>,
    /// Dictionaries, sorted by name.
    pub dictionaries: Vec<Dictionary>,
    /// Enums, sorted by name.
    pub enums: Vec<Enum>,
    /// Typedefs, sorted by name.
    pub typedefs: Vec<Typedef>,
    /// Callbacks, sorted by name.
    pub callbacks: Vec<Callback>,
    /// How many mixins there were (they are resolved into their includers).
    pub mixins: usize,
    /// The external names that are referenced, sorted.
    pub external: Vec<String>,
    /// `includes` statements whose interface another standard defines
    /// (`EXTERNAL`), as (interface, mixin), in order.
    pub foreign_includes: Vec<(String, String)>,
}

/// What a name defines, for the single namespace of definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Interface,
    Mixin,
    Namespace,
    Dictionary,
    Enum,
    Typedef,
    Callback,
}

struct Mixin {
    ext_members: Vec<Member>,
}

/// Merge `files` (name and definitions of each, in order) into a model.
pub fn resolve(files: &[(String, Vec<Definition>)]) -> Result<Model, String> {
    let mut kinds: BTreeMap<String, (Kind, &str)> = BTreeMap::new();
    // First pass: the one non-partial definition of each name.
    for (file, defs) in files {
        for d in defs {
            let (name, kind) = match d {
                Definition::Interface {
                    name,
                    partial: false,
                    ..
                } => (name, Kind::Interface),
                Definition::Mixin {
                    name,
                    partial: false,
                    ..
                } => (name, Kind::Mixin),
                Definition::Namespace {
                    name,
                    partial: false,
                    ..
                } => (name, Kind::Namespace),
                Definition::Dictionary {
                    name,
                    partial: false,
                    ..
                } => (name, Kind::Dictionary),
                Definition::Enum { name, .. } => (name, Kind::Enum),
                Definition::Typedef { name, .. } => (name, Kind::Typedef),
                Definition::Callback { name, .. } => (name, Kind::Callback),
                _ => continue,
            };
            if let Some((_, other)) = kinds.insert(name.clone(), (kind, file.as_str())) {
                return Err(format!("{name} is defined in both {other} and {file}"));
            }
        }
    }
    let kind_of = |name: &str| kinds.get(name).map(|(k, _)| *k);

    let mut interfaces: BTreeMap<String, Interface> = BTreeMap::new();
    let mut mixins: BTreeMap<String, Mixin> = BTreeMap::new();
    let mut namespaces: BTreeMap<String, Namespace> = BTreeMap::new();
    let mut dictionaries: BTreeMap<String, Dictionary> = BTreeMap::new();
    let mut model = Model::default();
    let mut foreign_mixins: BTreeSet<String> = BTreeSet::new();
    // Partials are applied in file order after every main definition exists.
    let mut includes: Vec<(&str, &str, &str)> = Vec::new();
    for (file, defs) in files {
        for d in defs {
            match d {
                Definition::Interface {
                    ext,
                    name,
                    parent,
                    partial: false,
                    callback,
                    members,
                } => {
                    interfaces.insert(
                        name.clone(),
                        Interface {
                            name: name.clone(),
                            parent: parent.clone(),
                            callback: *callback,
                            ext: ext.clone(),
                            includes: Vec::new(),
                            members: members.clone(),
                        },
                    );
                }
                Definition::Mixin {
                    name,
                    partial: false,
                    ext,
                    members,
                } => {
                    mixins.insert(
                        name.clone(),
                        Mixin {
                            ext_members: passing_on(ext, members),
                        },
                    );
                }
                Definition::Namespace {
                    name,
                    partial: false,
                    ext,
                    members,
                } => {
                    namespaces.insert(
                        name.clone(),
                        Namespace {
                            name: name.clone(),
                            ext: ext.clone(),
                            members: members.clone(),
                        },
                    );
                }
                Definition::Dictionary {
                    name,
                    partial: false,
                    ext,
                    parent,
                    members,
                } => {
                    dictionaries.insert(
                        name.clone(),
                        Dictionary {
                            name: name.clone(),
                            parent: parent.clone(),
                            ext: ext.clone(),
                            members: members.clone(),
                        },
                    );
                }
                Definition::Enum { ext, name, values } => model.enums.push(Enum {
                    name: name.clone(),
                    ext: ext.clone(),
                    values: values.clone(),
                }),
                Definition::Typedef { ext, name, ty } => model.typedefs.push(Typedef {
                    name: name.clone(),
                    ext: ext.clone(),
                    ty: ty.clone(),
                }),
                Definition::Callback {
                    ext,
                    name,
                    ret,
                    args,
                } => model.callbacks.push(Callback {
                    name: name.clone(),
                    ext: ext.clone(),
                    ret: ret.clone(),
                    args: args.clone(),
                }),
                Definition::Includes { target, mixin } => {
                    includes.push((file.as_str(), target.as_str(), mixin.as_str()));
                }
                _ => {}
            }
        }
    }
    // Partials.
    for (file, defs) in files {
        for d in defs {
            match d {
                Definition::Interface {
                    name,
                    ext,
                    partial: true,
                    members,
                    ..
                } => {
                    let target = interfaces.get_mut(name).ok_or_else(|| {
                        format!("{file}: partial interface {name} has no interface")
                    })?;
                    target.members.extend(passing_on(ext, members));
                }
                Definition::Mixin {
                    name,
                    ext,
                    partial: true,
                    members,
                } => {
                    let target = mixins.get_mut(name).ok_or_else(|| {
                        format!("{file}: partial interface mixin {name} has no mixin")
                    })?;
                    target.ext_members.extend(passing_on(ext, members));
                }
                Definition::Namespace {
                    name,
                    ext,
                    partial: true,
                    members,
                } => {
                    let target = namespaces.get_mut(name).ok_or_else(|| {
                        format!("{file}: partial namespace {name} has no namespace")
                    })?;
                    target.members.extend(passing_on(ext, members));
                }
                Definition::Dictionary {
                    name,
                    partial: true,
                    members,
                    ..
                } => {
                    let target = dictionaries.get_mut(name).ok_or_else(|| {
                        format!("{file}: partial dictionary {name} has no dictionary")
                    })?;
                    target.members.extend(members.iter().cloned());
                }
                _ => {}
            }
        }
    }
    // Includes.
    for (file, target, mixin) in includes {
        let external_mixin = kind_of(mixin).is_none() && EXTERNAL.iter().any(|(n, _)| *n == mixin);
        if kind_of(mixin) != Some(Kind::Mixin) && !external_mixin {
            return Err(format!(
                "{file}: {target} includes {mixin}, which is not an interface mixin"
            ));
        }
        let Some(iface) = interfaces.get_mut(target) else {
            // An interface of another standard: the statement is recorded,
            // its members are not (the interface is not in the model).
            if EXTERNAL.iter().any(|(n, _)| *n == target) {
                model
                    .foreign_includes
                    .push((target.to_owned(), mixin.to_owned()));
                continue;
            }
            return Err(format!(
                "{file}: {target} includes {mixin}, but {target} is not an interface"
            ));
        };
        if iface.includes.iter().any(|m| m == mixin) {
            return Err(format!("{file}: {target} includes {mixin} twice"));
        }
        iface.includes.push(mixin.to_owned());
    }
    for iface in interfaces.values_mut() {
        for m in iface.includes.clone() {
            if let Some(mixin) = mixins.get(&m) {
                for member in &mixin.ext_members {
                    let mut member = member.clone();
                    member.mixin = Some(m.clone());
                    iface.members.push(member);
                }
            }
        }
    }
    // Mixins of other standards that an interface includes: the name is
    // kept in `includes`, and counted as a used external name.
    for iface in interfaces.values() {
        for m in &iface.includes {
            if !mixins.contains_key(m) {
                foreign_mixins.insert(m.clone());
            }
        }
    }
    model.mixins = mixins.len();
    model.interfaces = interfaces.into_values().collect();
    model.namespaces = namespaces.into_values().collect();
    model.dictionaries = dictionaries.into_values().collect();
    model.enums.sort_by(|a, b| a.name.cmp(&b.name));
    model.typedefs.sort_by(|a, b| a.name.cmp(&b.name));
    model.callbacks.sort_by(|a, b| a.name.cmp(&b.name));
    check_unique_members(&model)?;
    check_references(&mut model, foreign_mixins, &|n| {
        kind_of(n).is_some_and(|k| k != Kind::Mixin)
    })?;
    Ok(model)
}

/// `members`, each with a copy of the [`PASSED_ON`] attributes of `ext`
/// that it lacks.
fn passing_on(ext: &[ExtAttr], members: &[Member]) -> Vec<Member> {
    members
        .iter()
        .map(|m| {
            let mut m = m.clone();
            for a in ext.iter().filter(|a| PASSED_ON.contains(&a.name.as_str())) {
                if !m.ext.iter().any(|b| b.name == a.name) {
                    m.ext.push(a.clone());
                }
            }
            m
        })
        .collect()
}

/// The name a member is known by, for duplicate checks of attributes and
/// constants (operations overload, so repeat freely).
fn unique_name(m: &Member) -> Option<(&'static str, &str)> {
    match &m.kind {
        MemberKind::Const(c) => Some(("constant", c.name.as_str())),
        MemberKind::Attribute(a) => Some(("attribute", a.name.as_str())),
        _ => None,
    }
}

fn check_unique_members(model: &Model) -> Result<(), String> {
    for i in &model.interfaces {
        let mut seen = BTreeSet::new();
        let mut statics = BTreeSet::new();
        for m in &i.members {
            if let Some((what, name)) = unique_name(m) {
                let is_static = matches!(&m.kind, MemberKind::Attribute(a) if a.is_static);
                let set = if is_static { &mut statics } else { &mut seen };
                if !set.insert(name) {
                    return Err(format!(
                        "interface {}: {what} {name} is defined twice",
                        i.name
                    ));
                }
            }
        }
    }
    for i in &model.interfaces {
        // WebIDL: at most one of iterable, async iterable, maplike, setlike.
        let declarations = i
            .members
            .iter()
            .filter(|m| matches!(m.kind, MemberKind::Iterable(_) | MemberKind::Collection(_)))
            .count();
        if declarations > 1 {
            return Err(format!(
                "interface {}: more than one of iterable, maplike and setlike",
                i.name
            ));
        }
    }
    for d in &model.dictionaries {
        let mut seen = BTreeSet::new();
        for m in &d.members {
            if !seen.insert(m.name.as_str()) {
                return Err(format!(
                    "dictionary {}: member {} is defined twice",
                    d.name, m.name
                ));
            }
        }
    }
    Ok(())
}

/// Every `Named` type, parent and `includes` target resolves, or is
/// external; collects the external names used.
fn check_references(
    model: &mut Model,
    foreign_mixins: BTreeSet<String>,
    defined: &dyn Fn(&str) -> bool,
) -> Result<(), String> {
    let mut used_external = foreign_mixins;
    let mut missing: BTreeSet<String> = BTreeSet::new();
    for (target, _) in &model.foreign_includes {
        used_external.insert(target.clone());
    }
    let mut check = |name: &str, whence: &str| -> Result<(), String> {
        if defined(name) {
            return Ok(());
        }
        if EXTERNAL.iter().any(|(n, _)| *n == name) {
            used_external.insert(name.to_owned());
            return Ok(());
        }
        missing.insert(format!("{name} (first in {whence})"));
        Ok(())
    };
    for i in &model.interfaces {
        let whence = format!("interface {}", i.name);
        if let Some(p) = &i.parent {
            check(p, &whence)?;
        }
        walk_ext(&i.ext, &whence, &mut check)?;
        for m in &i.members {
            walk_member(m, &whence, &mut check)?;
        }
    }
    for n in &model.namespaces {
        let whence = format!("namespace {}", n.name);
        walk_ext(&n.ext, &whence, &mut check)?;
        for m in &n.members {
            walk_member(m, &whence, &mut check)?;
        }
    }
    for d in &model.dictionaries {
        let whence = format!("dictionary {}", d.name);
        if let Some(p) = &d.parent {
            check(p, &whence)?;
        }
        walk_ext(&d.ext, &whence, &mut check)?;
        for m in &d.members {
            walk_ext(&m.ext, &whence, &mut check)?;
            walk_ty(&m.ty, &whence, &mut check)?;
        }
    }
    for t in &model.typedefs {
        let whence = format!("typedef {}", t.name);
        walk_ext(&t.ext, &whence, &mut check)?;
        walk_ty(&t.ty, &whence, &mut check)?;
    }
    for c in &model.callbacks {
        let whence = format!("callback {}", c.name);
        walk_ext(&c.ext, &whence, &mut check)?;
        walk_ty(&c.ret, &whence, &mut check)?;
        walk_args(&c.args, &whence, &mut check)?;
    }
    for e in &model.enums {
        walk_ext(&e.ext, &format!("enum {}", e.name), &mut check)?;
    }
    if !missing.is_empty() {
        return Err(format!(
            "names no vendored file defines and EXTERNAL does not list: {}",
            missing.into_iter().collect::<Vec<_>>().join("; ")
        ));
    }
    model.external = used_external.into_iter().collect();
    Ok(())
}

type Check<'a> = dyn FnMut(&str, &str) -> Result<(), String> + 'a;

fn walk_ty(ty: &Ty, whence: &str, check: &mut Check<'_>) -> Result<(), String> {
    walk_ext(&ty.ext, whence, check)?;
    match &ty.kind {
        TyKind::Simple(_) | TyKind::Buffer(_) => Ok(()),
        TyKind::Named(n) => check(n, whence),
        TyKind::Sequence(t)
        | TyKind::FrozenArray(t)
        | TyKind::ObservableArray(t)
        | TyKind::Promise(t) => walk_ty(t, whence, check),
        TyKind::Record(k, v) => {
            walk_ty(k, whence, check)?;
            walk_ty(v, whence, check)
        }
        TyKind::Union(ts) => ts.iter().try_for_each(|t| walk_ty(t, whence, check)),
    }
}

fn walk_args(args: &[Argument], whence: &str, check: &mut Check<'_>) -> Result<(), String> {
    for a in args {
        walk_ext(&a.ext, whence, check)?;
        walk_ty(&a.ty, whence, check)?;
    }
    Ok(())
}

fn walk_ext(ext: &[ExtAttr], whence: &str, check: &mut Check<'_>) -> Result<(), String> {
    for a in ext {
        match &a.value {
            ExtValue::Args(args) | ExtValue::NamedArgs(_, args) => walk_args(args, whence, check)?,
            _ => {}
        }
    }
    Ok(())
}

fn walk_member(m: &Member, whence: &str, check: &mut Check<'_>) -> Result<(), String> {
    walk_ext(&m.ext, whence, check)?;
    match &m.kind {
        MemberKind::Const(Const { ty, .. }) | MemberKind::Attribute(Attribute { ty, .. }) => {
            walk_ty(ty, whence, check)
        }
        MemberKind::Operation(Operation { ret, args, .. }) => {
            walk_ty(ret, whence, check)?;
            walk_args(args, whence, check)
        }
        MemberKind::Constructor(args) => walk_args(args, whence, check),
        MemberKind::Iterable(Iterable {
            key, value, args, ..
        }) => {
            if let Some(k) = key {
                walk_ty(k, whence, check)?;
            }
            walk_ty(value, whence, check)?;
            walk_args(args, whence, check)
        }
        MemberKind::Collection(c) => {
            if let Some(k) = &c.key {
                walk_ty(k, whence, check)?;
            }
            walk_ty(&c.value, whence, check)
        }
    }
}
