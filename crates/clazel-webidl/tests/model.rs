//! Tests of the generated interface model (`src/generated/`) against facts of
//! the standards, which these tests state independently of the generator.

use clazel_webidl::generated::{
    CALLBACKS, DICTIONARIES, ENUMS, EXTERNAL, FOREIGN_INCLUDES, INTERFACES, NAMESPACES, TYPEDEFS,
};
use clazel_webidl::model::{
    Argument, ExtAttr, ExtValue, Simple, Type, TypeRef, Value, callback, dictionary, enumeration,
    ext_attr, interface, namespace, typedef,
};

type T = Result<(), String>;

fn need<X>(o: Option<X>, what: &str) -> Result<X, String> {
    o.ok_or_else(|| format!("missing {what}"))
}

fn check(cond: bool, msg: &str) -> T {
    if cond { Ok(()) } else { Err(msg.to_owned()) }
}

fn sorted_and_unique(names: Vec<&str>) -> bool {
    names.windows(2).all(|w| match w {
        [a, b] => a < b,
        _ => true,
    })
}

/// The counts the PR reports; a change to the vendored IDL or to the
/// generator changes them, and this test is where that is noticed.
#[test]
fn counts() -> T {
    check(INTERFACES.len() == 233, "interfaces")?;
    check(
        INTERFACES.iter().filter(|i| i.callback).count() == 3,
        "callback interfaces",
    )?;
    check(NAMESPACES.len() == 1, "namespaces")?;
    check(DICTIONARIES.len() == 73, "dictionaries")?;
    check(
        DICTIONARIES.iter().map(|d| d.members.len()).sum::<usize>() == 210,
        "dictionary members",
    )?;
    check(ENUMS.len() == 45, "enums")?;
    check(
        ENUMS.iter().map(|e| e.values.len()).sum::<usize>() == 173,
        "enum values",
    )?;
    check(TYPEDEFS.len() == 22, "typedefs")?;
    check(CALLBACKS.len() == 10, "callbacks")?;
    check(EXTERNAL.len() == 37, "external names")?;
    check(
        INTERFACES.iter().map(|i| i.attributes.len()).sum::<usize>()
            == 1512 - namespace_members()?.0,
        "attributes",
    )?;
    check(
        INTERFACES.iter().map(|i| i.operations.len()).sum::<usize>()
            == 731 - namespace_members()?.1,
        "operations",
    )?;
    check(
        INTERFACES.iter().map(|i| i.constants.len()).sum::<usize>() == 89 - namespace_members()?.2,
        "constants",
    )?;
    check(
        INTERFACES
            .iter()
            .map(|i| i.constructors.len())
            .sum::<usize>()
            == 131,
        "constructors",
    )?;
    check(
        INTERFACES.iter().filter(|i| i.iterable.is_some()).count() == 5,
        "iterables",
    )?;
    check(
        INTERFACES.iter().filter(|i| i.collection.is_some()).count() == 1,
        "maplike and setlike",
    )?;
    check(
        FOREIGN_INCLUDES.len() == 2,
        "includes of foreign interfaces",
    )
}

/// Attributes, operations and constants of the namespaces.
fn namespace_members() -> Result<(usize, usize, usize), String> {
    Ok((
        NAMESPACES.iter().map(|n| n.attributes.len()).sum(),
        NAMESPACES.iter().map(|n| n.operations.len()).sum(),
        NAMESPACES.iter().map(|n| n.constants.len()).sum(),
    ))
}

#[test]
fn tables_are_sorted_so_lookups_can_bisect() -> T {
    check(
        sorted_and_unique(INTERFACES.iter().map(|i| i.name).collect()),
        "interfaces",
    )?;
    check(
        sorted_and_unique(NAMESPACES.iter().map(|i| i.name).collect()),
        "namespaces",
    )?;
    check(
        sorted_and_unique(DICTIONARIES.iter().map(|i| i.name).collect()),
        "dictionaries",
    )?;
    check(
        sorted_and_unique(ENUMS.iter().map(|i| i.name).collect()),
        "enums",
    )?;
    check(
        sorted_and_unique(TYPEDEFS.iter().map(|i| i.name).collect()),
        "typedefs",
    )?;
    check(
        sorted_and_unique(CALLBACKS.iter().map(|i| i.name).collect()),
        "callbacks",
    )?;
    check(
        sorted_and_unique(EXTERNAL.iter().map(|i| i.name).collect()),
        "external",
    )?;
    for i in INTERFACES {
        check(interface(i.name).is_some_and(|f| f.name == i.name), i.name)?;
    }
    check(interface("NoSuchInterface").is_none(), "absent name")
}

struct Names;

impl Names {
    fn defined(name: &str) -> bool {
        interface(name).is_some()
            || dictionary(name).is_some()
            || enumeration(name).is_some()
            || typedef(name).is_some()
            || callback(name).is_some()
            || EXTERNAL.iter().any(|e| e.name == name)
    }
}

fn walk_ext(attrs: &[ExtAttr], bad: &mut Vec<String>) {
    for a in attrs {
        match a.value {
            ExtValue::Args(args) | ExtValue::NamedArgs(_, args) => walk_args(args, bad),
            _ => {}
        }
    }
}

fn walk_args(args: &[Argument], bad: &mut Vec<String>) {
    for a in args {
        walk_ext(a.ext_attrs, bad);
        walk_ty(&a.ty, bad);
    }
}

fn walk_ty(t: &TypeRef, bad: &mut Vec<String>) {
    walk_ext(t.ext_attrs, bad);
    match t.ty {
        Type::Simple(_) | Type::Buffer(_) => {}
        Type::Named(n) => {
            if !Names::defined(n) {
                bad.push(n.to_owned());
            }
        }
        Type::Sequence(i) | Type::FrozenArray(i) | Type::ObservableArray(i) | Type::Promise(i) => {
            walk_ty(i, bad);
        }
        Type::Record(k, v) => {
            walk_ty(k, bad);
            walk_ty(v, bad);
        }
        Type::Union(members) => members.iter().for_each(|m| walk_ty(m, bad)),
    }
}

/// Every name the model uses resolves inside the model or is external,
/// checked here over the generated data and not over the parser's output.
#[test]
fn every_reference_resolves() -> T {
    let mut bad = Vec::new();
    for i in INTERFACES {
        if let Some(p) = i.parent {
            let defined = interface(p).is_some_and(|p| !p.callback);
            check(
                defined || EXTERNAL.iter().any(|e| e.name == p),
                &format!("{}: parent {p}", i.name),
            )?;
        }
        walk_ext(i.ext_attrs, &mut bad);
        for c in i.constructors {
            walk_args(c.args, &mut bad);
        }
        for a in i.attributes {
            walk_ty(&a.ty, &mut bad);
            walk_ext(a.ext_attrs, &mut bad);
        }
        for o in i.operations {
            walk_ty(&o.ret, &mut bad);
            walk_args(o.args, &mut bad);
            walk_ext(o.ext_attrs, &mut bad);
        }
        for c in i.constants {
            walk_ty(&c.ty, &mut bad);
        }
        if let Some(it) = i.iterable {
            it.key
                .iter()
                .chain([&it.value])
                .for_each(|t| walk_ty(t, &mut bad));
        }
        if let Some(c) = i.collection {
            c.key
                .iter()
                .chain([&c.value])
                .for_each(|t| walk_ty(t, &mut bad));
        }
    }
    for d in DICTIONARIES {
        if let Some(p) = d.parent {
            let defined = dictionary(p).is_some();
            check(
                defined || EXTERNAL.iter().any(|e| e.name == p),
                &format!("{}: parent {p}", d.name),
            )?;
        }
        for m in d.members {
            walk_ty(&m.ty, &mut bad);
        }
    }
    for t in TYPEDEFS {
        walk_ty(&t.ty, &mut bad);
    }
    for c in CALLBACKS {
        walk_ty(&c.ret, &mut bad);
        walk_args(c.args, &mut bad);
    }
    for n in NAMESPACES {
        for o in n.operations {
            walk_ty(&o.ret, &mut bad);
            walk_args(o.args, &mut bad);
        }
    }
    check(bad.is_empty(), &format!("unresolved: {bad:?}"))
}

#[test]
fn includes_name_a_mixin_with_members_or_an_external_one() -> T {
    for i in INTERFACES {
        for m in i.includes {
            let has_members = i
                .attributes
                .iter()
                .map(|a| a.mixin)
                .chain(i.operations.iter().map(|o| o.mixin))
                .chain(i.constants.iter().map(|c| c.mixin))
                .any(|x| x == Some(*m));
            check(
                has_members || EXTERNAL.iter().any(|e| e.name == *m),
                &format!("{} includes {m}", i.name),
            )?;
        }
        // A member marked with a mixin names one the interface includes.
        for mixin in i
            .attributes
            .iter()
            .filter_map(|a| a.mixin)
            .chain(i.operations.iter().filter_map(|o| o.mixin))
        {
            check(i.includes.contains(&mixin), &format!("{}: {mixin}", i.name))?;
        }
    }
    Ok(())
}

#[test]
fn inheritance_and_mixins() -> T {
    let node = need(interface("Node"), "Node")?;
    check(node.parent == Some("EventTarget"), "Node : EventTarget")?;
    let element = need(interface("Element"), "Element")?;
    check(element.parent == Some("Node"), "Element : Node")?;
    for m in [
        "ParentNode",
        "ChildNode",
        "NonDocumentTypeChildNode",
        "Slottable",
    ] {
        check(element.includes.contains(&m), m)?;
    }
    let append = need(
        element.operations.iter().find(|o| o.name == Some("append")),
        "Element.append",
    )?;
    check(
        append.mixin == Some("ParentNode"),
        "append comes from ParentNode",
    )?;
    check(
        append.args.len() == 1 && append.args.iter().all(|a| a.variadic),
        "append(...nodes)",
    )?;
    // The mixin's own [CEReactions, Unscopable] are the member's.
    check(
        ext_attr(append.ext_attrs, "CEReactions").is_some(),
        "append is [CEReactions]",
    )?;
    check(
        ext_attr(append.ext_attrs, "Unscopable").is_some(),
        "append is [Unscopable]",
    )?;
    let event_target = need(interface("EventTarget"), "EventTarget")?;
    check(
        event_target.parent.is_none() && event_target.constructors.len() == 1,
        "EventTarget()",
    )
}

#[test]
fn partial_interfaces_from_several_files_are_merged() -> T {
    let window = need(interface("Window"), "Window")?;
    let has = |n: &str| {
        window.attributes.iter().any(|a| a.name == n)
            || window.operations.iter().any(|o| o.name == Some(n))
    };
    // dom.idl (partial interface Window), cssom.idl and html.idl.
    check(has("event"), "Window.event (DOM)")?;
    check(has("getComputedStyle"), "Window.getComputedStyle (CSSOM)")?;
    check(has("document"), "Window.document (HTML)")?;
    check(
        window.includes.contains(&"GlobalEventHandlers"),
        "Window includes GlobalEventHandlers",
    )?;
    // `[Replaceable]` of `Window.event` (dom.idl) is the member's own.
    let event = need(
        window.attributes.iter().find(|a| a.name == "event"),
        "event",
    )?;
    check(
        ext_attr(event.ext_attrs, "Replaceable").is_some(),
        "[Replaceable] event",
    )
}

#[test]
fn extended_attributes_item_7_12_lists() -> T {
    let event = need(interface("Event"), "Event")?;
    let is_trusted = need(
        event.attributes.iter().find(|a| a.name == "isTrusted"),
        "isTrusted",
    )?;
    check(
        ext_attr(is_trusted.ext_attrs, "LegacyUnforgeable").is_some(),
        "[LegacyUnforgeable]",
    )?;
    let document = need(interface("Document"), "Document")?;
    let implementation = need(
        document
            .attributes
            .iter()
            .find(|a| a.name == "implementation"),
        "Document.implementation",
    )?;
    check(
        ext_attr(implementation.ext_attrs, "SameObject").is_some(),
        "[SameObject]",
    )?;
    let window = need(interface("Window"), "Window")?;
    let location = need(
        window.attributes.iter().find(|a| a.name == "location"),
        "Window.location",
    )?;
    check(
        ext_attr(location.ext_attrs, "PutForwards").map(|a| a.value)
            == Some(ExtValue::Ident("href")),
        "[PutForwards=href]",
    )?;
    let collection = need(interface("HTMLCollection"), "HTMLCollection")?;
    check(
        ext_attr(collection.ext_attrs, "LegacyUnenumerableNamedProperties").is_some(),
        "[LegacyUnenumerableNamedProperties]",
    )?;
    check(
        ext_attr(collection.ext_attrs, "Exposed").map(|a| a.value)
            == Some(ExtValue::Ident("Window")),
        "[Exposed=Window]",
    )
}

#[test]
fn types_and_defaults() -> T {
    let ctor = need(interface("Event"), "Event")?
        .constructors
        .first()
        .copied();
    let ctor = need(ctor, "Event()")?;
    check(ctor.args.len() == 2, "Event(type, eventInitDict)")?;
    let init = need(ctor.args.get(1), "eventInitDict")?;
    check(
        init.optional && init.default == Some(Value::EmptyDictionary),
        "optional EventInit = {}",
    )?;
    check(init.ty.ty == Type::Named("EventInit"), "EventInit")?;
    let event_init = need(dictionary("EventInit"), "EventInit")?;
    check(event_init.members.len() == 3, "EventInit has 3 members")?;
    check(
        event_init
            .members
            .iter()
            .all(|m| m.default == Some(Value::Bool(false))),
        "every EventInit member defaults to false",
    )?;
    let custom = need(dictionary("CustomEventInit"), "CustomEventInit")?;
    check(
        custom.parent == Some("EventInit"),
        "CustomEventInit : EventInit",
    )?;
    let detail = need(custom.members.first(), "detail")?;
    check(
        detail.default == Some(Value::Null) && detail.ty.ty == Type::Simple(Simple::Any),
        "any detail = null",
    )?;
    // A required member, and a nullable union.
    let init = need(dictionary("ShadowRootInit"), "ShadowRootInit")?;
    check(
        init.members.iter().any(|m| m.name == "mode" && m.required),
        "required mode",
    )?;
    let el = need(interface("Element"), "Element")?;
    let get = need(
        el.operations
            .iter()
            .find(|o| o.name == Some("getAttribute")),
        "getAttribute",
    )?;
    check(
        get.ret.nullable && get.ret.ty == Type::Simple(Simple::DomString),
        "DOMString? getAttribute",
    )
}

#[test]
fn enums_callbacks_typedefs_namespaces_and_iterables() -> T {
    let mode = need(enumeration("ShadowRootMode"), "ShadowRootMode")?;
    check(mode.values == ["open", "closed"], "ShadowRootMode values")?;
    let listener = need(interface("EventListener"), "EventListener")?;
    check(
        listener.callback && listener.operations.len() == 1,
        "callback interface EventListener",
    )?;
    let cb = need(callback("EventHandlerNonNull"), "EventHandlerNonNull")?;
    check(
        cb.ret.ty == Type::Simple(Simple::Any),
        "EventHandlerNonNull returns any",
    )?;
    check(typedef("EventHandler").is_some(), "typedef EventHandler")?;
    check(
        namespace("CSS").is_some_and(|n| n.operations.iter().any(|o| o.name == Some("escape"))),
        "namespace CSS",
    )?;
    let params = need(interface("URLSearchParams"), "URLSearchParams")?;
    let it = need(params.iterable, "URLSearchParams iterable")?;
    check(
        !it.is_async && it.key.is_some(),
        "iterable<USVString, USVString>",
    )
}
