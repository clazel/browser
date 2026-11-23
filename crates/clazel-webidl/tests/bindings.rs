//! The generated bindings over a small platform (item 7.12): interface
//! objects and prototypes as WebIDL §3.7† lays them out (the checks WPT's
//! `idlharness.js` makes), `DOMException`, the conversions of §3.2†,
//! overload resolution, wrappers, `[LegacyUnforgeable]`, `[SameObject]`,
//! `[PutForwards]` and `[Replaceable]`.
//!
//! `clazel-web` implements the platform for real (its `tests/bindings.rs`);
//! the platform here keeps a handful of `Event`s and `Location`s so that the
//! glue itself is tested without a document.

use std::collections::HashMap;

use clazel_js::{
    Config, Error, Handle, Host, Key, Limits, Realm, RealmOptions, Result, Runtime, Scope, Source,
};
use clazel_webidl::convert::{self, DomString, IntegerFlags};
use clazel_webidl::generated::bindings::*;
use clazel_webidl::platform::{Bindings, ObjectKey, Platform};

const WINDOW: ObjectKey = ObjectKey(0);

/// A platform with events (`EventTarget` and `Event`) and locations.
#[derive(Default)]
struct Mock {
    bindings: Bindings,
    wrappers: HashMap<ObjectKey, Handle>,
    objects: HashMap<ObjectKey, (InterfaceId, Vec<u16>)>,
    next: u64,
    log: Vec<String>,
}

impl Host for Mock {
    fn random_u64(&mut self) -> u64 {
        4
    }
}

impl Platform for Mock {
    fn interface_of(&mut self, key: ObjectKey) -> Option<InterfaceId> {
        if key == WINDOW {
            return Some(InterfaceId::Window);
        }
        self.objects.get(&key).map(|o| o.0)
    }
    fn wrapper(&mut self, key: ObjectKey) -> Option<Handle> {
        self.wrappers.get(&key).cloned()
    }
    fn set_wrapper(&mut self, key: ObjectKey, wrapper: Handle) {
        self.wrappers.insert(key, wrapper);
    }
    fn window_key(&self) -> ObjectKey {
        WINDOW
    }
    fn bindings(&mut self) -> &mut Bindings {
        &mut self.bindings
    }
    fn reflect_get(_: &mut Scope<'_>, _: ObjectKey, _: &str) -> Result<Option<DomString>> {
        Ok(None)
    }
    fn reflect_set(_: &mut Scope<'_>, _: ObjectKey, _: &str, _: Option<DomString>) -> Result<()> {
        Ok(())
    }
}

fn new_object(scope: &mut Scope<'_>, iface: InterfaceId, text: &str) -> Result<ObjectKey> {
    let m = scope.host_mut::<Mock>()?;
    m.next = m.next.saturating_add(1);
    let key = ObjectKey(m.next);
    m.objects
        .insert(key, (iface, text.encode_utf16().collect()));
    Ok(key)
}

fn text(scope: &mut Scope<'_>, key: ObjectKey) -> Result<DomString> {
    Ok(scope
        .host_mut::<Mock>()?
        .objects
        .get(&key)
        .map(|o| o.1.clone())
        .unwrap_or_default())
}

impl EventTargetImpl for Mock {
    fn constructor<'s>(scope: &mut Scope<'s>) -> Result<ObjectKey> {
        new_object(scope, InterfaceId::EventTarget, "")
    }
}

impl EventImpl for Mock {
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: EventInit,
    ) -> Result<ObjectKey> {
        let s = String::from_utf16_lossy(&type_);
        let k = new_object(scope, InterfaceId::Event, &s)?;
        scope
            .host_mut::<Mock>()?
            .log
            .push(format!("bubbles={}", init.bubbles));
        Ok(k)
    }
    fn type_<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        text(scope, this)
    }
    fn is_trusted<'s>(_: &mut Scope<'s>, _: ObjectKey) -> Result<bool> {
        Ok(false)
    }
    fn composed_path<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Vec<ObjectKey>> {
        let _ = scope;
        Ok(vec![this])
    }
    fn time_stamp<'s>(_: &mut Scope<'s>, _: ObjectKey) -> Result<f64> {
        Ok(1.5)
    }
}

impl LocationImpl for Mock {
    fn href<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<String> {
        Ok(String::from_utf16_lossy(&text(scope, this)?))
    }
    fn set_href<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: String) -> Result<()> {
        if let Some(o) = scope.host_mut::<Mock>()?.objects.get_mut(&this) {
            o.1 = value.encode_utf16().collect();
        }
        Ok(())
    }
}

impl WindowImpl for Mock {
    fn location<'s>(scope: &mut Scope<'s>, _: ObjectKey) -> Result<ObjectKey> {
        let existing = scope
            .host_mut::<Mock>()?
            .objects
            .iter()
            .find(|(_, o)| o.0 == InterfaceId::Location)
            .map(|(k, _)| *k);
        match existing {
            Some(k) => Ok(k),
            None => new_object(scope, InterfaceId::Location, "about:blank"),
        }
    }
    fn name<'s>(_: &mut Scope<'s>, _: ObjectKey) -> Result<DomString> {
        Ok("w".encode_utf16().collect())
    }
    fn self_<'s>(_: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        Ok(this)
    }
    fn window<'s>(_: &mut Scope<'s>, this: ObjectKey) -> Result<ObjectKey> {
        Ok(this)
    }
    fn btoa<'s>(_: &mut Scope<'s>, _: ObjectKey, data: DomString) -> Result<DomString> {
        Ok(data)
    }
    fn alert_0<'s>(scope: &mut Scope<'s>, _: ObjectKey) -> Result<()> {
        scope.host_mut::<Mock>()?.log.push("alert()".into());
        Ok(())
    }
    fn alert_1<'s>(scope: &mut Scope<'s>, _: ObjectKey, message: DomString) -> Result<()> {
        let m = String::from_utf16_lossy(&message);
        scope.host_mut::<Mock>()?.log.push(format!("alert({m})"));
        Ok(())
    }
}

impl AbortSignalImpl for Mock {}
impl AbortControllerImpl for Mock {}
impl CustomEventImpl for Mock {}
impl NodeImpl for Mock {}
impl DocumentImpl for Mock {}
impl DocumentTypeImpl for Mock {}
impl DocumentFragmentImpl for Mock {}
impl CharacterDataImpl for Mock {}
impl TextImpl for Mock {}
impl CommentImpl for Mock {}
impl ElementImpl for Mock {}
impl HTMLElementImpl for Mock {}
impl HTMLUnknownElementImpl for Mock {}
impl HTMLHtmlElementImpl for Mock {}
impl HTMLHeadElementImpl for Mock {}
impl HTMLTitleElementImpl for Mock {}
impl HTMLBodyElementImpl for Mock {}
impl HTMLDivElementImpl for Mock {}
impl HTMLSpanElementImpl for Mock {}
impl HTMLParagraphElementImpl for Mock {}
impl HTMLAnchorElementImpl for Mock {}
impl NodeListImpl for Mock {}
impl HTMLCollectionImpl for Mock {}
impl DOMTokenListImpl for Mock {}
impl HistoryImpl for Mock {}
impl NavigatorImpl for Mock {}

type Test = core::result::Result<(), Error>;

fn setup() -> Result<(Runtime, Realm)> {
    let mut rt = Runtime::new(Config::new(Limits::unlimited()), Mock::default())?;
    let realm = rt.scope(|scope| {
        let realm = scope.create_realm(RealmOptions::default())?;
        install::<Mock>(scope, &realm)?;
        Ok(realm)
    })?;
    Ok((rt, realm))
}

/// Runs `script` and returns the global `r` as a string.
fn run(rt: &mut Runtime, realm: &Realm, script: &str) -> Result<String> {
    rt.scope(|scope| {
        if let Err(Error::Thrown(e)) = scope.eval_script(realm, Source::new("test.js", script)) {
            let report = scope.report(&e)?;
            return Err(Error::WrongType(Box::leak(
                format!("uncaught {report:?}").into_boxed_str(),
            )));
        }
        let g = scope.global(realm)?;
        let r = scope.get(g, Key::Str("r"))?;
        let s = scope.to_string(r)?;
        scope.string_to_string_lossy(s)
    })
}

#[test]
fn interface_objects_and_prototypes() -> Test {
    let (mut rt, realm) = setup()?;
    // §3.7.1†: a function with name and length, `prototype` not writable,
    // enumerable or configurable; [[Prototype]] the parent's interface object.
    let r = run(
        &mut rt,
        &realm,
        "var r = [typeof Node, Node.name, Event.length, Object.getPrototypeOf(Element) === Node,\n\
         Object.getPrototypeOf(Node.prototype) === EventTarget.prototype,\n\
         Node.prototype.constructor === Node, Element.prototype instanceof Node].join(',');",
    )?;
    assert_eq!(r, "function,Node,1,true,true,true,true");
    rt.scope(|scope| {
        let g = scope.global(&realm)?;
        let node = scope.get(g, Key::Str("Node"))?;
        let d = scope
            .get_own_property(node, Key::Str("prototype"))?
            .ok_or(Error::WrongType("prototype"))?;
        assert_eq!(
            (d.writable, d.enumerable, d.configurable),
            (Some(false), Some(false), Some(false))
        );
        // §3.7†: the interface object is a non-enumerable property of the global.
        let d = scope
            .get_own_property(g, Key::Str("Node"))?
            .ok_or(Error::WrongType("Node"))?;
        assert_eq!(
            (d.writable, d.enumerable, d.configurable),
            (Some(true), Some(false), Some(true))
        );
        // §3.7.4†: constants on both, read-only and enumerable.
        let proto = scope.get(node, Key::Str("prototype"))?;
        for o in [node, proto] {
            let d = scope
                .get_own_property(o, Key::Str("ELEMENT_NODE"))?
                .ok_or(Error::WrongType("const"))?;
            assert_eq!(
                (d.writable, d.enumerable, d.configurable),
                (Some(false), Some(true), Some(false))
            );
            let v = d.value.ok_or(Error::WrongType("value"))?;
            assert_eq!(scope.as_number(v), Some(1.0));
        }
        // §3.7.5†: an attribute is an accessor on the prototype, enumerable
        // and configurable, with a getter named "get nodeType".
        let d = scope
            .get_own_property(proto, Key::Str("nodeType"))?
            .ok_or(Error::WrongType("attr"))?;
        assert_eq!((d.enumerable, d.configurable), (Some(true), Some(true)));
        let getter = d.get.ok_or(Error::WrongType("getter"))?;
        let name = scope.get(getter, Key::Str("name"))?;
        assert_eq!(scope.string_to_string_lossy(name)?, "get nodeType");
        // readonly: no setter.
        let set = d.set.ok_or(Error::WrongType("set"))?;
        assert_eq!(scope.kind(set), clazel_js::ValueKind::Undefined);
        // §3.7.6†: an operation is a writable, enumerable, configurable data
        // property, with length its required argument count.
        let d = scope
            .get_own_property(proto, Key::Str("appendChild"))?
            .ok_or(Error::WrongType("op"))?;
        assert_eq!(
            (d.writable, d.enumerable, d.configurable),
            (Some(true), Some(true), Some(true))
        );
        let f = d.value.ok_or(Error::WrongType("fn"))?;
        let len = scope.get(f, Key::Str("length"))?;
        assert_eq!(scope.as_number(len), Some(1.0));
        Ok(())
    })
}

#[test]
fn constructors_and_illegal_constructors() -> Test {
    let (mut rt, realm) = setup()?;
    let r = run(
        &mut rt,
        &realm,
        "var r = '';\n\
         try { Node(); } catch (e) { r += e.name; }\n\
         try { new Node(); } catch (e) { r += ',' + e.name; }\n\
         try { Event('x'); } catch (e) { r += ',' + e.name; }\n\
         try { new HTMLElement(); } catch (e) { r += ',' + e.name; }\n\
         var t = new EventTarget(); r += ',' + (t instanceof EventTarget);\n\
         var ev = new Event('click', { bubbles: true }); r += ',' + ev.type + ',' + (ev instanceof Event);\n\
         try { new Event(); } catch (e) { r += ',' + e.name; }",
    )?;
    assert_eq!(
        r,
        "TypeError,TypeError,TypeError,TypeError,true,click,true,TypeError"
    );
    let log = rt.scope(|scope| Ok(scope.host_mut::<Mock>()?.log.clone()))?;
    assert_eq!(log, vec!["bubbles=true".to_owned()]);
    Ok(())
}

#[test]
fn brand_checks() -> Test {
    let (mut rt, realm) = setup()?;
    // §3.7.5.1† step 1.2: a getter on the wrong object is a TypeError.
    let r = run(
        &mut rt,
        &realm,
        "var r = '';\n\
         var get = Object.getOwnPropertyDescriptor;\n\
         var ev = new Event('a');\n\
         try { Event.prototype.type; } catch (e) { r += e.name; }\n\
         var o = Object.create(Event.prototype);\n\
         try { o.type; } catch (e) { r += ',' + e.name; }\n\
         try { Event.prototype.stopPropagation.call({}); } catch (e) { r += ',' + e.name; }\n\
         r += ',' + ev.type;",
    )?;
    assert_eq!(r, "TypeError,TypeError,TypeError,a");
    Ok(())
}

#[test]
fn one_wrapper_per_object_and_unforgeable() -> Test {
    let (mut rt, realm) = setup()?;
    // The same platform object gives the same wrapper; Location's members are
    // [LegacyUnforgeable]: own, non-configurable properties of each wrapper.
    let r = run(
        &mut rt,
        &realm,
        "var a = window.location, b = location;\n\
         a.expando = 1;\n\
         var d = Object.getOwnPropertyDescriptor ? 0 : 0;\n\
         var r = [a === b, b.expando, a.hasOwnProperty('href'), 'href' in Location.prototype,\n\
         a.href, String(a)].join(',');",
    )?;
    assert_eq!(r, "true,1,true,false,about:blank,about:blank");
    rt.scope(|scope| {
        let g = scope.global(&realm)?;
        let loc = scope.get(g, Key::Str("location"))?;
        let d = scope
            .get_own_property(loc, Key::Str("href"))?
            .ok_or(Error::WrongType("href"))?;
        assert_eq!(d.configurable, Some(false));
        // Window's own [LegacyUnforgeable] location is on the global itself.
        let d = scope
            .get_own_property(g, Key::Str("location"))?
            .ok_or(Error::WrongType("location"))?;
        assert_eq!(d.configurable, Some(false));
        Ok(())
    })
}

#[test]
fn put_forwards_and_replaceable() -> Test {
    let (mut rt, realm) = setup()?;
    // [PutForwards=href] on Window.location: assigning sets location.href.
    // [Replaceable] on Window.self: assigning shadows it.
    let r = run(
        &mut rt,
        &realm,
        "location = 'https://example.org/';\n\
         var r = location.href;\n\
         var s1 = self === window;\n\
         self = 5;\n\
         r += ',' + s1 + ',' + self;",
    )?;
    assert_eq!(r, "https://example.org/,true,5");
    Ok(())
}

#[test]
fn global_members_and_overloads() -> Test {
    let (mut rt, realm) = setup()?;
    // Window is [Global]: its operations are own properties of the global,
    // and `this` undefined means the global (§3.7.6† step 2.1.2).
    let r = run(
        &mut rt,
        &realm,
        "alert(); alert('hi'); var f = alert; f('x');\n\
         var r = [name, window.name, globalThis.hasOwnProperty('alert'),\n\
         Object.getPrototypeOf(globalThis) === Window.prototype,\n\
         window instanceof EventTarget].join(',');",
    )?;
    assert_eq!(r, "w,w,true,true,true");
    let log = rt.scope(|scope| Ok(scope.host_mut::<Mock>()?.log.clone()))?;
    assert_eq!(
        log,
        vec![
            "alert()".to_owned(),
            "alert(hi)".to_owned(),
            "alert(x)".to_owned()
        ]
    );
    Ok(())
}

#[test]
fn dom_exception() -> Test {
    let (mut rt, realm) = setup()?;
    // WebIDL §4.3†, the checks of WPT's webidl/ecmascript-binding/es-exceptions
    // (DOMException-constants.any.js, DOMException-constructor-behavior.any.js).
    let r = run(
        &mut rt,
        &realm,
        "var e = new DOMException('msg', 'NotFoundError');\n\
         var d = new DOMException();\n\
         var r = [e.name, e.message, e.code, d.name, d.message, d.code,\n\
         DOMException.NOT_FOUND_ERR, DOMException.prototype.DATA_CLONE_ERR,\n\
         e instanceof DOMException, e instanceof Error, String(e),\n\
         new DOMException('', 'IndexSizeError').code, new DOMException('', 'Foo').code].join(',');",
    )?;
    assert_eq!(
        r,
        "NotFoundError,msg,8,Error,,0,8,25,true,true,NotFoundError: msg,1,0"
    );
    // NotSupportedError from a member the platform does not implement.
    let r = run(
        &mut rt,
        &realm,
        "var r; try { new EventTarget().addEventListener('x', null); } catch (e) { r = e.name + ':' + e.code + ':' + (e instanceof DOMException); }",
    )?;
    assert_eq!(r, "NotSupportedError:9:true");
    Ok(())
}

#[test]
fn conversions() -> Test {
    let (mut rt, _realm) = setup()?;
    rt.scope(|scope| {
        let flags = IntegerFlags::default();
        let enforce = IntegerFlags {
            enforce_range: true,
            clamp: false,
        };
        let clamp = IntegerFlags {
            enforce_range: false,
            clamp: true,
        };
        // §3.2.4.9† ConvertToInt: modulo, then signed wrap.
        let v = scope.number(4_294_967_297.0);
        assert_eq!(convert::long(scope, v, flags)?, 1);
        let v = scope.number(2_147_483_648.0);
        assert_eq!(convert::long(scope, v, flags)?, -2_147_483_648);
        let v = scope.number(-1.0);
        assert_eq!(convert::unsigned_short(scope, v, flags)?, 65535);
        let v = scope.number(3.9);
        assert_eq!(convert::octet(scope, v, flags)?, 3);
        let v = scope.number(f64::NAN);
        assert_eq!(convert::long(scope, v, flags)?, 0);
        // [EnforceRange]: out of range and non-finite throw.
        let v = scope.number(256.0);
        assert!(convert::octet(scope, v, enforce).is_err());
        let v = scope.number(f64::INFINITY);
        assert!(convert::long(scope, v, enforce).is_err());
        // [Clamp]: round half to even within the bounds.
        let v = scope.number(300.0);
        assert_eq!(convert::octet(scope, v, clamp)?, 255);
        let v = scope.number(2.5);
        assert_eq!(convert::octet(scope, v, clamp)?, 2);
        let v = scope.number(3.5);
        assert_eq!(convert::octet(scope, v, clamp)?, 4);
        // long long: 2^53 range.
        let v = scope.number(-9_007_199_254_740_991.0);
        assert_eq!(convert::long_long(scope, v, flags)?, -9_007_199_254_740_991);
        // double rejects NaN; unrestricted double keeps it.
        let v = scope.number(f64::NAN);
        assert!(convert::double(scope, v, false).is_err());
        assert!(convert::double(scope, v, true)?.is_nan());
        // float: out of range throws, unrestricted gives infinity.
        let v = scope.number(1e39);
        assert!(convert::float(scope, v, false).is_err());
        assert!(convert::float(scope, v, true)?.is_infinite());
        // DOMString: ToString, and [LegacyNullToEmptyString].
        let null = scope.null();
        assert_eq!(
            convert::dom_string(scope, null, false)?,
            "null".encode_utf16().collect::<Vec<_>>()
        );
        assert!(convert::dom_string(scope, null, true)?.is_empty());
        // USVString: a lone surrogate becomes U+FFFD.
        let lone = scope.string_utf16(&[0x61, 0xD800]);
        assert_eq!(convert::usv_string(scope, lone)?, "a\u{FFFD}");
        // ByteString: a code unit above 255 throws.
        let wide = scope.string("\u{100}");
        assert!(convert::byte_string(scope, wide).is_err());
        let ok = scope.string("\u{ff}");
        assert_eq!(convert::byte_string(scope, ok)?, vec![255u8]);
        // object: a primitive throws.
        let one = scope.number(1.0);
        assert!(convert::object(scope, one).is_err());
        Ok(())
    })
}

#[test]
fn dictionaries_and_sequences_through_the_glue() -> Test {
    let (mut rt, realm) = setup()?;
    // EventInit: a non-object throws; members are read, with defaults.
    let r = run(
        &mut rt,
        &realm,
        "var r = '';\n\
         try { new Event('a', 5); } catch (e) { r += e.name; }\n\
         new Event('b', null); new Event('c', { bubbles: 1 });\n\
         var p = new Event('d').composedPath(); r += ',' + p.length + ',' + (p[0] instanceof Event);",
    )?;
    assert_eq!(r, "TypeError,1,true");
    let log = rt.scope(|scope| Ok(scope.host_mut::<Mock>()?.log.clone()))?;
    assert_eq!(log, vec!["bubbles=false", "bubbles=true", "bubbles=false"]);
    Ok(())
}
