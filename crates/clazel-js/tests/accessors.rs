//! Accessor properties, re-entrant shared natives, arrays and `delete`
//! through the public API (item 7.12 needs them: WebIDL attributes are
//! accessor properties, WebIDL §3.7.6, and event dispatch re-enters natives).

use clazel_js::{
    Callable, Config, DefaultHost, Error, Key, Limits, Local, PropertyDescriptor, Realm,
    RealmOptions, Result, Runtime, Scope, Source,
};

type Test = core::result::Result<(), Error>;

fn runtime() -> Result<(Runtime, Realm)> {
    let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    Ok((rt, realm))
}

/// Runs `statements`, then reads the global `r`.
fn run<'s>(scope: &mut Scope<'s>, realm: &Realm, statements: &str) -> Result<Local<'s>> {
    scope.eval_script(realm, Source::new("test.js", statements))?;
    let global = scope.global(realm)?;
    scope.get(global, Key::from("r"))
}

fn text(scope: &mut Scope<'_>, value: Local<'_>) -> Result<String> {
    let s = scope.to_string(value)?;
    scope.string_to_string_lossy(s)
}

#[test]
fn a_native_getter_and_setter_see_the_receiver() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let proto = scope.new_object()?;
        let getter = scope.shared_function("get x", 0, Callable::Function, |scope, args| {
            let this = args.this();
            let v = scope.get(this, Key::from("_x"))?;
            let n = scope.to_number(v)?;
            Ok(scope.number(n * 2.0))
        })?;
        let setter = scope.shared_function("set x", 1, Callable::Function, |scope, args| {
            let this = args.this();
            scope.set(this, Key::from("_x"), args.get(0))?;
            Ok(scope.undefined())
        })?;
        scope.define_property(
            proto,
            Key::from("x"),
            PropertyDescriptor {
                get: Some(getter),
                set: Some(setter),
                enumerable: Some(true),
                configurable: Some(true),
                ..PropertyDescriptor::default()
            },
        )?;
        scope.set(global, Key::from("P"), proto)?;
        let r = run(
            scope,
            &realm,
            "var o = Object.create(P); o.x = 21; var r = o.x + ':' + o._x + ':' + ('x' in o);",
        )?;
        assert_eq!(text(scope, r)?, "42:21:true");
        // The descriptor reads back as an accessor.
        let d = scope.get_own_property(proto, Key::from("x"))?;
        let d = d.ok_or(Error::WrongType("an own property"))?;
        assert!(d.get.is_some() && d.set.is_some() && d.value.is_none());
        assert_eq!(d.enumerable, Some(true));
        Ok(())
    })
}

#[test]
fn a_getter_without_a_setter_throws_in_strict_code_only() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let r = run(
            scope,
            &realm,
            "var o = { get g() { return 7; } };\n\
             o.g = 1;\n\
             var r = o.g;\n\
             (function () { 'use strict'; try { o.g = 2; r = r + ':no'; } \
             catch (e) { r = r + ':' + (e instanceof TypeError); } })();",
        )?;
        assert_eq!(text(scope, r)?, "7:true");
        // An API `set` is strict.
        let global = scope.global(&realm)?;
        let o = scope.get(global, Key::from("o"))?;
        let one = scope.number(1.0);
        assert!(matches!(
            scope.set(o, Key::from("g"), one),
            Err(Error::Thrown(_))
        ));
        Ok(())
    })
}

#[test]
fn object_literal_accessors_and_define_property() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let r = run(
            scope,
            &realm,
            "var log = '';\n\
             var o = { v: 1, get a() { return this.v; }, set a(x) { log += x; this.v = x; } };\n\
             o.a = 5;\n\
             Object.defineProperty(o, 'b', { get: function () { return 'b' + this.v; }, \
             configurable: true });\n\
             var keys = Object.keys(o).join(',');\n\
             Object.defineProperty(o, 'b', { value: 3 });\n\
             var r = o.a + log + o.b + keys;",
        )?;
        // `b` was defined non-enumerable, so `keys` lists `v,a`; redefining it
        // as data replaces the accessor.
        assert_eq!(text(scope, r)?, "553v,a");
        let r = run(
            scope,
            &realm,
            "var r; try { Object.defineProperty({}, 'x', { get: 1 }); } \
             catch (e) { r = e instanceof TypeError; }",
        )?;
        assert_eq!(scope.as_boolean(r), Some(true));
        Ok(())
    })
}

#[test]
fn a_global_accessor_is_read_as_an_identifier() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let getter = scope.shared_function("get answer", 0, Callable::Function, |scope, _| {
            Ok(scope.number(42.0))
        })?;
        scope.define_property(
            global,
            Key::from("answer"),
            PropertyDescriptor {
                get: Some(getter),
                configurable: Some(false),
                enumerable: Some(true),
                ..PropertyDescriptor::default()
            },
        )?;
        let r = run(scope, &realm, "var r = answer + 1;")?;
        assert_eq!(scope.as_number(r), Some(43.0));
        // Not configurable: redefining it is refused.
        let one = scope.number(1.0);
        assert!(
            scope
                .define_property(
                    global,
                    Key::from("answer"),
                    PropertyDescriptor {
                        value: Some(one),
                        ..PropertyDescriptor::default()
                    },
                )
                .is_err()
        );
        Ok(())
    })
}

#[test]
fn a_shared_function_can_be_reentered() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let relay = scope.shared_function("relay", 1, Callable::Function, |scope, args| {
            let this = scope.undefined();
            scope.call(args.get(0), this, &[])
        })?;
        scope.set(global, Key::from("relay"), relay)?;
        let r = run(
            scope,
            &realm,
            "var r = relay(function () { return relay(function () { return 3; }) + 1; });",
        )?;
        assert_eq!(scope.as_number(r), Some(4.0));
        Ok(())
    })
}

#[test]
fn arrays_and_delete() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let a = scope.string("a");
        let b = scope.number(2.0);
        let array = scope.new_array_from(&[a, b])?;
        assert!(scope.is_array(array)?);
        scope.set(global, Key::from("arr"), array)?;
        let r = run(scope, &realm, "var r = arr.length + arr.join('-');")?;
        assert_eq!(text(scope, r)?, "2a-2");
        let empty = scope.new_array(3)?;
        let len = scope.get(empty, Key::from("length"))?;
        assert_eq!(scope.as_number(len), Some(3.0));
        let o = run(scope, &realm, "var r = { k: 1 };")?;
        assert!(scope.has_property(o, Key::from("k"))?);
        assert!(scope.delete_property(o, Key::from("k"))?);
        assert!(!scope.has_property(o, Key::from("k"))?);
        Ok(())
    })
}
