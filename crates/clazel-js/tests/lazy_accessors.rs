//! `Scope::define_accessor`: an accessor property whose getter and setter
//! function objects are made when they are first needed. Script must not be
//! able to tell that from making them at once, so every test here runs the
//! same script on two objects, one built each way, and compares what the
//! script saw. Each script is the first thing to touch its object, so each
//! is a different first use of a pair that is still lazy.

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

fn text(scope: &mut Scope<'_>, value: Local<'_>) -> Result<String> {
    let s = scope.to_string(value)?;
    scope.string_to_string_lossy(s)
}

/// `x`'s getter: twice the receiver's `_x`.
fn get_x<'s>(scope: &mut Scope<'s>, this: Local<'s>) -> Result<Local<'s>> {
    let v = scope.get(this, Key::from("_x"))?;
    let n = scope.to_number(v)?;
    Ok(scope.number(n * 2.0))
}

/// `x`'s setter: stores the value as the receiver's `_x`.
fn set_x<'s>(scope: &mut Scope<'s>, this: Local<'s>, v: Local<'s>) -> Result<Local<'s>> {
    scope.set(this, Key::from("_x"), v)?;
    Ok(scope.undefined())
}

fn data<'s>(scope: &mut Scope<'s>, o: Local<'s>, name: &str, n: f64) -> Result<()> {
    let v = scope.number(n);
    scope.define_property(
        o,
        Key::from(name),
        PropertyDescriptor {
            value: Some(v),
            writable: Some(true),
            enumerable: Some(true),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )
}

/// An object with, in order: the data property `first`; the accessor `x`
/// (getter and setter, enumerable, configurable); the accessor `y` (getter
/// only, not enumerable, not configurable); the data property `last`. With
/// `lazy`, the accessors are defined by `define_accessor`; without, their
/// functions are made first and defined with `define_property`, as WebIDL's
/// bindings did before.
fn object<'s>(scope: &mut Scope<'s>, lazy: bool) -> Result<Local<'s>> {
    let o = scope.new_object()?;
    data(scope, o, "first", 1.0)?;
    if lazy {
        scope.define_accessor(
            o,
            "x",
            |scope, args| get_x(scope, args.this()),
            Some(std::sync::Arc::new(|scope, args| {
                set_x(scope, args.this(), args.get(0))
            })),
            true,
            true,
        )?;
        scope.define_accessor(o, "y", |scope, _| Ok(scope.number(7.0)), None, false, false)?;
    } else {
        let get = scope.shared_function("get x", 0, Callable::Function, |scope, args| {
            get_x(scope, args.this())
        })?;
        let set = scope.shared_function("set x", 1, Callable::Function, |scope, args| {
            set_x(scope, args.this(), args.get(0))
        })?;
        scope.define_property(
            o,
            Key::from("x"),
            PropertyDescriptor {
                get: Some(get),
                set: Some(set),
                enumerable: Some(true),
                configurable: Some(true),
                ..PropertyDescriptor::default()
            },
        )?;
        let get = scope.shared_function("get y", 0, Callable::Function, |scope, _| {
            Ok(scope.number(7.0))
        })?;
        let undefined = scope.undefined();
        scope.define_property(
            o,
            Key::from("y"),
            PropertyDescriptor {
                get: Some(get),
                set: Some(undefined),
                enumerable: Some(false),
                configurable: Some(false),
                ..PropertyDescriptor::default()
            },
        )?;
    }
    data(scope, o, "last", 2.0)?;
    Ok(o)
}

/// Everything a script can read of an object's own properties.
const DUMP: &str = "function dump(o) {\n\
    var out = [], names = Object.getOwnPropertyNames(o);\n\
    out.push(names.join(','), Object.keys(o).join(','));\n\
    for (var i = 0; i < names.length; i++) {\n\
        var d = Object.getOwnPropertyDescriptor(o, names[i]);\n\
        var e = Object.getOwnPropertyDescriptor(o, names[i]);\n\
        out.push(names[i], Object.getOwnPropertyNames(d).join(','), d.enumerable, d.configurable,\n\
            typeof d.get, typeof d.set, d.get === e.get, d.set === e.set, d.value, d.writable);\n\
        var fs = [d.get, d.set];\n\
        for (var j = 0; j < 2; j++) {\n\
            var f = fs[j];\n\
            if (typeof f !== 'function') continue;\n\
            out.push(f.name, f.length, Object.getPrototypeOf(f) === Function.prototype,\n\
                Object.getOwnPropertyNames(f).join(','), Object.isExtensible(f),\n\
                Object.prototype.toString.call(f));\n\
            var fn = Object.getOwnPropertyDescriptor(f, 'name');\n\
            var fl = Object.getOwnPropertyDescriptor(f, 'length');\n\
            out.push(fn.writable, fn.enumerable, fn.configurable, fl.writable, fl.enumerable, fl.configurable);\n\
            try { new f(); out.push('constructed'); } catch (err) { out.push(err instanceof TypeError); }\n\
        }\n\
    }\n\
    for (var k in o) out.push('in ' + k);\n\
    return out.join('|');\n\
}\n";

/// First uses of the object `o`, each run on a fresh object of each kind.
/// Every one ends by setting `r`.
const FIRST_USES: &[&str] = &[
    // Nothing but the dump.
    "var r = dump(o);",
    // [[Get]] and [[Set]] through the property, own and inherited.
    "o._x = 4; var r = o.x + ':' + dump(o);",
    "o.x = 5; var r = o._x + ':' + o.x + ':' + dump(o);",
    "var c = Object.create(o); c.x = 3; var r = c.x + ':' + c._x + ':' + o._x + ':' + \
     Object.getOwnPropertyNames(c).join(',') + ':' + dump(o);",
    "var r = o.y + ':' + dump(o);",
    // A getter with no setter: [[Set]] fails, and strict code throws.
    "o.y = 1; var r = o.y; (function () { 'use strict'; try { o.y = 2; r += ':set'; } \
     catch (e) { r += ':' + (e instanceof TypeError); } })(); r += dump(o);",
    // The functions, reached before anything was read through the property.
    "var d = Object.getOwnPropertyDescriptor(o, 'x'); var r = d.get.name + ':' + d.set.name + ':' + \
     d.get.call({ _x: 21 }) + ':' + (d.get === Object.getOwnPropertyDescriptor(o, 'x').get) + dump(o);",
    "var d = Object.getOwnPropertyDescriptor(o, 'y'); var r = typeof d.get + ':' + d.set + ':' + \
     ('set' in d) + dump(o);",
    "var g = o.__lookupGetter__('x'), s = o.__lookupSetter__('x'); var r = g.name + ':' + s.name + ':' + \
     o.__lookupSetter__('y') + ':' + (g === o.__lookupGetter__('x')) + dump(o);",
    "var all = Object.getOwnPropertyDescriptors(o); var r = Object.keys(all).join(',') + ':' + \
     all.x.get.name + ':' + all.y.get.name + ':' + (all.x.get === Object.getOwnPropertyDescriptor(o, 'x').get) + dump(o);",
    "var d = Reflect.getOwnPropertyDescriptor(o, 'x'); var r = Reflect.ownKeys(o).join(',') + ':' + \
     d.set.length + ':' + Reflect.get(o, 'x', { _x: 8 }) + ':' + Reflect.has(o, 'y') + dump(o);",
    // Operations that need no function.
    "var r = [o.hasOwnProperty('x'), o.propertyIsEnumerable('x'), o.propertyIsEnumerable('y'), \
     'x' in o, 'y' in o, Object.keys(o).length].join(',') + dump(o);",
    "var r = ''; for (var k in o) r += k + ','; r += Object.getOwnPropertyNames(o).join(',') + dump(o);",
    // Readers of every enumerable own property.
    "o._x = 2; var c = Object.assign({}, o); var r = Object.keys(c).join(',') + ':' + c.x + ':' + \
     typeof Object.getOwnPropertyDescriptor(c, 'x').get + dump(o);",
    "o._x = 2; var r = JSON.stringify(o) + ':' + Object.entries(o).join(';') + ':' + \
     Object.values(o).join(';') + dump(o);",
    // Deleting, and the property order after it.
    "var r = (delete o.x) + ':' + ('x' in o) + ':' + Object.getOwnPropertyNames(o).join(',') + dump(o);",
    "var r; (function () { 'use strict'; try { delete o.y; r = 'deleted'; } \
     catch (e) { r = String(e instanceof TypeError); } })(); r += (delete o.y) + dump(o);",
    "delete o.x; o.x = 9; var r = Object.getOwnPropertyNames(o).join(',') + dump(o);",
    // Redefining: attributes alone, one half, to a data property, refused.
    "Object.defineProperty(o, 'x', { enumerable: false }); o._x = 1; var r = o.x + dump(o);",
    "Object.defineProperty(o, 'x', { get: function g() { return 9; } }); o.x = 4; \
     var r = o.x + ':' + o._x + ':' + Object.getOwnPropertyDescriptor(o, 'x').set.name + dump(o);",
    "Object.defineProperty(o, 'x', { set: undefined }); o.x = 4; o._x = 3; var r = o.x + dump(o);",
    "Object.defineProperty(o, 'x', { value: 5 }); var r = o.x + dump(o);",
    "var r = ''; try { Object.defineProperty(o, 'y', { get: function () {} }); r = 'redefined'; } \
     catch (e) { r = String(e instanceof TypeError); } \
     try { Object.defineProperty(o, 'y', { enumerable: true }); r += 'redefined'; } \
     catch (e) { r += String(e instanceof TypeError); } \
     Object.defineProperty(o, 'y', { get: Object.getOwnPropertyDescriptor(o, 'y').get }); r += dump(o);",
    "var r = Reflect.defineProperty(o, 'y', { value: 1 }) + ':' + \
     Reflect.defineProperty(o, 'y', { configurable: false, enumerable: false }) + dump(o);",
    // Integrity levels. (The setter's own `Set` of `_x` is strict, so it
    // throws on an object that takes no new property.)
    "Object.freeze(o); var r = Object.isFrozen(o) + ':' + Object.isSealed(o) + dump(o); \
     try { o.x = 6; r += 'set'; } catch (e) { r += (e instanceof TypeError); } r += o.x;",
    "o._x = 1; Object.seal(o); o.x = 6; var r = Object.isFrozen(o) + ':' + Object.isSealed(o) + ':' + o.x + dump(o);",
    "Object.preventExtensions(o); var r = Object.isExtensible(o) + ':'; \
     try { o.x = 6; r += 'set'; } catch (e) { r += (e instanceof TypeError); } r += o._x + dump(o);",
    // A copy of the pair onto another object keeps the same functions.
    "var p = {}; Object.defineProperty(p, 'x', Object.getOwnPropertyDescriptor(o, 'x')); p._x = 5; \
     var r = p.x + ':' + (Object.getOwnPropertyDescriptor(p, 'x').get === Object.getOwnPropertyDescriptor(o, 'x').get) + dump(o);",
];

#[test]
fn script_cannot_tell_a_lazy_accessor_from_an_eager_one() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        scope.eval_script(&realm, Source::new("dump.js", DUMP))?;
        let global = scope.global(&realm)?;
        // Under Miri two first uses, the third and the twenty-first: a
        // write and a read through the property, and a redefinition of one
        // half. Each first use is two objects and a `dump` of each, about
        // 48 s of Miri time (measured: ten took 483 s). Miri looks for
        // undefined behaviour in the paths that make the functions, which
        // those two cross (the other tests of this file run there whole);
        // the native run compares every first use.
        let (first, step) = if cfg!(miri) { (2, 18) } else { (0, 1) };
        for (i, use_) in FIRST_USES.iter().enumerate().skip(first).step_by(step) {
            let mut seen = Vec::new();
            for lazy in [false, true] {
                let o = object(scope, lazy)?;
                scope.set(global, Key::from("o"), o)?;
                // An uncaught exception is a result like any other.
                match scope.eval_script(&realm, Source::new("use.js", use_)) {
                    Ok(_) => {
                        let r = scope.get(global, Key::from("r"))?;
                        seen.push(text(scope, r)?);
                    }
                    Err(Error::Thrown(e)) => {
                        let report = scope.report(&e)?;
                        seen.push(format!("uncaught {}: {}", report.name, report.message));
                    }
                    Err(e) => return Err(e),
                }
            }
            let [eager, lazy] = seen.as_slice() else {
                return Err(Error::WrongType("two runs"));
            };
            assert_eq!(lazy, eager, "first use {i}: {use_}");
            // The dump is not vacuous: it names both accessors' functions.
            assert!(
                eager.contains("get y") && !eager.contains("uncaught"),
                "first use {i}: {eager}"
            );
        }
        Ok(())
    })
}

#[test]
fn the_functions_are_made_once_and_by_the_first_use() -> Test {
    let (mut rt, realm) = runtime()?;
    // Both objects exist before either measurement, so interned names and
    // shapes are already there.
    let before = rt.heap_used()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let o = object(scope, false)?;
        scope.set(global, Key::from("eager"), o)
    })?;
    let eager = rt.heap_used()?.saturating_sub(before);
    let before = rt.heap_used()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let o = object(scope, true)?;
        scope.set(global, Key::from("lazy"), o)
    })?;
    let lazy = rt.heap_used()?.saturating_sub(before);
    // Three function objects (with a name string each) were not allocated.
    assert!(lazy < eager, "lazy {lazy} bytes, eager {eager} bytes");

    // Operations that need no function leave the pairs lazy.
    let before = rt.heap_used()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let o = scope.get(global, Key::from("lazy"))?;
        assert!(scope.has_property(o, Key::from("x"))?);
        assert!(scope.has_property(o, Key::from("y"))?);
        Ok(())
    })?;
    assert_eq!(rt.heap_used()?, before);

    // The first read through `x` makes its two functions; the second makes
    // nothing, and the descriptor has the same two objects each time.
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let o = scope.get(global, Key::from("lazy"))?;
        let v = scope.get(o, Key::from("x"))?;
        assert!(scope.to_number(v)?.is_nan());
        Ok(())
    })?;
    let after_first = rt.heap_used()?;
    assert!(after_first > before);
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let o = scope.get(global, Key::from("lazy"))?;
        scope.get(o, Key::from("x"))?;
        let none = Error::WrongType("an accessor property");
        let a = scope.get_own_property(o, Key::from("x"))?.ok_or(none)?;
        let none = Error::WrongType("an accessor property");
        let b = scope.get_own_property(o, Key::from("x"))?.ok_or(none)?;
        let (Some(ag), Some(bg), Some(a_set), Some(b_set)) = (a.get, b.get, a.set, b.set) else {
            return Err(Error::WrongType("both halves"));
        };
        assert!(scope.strict_equals(ag, bg));
        assert!(scope.strict_equals(a_set, b_set));
        let name = scope.get(a_set, Key::from("name"))?;
        assert_eq!(text(scope, name)?, "set x");
        Ok(())
    })?;
    assert_eq!(rt.heap_used()?, after_first);
    Ok(())
}

#[test]
fn where_the_property_cannot_just_be_created_it_is_define_property_or_throw() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let seven = |scope: &mut Scope<'_>, o: Local<'_>, name: &str| {
            scope.define_accessor(o, name, |scope, _| Ok(scope.number(7.0)), None, true, true)
        };
        let read = |scope: &mut Scope<'_>, script: &str| -> Result<String> {
            scope.eval_script(&realm, Source::new("t.js", script))?;
            let global = scope.global(&realm)?;
            let r = scope.get(global, Key::from("r"))?;
            text(scope, r)
        };

        // An existing configurable property is replaced where it stands.
        let o = scope.new_object()?;
        data(scope, o, "a", 1.0)?;
        data(scope, o, "x", 2.0)?;
        data(scope, o, "b", 3.0)?;
        seven(scope, o, "x")?;
        scope.set(global, Key::from("o"), o)?;
        let r = read(
            scope,
            "var d = Object.getOwnPropertyDescriptor(o, 'x'); \
             var r = [Object.keys(o).join(''), o.x, d.get.name, d.set, d.enumerable, d.configurable].join(',');",
        )?;
        assert_eq!(r, "axb,7,get x,,true,true");

        // An existing accessor, itself still lazy, keeps its setter (the
        // descriptor names only [[Get]] and the attributes... and [[Set]]
        // is given as undefined, which replaces it).
        seven(scope, o, "x")?;
        let r = read(
            scope,
            "var r = o.x + ':' + Object.getOwnPropertyDescriptor(o, 'x').set;",
        )?;
        assert_eq!(r, "7:undefined");

        // A non-configurable property refuses: a TypeError, and it stays.
        let fixed = scope.new_object()?;
        let one = scope.number(1.0);
        scope.define_property(
            fixed,
            Key::from("x"),
            PropertyDescriptor {
                value: Some(one),
                writable: Some(false),
                enumerable: Some(true),
                configurable: Some(false),
                ..PropertyDescriptor::default()
            },
        )?;
        assert!(matches!(seven(scope, fixed, "x"), Err(Error::Thrown(_))));
        let v = scope.get(fixed, Key::from("x"))?;
        assert!(scope.to_number(v)?.to_bits() == 1.0f64.to_bits());

        // An object that is not extensible refuses a new property.
        scope.set(global, Key::from("o"), fixed)?;
        read(scope, "Object.preventExtensions(o); var r = 0;")?;
        assert!(matches!(seven(scope, fixed, "z"), Err(Error::Thrown(_))));
        assert!(!scope.has_property(fixed, Key::from("z"))?);

        // An Array takes its own [[DefineOwnProperty]].
        let array = scope.new_array(0)?;
        seven(scope, array, "x")?;
        seven(scope, array, "1")?;
        scope.set(global, Key::from("o"), array)?;
        let r = read(scope, "var r = [o.x, o[1], o.length].join(',');")?;
        assert_eq!(r, "7,7,2");

        // A value that is not an object is the API's own error.
        let n = scope.number(1.0);
        assert!(matches!(seven(scope, n, "x"), Err(Error::WrongType(_))));
        Ok(())
    })
}
