//! Tests of `Date` (§21.4) with the built-ins installed, as small scripts
//! whose result is the global `r` as its ToString. No files are read, so these
//! run under Miri too (every eighth case, since each case builds a VM).
//!
//! The first group runs in a bare VM, whose clock is the epoch and whose time
//! zone is UTC; the second installs a world hook with a clock and a +01:00
//! offset, the way `clazel-js` forwards `Host::now_ms` and `Host::local_tza`.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Abrupt, Config, Vm, World};

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

fn config() -> Config {
    if cfg!(miri) {
        Config {
            region_slots: 1 << 12,
            heap_cells: 1 << 14,
        }
    } else {
        Config::default()
    }
}

/// A clock of 1700000000123 ms and a fixed offset of one hour.
fn hook(_vm: &mut Vm, q: World) -> f64 {
    match q {
        World::NowMs => 1_700_000_000_123.0,
        World::LocalTza { .. } => 3_600_000.0,
    }
}

fn r_of(src: &str, hooked: bool) -> Result<String, String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    if hooked {
        vm.set_world_hook(hook);
    }
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("install: {e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.set_budget(5_000_000);
    if let Err(e) = vm.run(&script) {
        let d = match e {
            Abrupt::Throw(v) => vm.describe(v),
            other => format!("{other:?}"),
        };
        return Err(format!("{src}: {d}"));
    }
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    let s = vm.to_js_string(r).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(s.to_string_lossy())
}

fn check(cases: &[(&str, &str)], hooked: bool) -> Result<(), String> {
    let stride = if cfg!(miri) { 8 } else { 1 };
    for (src, want) in cases.iter().step_by(stride) {
        let got = r_of(src, hooked)?;
        if got != *want {
            return Err(format!("{src}: expected {want:?}, got {got:?}"));
        }
    }
    Ok(())
}

/// `r` is true when the body throws an instance of `ctor`.
fn throws(ctor: &str, body: &str) -> String {
    format!("var r; try {{ {body}; r = 'no throw'; }} catch (e) {{ r = e instanceof {ctor}; }}")
}

#[test]
fn date_in_a_bare_vm() -> Result<(), String> {
    let invalid_iso = throws("RangeError", "new Date(NaN).toISOString()");
    let brand = throws("TypeError", "Date.prototype.getTime.call({})");
    let proto_brand = throws("TypeError", "Date.prototype.valueOf.call(Date.prototype)");
    let bad_hint = throws("TypeError", "new Date(0)[Symbol.toPrimitive]('x')");
    check(
        &[
            (
                "var r = new Date(0).toISOString();",
                "1970-01-01T00:00:00.000Z",
            ),
            (
                "var r = new Date(2000, 1, 29, 12, 34, 56, 789).getTime();",
                "951827696789",
            ),
            ("var r = Date.UTC(99, 0);", "915148800000"),
            ("var r = Date.UTC();", "NaN"),
            (
                "var r = Date.parse('2000-02-29T12:34:56.789Z');",
                "951827696789",
            ),
            ("var r = Date.parse('2000-02-30');", "NaN"),
            (
                "var r = Date.parse('Tue, 29 Feb 2000 12:34:56 GMT');",
                "951827696000",
            ),
            ("var r = typeof Date();", "string"),
            (
                "var d = new Date(NaN); var r = d.getTime() + ',' + String(d) + ',' + d.getDay();",
                "NaN,Invalid Date,NaN",
            ),
            (&invalid_iso, "true"),
            (
                "var d = new Date(0); d.setUTCFullYear(2000, 1, 29); d.setUTCHours(1, 2, 3, 4); var r = d.toISOString();",
                "2000-02-29T01:02:03.004Z",
            ),
            (
                "var d = new Date(0); var x = d.setMonth(13); var r = d.toISOString() + ',' + x;",
                "1971-02-01T00:00:00.000Z,34214400000",
            ),
            (
                "var d = new Date(NaN); d.setFullYear(2001); var r = d.toISOString() + ',' + new Date(NaN).setMonth(1);",
                "2001-01-01T00:00:00.000Z,NaN",
            ),
            (
                "var d = new Date(1000); var x = d.setSeconds(); var r = x + ',' + d.getTime();",
                "NaN,NaN",
            ),
            (
                "var r = JSON.stringify([new Date(0), new Date(NaN)]);",
                "[\"1970-01-01T00:00:00.000Z\",null]",
            ),
            (
                "var r = (new Date(0) + 1) + ',' + (new Date(5) - 1) + ',' + new Date(0)[Symbol.toPrimitive]('number');",
                "Thu Jan 01 1970 00:00:00 GMT+00001,4,0",
            ),
            (
                "var r = new Date(2016, 6).toISOString();",
                "2016-07-01T00:00:00.000Z",
            ),
            (
                "var d = new Date(951827696789); var r = [d.toString(), d.toDateString(), d.toTimeString(), d.toUTCString(), d.toLocaleString(), d.toLocaleDateString(), d.toLocaleTimeString()].join('|');",
                "Tue Feb 29 2000 12:34:56 GMT+0000|Tue Feb 29 2000|12:34:56 GMT+0000|Tue, 29 Feb 2000 12:34:56 GMT|2/29/2000, 12:34:56 PM|2/29/2000|12:34:56 PM",
            ),
            (
                "var r = (Date.prototype.toGMTString === Date.prototype.toUTCString) + ',' + Date.length + Date.UTC.length + Date.parse.length + Date.now.length + ',' + Date.name;",
                "true,7710,Date",
            ),
            (&brand, "true"),
            (&proto_brand, "true"),
            (&bad_hint, "true"),
            (
                "var r = new Date(new Date(5)).getTime() + ',' + new Date('2000-01-01').getTime() + ',' + new Date(8.64e15 + 1).getTime() + ',' + new Date(2000, 0).getYear();",
                "5,946684800000,NaN,100",
            ),
            (
                "class D extends Date {} var d = new D(0); var r = (d instanceof D) + ',' + (d instanceof Date) + ',' + d.getTime();",
                "true,true,0",
            ),
            (
                "var r = Date.prototype.toJSON.call({ toISOString: function () { return 'x'; } }) + ',' + Date.prototype.toJSON.call({ valueOf: function () { return Infinity; } });",
                "x,null",
            ),
            (
                "var r = Object.prototype.toString.call(new Date(0)) + ',' + Object.prototype.toString.call(Date.prototype);",
                "[object Date],[object Object]",
            ),
        ],
        false,
    )
}

#[test]
fn date_with_a_clock_and_a_zone() -> Result<(), String> {
    check(
        &[
            (
                "var r = Date.now() + ',' + new Date().getTime();",
                "1700000000123,1700000000123",
            ),
            (
                "var d = new Date(0); var r = d.getHours() + ',' + d.getUTCHours() + ',' + d.getTimezoneOffset();",
                "1,0,-60",
            ),
            (
                "var r = new Date(0).toString();",
                "Thu Jan 01 1970 01:00:00 GMT+0100",
            ),
            (
                "var r = new Date(1970, 0, 1).getTime() + ',' + Date.UTC(1970, 0, 1);",
                "-3600000,0",
            ),
            (
                "var r = Date.parse('1970-01-01T01:00:00') + ',' + Date.parse('1970-01-01') + ',' + Date.parse('1970-01-01T01:00:00Z');",
                "0,0,3600000",
            ),
            (
                "var d = new Date(0); d.setHours(5); var r = d.getTime();",
                "14400000",
            ),
            (
                "var d = new Date(0); var r = d.toLocaleTimeString() + ',' + d.toISOString();",
                "1:00:00 AM,1970-01-01T00:00:00.000Z",
            ),
            (
                "var r = Date.parse(new Date(1e12).toString()) + ',' + Date.parse(new Date(1e12).toUTCString());",
                "1000000000000,1000000000000",
            ),
            (
                "var r = (typeof Date()) + ',' + Date().slice(-8);",
                "string,GMT+0100",
            ),
        ],
        true,
    )
}
