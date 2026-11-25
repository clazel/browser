//! `console` (the Console Standard, §1†), written to the host's log and
//! never to the page (phase-7.md item 7.15).
//!
//! <https://console.spec.whatwg.org/>
//!
//! `console.idl` is not among the vendored IDL files, so the namespace is
//! made here by hand, as WebIDL §3.13† "namespace objects" lays one out: an
//! ordinary object whose prototype is `Object.prototype`, with an operation
//! property for each member ({ writable, enumerable, configurable }: true),
//! reachable as the global's `console` ({ writable: true, enumerable: false,
//! configurable: true }).
//!
//! Modelling choices:
//! - **Formatting** (Console §2.2† "Formatter") is simplified: the
//!   arguments are converted with ToString and joined with spaces; the
//!   `%s`, `%d`, `%o` and `%c` directives are not interpreted.
//! - **Grouping** writes the group's label and does not indent.
//! - **Counting and timing** (`count`, `time` and friends) are not
//!   implemented.

use clazel_js::{Args, Key, PropertyDescriptor, Realm, Result, Scope};
use clazel_webidl::install;

use super::{HookCall, LogLevel, page};

/// "Printer" (Console §2.3†): the arguments as text, for the host's log.
fn text(scope: &mut Scope<'_>, args: &Args<'_>, from: usize) -> Result<String> {
    let mut parts = Vec::new();
    for i in from..args.len() {
        let s = scope.to_string(args.get(i))?;
        parts.push(scope.string_to_string_lossy(s)?);
    }
    Ok(parts.join(" "))
}

fn emit(scope: &mut Scope<'_>, level: LogLevel, message: String) -> Result<()> {
    page(scope)?.record(HookCall::Log(level, message));
    Ok(())
}

/// Installs `console` on the realm's global object.
///
/// # Errors
/// What `clazel-js` returns.
pub fn install(scope: &mut Scope<'_>, realm: &Realm) -> Result<()> {
    let console = scope.new_object()?;
    // Console §1.1†: log, info, debug, warn, error, trace, dir, dirxml and
    // table are "Logger(logLevel, data)" with their log level.
    let loggers: &[(&str, LogLevel)] = &[
        ("log", LogLevel::Log),
        ("info", LogLevel::Log),
        ("debug", LogLevel::Debug),
        ("warn", LogLevel::Warn),
        ("error", LogLevel::Error),
        ("trace", LogLevel::Log),
        ("dir", LogLevel::Log),
        ("dirxml", LogLevel::Log),
        ("table", LogLevel::Log),
        ("group", LogLevel::Log),
        ("groupCollapsed", LogLevel::Log),
    ];
    for &(name, level) in loggers {
        install::operation(
            scope,
            console,
            name,
            0,
            move |scope: &mut Scope<'_>, args: &Args<'_>| {
                let t = text(scope, args, 0)?;
                emit(scope, level, t)?;
                Ok(scope.undefined())
            },
            false,
        )?;
    }
    // Console §1.1.1† assert(condition, ...data): "1. If condition is true,
    // return. 2. Let message be a string without any formatting specifiers
    // indicating generically an assertion failure (such as "Assertion
    // failed"). 3. If data is empty, append message to data. 4. Otherwise,
    // ... prepend message. 5. Perform Logger("assert", data)."
    install::operation(
        scope,
        console,
        "assert",
        0,
        |scope: &mut Scope<'_>, args: &Args<'_>| {
            if scope.to_boolean(args.get(0)) {
                return Ok(scope.undefined());
            }
            let rest = text(scope, args, 1)?;
            let message = if rest.is_empty() {
                "Assertion failed".to_owned()
            } else {
                format!("Assertion failed: {rest}")
            };
            emit(scope, LogLevel::Error, message)?;
            Ok(scope.undefined())
        },
        false,
    )?;
    // clear() and groupEnd(): nothing to do in a log.
    for name in ["clear", "groupEnd"] {
        install::operation(
            scope,
            console,
            name,
            0,
            |scope: &mut Scope<'_>, _: &Args<'_>| Ok(scope.undefined()),
            false,
        )?;
    }
    let global = scope.global(realm)?;
    scope.define_property(
        global,
        Key::Str("console"),
        PropertyDescriptor {
            value: Some(console),
            writable: Some(true),
            enumerable: Some(false),
            configurable: Some(true),
            ..PropertyDescriptor::default()
        },
    )
}
