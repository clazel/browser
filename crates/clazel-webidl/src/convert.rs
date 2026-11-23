//! The conversions between ECMAScript values and IDL values (WebIDL §3.2†,
//! "ECMAScript type mapping"), for every type the exposed IDL uses.
//!
//! <https://webidl.spec.whatwg.org/#es-type-mapping>
//!
//! Each function converts one way and cites its section; the steps are
//! quoted where the function is more than one call. The generated bindings
//! (`crate::generated::bindings`) call these for every argument, attribute
//! value and return value; dictionaries, enumerations and unions are
//! generated from the same steps (§3.2.18†, §3.2.19†, §3.2.24†).
//!
//! Representations of IDL values in Rust:
//! - `DOMString` is its code units, `Vec<u16>` ([`DomString`]);
//!   `USVString` is a Rust `String` (scalar values); `ByteString` is bytes.
//! - The integer types are the Rust integers of the same width, `float` is
//!   `f32` and `double` is `f64`.
//! - `any`, `object`, callback functions and callback interfaces are
//!   [`Local`] values.
//! - An interface type is the platform object's key ([`ObjectKey`]).
//!
//! Modelling choices:
//! - **`sequence<T>` from an Array only.** §3.2.20† reads a sequence with
//!   the iterator protocol (GetMethod(V, %Symbol.iterator%)), and the engine
//!   has no Symbols yet (`clazel-js`'s README). An Array exotic object is
//!   read by its indices (`length`, then `Get` of each), which is what its
//!   %Array.prototype.values% would yield for an unmodified array; any other
//!   object is a `TypeError`. Listed in the README.
//! - **`bigint`, `symbol`, buffer types, `Promise<T>` and `record<K, V>`**
//!   are not converted: the generator leaves out every member that uses
//!   them (it lists them in the generated file's header).

use clazel_js::{ErrorKind, Key, Local, Result, Scope, ValueKind};

use crate::generated::bindings::{AllInterfaces, InterfaceId};
use crate::platform::{ObjectKey, Platform, implements, wrap};

/// A `DOMString`: its UTF-16 code units, lone surrogates included.
pub type DomString = Vec<u16>;

/// `[EnforceRange]` and `[Clamp]` on an integer type (§3.3.? both).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct IntegerFlags {
    /// `[EnforceRange]`.
    pub enforce_range: bool,
    /// `[Clamp]`.
    pub clamp: bool,
}

fn type_error(scope: &mut Scope<'_>, message: &str) -> clazel_js::Error {
    scope.throw_error(ErrorKind::TypeError, message)
}

/// Whether a value is undefined or null.
#[must_use]
pub fn is_nullish(scope: &Scope<'_>, v: Local<'_>) -> bool {
    matches!(scope.kind(v), ValueKind::Undefined | ValueKind::Null)
}

/// Whether a value is an Object (functions included): ECMAScript's
/// "Type(V) is Object".
#[must_use]
pub fn is_object(scope: &Scope<'_>, v: Local<'_>) -> bool {
    matches!(scope.kind(v), ValueKind::Object | ValueKind::Function)
}

/// §3.2.2† `boolean`: "Let x be the result of computing ToBoolean(V)."
#[must_use]
pub fn boolean(scope: &mut Scope<'_>, v: Local<'_>) -> bool {
    scope.to_boolean(v)
}

/// IntegerPart(n), §3.2.4.? : "Let r be floor(abs(n)). If n < 0, then
/// return -1 × r. Otherwise, return r."
fn integer_part(n: f64) -> f64 {
    let r = n.abs().floor();
    if n < 0.0 { -r } else { r }
}

/// ConvertToInt ( V, bitLength, signedness ), §3.2.4.9†:
/// 1. If bitLength is 64, then a. Let upperBound be 2^53 − 1. b. If
///    signedness is "unsigned", then let lowerBound be 0. c. Otherwise let
///    lowerBound be −2^53 + 1. d. (2^53 − 1 is the largest exact integer.)
/// 2. Otherwise, if signedness is "unsigned", then a. Let lowerBound be 0.
///    b. Let upperBound be 2^bitLength − 1.
/// 3. Otherwise: a. Let lowerBound be −2^(bitLength − 1). b. Let upperBound
///    be 2^(bitLength − 1) − 1.
/// 4. Let x be ? ToNumber(V).
/// 5. If x is −0, then set x to +0.
/// 6. If the conversion is to an IDL type associated with the
///    [EnforceRange] extended attribute, then: 1. If x is NaN, +∞, or −∞,
///    then throw a TypeError. 2. Set x to IntegerPart(x). 3. If x <
///    lowerBound or x > upperBound, then throw a TypeError. 4. Return x.
/// 7. If x is not NaN and the conversion is to an IDL type associated with
///    the [Clamp] extended attribute, then: 1. Set x to min(max(x,
///    lowerBound), upperBound). 2. Round x to the nearest integer, choosing
///    the even integer if it lies halfway between two, and choosing +0
///    rather than −0. 3. Return x.
/// 8. If x is NaN, +0, +∞, or −∞, then return +0.
/// 9. Set x to IntegerPart(x).
/// 10. Set x to x modulo 2^bitLength.
/// 11. If signedness is "signed" and x ≥ 2^(bitLength − 1), then return x −
///     2^bitLength.
/// 12. Otherwise, return x.
///
/// The result is an exact integer in range, as an `i128`.
///
/// # Errors
/// What ToNumber throws, and step 6's TypeErrors.
pub fn convert_to_int(
    scope: &mut Scope<'_>,
    v: Local<'_>,
    bits: u32,
    signed: bool,
    flags: IntegerFlags,
) -> Result<i128> {
    let (lower, upper): (f64, f64) = if bits == 64 {
        let upper = 9_007_199_254_740_991.0;
        (if signed { -upper } else { 0.0 }, upper)
    } else if !signed {
        (0.0, 2f64.powi(bits as i32) - 1.0)
    } else {
        let half = 2f64.powi(bits.saturating_sub(1) as i32);
        (-half, half - 1.0)
    };
    let mut x = scope.to_number(v)?;
    if x == 0.0 {
        x = 0.0;
    }
    if flags.enforce_range {
        if !x.is_finite() {
            return Err(type_error(
                scope,
                "Value is not a finite number ([EnforceRange])",
            ));
        }
        let x = integer_part(x);
        if x < lower || x > upper {
            return Err(type_error(
                scope,
                "Value is outside the range of the type ([EnforceRange])",
            ));
        }
        return Ok(x as i128);
    }
    if !x.is_nan() && flags.clamp {
        let x = x.max(lower).min(upper);
        // Round half to even; +0 rather than -0 (an i128 has no -0).
        let r = x.round();
        let r = if (x - x.trunc()).abs() == 0.5 && (r as i128) & 1 != 0 {
            r - x.signum()
        } else {
            r
        };
        return Ok(r as i128);
    }
    if !x.is_finite() || x == 0.0 {
        return Ok(0);
    }
    let x = integer_part(x);
    // Step 10: x modulo 2^bitLength, the mathematical modulo (non-negative).
    // Computed exactly on the double's bits, in integers: x is a non-zero
    // integer, |x| = significand × 2^exponent, and bits is 8, 16, 32 or 64,
    // so every intermediate fits a u128 (float `%` is not relied on: its
    // result differed under Miri).
    let full = 1i128.checked_shl(bits).unwrap_or(i128::MAX);
    let mask = u128::try_from(full).unwrap_or(u128::MAX).wrapping_sub(1);
    let raw = x.to_bits();
    let biased = i32::try_from(raw.wrapping_shr(52) & 0x7FF).unwrap_or(0);
    let fraction = raw & 0x000F_FFFF_FFFF_FFFF;
    let (significand, exponent) = if biased == 0 {
        (fraction, -1074)
    } else {
        (
            fraction | 0x0010_0000_0000_0000,
            biased.saturating_sub(1075),
        )
    };
    let magnitude: u128 = if exponent >= 0 {
        match u32::try_from(exponent) {
            Ok(e) if e < bits => u128::from(significand).wrapping_shl(e) & mask,
            _ => 0,
        }
    } else {
        let shift = exponent.unsigned_abs();
        if shift >= 64 {
            0
        } else {
            u128::from(significand.wrapping_shr(shift)) & mask
        }
    };
    let unsigned = if x < 0.0 {
        u128::try_from(full)
            .unwrap_or(u128::MAX)
            .wrapping_sub(magnitude)
            & mask
    } else {
        magnitude
    };
    let r = i128::try_from(unsigned).unwrap_or(0);
    let half = 1i128
        .checked_shl(bits.saturating_sub(1))
        .unwrap_or(i128::MAX);
    if signed && r >= half {
        return Ok(r.saturating_sub(full));
    }
    Ok(r)
}

macro_rules! integer {
    ($(#[$doc:meta])* $name:ident, $t:ty, $bits:expr, $signed:expr) => {
        $(#[$doc])*
        ///
        /// # Errors
        /// As [`convert_to_int`].
        pub fn $name(scope: &mut Scope<'_>, v: Local<'_>, flags: IntegerFlags) -> Result<$t> {
            let x = convert_to_int(scope, v, $bits, $signed, flags)?;
            <$t>::try_from(x).map_err(|_| type_error(scope, "integer out of range"))
        }
    };
}

integer!(
    /// §3.2.4.1† `byte`: ConvertToInt(V, 8, "signed").
    byte, i8, 8, true
);
integer!(
    /// §3.2.4.2† `octet`: ConvertToInt(V, 8, "unsigned").
    octet, u8, 8, false
);
integer!(
    /// §3.2.4.3† `short`: ConvertToInt(V, 16, "signed").
    short, i16, 16, true
);
integer!(
    /// §3.2.4.4† `unsigned short`: ConvertToInt(V, 16, "unsigned").
    unsigned_short, u16, 16, false
);
integer!(
    /// §3.2.4.5† `long`: ConvertToInt(V, 32, "signed").
    long, i32, 32, true
);
integer!(
    /// §3.2.4.6† `unsigned long`: ConvertToInt(V, 32, "unsigned").
    unsigned_long, u32, 32, false
);
integer!(
    /// §3.2.4.7† `long long`: ConvertToInt(V, 64, "signed").
    long_long, i64, 64, true
);
integer!(
    /// §3.2.4.8† `unsigned long long`: ConvertToInt(V, 64, "unsigned").
    unsigned_long_long, u64, 64, false
);

/// §3.2.5† `float` and §3.2.6† `unrestricted float`:
/// 1. Let x be ? ToNumber(V).
/// 2. (`float` only) If x is NaN, +∞, or −∞, then throw a TypeError.
/// 3. Let S be the set of finite IEEE 754 single-precision floating point
///    values except −0, but with two special values added: 2^128 and −2^128.
/// 4. Let y be the number in S that is closest to x, selecting the number
///    with an even significand if there are two equally close values.
/// 5. (`float` only) If y is 2^128 or −2^128, then throw a TypeError.
/// 6. If y is +0 and x is −0, then return −0.
/// 7. Return y.
///
/// `as f32` rounds to nearest, ties to even, and gives ±∞ beyond the
/// largest finite value, which is where steps 3 and 4 give ±2^128; for
/// `unrestricted float` those are ±∞ (§3.2.6† step "If y is 2^128, return
/// +∞").
///
/// # Errors
/// What ToNumber throws; the TypeErrors of `float`.
pub fn float(scope: &mut Scope<'_>, v: Local<'_>, unrestricted: bool) -> Result<f32> {
    let x = scope.to_number(v)?;
    if !unrestricted && !x.is_finite() {
        return Err(type_error(
            scope,
            "Value is not a finite floating-point value",
        ));
    }
    let y = x as f32;
    if !unrestricted && !y.is_finite() {
        return Err(type_error(scope, "Value is outside the range of float"));
    }
    Ok(y)
}

/// §3.2.7† `double` and §3.2.8† `unrestricted double`: "Let x be ?
/// ToNumber(V). (`double` only) If x is NaN, +∞, or −∞, then throw a
/// TypeError. Return the IDL value that represents the same numeric value
/// as x."
///
/// # Errors
/// What ToNumber throws; the TypeError of `double`.
pub fn double(scope: &mut Scope<'_>, v: Local<'_>, unrestricted: bool) -> Result<f64> {
    let x = scope.to_number(v)?;
    if !unrestricted && !x.is_finite() {
        return Err(type_error(
            scope,
            "Value is not a finite floating-point value",
        ));
    }
    Ok(x)
}

/// §3.2.10† `DOMString`:
/// 1. If V is null and the conversion is to an IDL type associated with the
///    [LegacyNullToEmptyString] extended attribute, then return the
///    DOMString value that represents the empty string.
/// 2. Let x be ? ToString(V).
/// 3. Return the IDL DOMString value that represents the same sequence of
///    code units as the one the ECMAScript String value x represents.
///
/// # Errors
/// What ToString throws.
pub fn dom_string(
    scope: &mut Scope<'_>,
    v: Local<'_>,
    legacy_null_to_empty: bool,
) -> Result<DomString> {
    if legacy_null_to_empty && scope.kind(v) == ValueKind::Null {
        return Ok(Vec::new());
    }
    let s = scope.to_string(v)?;
    scope.string_to_utf16(s)
}

/// §3.2.11† `ByteString`:
/// 1. Let x be ? ToString(V).
/// 2. If the value of any element of x is greater than 255, then throw a
///    TypeError.
/// 3. Return an IDL ByteString value whose length is the length of x, and
///    where the value of each element is the value of the corresponding
///    element of x.
///
/// # Errors
/// What ToString throws, and the TypeError.
pub fn byte_string(scope: &mut Scope<'_>, v: Local<'_>) -> Result<Vec<u8>> {
    let units = dom_string(scope, v, false)?;
    let mut out = Vec::with_capacity(units.len());
    for u in units {
        match u8::try_from(u) {
            Ok(b) => out.push(b),
            Err(_) => return Err(type_error(scope, "Value is not a valid ByteString")),
        }
    }
    Ok(out)
}

/// §3.2.12† `USVString`: "Let string be the result of converting V to a
/// DOMString. Return an IDL USVString value that is the result of
/// converting string to a sequence of scalar values." (Infra: each lone
/// surrogate becomes U+FFFD.)
///
/// # Errors
/// What ToString throws.
pub fn usv_string(scope: &mut Scope<'_>, v: Local<'_>) -> Result<String> {
    let units = dom_string(scope, v, false)?;
    Ok(char::decode_utf16(units)
        .map(|c| c.unwrap_or('\u{FFFD}'))
        .collect())
}

/// §3.2.13† `object`: "If V is not an Object, then throw a TypeError.
/// Return the IDL object value that is a reference to the same object as V."
///
/// # Errors
/// The TypeError.
pub fn object<'s>(scope: &mut Scope<'_>, v: Local<'s>) -> Result<Local<'s>> {
    if !is_object(scope, v) {
        return Err(type_error(scope, "Value is not an object"));
    }
    Ok(v)
}

/// §3.2.15† interface types: "If V implements I, then return the IDL
/// interface type value that represents a reference to that platform
/// object. Throw a TypeError."
///
/// # Errors
/// The TypeError.
pub fn interface<P: Platform>(
    scope: &mut Scope<'_>,
    v: Local<'_>,
    iface: InterfaceId,
) -> Result<ObjectKey> {
    match implements::<P>(scope, v, iface)? {
        Some(key) => Ok(key),
        None => {
            let message = format!("Value is not of type '{}'", iface.name());
            Err(type_error(scope, &message))
        }
    }
}

/// §3.2.16† callback interface types: "If V is not an Object, then throw a
/// TypeError. Return the IDL callback interface type value that represents
/// a reference to V, with the incumbent realm as the callback context."
/// (There is one realm, so the callback context is not kept.)
///
/// # Errors
/// The TypeError.
pub fn callback_interface<'s>(scope: &mut Scope<'_>, v: Local<'s>) -> Result<Local<'s>> {
    if !is_object(scope, v) {
        return Err(type_error(
            scope,
            "Value is not an object, so not a callback interface",
        ));
    }
    Ok(v)
}

/// §3.2.21† callback function types: "If the result of calling IsCallable(V)
/// is false and the conversion to an IDL value is not being performed due to
/// V being assigned to an attribute whose type is a nullable callback
/// function that is annotated with [LegacyTreatNonObjectAsNull], then throw
/// a TypeError. Return the IDL callback function type value that represents
/// a reference to the same object that V represents."
///
/// # Errors
/// The TypeError.
pub fn callback_function<'s>(scope: &mut Scope<'_>, v: Local<'s>) -> Result<Local<'s>> {
    if !scope.is_callable(v) {
        return Err(type_error(scope, "Value is not a function"));
    }
    Ok(v)
}

/// The conversion of an event handler IDL attribute's value (HTML §8.1.8.1†
/// `EventHandler`: a nullable `[LegacyTreatNonObjectAsNull]` callback
/// function, §3.2.21†): "If V is not an Object, return null" (so `undefined`,
/// numbers and strings clear the handler), and an Object, callable or not, is
/// the callback; one that is not callable does nothing when it is called
/// ("invoke": "If IsCallable(F) is false ... return").
#[must_use]
pub fn event_handler<'s>(scope: &Scope<'_>, v: Local<'s>) -> Option<Local<'s>> {
    is_object(scope, v).then_some(v)
}

/// §3.2.20† `sequence<T>`, for an Array only (see the module's modelling
/// choices): "If V is not an Object, throw a TypeError." Then the elements
/// in index order, each converted with `item`.
///
/// # Errors
/// The TypeErrors, and what `item` throws.
pub fn sequence<T>(
    scope: &mut Scope<'_>,
    v: Local<'_>,
    mut item: impl FnMut(&mut Scope<'_>, Local<'_>) -> Result<T>,
) -> Result<Vec<T>> {
    if !is_object(scope, v) {
        return Err(type_error(
            scope,
            "Value is not an object, so not a sequence",
        ));
    }
    if !scope.is_array(v)? {
        return Err(type_error(
            scope,
            "Only an Array converts to a sequence (the engine has no Symbol.iterator yet)",
        ));
    }
    let len = scope.get(v, Key::Str("length"))?;
    let len = scope.to_number(len)?;
    let mut out = Vec::new();
    let mut i: u32 = 0;
    while f64::from(i) < len {
        let e = scope.get(v, Key::Index(i))?;
        out.push(item(scope, e)?);
        match i.checked_add(1) {
            Some(n) => i = n,
            None => break,
        }
    }
    Ok(out)
}

/// §3.2.20† the other way: "Let A be ! ArrayCreate(0). ... For each element
/// of the sequence, CreateDataPropertyOrThrow(A, i, the element converted)."
///
/// # Errors
/// What making the array throws.
pub fn from_sequence<'s>(scope: &mut Scope<'s>, items: &[Local<'_>]) -> Result<Local<'s>> {
    scope.new_array_from(items)
}

/// §3.2.10† the other way: "the ECMAScript String value that represents the
/// same sequence of code units".
#[must_use]
pub fn from_dom_string<'s>(scope: &mut Scope<'s>, s: &[u16]) -> Local<'s> {
    scope.string_utf16(s)
}

/// §3.2.12† the other way, for a `USVString`.
#[must_use]
pub fn from_usv_string<'s>(scope: &mut Scope<'s>, s: &str) -> Local<'s> {
    scope.string(s)
}

/// §3.2.11† the other way, for a `ByteString`: each byte a code unit.
#[must_use]
pub fn from_byte_string<'s>(scope: &mut Scope<'s>, s: &[u8]) -> Local<'s> {
    let units: Vec<u16> = s.iter().map(|b| u16::from(*b)).collect();
    scope.string_utf16(&units)
}

/// §3.2.15† the other way: the wrapper ([`wrap`]).
///
/// # Errors
/// As [`wrap`].
pub fn from_interface<'s, P: AllInterfaces>(
    scope: &mut Scope<'s>,
    key: ObjectKey,
) -> Result<Local<'s>> {
    wrap::<P>(scope, key)
}

/// For a nullable value: "If V is null, return null" the other way.
///
/// # Errors
/// What `f` returns.
pub fn from_nullable<'s, T>(
    scope: &mut Scope<'s>,
    v: Option<T>,
    f: impl FnOnce(&mut Scope<'s>, T) -> Result<Local<'s>>,
) -> Result<Local<'s>> {
    match v {
        Some(x) => f(scope, x),
        None => Ok(scope.null()),
    }
}

/// A numeric IDL value as an ECMAScript Number (§3.2.4† to §3.2.8† the other
/// way: "the Number value that represents the same numeric value").
#[must_use]
pub fn from_number<'s>(scope: &mut Scope<'s>, x: f64) -> Local<'s> {
    scope.number(x)
}

/// Calls a user object's operation (WebIDL §3.11† "call a user object's
/// operation", for a callback interface value such as an `EventListener`):
/// 4. Let X be O. (thisArg)
/// 5. If IsCallable(O) is false, then: 1. Let getResult be Get(O, opName).
///    2. ... 3. Set X to getResult.[[Value]]. 4. If IsCallable(X) is false,
///    then throw a TypeError. 5. Set thisArg to O.
/// 6. Let esArgs be the result of converting args to an ECMAScript
///    arguments list.
/// 7. Let callResult be Call(X, thisArg, esArgs).
///
/// # Errors
/// The TypeError, and what the callback throws.
pub fn call_user_object_operation<'s>(
    scope: &mut Scope<'s>,
    object: Local<'_>,
    op: &str,
    this: Local<'_>,
    args: &[Local<'_>],
) -> Result<Local<'s>> {
    if scope.is_callable(object) {
        return scope.call(object, this, args);
    }
    let x = scope.get(object, Key::Str(op))?;
    if !scope.is_callable(x) {
        let message = format!("'{op}' of the listener is not a function");
        return Err(type_error(scope, &message));
    }
    scope.call(x, object, args)
}
