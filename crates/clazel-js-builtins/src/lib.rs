//! The global object's built-ins (phase-7.md item 7.9, the first groups).
//!
//! [`install`] adds to a [`Vm`]'s global object, and to its intrinsics table
//! ([`clazel_js_vm::interp::Intrinsic`]), these built-ins of ECMA-262:
//!
//! - [`object`]: `Object` (§20.1†), `Object.prototype.toString` (with
//!   `@@toStringTag`), `toLocaleString`, `hasOwnProperty`, `valueOf`, and
//!   `Object.keys`, `defineProperty`, `getPrototypeOf`, `create`;
//! - [`function`]: `Function` (§20.2†, whose constructor needs the compiler
//!   and so throws `NotYet`) and `Function.prototype.call`, `apply`, `bind`,
//!   `@@hasInstance`;
//! - [`error`]: `Error` and the `TypeError`, `RangeError`, `SyntaxError` and
//!   `ReferenceError` native errors (§20.5†), which the VM's own throws use;
//! - [`symbol`]: `Symbol` (§20.4†) with `Symbol.for`, `Symbol.keyFor`, the
//!   well-known symbols, and `Symbol.prototype.toString`, `valueOf`,
//!   `@@toPrimitive`, `@@toStringTag`;
//! - [`iterator`]: `%Iterator.prototype%` (§27.1.2†), and the Array and String
//!   iterators (§23.1.5†, §22.1.5†) that spread, `for`-`of` and
//!   destructuring run through the VM's iteration ops;
//! - [`boolean`]: `Boolean` (§20.3†);
//! - [`number`]: `Number` (§21.1†) with `toString`, `toFixed`,
//!   `toExponential`, `toPrecision`, `toLocaleString` over
//!   `clazel-js-number`;
//! - [`string`]: `String` (§22.1†) with `fromCharCode`, `fromCodePoint`,
//!   `raw` and the methods of `String.prototype` but `normalize` and the
//!   Annex B HTML methods (its module header lists them, and what waits for
//!   RegExp);
//! - [`array`]: `Array` (§23.1†), `Array.isArray`, `Array.of`, `Array.from`
//!   and `Array.prototype` (its module header lists the methods), with
//!   `@@iterator` and `@@unscopables`;
//! - [`json`]: `JSON.parse` and `JSON.stringify` (§25.5†) over `clazel-json`;
//! - [`math`]: the pure functions of `Math` (§21.3†);
//! - [`global`]: `globalThis`, `isNaN`, `isFinite`, `parseInt`, `parseFloat`
//!   (§19†).
//!
//! # What this slice does not have, all listed
//!
//! - **`get Array [ @@species ]`** and every other accessor: the VM has data
//!   properties only, so a descriptor with `get` or `set` is `NotYet`,
//!   `Symbol.prototype.description` is absent, and ArraySpeciesCreate uses
//!   the constructor itself when it has no `@@species` property (see
//!   [`array`]). Objects are always extensible.
//! - **No `Iterator` constructor or iterator helpers** (§27.1.3†), no
//!   generators' `%GeneratorPrototype%`, no `Array.fromAsync`.
//! - **Array elements are ordinary shape properties** (the heap's elements
//!   are an open pull request), so a huge sparse index or a long `shift` is
//!   slow, not wrong.
//! - **`Function.prototype` is an ordinary object**, not a function (a
//!   `typeof Function.prototype` of `"object"`).
//! - **A `String` wrapper object has no index properties**, only `length`
//!   (a String exotic object's `[[GetOwnProperty]]`, §10.4.3.1†, is a later
//!   slice): `Object('ab')[0]` is `undefined`, and the generic `Array`
//!   methods see a String object's elements as holes. A primitive string's
//!   indices, and its iterator, are right.
//! - **`Number.prototype.toString` with a radix other than 10** gives the
//!   exact digits of the integer part and up to 52 binary places of the
//!   fraction; §21.1.3.6† leaves other radixes implementation-approximated.
//! - **No ECMA-402**: `toLocaleString`, `localeCompare` and the locale case
//!   conversions are the plain ones ([`string`] lists how).
//!
//! ECMA-262 is cited as `§n†`, the numbering of the pinned edition; each
//! built-in's comment quotes the algorithm's steps it covers.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod array;
pub mod boolean;
pub mod error;
pub mod function;
pub mod global;
pub mod iterator;
pub mod json;
pub mod math;
pub mod number;
pub mod object;
pub mod promise;
pub mod string;
pub mod symbol;
pub mod util;

use clazel_js_vm::interp::{Abrupt, Vm};

/// Installs the built-ins of this crate in the realm of `vm`.
///
/// # Errors
/// [`Abrupt::OutOfMemory`] if the heap is too small, or the error of a
/// heap operation that fails.
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    object::install(vm)?;
    symbol::install(vm)?;
    iterator::install(vm)?;
    function::install(vm)?;
    array::install(vm)?;
    error::install(vm)?;
    boolean::install(vm)?;
    number::install(vm)?;
    string::install(vm)?;
    math::install(vm)?;
    json::install(vm)?;
    promise::install(vm)?;
    global::install(vm)
}
