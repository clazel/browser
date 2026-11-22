//! The global object's built-ins (phase-7.md item 7.9, first group).
//!
//! [`install`] adds to a [`Vm`]'s global object, and to its intrinsics table
//! ([`clazel_js_vm::interp::Intrinsic`]), these built-ins of ECMA-262:
//!
//! - [`object`]: `Object` (§20.1†), `Object.prototype.toString`,
//!   `hasOwnProperty`, `valueOf`, and `Object.keys`, `defineProperty`,
//!   `getPrototypeOf`, `create`;
//! - [`function`]: `Function` (§20.2†, whose constructor needs the compiler
//!   and so throws `NotYet`) and `Function.prototype.call`, `apply`, `bind`;
//! - [`error`]: `Error` and the `TypeError`, `RangeError`, `SyntaxError` and
//!   `ReferenceError` native errors (§20.5†), which the VM's own throws use;
//! - [`boolean`]: `Boolean` (§20.3†);
//! - [`number`]: `Number` (§21.1†) with `toString` and `toFixed` over
//!   `clazel-js-number`;
//! - [`string`]: `String` (§22.1†) with `charAt`, `charCodeAt`, `indexOf`,
//!   `slice`, `substring`;
//! - [`array`]: `Array` (§23.1†), `Array.isArray`, `Array.of` and the core of
//!   `Array.prototype` (`push`, `pop`, `shift`, `unshift`, `slice`, `splice`,
//!   `concat`, `join`, `toString`, `indexOf`, `lastIndexOf`, `includes`,
//!   `reverse`, `fill`, `forEach`, `map`, `filter`, `some`, `every`, `reduce`,
//!   `reduceRight`, `find`, `findIndex`, `sort`);
//! - [`json`]: `JSON.parse` and `JSON.stringify` (§25.5†) over `clazel-json`;
//! - [`math`]: the pure functions of `Math` (§21.3†);
//! - [`global`]: `globalThis`, `isNaN`, `isFinite`, `parseInt`, `parseFloat`
//!   (§19†).
//!
//! # What this slice does not have, all listed
//!
//! - **Array iteration is missing**: `Array.from`, `entries`, `keys`,
//!   `values` and `@@iterator` wait for Symbols and iterators; so does array
//!   spread (`GetIterator` is `NotYet`). `@@species` and
//!   `@@isConcatSpreadable` are not consulted: `ArraySpeciesCreate` uses the
//!   receiver's `constructor` itself. Not yet: `at`, `copyWithin`, `flat`,
//!   `flatMap`, `findLast`, `findLastIndex`, `toLocaleString`, the change-by-
//!   copy methods. Array elements are ordinary shape properties (the heap's
//!   elements are an open pull request), so a huge sparse index or a long
//!   `shift` is slow, not wrong.
//! - **No Symbols**, so `@@toPrimitive`, `@@toStringTag` and `@@hasInstance`
//!   are not consulted; `Object.prototype.toString` tags by internal slot
//!   only.
//! - **Data properties only**: no accessors, so a descriptor with `get` or
//!   `set` is `NotYet`; objects are always extensible.
//! - **`Function.prototype` is an ordinary object**, not a function (a
//!   `typeof Function.prototype` of `"object"`).
//! - **A `String` wrapper object has no index properties**, only `length`
//!   (a String exotic object's `[[GetOwnProperty]]`, §10.4.3.1†, is a later
//!   slice).
//! - **`Number.prototype.toString` with a radix other than 10** gives the
//!   exact digits of the integer part and up to 52 binary places of the
//!   fraction; §21.1.3.6† leaves other radixes implementation-approximated.
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
pub mod json;
pub mod math;
pub mod number;
pub mod object;
pub mod string;
pub mod util;

use clazel_js_vm::interp::{Abrupt, Vm};

/// Installs the built-ins of this crate in the realm of `vm`.
///
/// # Errors
/// [`Abrupt::OutOfMemory`] if the heap is too small, or the error of a
/// heap operation that fails.
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    object::install(vm)?;
    function::install(vm)?;
    array::install(vm)?;
    error::install(vm)?;
    boolean::install(vm)?;
    number::install(vm)?;
    string::install(vm)?;
    math::install(vm)?;
    json::install(vm)?;
    global::install(vm)
}
