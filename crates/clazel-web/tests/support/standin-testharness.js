// A stand-in for WPT's /resources/testharness.js and the execution-timing
// tests' testlib/testlib.js, for clazel-web's tests/scripting.rs
// (wpt_execution_timing). It is NOT testharness.js: the engine cannot run
// that yet (it needs try/catch, RegExp and Promise), and testlib.js needs
// the DOM bindings of item 7.12. It defines only what the listed tests call,
// in the subset of the language the engine has: a test passes when its
// `t.done()` runs and nothing threw.
var window = this;
var self = this;
var eventOrder = [];
var __done = false;
function log(s) {
  eventOrder.push(s);
}
function setup() {}
function __fail(message) {
  throw new Error(message);
}
function async_test() {
  return {
    step_func: function (f) {
      return f;
    },
    step: function (f) {
      f();
    },
    done: function () {
      __done = true;
    }
  };
}
function assert_array_equals(actual, expected) {
  if (actual.length !== expected.length) {
    __fail("lengths differ: got [" + actual.join(", ") + "], expected [" + expected.join(", ") + "]");
  }
  for (var i = 0; i < actual.length; i++) {
    if (actual[i] !== expected[i]) {
      __fail("item " + i + " differs: got [" + actual.join(", ") + "], expected [" + expected.join(", ") + "]");
    }
  }
}
