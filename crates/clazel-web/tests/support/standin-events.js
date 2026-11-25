// A stand-in for WPT's /resources/testharness.js, for clazel-web's
// tests/wpt_events.rs. It is NOT testharness.js: the engine cannot run that
// yet (it needs Promise and RegExp, which are the engine crates' work). It
// defines what the listed dom/events pages call, in the subset of the
// language the engine has, with the same meaning: `test` runs its function
// at once, `async_test` waits for `done()`, `step_func` and friends run a
// function inside the test and fail it if an assertion throws. A page passes
// when every subtest it made passed and was done. The runner reads
// `__summary()`.
var window = this;
var self = this;
var __tests = [];

function __AssertionError(message) {
  this.message = message;
  this.name = "AssertionError";
}

function __fail(message) {
  throw new __AssertionError(message);
}

function __show(v) {
  if (v === null) return "null";
  if (v === undefined) return "undefined";
  if (typeof v === "string") return '"' + v + '"';
  if (typeof v === "object" || typeof v === "function") {
    try {
      var s = v.nodeName || v.type || String(v);
      return "[" + typeof v + " " + s + "]";
    } catch (e) {
      return "[" + typeof v + "]";
    }
  }
  return String(v);
}

function __same(a, b) {
  if (a !== a && b !== b) return true;
  if (a === 0 && b === 0) return 1 / a === 1 / b;
  return a === b;
}

function Test(name) {
  this.name = name;
  this.status = "running";
  this.message = "";
  this.cleanups = [];
  __tests.push(this);
}

Test.prototype.__fail = function (e) {
  if (this.status !== "running") return;
  this.status = "fail";
  this.message = (e && e.message !== undefined) ? e.name + ": " + e.message : String(e);
};

// The engine has no `arguments` object yet: the functions below take up to
// four arguments, which is what the listed pages pass.
Test.prototype.step = function (f, thisObj, a, b, c, d) {
  try {
    return f.call(thisObj === undefined ? this : thisObj, a, b, c, d);
  } catch (e) {
    this.__fail(e);
  }
};

// As testharness.js has it, `this` inside the function is the test (not the
// caller's `this`) unless `thisObj` is given.
Test.prototype.step_func = function (f, thisObj) {
  var t = this;
  return function (a, b, c, d) {
    try {
      return f.call(thisObj === undefined ? t : thisObj, a, b, c, d);
    } catch (e) {
      t.__fail(e);
    }
  };
};

Test.prototype.step_func_done = function (f, thisObj) {
  var t = this;
  return function (a, b, c, d) {
    try {
      if (f) f.call(thisObj === undefined ? t : thisObj, a, b, c, d);
    } catch (e) {
      t.__fail(e);
    }
    t.done();
  };
};

Test.prototype.unreached_func = function (message) {
  var t = this;
  return function () {
    t.__fail(new __AssertionError("unreachable: " + message));
  };
};

Test.prototype.add_cleanup = function (f) {
  this.cleanups.push(f);
};

Test.prototype.done = function () {
  if (this.status === "running") this.status = "pass";
  for (var i = 0; i < this.cleanups.length; i++) {
    try {
      this.cleanups[i]();
    } catch (e) {}
  }
  this.cleanups = [];
};

// `setup({single_test: true})`: the page is one test that `done()` ends, and
// an assertion that throws outside a step is an uncaught exception, which
// the runner counts as a failure of the page.
var __single = null;

function setup(options) {
  if (options && options.single_test) __single = new Test("single test");
}

function done() {
  if (__single) __single.done();
}
function add_completion_callback() {}
function add_result_callback() {}

function test(f, name) {
  var t = new Test(name === undefined ? "" : name);
  t.step(f, t, t);
  t.done();
  return t;
}

function async_test(a, b) {
  var name = typeof a === "string" ? a : (b === undefined ? "" : b);
  var t = new Test(name);
  if (typeof a === "function") t.step(a, t, t);
  return t;
}

function generate_tests(f, rows) {
  for (var i = 0; i < rows.length; i++) {
    var row = rows[i];
    var t = new Test(row[0]);
    t.step(function () {
      f.call(t, row[1], row[2], row[3], row[4]);
    });
    t.done();
  }
}

function assert_true(v, d) {
  if (v !== true) __fail("expected true, got " + __show(v) + (d ? " (" + d + ")" : ""));
}

function assert_false(v, d) {
  if (v !== false) __fail("expected false, got " + __show(v) + (d ? " (" + d + ")" : ""));
}

function assert_equals(a, b, d) {
  if (!__same(a, b)) {
    __fail("expected " + __show(b) + ", got " + __show(a) + (d ? " (" + d + ")" : ""));
  }
}

function assert_not_equals(a, b, d) {
  if (__same(a, b)) __fail("got disallowed value " + __show(a) + (d ? " (" + d + ")" : ""));
}

function assert_array_equals(a, b, d) {
  if (a.length !== b.length) {
    __fail("lengths differ: got " + a.length + ", expected " + b.length + (d ? " (" + d + ")" : ""));
  }
  for (var i = 0; i < a.length; i++) {
    if (!__same(a[i], b[i])) {
      __fail("item " + i + ": got " + __show(a[i]) + ", expected " + __show(b[i]) + (d ? " (" + d + ")" : ""));
    }
  }
}

function assert_in_array(v, list, d) {
  for (var i = 0; i < list.length; i++) {
    if (list[i] === v) return;
  }
  __fail(__show(v) + " not in array" + (d ? " (" + d + ")" : ""));
}

function assert_unreached(d) {
  __fail("reached unreachable code" + (d ? ": " + d : ""));
}

function assert_class_string(o, s, d) {
  var got = Object.prototype.toString.call(o);
  if (got !== "[object " + s + "]") __fail("class: expected " + s + ", got " + got);
}

function assert_own_property(o, p, d) {
  if (!Object.prototype.hasOwnProperty.call(o, p)) __fail("expected own property " + p);
}

function assert_throws_dom(name, f, d) {
  if (typeof name === "function") {
    d = f;
    f = name;
    name = undefined;
  }
  try {
    f();
  } catch (e) {
    if (name !== undefined && e.name !== name) {
      __fail("expected DOMException " + name + ", got " + e.name);
    }
    return;
  }
  __fail("expected a DOMException " + name + ", nothing was thrown");
}

function assert_throws_exactly(exp, f, d) {
  try {
    f();
  } catch (e) {
    if (e !== exp) __fail("expected to throw the given value, threw " + __show(e));
    return;
  }
  __fail("expected the given value to be thrown, nothing was");
}

function assert_throws_js(ctor, f, d) {
  try {
    f();
  } catch (e) {
    if (!(e instanceof ctor)) __fail("expected " + ctor.name + ", got " + (e && e.name));
    return;
  }
  __fail("expected " + ctor.name + ", nothing was thrown");
}

function assert_greater_than(a, b, d) {
  if (!(a > b)) __fail(a + " is not greater than " + b);
}

function assert_greater_than_equal(a, b, d) {
  if (!(a >= b)) __fail(a + " is not greater than or equal to " + b);
}

function assert_less_than_equal(a, b, d) {
  if (!(a <= b)) __fail(a + " is not less than or equal to " + b);
}

function format_value(v) {
  return __show(v);
}

// The runner's reading: "pass/fail/running" counts and the failures.
function __summary() {
  var pass = 0, fail = 0, running = 0, notes = [];
  for (var i = 0; i < __tests.length; i++) {
    var t = __tests[i];
    if (t.status === "pass") pass++;
    else if (t.status === "fail") {
      fail++;
      notes.push(t.name + ": " + t.message);
    } else {
      running++;
      notes.push(t.name + ": did not finish");
    }
  }
  return pass + "/" + fail + "/" + running + (notes.length ? " " + notes.join(" | ") : "");
}
