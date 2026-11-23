// A stand-in for WPT's /resources/testharness.js, for clazel-web's
// tests/wpt_dom.rs. It is NOT testharness.js: the engine cannot load that
// file yet (it fails at load with "undefined is not a function"; it needs
// Promise, RegExp and more). It defines the synchronous subset the dom/ tests
// use, in the language the engine has: `test` runs its function and records
// a pass, or a failure with the thrown message; the assertions throw. An
// `async_test` or `promise_test` is recorded as "skipped" (the page has no
// event loop wired to the engine yet, item 7.15), never as a pass.
var window = this;
var self = this;
var __results = [];
var __cleanups = [];

function __message(e) {
  if (e && typeof e === "object" && typeof e.message === "string") {
    return (e.name ? e.name + ": " : "") + e.message;
  }
  return String(e);
}

function __show(v) {
  if (typeof v === "string") {
    return '"' + v + '"';
  }
  if (v === null || v === undefined || typeof v !== "object") {
    return String(v);
  }
  if (typeof v.nodeType === "number") {
    return "node " + v.nodeName;
  }
  return "object";
}

function __fail(desc, message) {
  throw new Error((desc ? desc + ": " : "") + message);
}

function setup() {}
function done() {}
function add_completion_callback() {}
function add_result_callback() {}
function step_timeout(f) {}

function test(fn, name) {
  var t = {
    name: name,
    step: function (f) {
      var args = [];
      for (var i = 1; i < arguments.length; i++) {
        args.push(arguments[i]);
      }
      return f.apply(t, args);
    },
    step_func: function (f) {
      return function () {
        return f.apply(t, arguments);
      };
    },
    add_cleanup: function (f) {
      __cleanups.push(f);
    },
    unreached_func: function (m) {
      return function () {
        __fail(m, "unreached");
      };
    },
    done: function () {}
  };
  var ok = true;
  var message = "";
  try {
    fn.call(t, t);
  } catch (e) {
    ok = false;
    message = __message(e);
  }
  while (__cleanups.length > 0) {
    var c = __cleanups.pop();
    try {
      c();
    } catch (e2) {}
  }
  __results.push({ name: name, status: ok ? "pass" : "fail", message: message });
  return t;
}

function async_test(a, b) {
  __results.push({ name: String(typeof a === "string" ? a : b), status: "skip", message: "async_test" });
  return {
    step: function () {},
    step_func: function (f) { return f; },
    step_func_done: function (f) { return f; },
    unreached_func: function () { return function () {}; },
    add_cleanup: function () {},
    done: function () {}
  };
}

function promise_test(f, name) {
  __results.push({ name: String(name), status: "skip", message: "promise_test" });
}

function generate_tests(fn, rows) {
  for (var i = 0; i < rows.length; i++) {
    var row = rows[i];
    var args = row.slice(1);
    (function (row, args) {
      test(function () {
        fn.apply(this, args);
      }, row[0]);
    })(row, args);
  }
}

function __same(a, b) {
  if (a !== a && b !== b) {
    return true;
  }
  if (a === 0 && b === 0) {
    return 1 / a === 1 / b;
  }
  return a === b;
}

function assert_equals(actual, expected, desc) {
  if (!__same(actual, expected)) {
    __fail(desc, "expected " + __show(expected) + " but got " + __show(actual));
  }
}

function assert_not_equals(actual, expected, desc) {
  if (__same(actual, expected)) {
    __fail(desc, "got disallowed value " + __show(actual));
  }
}

function assert_true(actual, desc) {
  if (actual !== true) {
    __fail(desc, "expected true but got " + __show(actual));
  }
}

function assert_false(actual, desc) {
  if (actual !== false) {
    __fail(desc, "expected false but got " + __show(actual));
  }
}

function assert_array_equals(actual, expected, desc) {
  if (actual === null || actual === undefined || typeof actual.length !== "number") {
    __fail(desc, "value is not an array-like: " + __show(actual));
  }
  if (actual.length !== expected.length) {
    __fail(desc, "lengths differ, expected " + expected.length + " got " + actual.length);
  }
  for (var i = 0; i < actual.length; i++) {
    if (!__same(actual[i], expected[i])) {
      __fail(desc, "item " + i + " differs: expected " + __show(expected[i]) + " got " + __show(actual[i]));
    }
  }
}

function assert_in_array(actual, expected, desc) {
  for (var i = 0; i < expected.length; i++) {
    if (expected[i] === actual) {
      return;
    }
  }
  __fail(desc, "value " + __show(actual) + " not in array");
}

function assert_unreached(desc) {
  __fail(desc, "reached unreachable code");
}

function assert_class_string(object, class_string, desc) {
  var actual = Object.prototype.toString.call(object);
  if (actual !== "[object " + class_string + "]") {
    __fail(desc, "expected [object " + class_string + "] but got " + actual);
  }
}

var __CODES = {
  IndexSizeError: 1, HierarchyRequestError: 3, WrongDocumentError: 4,
  InvalidCharacterError: 5, NoModificationAllowedError: 7, NotFoundError: 8,
  NotSupportedError: 9, InUseAttributeError: 10, InvalidStateError: 11,
  SyntaxError: 12, InvalidModificationError: 13, NamespaceError: 14,
  InvalidAccessError: 15, TypeMismatchError: 17, SecurityError: 18,
  NetworkError: 19, AbortError: 20, URLMismatchError: 21, TimeoutError: 23,
  InvalidNodeTypeError: 24, DataCloneError: 25
};

// testharness.js's table of legacy constant names.
var __LEGACY = {
  INDEX_SIZE_ERR: "IndexSizeError", HIERARCHY_REQUEST_ERR: "HierarchyRequestError",
  WRONG_DOCUMENT_ERR: "WrongDocumentError", INVALID_CHARACTER_ERR: "InvalidCharacterError",
  NO_MODIFICATION_ALLOWED_ERR: "NoModificationAllowedError", NOT_FOUND_ERR: "NotFoundError",
  NOT_SUPPORTED_ERR: "NotSupportedError", INUSE_ATTRIBUTE_ERR: "InUseAttributeError",
  INVALID_STATE_ERR: "InvalidStateError", SYNTAX_ERR: "SyntaxError",
  INVALID_MODIFICATION_ERR: "InvalidModificationError", NAMESPACE_ERR: "NamespaceError",
  INVALID_ACCESS_ERR: "InvalidAccessError", TYPE_MISMATCH_ERR: "TypeMismatchError",
  SECURITY_ERR: "SecurityError", NETWORK_ERR: "NetworkError", ABORT_ERR: "AbortError",
  URL_MISMATCH_ERR: "URLMismatchError", TIMEOUT_ERR: "TimeoutError",
  INVALID_NODE_TYPE_ERR: "InvalidNodeTypeError", DATA_CLONE_ERR: "DataCloneError"
};

function assert_throws_dom(type, funcOrCtor, descOrFunc, desc) {
  if (typeof type === "string" && __LEGACY[type] !== undefined) {
    type = __LEGACY[type];
  }
  var func = funcOrCtor;
  if (typeof funcOrCtor === "function" && typeof descOrFunc === "function") {
    func = descOrFunc;
    desc = desc;
  } else {
    desc = descOrFunc;
  }
  var threw = false;
  var error;
  try {
    func.call(this);
  } catch (e) {
    threw = true;
    error = e;
  }
  if (!threw) {
    __fail(desc, "function did not throw");
  }
  if (typeof type === "number") {
    if (!error || error.code !== type) {
      __fail(desc, "expected code " + type + " got " + __show(error && error.name));
    }
  } else {
    if (!error || error.name !== type) {
      __fail(desc, "expected " + type + " got " + __message(error));
    }
    if (error.code !== __CODES[type] && __CODES[type] !== undefined) {
      __fail(desc, "wrong code " + error.code + " for " + type);
    }
  }
}

function assert_throws_js(constructor, func, desc) {
  var threw = false;
  var error;
  try {
    func.call(this);
  } catch (e) {
    threw = true;
    error = e;
  }
  if (!threw) {
    __fail(desc, "function did not throw");
  }
  if (!(error instanceof constructor)) {
    __fail(desc, "expected " + constructor.name + " got " + __message(error));
  }
}

function assert_throws_exactly(exception, func, desc) {
  var threw = false;
  var error;
  try {
    func.call(this);
  } catch (e) {
    threw = true;
    error = e;
  }
  if (!threw) {
    __fail(desc, "function did not throw");
  }
  if (error !== exception) {
    __fail(desc, "threw a different value");
  }
}

function assert_readonly(object, property, desc) {
  var initial = object[property];
  try {
    object[property] = initial + "a";
    assert_equals(object[property], initial, desc);
  } finally {
    object[property] = initial;
  }
}

function __summary() {
  var pass = 0;
  var fail = 0;
  var skip = 0;
  var lines = [];
  for (var i = 0; i < __results.length; i++) {
    var r = __results[i];
    if (r.status === "pass") {
      pass++;
    } else if (r.status === "fail") {
      fail++;
      lines.push("FAIL " + r.name + " -- " + r.message);
    } else {
      skip++;
      lines.push("SKIP " + r.name + " -- " + r.message);
    }
  }
  return pass + "|" + fail + "|" + skip + "\n" + lines.join("\n");
}
