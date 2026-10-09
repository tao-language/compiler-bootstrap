/// Tests for the canonical naming rule and the unified project loader.
import gleam/list
import gleam/option.{None, Some}
import tao/load

pub fn canonical_name_in_package_test() {
  let paths = ["lib"]
  let pkg_names = ["prelude"]
  assert load.canonical_name(paths, pkg_names, "lib/prelude/v0.0.1/bool.tao")
    == "/prelude/bool"
}

pub fn canonical_name_in_package_nested_test() {
  let paths = ["lib"]
  let pkg_names = ["prelude"]
  assert
    load.canonical_name(paths, pkg_names, "lib/prelude/v0.0.1/operators/add.tao")
    == "/prelude/operators/add"
}

pub fn canonical_name_not_in_package_test() {
  let paths = ["lib"]
  let pkg_names = ["prelude"]
  assert load.canonical_name(paths, pkg_names, "main.tao") == "/main"
}

pub fn canonical_name_not_in_package_nested_test() {
  let paths = ["lib"]
  let pkg_names = ["prelude"]
  assert load.canonical_name(paths, pkg_names, "src/foo/bar.tao")
    == "/src/foo/bar"
}

pub fn canonical_name_multiple_packages_test() {
  let paths = ["lib"]
  let pkg_names = ["prelude", "foo"]
  assert load.canonical_name(paths, pkg_names, "lib/foo/v1.0.0/baz.tao")
    == "/foo/baz"
  assert load.canonical_name(paths, pkg_names, "lib/prelude/v0.0.1/bool.tao")
    == "/prelude/bool"
}

pub fn canonical_name_multiple_paths_test() {
  let paths = ["lib", "vendor"]
  let pkg_names = ["bar"]
  assert load.canonical_name(paths, pkg_names, "vendor/bar/v2.0.0/qux.tao")
    == "/bar/qux"
}

pub fn canonical_name_prefix_not_confused_test() {
  // "lib/prelude2/" should NOT match package "prelude"
  let paths = ["lib"]
  let pkg_names = ["prelude"]
  assert load.canonical_name(paths, pkg_names, "lib/prelude2/v1/a.tao")
    == "/lib/prelude2/v1/a"
}

// ── Prelude identity (Task 4) ────────────────────────────────────────────

pub fn is_prelude_root_test() {
  assert load.is_prelude("/prelude")
}

pub fn is_prelude_nested_test() {
  assert load.is_prelude("/prelude/bool")
  assert load.is_prelude("/prelude/operators/and")
}

pub fn is_prelude_prefix_not_confused_test() {
  // "/prelude2" must NOT be treated as the prelude.
  assert !load.is_prelude("/prelude2")
  assert !load.is_prelude("/prelude2/bool")
}

pub fn is_prelude_other_packages_test() {
  assert !load.is_prelude("/foo/a")
  assert !load.is_prelude("/main")
}

pub fn prelude_modules_filters_test() {
  let mods = [
    #("/prelude/bool", []),
    #("/main", []),
    #("/prelude/option", []),
    #("/foo/a", []),
  ]
  let names = list.map(load.prelude_modules(mods), fn(m) { m.0 })
  assert names == ["/prelude/bool", "/prelude/option"]
}

pub fn with_prelude_adds_when_absent_test() {
  assert load.with_prelude([]) == [#("prelude", None)]
}

pub fn with_prelude_idempotent_test() {
  let pkgs = [#("foo", Some("1.0")), #("prelude", None)]
  assert load.with_prelude(pkgs) == pkgs
  let pkgs2 = [#("foo", Some("1.0"))]
  assert load.with_prelude(pkgs2)
    == [#("foo", Some("1.0")), #("prelude", None)]
}
