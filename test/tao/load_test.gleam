/// Tests for the canonical naming rule and the unified project loader.
import gleam/option.{None}
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
