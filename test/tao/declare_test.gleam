import gleam/list
import gleam/option.{None}
import syntax/span.{Span}
import tao/ast as tao
import tao/declare

const s = Span("declare_test", 0, 0, 0, 0)

// TODO: declare.statement

pub fn declare_modules_empty_test() {
  assert declare.modules([]) == #([], [])
}

pub fn declare_modules_stmts0_test() {
  let mods = [#("m", [])]
  assert declare.modules(mods) == #([#("m", [])], [])
}

pub fn declare_modules_stmts1_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let mods = [#("m", [let_x])]
  assert declare.modules(mods) == #([#("m", [#("x", let_x)])], [])
}

pub fn declare_modules_stmts2_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let let_y = tao.let_var("y", None, tao.int(2, s), s)
  let mods = [#("m", [let_x, let_y])]
  assert declare.modules(mods) == #([#("m", [#("x", let_x), #("y", let_y)])], [])
}

pub fn declare_modules_multi_module_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let let_y = tao.let_var("y", None, tao.int(2, s), s)
  let mods = [#("m1", [let_x]), #("m2", [let_y])]
  assert declare.modules(mods)
    == #([#("m1", [#("x", let_x)]), #("m2", [#("y", let_y)])], [])
}

pub fn declare_modules_missing_import_test() {
  let import_stmt = tao.import_all("/nonexistent", "alias", s)
  let mods = [#("m", [import_stmt])]
  let #(defs, errors) = declare.modules(mods)
  assert list.length(errors) == 1
  assert list.length(defs) == 1
}
// ============================================================================
// Relative import resolution
// ============================================================================

pub fn declare_relative_import_dot_test() {
  let import_stmt = tao.import_all("./bool", "bool", s)
  let mods = [#("/prelude/operators/and", [import_stmt])]
  let resolved = declare.resolve_relative_imports(mods)
  assert case resolved {
    [#("/prelude/operators/and", [tao.Stmt(tao.Import(path, _, _), _)])] ->
      path == "/prelude/operators/bool"
    _ -> False
  }
}

pub fn declare_relative_import_parent_test() {
  let import_stmt = tao.import_all("../bool", "bool", s)
  let mods = [#("/prelude/operators/and", [import_stmt])]
  let resolved = declare.resolve_relative_imports(mods)
  assert case resolved {
    [#("/prelude/operators/and", [tao.Stmt(tao.Import(path, _, _), _)])] ->
      path == "/prelude/bool"
    _ -> False
  }
}

pub fn declare_relative_import_grandparent_test() {
  let import_stmt = tao.import_all("../../bool", "bool", s)
  let mods = [#("/prelude/operators/and", [import_stmt])]
  let resolved = declare.resolve_relative_imports(mods)
  assert case resolved {
    [#("/prelude/operators/and", [tao.Stmt(tao.Import(path, _, _), _)])] ->
      path == "/bool"
    _ -> False
  }
}

pub fn declare_relative_import_subdir_test() {
  let import_stmt = tao.import_all("./sub/bool", "bool", s)
  let mods = [#("/prelude/operators/and", [import_stmt])]
  let resolved = declare.resolve_relative_imports(mods)
  assert case resolved {
    [#("/prelude/operators/and", [tao.Stmt(tao.Import(path, _, _), _)])] ->
      path == "/prelude/operators/sub/bool"
    _ -> False
  }
}

pub fn declare_absolute_import_unchanged_test() {
  let import_stmt = tao.import_all("/prelude/bool", "bool", s)
  let mods = [#("/prelude/operators/and", [import_stmt])]
  let resolved = declare.resolve_relative_imports(mods)
  assert case resolved {
    [#("/prelude/operators/and", [tao.Stmt(tao.Import(path, _, _), _)])] ->
      path == "/prelude/bool"
    _ -> False
  }
}

pub fn declare_relative_import_non_import_unchanged_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let mods = [#("/prelude/operators/and", [let_x])]
  let resolved = declare.resolve_relative_imports(mods)
  assert resolved == mods
}

/// Integration: a module with a relative import that resolves to an
/// existing module in the set.
pub fn declare_modules_relative_import_resolves_test() {
  let import_stmt = tao.import_all("../bool", "bool", s)
  let bool_def = tao.let_var("True", None, tao.int(1, s), s)
  let mods = [
    #("/prelude/bool", [bool_def]),
    #("/prelude/operators/and", [import_stmt]),
  ]
  let #(defs, errors) = declare.modules(mods)
  assert errors == []
  // The import should have been resolved to /prelude/bool and expanded
  assert case defs {
    [#(_bool_name, _bool_defs), #("/prelude/operators/and", and_defs), ..] ->
      list.any(and_defs, fn(d) { d.0 == "bool" })
    _ -> False
  }
}

/// Integration: a relative import that resolves to a non-existent module
/// produces an error.
pub fn declare_modules_relative_import_missing_test() {
  let import_stmt = tao.import_all("../nonexistent", "alias", s)
  let mods = [#("/prelude/operators/and", [import_stmt])]
  let #(_, errors) = declare.modules(mods)
  assert list.length(errors) == 1
}
