import core/context
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/declare

const s = Span("declare_test", 0, 0, 0, 0)

// TODO: declare.statement

pub fn declare_modules_empty_test() {
  assert declare.modules([]) == []
}

pub fn declare_modules_stmts0_test() {
  let mods = [#("m", [])]
  assert declare.modules(mods) == [#("m", [])]
}

pub fn declare_modules_stmts1_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let mods = [#("m", [let_x])]
  assert declare.modules(mods) == [#("m", [#("x", let_x)])]
}

pub fn declare_modules_stmts2_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let let_y = tao.let_var("y", None, tao.int(2, s), s)
  let mods = [#("m", [let_x, let_y])]
  assert declare.modules(mods) == [#("m", [#("x", let_x), #("y", let_y)])]
}

pub fn declare_modules_multi_module_test() {
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let let_y = tao.let_var("y", None, tao.int(2, s), s)
  let mods = [#("m1", [let_x]), #("m2", [let_y])]
  assert declare.modules(mods)
    == [#("m1", [#("x", let_x)]), #("m2", [#("y", let_y)])]
}
// TODO: declare.exports (trivial)

// pub fn declare_stmt_import_test() {
//   let stmt = tao.import_("mod", None, [], s)
//   assert declare.stmt(stmt) == []
// }

// pub fn declare_stmt_let_var_untyped_test() {
//   let mods = []
//   let stmt = tao.let_var("x", None, tao.int(42, s), s)
//   assert declare.stmt(mods, stmt) == [#("x", None)]
// }

// pub fn declare_stmt_let_var_typed_test() {
//   let mods = []
//   let stmt = tao.let_var("x", Some(tao.int_t(s)), tao.int(42, s), s)
//   assert declare.stmt(mods, stmt) == [#("x", Some(tao.int_t(s)))]
// }

// pub fn declare_stmt_test_test() {
//   let mods = []
//   let stmt = tao.test_(">>> test", tao.int(42, s), tao.pany(s), s)
//   assert declare.stmt(mods, stmt) == [#(">>> test", None)]
// }
