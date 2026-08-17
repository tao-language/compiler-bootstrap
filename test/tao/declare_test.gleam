import core/context
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/declare

const s = Span("declare_test", 0, 0, 0, 0)

pub fn declare_stmt_import_test() {
  let stmt = tao.import_("mod", None, [], s)
  assert declare.stmt(stmt) == []
}
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
