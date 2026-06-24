import core/ast as core
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/desugar.{new_block_ctx}

const s = Span("desugar_test", 1, 1, 1, 1)

const unit = core.Expr(core.Rcd([]), s)

pub fn desugar_stmt_import_simple_test() {
  let stmt = tao.import_("m", None, [], s)
  assert desugar.statement(new_block_ctx, stmt, unit)
    == core.let_var(#("m", None, core.var("@m", s)), unit, s)
}

pub fn desugar_stmt_import_path_name_test() {
  let stmt = tao.import_("path/to/m", None, [], s)
  assert desugar.statement(new_block_ctx, stmt, unit)
    == core.let_var(#("m", None, core.var("@path/to/m", s)), unit, s)
}

pub fn desugar_stmt_import_alias_test() {
  let stmt = tao.import_("path/to/m", Some("n"), [], s)
  assert desugar.statement(new_block_ctx, stmt, unit)
    == core.let_var(#("n", None, core.var("@path/to/m", s)), unit, s)
}

pub fn desugar_stmt_import_expose_name_test() {
  let stmt = tao.import_("m", None, [#("x", None)], s)
  assert desugar.statement(new_block_ctx, stmt, unit)
    == core.let_var(
      #("m", None, core.var("@m", s)),
      core.let_var(#("x", None, core.dot(core.var("@m", s), "x", s)), unit, s),
      s,
    )
}

pub fn desugar_stmt_import_expose_name_alias_test() {
  let stmt = tao.import_("m", None, [#("x", Some("y"))], s)
  assert desugar.statement(new_block_ctx, stmt, unit)
    == core.let_var(
      #("m", None, core.var("@m", s)),
      core.let_var(#("y", None, core.dot(core.var("@m", s), "x", s)), unit, s),
      s,
    )
}
