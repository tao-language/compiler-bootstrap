import core/ast as core
import core/format
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/desugar.{new_block_ctx}

const s = Span("desugar_test", 1, 1, 1, 1)

const unit = core.Expr(core.Rcd([], None), s, None)

fn fmt(e) {
  format.expr(e, 80, 2)
}

pub fn desugar_stmt_import_simple_test() {
  let stmt = tao.import_("m", None, [], s)
  let expr = desugar.statement([], new_block_ctx, stmt, unit)
  assert expr.trace == Some("import m")
  assert fmt(expr) == "%let m = `/m`\n{}"
}

pub fn desugar_stmt_import_path_name_test() {
  let stmt = tao.import_("path/to/m", None, [], s)
  let expr = desugar.statement([], new_block_ctx, stmt, unit)
  assert expr.trace == Some("import path/to/m")
  assert fmt(expr) == "%let m = `/path/to/m`\n{}"
}

pub fn desugar_stmt_import_alias_test() {
  let stmt = tao.import_("path/to/m", Some("n"), [], s)
  let expr = desugar.statement([], new_block_ctx, stmt, unit)
  assert expr.trace == Some("import path/to/m")
  assert fmt(expr) == "%let n = `/path/to/m`\n{}"
}

pub fn desugar_stmt_import_expose_name_test() {
  let stmt = tao.import_("m", None, [#("x", None)], s)
  let expr = desugar.statement([], new_block_ctx, stmt, unit)
  assert expr.trace == Some("import m")
  assert fmt(expr) == "%let m = `/m`\n%let x = %get(`/m`).x\n{}"
}

pub fn desugar_stmt_import_expose_name_alias_test() {
  let stmt = tao.import_("m", None, [#("x", Some("y"))], s)
  let expr = desugar.statement([], new_block_ctx, stmt, unit)
  assert expr.trace == Some("import m")
  assert fmt(expr) == "%let m = `/m`\n%let y = %get(`/m`).x\n{}"
}
