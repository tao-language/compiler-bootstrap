import core/ast as core
import core/format
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/desugar

const s = Span("desugar_test", 1, 1, 1, 1)

const unit = core.Expr(core.Rcd([], None), s, None)

fn fmt(e) {
  format.expr(e, 80, 2)
}

pub fn desugar_stmt_import_simple_test() {
  let stmt = tao.import_some("m", "n", [], s)
  let expr = desugar.statement([], stmt, unit)
  assert expr.trace == Some("import m")
  assert fmt(expr) == "%let n = m\n{}"
}

pub fn desugar_stmt_import_expose_name_test() {
  let stmt = tao.import_some("m", "n", [#("x", "y")], s)
  let expr = desugar.statement([], stmt, unit)
  assert expr.trace == Some("import m")
  assert fmt(expr) == "%let n = m\n%let y = %get(m).x\n{}"
}

pub fn desugar_stmt_type_def_bool_test() {
  let stmt =
    tao.Stmt(
      tao.TypeDef(
        "Bool",
        tao.TypeDefinition([], [
          tao.Variant("True", [], [], tao.ctr("Bool", [], s)),
          tao.Variant("False", [], [], tao.ctr("Bool", [], s)),
        ]),
      ),
      s,
    )
  let expr = desugar.statement([], stmt, unit)
  // A type definition is let-bound under its name with the universe type.
  assert fmt(expr)
    == "%let Bool: %Type = type {\n| True -> #Bool|\n  | False -> #Bool\n}\n{}"
}

pub fn desugar_stmt_type_def_option_test() {
  let stmt =
    tao.Stmt(
      tao.TypeDef(
        "Option",
        tao.TypeDefinition([#("a", None)], [
          tao.Variant(
            "Some",
            [],
            [#("", tao.var("a", s))],
            tao.ctr("Option", [#("a", tao.var("a", s))], s),
          ),
          tao.Variant(
            "None",
            [],
            [],
            tao.ctr("Option", [#("a", tao.var("a", s))], s),
          ),
        ]),
      ),
      s,
    )
  let expr = desugar.statement([], stmt, unit)
  assert fmt(expr)
    == "%let Option: %Type = type a: ? {\n| Some(a) -> #Option({a})|\n  | None -> #Option({a})\n}\n{}"
}
