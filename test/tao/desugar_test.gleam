import core/ast as core
import core/format
import core/literals as lit
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

// ============================================================================
// Tuples: strict numbered records (no tail)
// ============================================================================

pub fn desugar_tuple_expr_test() {
  // () => {} ; (x) => {1: x} ; (x, y, z) => {1: x, 2: y, 3: z}
  let e = tao.tuple([tao.int(1, s), tao.int(2, s)], s)
  let expected =
    core.rcd_values(
      [#("1", core.lit(lit.Int(1), s)), #("2", core.lit(lit.Int(2), s))],
      None,
      s,
    )
  assert desugar.expr([], e) == expected
  assert desugar.expr([], tao.tuple([], s)) == core.rcd_values([], None, s)
}

pub fn desugar_tuple_pattern_test() {
  // Tuple patterns desugar to strict (no-tail) numbered record patterns,
  // mirroring the tuple expression.
  let p = tao.ptuple([tao.pvar("x", s), tao.pvar("y", s)], s)
  let expected =
    core.prcd([#("1", core.pvar("x", s)), #("2", core.pvar("y", s))], None, s)
  assert desugar.pattern(p) == expected
  assert desugar.pattern(tao.ptuple([], s)) == core.prcd([], None, s)
}

pub fn desugar_op2_and_test() {
  // A named operator desugars to an application of its function:
  // `a and b` => and(#{1: a, 2: b})
  let e = tao.op2(tao.And, tao.var("a", s), tao.var("b", s), s)
  // Positional call arguments keep their empty names (`pop_field`
  // consumes them in order when the callee unpacks numbered parameters).
  let expected =
    core.app(
      core.var("and", s),
      core.rcd_values(
        [#("", core.var("a", s)), #("", core.var("b", s))],
        None,
        s,
      ),
      s,
    )
  assert desugar.expr([], e) == expected
}
