import core/context.{new_ctx}
import core/term as tm
import core/value as v
import gleam/option.{None}
import syntax/span.{Span}
import tao/ast as tao
import tao/compile

const s = Span("discover_test", 0, 0, 0, 0)

fn let_(pattern: tao.Pattern, value: tao.Expr) -> tao.Stmt {
  tao.let_(pattern, None, value, s)
}

pub fn compile_module_empty_test() {
  let ctx0 = new_ctx
  let stmts = []
  let #(term, type_, ctx) = compile.module(ctx0, #("m", stmts))
  assert ctx.errors == []
  assert term == tm.Rcd([])
  assert type_ == v.RcdT([])
}

pub fn compile_module_public_test() {
  let ctx0 = new_ctx
  let stmts = [
    let_(tao.pvar("x", s), tao.int(1, s)),
    let_(tao.pvar("y", s), tao.int(2, s)),
  ]
  let #(term, type_, ctx) = compile.module(ctx0, #("m", stmts))
  assert ctx.errors == []
  assert term == tm.Rcd([#("x", tm.int(1)), #("y", tm.int(2))])
  assert type_ == v.RcdT([#("x", #(v.int_t, None)), #("y", #(v.int_t, None))])
}

pub fn compile_module_private_test() {
  let ctx0 = new_ctx
  let stmts = [
    let_(tao.pvar("_x", s), tao.int(1, s)),
    let_(tao.pvar("_y", s), tao.int(2, s)),
  ]
  let #(term, type_, ctx) = compile.module(ctx0, #("m", stmts))
  assert ctx.errors == []
  assert term == tm.Rcd([])
  assert type_ == v.RcdT([])
}
