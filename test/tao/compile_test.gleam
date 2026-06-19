import core/context.{new_ctx}
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{None}
import syntax/span.{Span}
import tao/ast as tao
import tao/compile

const s = Span("compile_test", 1, 1, 1, 1)

pub fn compile_package_empty_test() {
  let ctx0 = new_ctx
  let #(mods, ctx) = compile.package(ctx0, [])
  assert ctx.errors == []
  assert mods == []
}

pub fn compile_package_modules_empty_test() {
  let ctx0 = new_ctx
  let m1 = []
  let m2 = []
  let #(mods, ctx) = compile.package(ctx0, [#("m1", m1), #("m2", m2)])
  assert ctx.errors == []
  assert list.map(mods, fn(m) { #(m.0, m.1.0) })
    == [
      #("m1", tm.Rcd([])),
      #("m2", tm.Rcd([])),
    ]
  assert list.map(mods, fn(m) { #(m.0, m.1.1) })
    == [
      #("m1", v.RcdT([])),
      #("m2", v.RcdT([])),
    ]
}

pub fn compile_package_imports_test() {
  let ctx0 = new_ctx
  let m1 = [tao.let_(tao.pvar("x", s), None, tao.int(42, s), s)]
  let m2 = [
    tao.import_("m1", None, [#("x", None)], s),
    tao.let_(tao.pvar("y", s), None, tao.var("x", s), s),
  ]
  let #(mods, ctx) = compile.package(ctx0, [#("m1", m1), #("m2", m2)])
  assert ctx.errors == []
  let tm_m1_value =
    tm.let_var(#("x", tm.int_t, tm.int(42)), tm.Rcd([#("x", tm.Var(0))]))
  let tm_m1_type = tm.RcdT([#("x", #(tm.int_t, None))])
  assert list.map(mods, fn(m) { #(m.0, m.1.0) })
    == [
      #("m1", tm_m1_value),
      #(
        "m2",
        tm.let_var_list(
          [
            #("m1", tm_m1_type, tm.Rcd([#("x", tm.int(42))])),
            #("x", tm.int_t, tm.int(42)),
            #("y", tm.int_t, tm.Var(0)),
          ],
          tm.Rcd([#("y", tm.Var(0))]),
        ),
      ),
    ]
  assert list.map(mods, fn(m) { #(m.0, m.1.1) })
    == [
      #("m1", v.RcdT([#("x", #(v.int_t, None))])),
      #("m2", v.RcdT([#("y", #(v.int_t, None))])),
    ]
}
