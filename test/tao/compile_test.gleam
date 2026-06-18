import core/context.{new_ctx}
import core/term as tm
import core/value as v
import gleam/option.{None}
import syntax/span.{Span}
import tao/ast as tao
import tao/compile

const s = Span("discover_test", 1, 1, 1, 1)

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
  assert mods
    == [#("m1", #(tm.Rcd([]), v.RcdT([]))), #("m2", #(tm.Rcd([]), v.RcdT([])))]
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
  assert mods
    == [
      #(
        "m1",
        #(tm.Rcd([#("x", tm.int(42))]), v.RcdT([#("x", #(v.int_t, None))])),
      ),
      #(
        "m2",
        #(tm.Rcd([#("y", tm.int(42))]), v.RcdT([#("y", #(v.int_t, None))])),
      ),
    ]
}
