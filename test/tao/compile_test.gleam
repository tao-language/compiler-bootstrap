import core/context.{new_ctx}
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/compile

const s = Span("compile_test", 1, 1, 1, 1)

pub fn compile_package_empty_test() {
  let ctx0 = new_ctx
  let ctx = compile.package(ctx0, [])
  assert ctx.errors == []
  assert ctx.env == []
  assert ctx.types == []
}

pub fn compile_package_modules_empty_test() {
  let ctx0 = new_ctx
  let m1 = []
  let m2 = []
  let ctx = compile.package(ctx0, [#("m1", m1), #("m2", m2)])
  assert ctx.errors == []
  assert ctx.env == [v.Rcd([]), v.Rcd([])]
  assert ctx.types == [#("@m2", v.RcdT([])), #("@m1", v.RcdT([]))]
}

pub fn compile_package_import_test() {
  let ctx0 = new_ctx
  let m1 = [tao.let_(tao.pvar("x", s), None, tao.int(42, s), s)]
  let m2 = [
    tao.import_("m1", None, [#("x", None)], s),
    tao.let_(tao.pvar("y", s), None, tao.var("x", s), s),
  ]
  let ctx = compile.package(ctx0, [#("m1", m1), #("m2", m2)])
  assert ctx.errors == []
  assert ctx.env == [v.Rcd([#("y", v.int(42))]), v.Rcd([#("x", v.int(42))])]
  assert ctx.types
    == [
      #("@m2", v.RcdT([#("y", #(v.int_t, None))])),
      #("@m1", v.RcdT([#("x", #(v.int_t, None))])),
    ]
}

pub fn compile_package_import_alias_test() {
  let ctx0 = new_ctx
  let m1 = [tao.let_(tao.pvar("x", s), None, tao.int(42, s), s)]
  let m2 = [
    tao.import_("m1", Some("m"), [#("x", Some("z"))], s),
    tao.let_(tao.pvar("y", s), None, tao.var("z", s), s),
  ]
  let ctx = compile.package(ctx0, [#("m1", m1), #("m2", m2)])
  assert ctx.errors == []
  assert ctx.env == [v.Rcd([#("y", v.int(42))]), v.Rcd([#("x", v.int(42))])]
  assert ctx.types
    == [
      #("@m2", v.RcdT([#("y", #(v.int_t, None))])),
      #("@m1", v.RcdT([#("x", #(v.int_t, None))])),
    ]
}
