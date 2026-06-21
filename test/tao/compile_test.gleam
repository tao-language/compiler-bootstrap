import core/context.{new_ctx}
import core/eval.{eval}
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/compile
import tao/tests

const s = Span("compile_test", 0, 0, 0, 0)

const s1 = Span("compile_test", 1, 1, 1, 1)

const s2 = Span("compile_test", 2, 2, 2, 2)

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
  assert ctx.types == [#("@m1", v.RcdT([])), #("@m2", v.RcdT([]))]
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
  assert ctx.env
    == [
      v.Rcd([#("x", v.int(42))]),
      v.Rcd([#("y", v.int(42))]),
    ]
  assert ctx.types
    == [
      #("@m1", v.RcdT([#("x", #(v.int_t, None))])),
      #("@m2", v.RcdT([#("y", #(v.int_t, None))])),
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
  assert ctx.env
    == [
      v.Rcd([#("x", v.int(42))]),
      v.Rcd([#("y", v.int(42))]),
    ]
  assert ctx.types
    == [
      #("@m1", v.RcdT([#("x", #(v.int_t, None))])),
      #("@m2", v.RcdT([#("y", #(v.int_t, None))])),
    ]
}

pub fn compile_tests_empty_test() {
  let ctx0 = new_ctx
  let m = []
  let #(tests, ctx) = compile.tests(ctx0, [#("empty", m)])
  assert ctx.errors == []
  assert tests == []
}

pub fn compile_tests_simple_test() {
  let vars = [
    #("x", Some(v.int(42)), None),
  ]
  let ctx0 = context.push_var_list(new_ctx, vars)
  let m = [
    tao.test_("test_pass", tao.var("x", s1), tao.pint(42, s2), s),
    tao.test_("test_fail", tao.var("x", s1), tao.pint(0, s2), s),
  ]
  let #(test_defs, ctx) = compile.tests(ctx0, [#("simple", m)])
  assert ctx.errors == []
  let results = list.map(test_defs, tests.run(ctx, _))
  let expected = [
    tests.TestPass("test_pass"),
    tests.TestFail("test_fail", v.int(42), tao.var("x", s1), tao.pint(0, s2)),
  ]
  assert results == expected
}
