import core/context
import core/resolve
import core/term as tm
import core/value as v
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/declare
import tao/define

const s = Span("define_test", 0, 0, 0, 0)

pub fn define_set_var_test() {
  let ctx = context.new_ctx

  let ctx = define.set_var(ctx, "m1", "x", v.int(1), v.int_t)
  assert ctx.errors == []
  assert ctx.types == [#("m1", v.rcd([#("x", v.int_t)]))]
  assert ctx.env == [v.rcd([#("x", v.int(1))])]

  let ctx = define.set_var(ctx, "m1", "y", v.int(2), v.int_t)
  assert ctx.errors == []
  assert ctx.types == [#("m1", v.rcd([#("x", v.int_t), #("y", v.int_t)]))]
  assert ctx.env == [v.rcd([#("x", v.int(1)), #("y", v.int(2))])]

  let ctx = define.set_var(ctx, "m2", "z", v.int(3), v.int_t)
  assert ctx.errors == []
  assert ctx.types
    == [
      #("m1", v.rcd([#("x", v.int_t), #("y", v.int_t)])),
      #("m2", v.rcd([#("z", v.int_t)])),
    ]
  assert ctx.env
    == [
      v.rcd([#("x", v.int(1)), #("y", v.int(2))]),
      v.rcd([#("z", v.int(3))]),
    ]
}

pub fn define_type_stmt_let_var_untyped_test() {
  let ctx = context.new_ctx
  let stmt = tao.let_var("x", None, tao.int(42, s), s)
  let #(val, typ, ctx) = define.type_stmt(ctx, [], "m", "x", stmt)
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
  assert ctx.env == [v.rcd([#("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_type_stmt_let_var_typed_test() {
  let ctx = context.new_ctx
  let stmt = tao.let_var("x", Some(tao.int_t(s)), tao.int(42, s), s)
  let #(val, typ, ctx) = define.type_stmt(ctx, [], "m", "x", stmt)
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.int_t
  assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
  assert ctx.env == [v.rcd([#("x", val)])]
  assert ctx.hole_counter == 1
}

pub fn define_type_stmt_extern_test() {
  let ctx = context.new_ctx
  let stmt = tao.extern("@f", #([], None), tao.int_t(s), s)
  let #(val, typ, ctx) = define.type_stmt(ctx, [], "m", "@f", stmt)
  assert ctx.errors == []
  assert val == v.Err
  assert typ
    == v.Pi(
      [],
      #("__args", v.rcd([])),
      tm.Match(tm.Var(0), [tm.Case(tm.PRcd([], None), None, tm.int_t)]),
    )
  assert ctx.types == [#("m", v.rcd([#("@f", typ)]))]
  assert ctx.env == [v.rcd([#("@f", val)])]
  assert ctx.hole_counter == 0
}

pub fn define_type_stmt_fn_overload_test() {
  let ctx = context.new_ctx
  let defs = [
    #("m", [
      #("f1", tao.extern("f1", #([], None), tao.int_t(s), s)),
      #("f2", tao.extern("f2", #([], None), tao.float_t(s), s)),
    ]),
  ]
  let choices = [
    tao.OverloadChoice(tao.OverloadCall("f1"), [], None, s),
    tao.OverloadChoice(tao.OverloadCall("f2"), [], None, s),
  ]
  let stmt = tao.fn_overload("f", choices, s)
  let #(val, typ, ctx) = define.type_stmt(ctx, defs, "m", "f", stmt)
  assert ctx.errors == []
  assert val == v.Err
  assert typ
    == v.Pi(
      [],
      #("__args", v.rcd([])),
      tm.Match(tm.Var(0), [tm.Case(tm.PRcd([], None), None, tm.int_t)]),
    )
  assert ctx.types == []
  assert ctx.env == []
  assert ctx.hole_counter == 0
}

pub fn define_type_name_cached_test() {
  let ctx = context.new_ctx
  let ctx = define.set_var(ctx, "m", "x", v.int(1), v.int_t)
  let #(val, typ, ctx) = define.type_name(ctx, [], "m", "x")
  assert ctx.errors == []
  assert val == v.int(1)
  assert typ == v.int_t
  assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
  assert ctx.env == [v.rcd([#("x", val)])]
  assert ctx.hole_counter == 0
}

// pub fn define_type_name_undefined_module_test() {
//   let ctx = context.new_ctx
//   let defs = []
//   let exports = declare.exports(defs)
//   let #(val, typ, ctx) = define.signature(ctx, defs, exports, "m", "x")
//   assert ctx.errors == []
//   assert val == v.Err
//   assert typ == v.Err
//   assert ctx.types == []
//   assert ctx.env == []
//   assert ctx.hole_counter == 0
// }

// pub fn define_type_name_undefined_definition_test() {
//   let ctx = context.new_ctx
//   let defs = []
//   let exports = declare.exports(defs)
//   let #(val, typ, ctx) = define.signature(ctx, defs, exports, "m", "x")
//   assert ctx.errors == []
//   assert val == v.int(1)
//   assert typ == v.int_t
//   assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
//   assert ctx.env == [v.rcd([#("x", val)])]
//   assert ctx.hole_counter == 0
// }

pub fn define_type_name_direct_test() {
  let ctx = context.new_ctx
  let let_x = tao.let_var("x", Some(tao.int_t(s)), tao.int(1, s), s)
  let defs = [#("m", [#("x", let_x)])]
  let #(val, typ, ctx) = define.type_name(ctx, defs, "m", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.int_t
  assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
  assert ctx.env == [v.rcd([#("x", val)])]
  assert ctx.hole_counter == 1
}

pub fn define_type_name_indirect_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let let_x = tao.let_var("x", Some(tao.var("int", s)), tao.int(1, s), s)
  let defs = [#("m", [#("int", let_int), #("x", let_x)])]
  let #(val, typ, ctx) = define.type_name(ctx, defs, "m", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types == [#("m", v.rcd([#("int", v.Typ(0)), #("x", typ)]))]
  assert ctx.env == [v.rcd([#("int", typ), #("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_type_name_indirect_reverse_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let let_x = tao.let_var("x", Some(tao.var("int", s)), tao.int(1, s), s)
  let defs = [#("m", [#("x", let_x), #("int", let_int)])]
  let #(val, typ, ctx) = define.type_name(ctx, defs, "m", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types == [#("m", v.rcd([#("int", v.Typ(0)), #("x", typ)]))]
  assert ctx.env == [v.rcd([#("int", typ), #("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_type_name_imported_name_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let import_m1_int = tao.import_some("m1", "", [#("int", "m1_int")], s)
  let let_x = tao.let_var("x", Some(tao.var("m1_int", s)), tao.int(1, s), s)
  let defs = [
    #("/m1", [#("int", let_int)]),
    #("/m2", [#("m1_int", import_m1_int), #("x", let_x)]),
  ]
  let #(val, typ, ctx) = define.type_name(ctx, defs, "/m2", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types
    == [
      #("/m1", v.rcd([#("int", v.Typ(0))])),
      #("/m2", v.rcd([#("x", v.hole([], 1))])),
    ]
  assert ctx.env == [v.rcd([#("int", typ)]), v.rcd([#("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_type_name_imported_name_reverse_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let import_m1_int = tao.import_some("m1", "", [#("int", "m1_int")], s)
  let let_x = tao.let_var("x", Some(tao.var("m1_int", s)), tao.int(1, s), s)
  let defs = [
    #("/m2", [#("m1_int", import_m1_int), #("x", let_x)]),
    #("/m1", [#("int", let_int)]),
  ]
  let #(val, typ, ctx) = define.type_name(ctx, defs, "/m2", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types
    == [
      #("/m1", v.rcd([#("int", v.Typ(0))])),
      #("/m2", v.rcd([#("x", v.hole([], 1))])),
    ]
  assert ctx.env == [v.rcd([#("int", typ)]), v.rcd([#("x", val)])]
  assert ctx.hole_counter == 2
}
