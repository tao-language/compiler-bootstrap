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
  let stmt = tao.extern("f", [], tao.int_t(s), s)
  let #(val, typ, ctx) = define.type_stmt(ctx, [], "m", "f", stmt)
  assert ctx.errors == []
  // Externs are first-class functions: the value is a hole that
  // define.values fills with a lambda wrapping the FFI call.
  assert val
    == v.Lam([], #("__args", v.rcd([])), tm.Call("f", tm.int_t, tm.Var(0)))
  // The type is a pi whose domain is the (empty) record of param types and
  // whose codomain is the return type directly (no unpack when there is
  // nothing to bind).
  assert typ == v.Pi([], #("__args", v.rcd([])), tm.int_t)
  assert ctx.types == [#("m", v.rcd([#("f", typ)]))]
  assert ctx.env == [v.rcd([#("f", val)])]
  assert ctx.hole_counter == 0
}

pub fn define_type_stmt_fn_overload_test() {
  todo
  // let ctx = context.new_ctx
  // let defs = [
  //   #("m", [
  //     #("call", tao.extern("call", #([], None), tao.int_t(s), s)),
  //   ]),
  // ]
  // let choices = [
  //   tao.OverloadVar("@call"), [], None, s),
  // ]
  // let stmt = tao.fn_overload("f", choices, s)
  // let #(val, typ, ctx) = define.type_stmt(ctx, defs, "m", "f", stmt)
  // // The extern's value is a hole (filled in define.values with a lambda
  // // wrapping the FFI call); the overload captures it in its environment.
  // let call_val = v.hole([], 0)
  // let call_typ = v.Pi([], #("__args", v.rcd([])), tm.int_t)
  // assert ctx.errors == []
  // assert val
  //   == v.For(
  //     [call_val, v.rcd([#("call", call_val)])],
  //     #("__type", v.Typ(0)),
  //     tm.Lam(
  //       #("__args", tm.Var(0)),
  //       tm.Match(tm.Var(1), [
  //         tm.Case(tm.prcd_strict([]), None, tm.Call("@call", tm.Var(0))),
  //       ]),
  //     ),
  //   )
  // assert typ
  //   == v.For(
  //     [call_val, v.rcd([#("call", call_val)])],
  //     #("__type", v.Typ(0)),
  //     tm.Pi(
  //       #("__args", tm.Var(0)),
  //       tm.Match(tm.Var(1), [tm.Case(tm.prcd_strict([]), None, tm.hole(1))]),
  //     ),
  //   )
  // assert ctx.types == [#("m", v.rcd([#("call", call_typ), #("f", typ)]))]
  // assert ctx.env == [v.rcd([#("call", call_val), #("f", val)])]
  // // Hole 0: the extern's value. Hole 1: the call's type (infer_call still
  // // gives builtin calls a fresh hole in this path).
  // assert ctx.hole_counter == 2
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
  let import_m1_int = tao.import_some("/m1", "", [#("int", "m1_int")], s)
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
      #("/m2", v.rcd([#("m1_int", v.Typ(0)), #("x", typ)])),
    ]
  assert ctx.env
    == [v.rcd([#("int", typ)]), v.rcd([#("m1_int", typ), #("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_type_name_imported_name_reverse_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let import_m1_int = tao.import_some("/m1", "", [#("int", "m1_int")], s)
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
      #("/m2", v.rcd([#("m1_int", v.Typ(0)), #("x", typ)])),
    ]
  assert ctx.env
    == [v.rcd([#("int", typ)]), v.rcd([#("m1_int", typ), #("x", val)])]
  assert ctx.hole_counter == 2
}
