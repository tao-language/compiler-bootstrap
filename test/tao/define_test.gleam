import core/context
import core/resolve
import core/value as v
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
import tao/declare
import tao/define

const s = Span("define_test", 0, 0, 0, 0)

// pub fn signature(
//   ctx: Context,
//   defs: List(#(ModName, List(#(Name, Stmt)))),
//   exports: List(#(ModName, List(Name))),
//   mod_name: ModName,
//   name: Name,
// ) -> #(v.Value, v.Type, Context) {

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

// TODO: define.stmt_type

pub fn define_signature_cached_test() {
  let ctx = context.new_ctx
  let ctx = define.set_var(ctx, "m", "x", v.int(1), v.int_t)
  let #(val, typ, ctx) = define.signature(ctx, [], "m", "x")
  assert ctx.errors == []
  assert val == v.int(1)
  assert typ == v.int_t
  assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
  assert ctx.env == [v.rcd([#("x", val)])]
  assert ctx.hole_counter == 0
}

// pub fn define_signature_undefined_module_test() {
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

// pub fn define_signature_undefined_definition_test() {
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

pub fn define_signature_direct_test() {
  let ctx = context.new_ctx
  let let_x = tao.let_var("x", Some(tao.int_t(s)), tao.int(1, s), s)
  let defs = [#("m", [#("x", let_x)])]
  let #(val, typ, ctx) = define.signature(ctx, defs, "m", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.int_t
  assert ctx.types == [#("m", v.rcd([#("x", typ)]))]
  assert ctx.env == [v.rcd([#("x", val)])]
  assert ctx.hole_counter == 1
}

pub fn define_signature_indirect_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let let_x = tao.let_var("x", Some(tao.var("int", s)), tao.int(1, s), s)
  let defs = [#("m", [#("int", let_int), #("x", let_x)])]
  let #(val, typ, ctx) = define.signature(ctx, defs, "m", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types == [#("m", v.rcd([#("int", v.Typ(0)), #("x", typ)]))]
  assert ctx.env == [v.rcd([#("int", typ), #("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_signature_indirect_reverse_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let let_x = tao.let_var("x", Some(tao.var("int", s)), tao.int(1, s), s)
  let defs = [#("m", [#("x", let_x), #("int", let_int)])]
  let #(val, typ, ctx) = define.signature(ctx, defs, "m", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types == [#("m", v.rcd([#("int", v.Typ(0)), #("x", typ)]))]
  assert ctx.env == [v.rcd([#("int", typ), #("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_signature_imported_name_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let import_m1_int = tao.import_("m1", None, [#("int", Some("m1_int"))], s)
  let let_x = tao.let_var("x", Some(tao.var("m1_int", s)), tao.int(1, s), s)
  let defs = [
    #("m1", [#("int", let_int)]),
    #("m2", [#("m1_int", import_m1_int), #("x", let_x)]),
  ]
  let #(val, typ, ctx) = define.signature(ctx, defs, "m2", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types
    == [
      #("m1", v.rcd([#("int", v.Typ(0))])),
      #("m2", v.rcd([#("x", v.hole([], 1))])),
    ]
  assert ctx.env == [v.rcd([#("int", typ)]), v.rcd([#("x", val)])]
  assert ctx.hole_counter == 2
}

pub fn define_signature_imported_name_reverse_test() {
  let ctx = context.new_ctx
  let let_int = tao.let_var("int", Some(tao.typ(s)), tao.int_t(s), s)
  let import_m1_int = tao.import_("m1", None, [#("int", Some("m1_int"))], s)
  let let_x = tao.let_var("x", Some(tao.var("m1_int", s)), tao.int(1, s), s)
  let defs = [
    #("m2", [#("m1_int", import_m1_int), #("x", let_x)]),
    #("m1", [#("int", let_int)]),
  ]
  let #(val, typ, ctx) = define.signature(ctx, defs, "m2", "x")
  assert ctx.errors == []
  assert val == v.hole([], 0)
  assert typ == v.hole([], 1)
  assert ctx.types
    == [
      #("m1", v.rcd([#("int", v.Typ(0))])),
      #("m2", v.rcd([#("x", v.hole([], 1))])),
    ]
  assert ctx.env == [v.rcd([#("int", typ)]), v.rcd([#("x", val)])]
  assert ctx.hole_counter == 2
}
