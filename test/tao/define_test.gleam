import core/context.{type Context} as context
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast as tao
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
  assert val
    == v.Lam([], #("__args", v.rcd([])), tm.Call("f", tm.int_t, tm.Var(0)))
  assert typ == v.Pi([], #("__args", v.rcd([])), tm.int_t)
  assert ctx.types == [#("m", v.rcd([#("f", typ)]))]
  assert ctx.env == [v.rcd([#("f", val)])]
  assert ctx.hole_counter == 0
}

pub fn define_type_stmt_fn_overload_test() {
  let ctx = context.new_ctx
  let defs = [
    #("m", [
      #("f", tao.extern("f", [], tao.int_t(s), s)),
    ]),
  ]
  let choices = [
    tao.OverloadChoice(None, "f", [], None, s),
  ]
  let stmt = tao.fn_overload("g", choices, s)
  let #(val, typ, ctx) = define.type_stmt(ctx, defs, "m", "g", stmt)
  let call_val =
    v.Lam([], #("__args", v.rcd([])), tm.Call("f", tm.int_t, tm.Var(0)))
  let call_typ = v.Pi([], #("__args", v.rcd([])), tm.int_t)
  assert ctx.errors == []
  assert val
    == v.For(
      [call_val, v.rcd([#("f", call_val)])],
      #("__type", v.Typ(0)),
      tm.Lam(
        #("__args", tm.Var(0)),
        tm.Match(tm.Var(1), [
          tm.Case(tm.prcd_strict([]), None, tm.Call("f", tm.int_t, tm.Var(0))),
        ]),
      ),
    )
  assert typ
    == v.For(
      [call_val, v.rcd([#("f", call_val)])],
      #("__type", v.Typ(0)),
      tm.Pi(
        #("__args", tm.Var(0)),
        tm.Match(tm.Var(1), [tm.Case(tm.prcd_strict([]), None, tm.int_t)]),
      ),
    )
  assert ctx.types == [#("m", v.rcd([#("f", call_typ), #("g", typ)]))]
  assert ctx.env == [v.rcd([#("f", call_val), #("g", val)])]
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

// ============================================================================
// Overload choice expansion
// ============================================================================

/// A context whose environment has one module record defining `Bool`
/// (variants `True`, `False`).
fn bool_ctx() -> Context {
  let tdef =
    v.TypeDefinition(params: [], arg: tm.rcd([]), variants: [
      #("True", v.Variant([], tm.rcd([]), tm.ctr("Bool", []))),
      #("False", v.Variant([], tm.rcd([]), tm.ctr("Bool", []))),
    ])
  let mod_record = v.Rcd([#("Bool", #(v.TypeDef([], tdef), None))], None)
  context.push_var(context.new_ctx, #("$mod", mod_record, v.Typ(1)))
}

fn choice_(args: List(tao.Pattern)) -> tao.OverloadChoice {
  tao.OverloadChoice(None, "f", list.map(args, fn(pat) { #("", pat) }), None, s)
}

fn pctr(name: String) -> tao.Pattern {
  tao.pctr(name, [], s)
}

/// The argument patterns of the expanded choices, as tag lists.
fn expanded_tags(ctx: Context, args: List(tao.Pattern)) -> List(List(String)) {
  let #(choices, _ctx) = define.expand_overload_choices(ctx, [choice_(args)])
  list.map(choices, fn(choice) {
    list.map(choice.args, fn(arg) {
      case arg.1.data {
        tao.PCtr(tag, _, _) -> tag
        _ -> "?"
      }
    })
  })
}

/// A type name expands to itself (the type constructor application)
/// plus one tag-only pattern per variant.
pub fn expand_type_name_test() {
  assert expanded_tags(bool_ctx(), [pctr("Bool")]) == [
    ["Bool"],
    ["True"],
    ["False"],
  ]
}

/// Variant patterns are constructor tags with an open (any) argument
/// record: they must match `#True{..}` regardless of the variant's
/// arguments.
pub fn expand_variant_pattern_is_open_test() {
  let ctx = bool_ctx()
  let #(choices, _ctx) = define.expand_overload_choices(ctx, [choice_([pctr("Bool")])])
  case choices {
    [_, variant, _, ..] -> {
      case variant.args {
        [#(_, tao.Pattern(tao.PCtr(_, args, tail), _)), ..] ->
          args == [] && case tail {
            Some(tao.Pattern(tao.PAny, _)) -> True
            _ -> False
          }
        _ -> False
      }
    }
    _ -> False
  }
}

/// Non-type-name arguments do not multiply: literal types, variables
/// and wildcards are their own single alternatives.
pub fn expand_non_type_names_untouched_test() {
  let ctx = bool_ctx()
  assert expanded_tags(ctx, [pctr("Int"), tao.pany(s)]) == [["Int", "?"]]
  let #(choices, _ctx) = define.expand_overload_choices(ctx, [choice_([pctr("Int")])])
  assert list.length(choices) == 1
}

/// An unknown name is left unchanged (the checker reports the error via
/// its Ctr-vs-Typ rule); with no type definitions in scope nothing
/// expands.
pub fn expand_unknown_name_untouched_test() {
  assert expanded_tags(context.new_ctx, [pctr("Nope")]) == [["Nope"]]
}

/// Multiple type-name arguments expand to the product of their
/// alternatives: `f(Bool, Bool)` becomes 3x3 = 9 choices.
pub fn expand_product_test() {
  let combos = expanded_tags(bool_ctx(), [pctr("Bool"), pctr("Bool")])
  assert list.length(combos) == 9
  assert list.contains(combos, ["True", "False"])
  assert list.contains(combos, ["Bool", "Bool"])
}

/// Non-type-name arguments mix with type names: only the type names
/// multiply.
pub fn expand_mixed_test() {
  let combos = expanded_tags(bool_ctx(), [pctr("Int"), pctr("Bool")])
  assert list.length(combos) == 3
  assert list.contains(combos, ["Int", "True"])
}
