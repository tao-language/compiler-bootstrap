import core/ast as core
import core/context.{Context, new_ctx}
import core/eval.{eval}
import core/infer.{check, infer}
import core/resolve
import core/term as tm
import core/unify.{unify}
import core/value as v
import gleam/option.{None, Some}
import syntax/span.{Span}

const s = Span("polymorphism_test", 0, 0, 0, 0)

fn monomorphic_expr() {
  // identity: %lam(x) => x
  core.lam(#("x", None), core.var("x", s), s)
}

fn monomorphic_term() {
  // identity: %lam(x: %Int) => x
  tm.Lam(#("x", tm.int_t), tm.Var(0))
}

fn monomorphic_val() {
  // identity: %lam(x: %Int) => x
  v.Lam([], #("x", v.int_t), tm.Var(0))
}

fn polymorphic_expr() {
  // typeof: %for(a: $Type). %lam(x: a) => x
  core.for(
    #("a", Some(core.typ(0, s))),
    core.lam(#("x", Some(core.var("a", s))), core.var("x", s), s),
    s,
  )
}

fn polymorphic_term() {
  // typeof: %for(a: $Type). %lam(x: a) => x
  tm.For(#("a", tm.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
}

fn polymorphic_val() {
  // typeof: %for(a: $Type). %lam(x: a) => a
  v.For([], #("a", v.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
}

pub fn polymorphism_monomorphic_lam_test() {
  let ctx = new_ctx
  let fn_expr = monomorphic_expr()
  let fn_term = monomorphic_term()
  let expr = core.app(fn_expr, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(fn_term, [tm.int(42)])
  assert type_ == v.int_t
  assert ctx.hole_counter == 0
}

pub fn polymorphism_monomorphic_var_test() {
  let ctx = new_ctx
  let fn_val = monomorphic_val()
  let ctx = context.push_var(ctx, #("fun", Some(fn_val), None))
  let f = core.var("fun", s)
  let expr = core.app(f, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(tm.Var(0), [tm.int(42)])
  assert type_ == v.hole([v.int(42), fn_val], 1)
  assert ctx.hole_counter == 2
}

pub fn polymorphism_monomorphic_declaration_test() {
  let ctx = new_ctx
  let fn_expr = monomorphic_expr()
  let fn_val = monomorphic_val()
  // Declarations (module skeletons)
  let #(value_id, ctx) = context.new_hole(ctx)
  let #(type_id, ctx) = context.new_hole(ctx)
  let mod_decl = v.rcd([#("fun", v.hole([], value_id))])
  let mod_types = v.rcd([#("fun", v.hole([], type_id))])
  let ctx = context.push_var(ctx, #("mod", Some(mod_decl), Some(mod_types)))
  let f = core.dot(core.var("mod", s), "fun", s)
  let expr = core.app(f, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(tm.hole(0), [tm.int(42)])
  assert type_ == v.hole([v.int(42), mod_decl], 4)
  assert ctx.hole_counter == 5
  // Definitions (solve declarations)
  let mod_expr = core.rcd_values([#("fun", fn_expr)], None, s)
  let #(mod_term, mod_type, ctx) = check(ctx, mod_expr, #(mod_types, s))
  let mod_val = eval(ctx.ffi, ctx.env, mod_term)
  let ctx = unify(ctx, #(mod_decl, s), #(mod_val, s))
  let ctx = resolve.context(ctx)
  // TODO: The Pi-parameter name should be "x", not "$4"
  // This comes from infer_app on neutral function type
  // Since we use DeBruijn indices, it's not incorrect, but name "x" is more readable
  let expected_mod_type =
    v.rcd([#("fun", v.Pi([], #("$4", v.int_t), tm.int_t))])
  assert resolve.value(ctx.ffi, ctx.subst, mod_type) == expected_mod_type
  assert ctx.types == [#("mod", expected_mod_type)]
  assert ctx.env == [v.rcd([#("fun", fn_val)])]
}

pub fn polymorphism_polymorphic_lam_test() {
  let ctx = new_ctx
  let fn_expr = polymorphic_expr()
  let fn_term = polymorphic_term()
  let expr = core.app(fn_expr, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(fn_term, [tm.hole(0), tm.int(42)])
  assert resolve.value(ctx.ffi, ctx.subst, type_) == v.int_t
  assert ctx.hole_counter == 1
}

pub fn polymorphism_polymorphic_var_test() {
  let ctx = new_ctx
  let fn_val = polymorphic_val()
  let ctx = context.push_var(ctx, #("fun", Some(fn_val), None))
  let f = core.var("fun", s)
  let expr = core.app(f, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(tm.Var(0), [tm.int(42)])
  assert type_ == v.hole([v.int(42), fn_val], 1)
  assert ctx.hole_counter == 2
}

pub fn polymorphism_polymorphic_declaration_test() {
  let ctx = new_ctx
  let fn_expr = polymorphic_expr()
  let fn_val = polymorphic_val()
  // Declarations (module skeletons)
  let #(value_id, ctx) = context.new_hole(ctx)
  let #(type_id, ctx) = context.new_hole(ctx)
  let mod_decl = v.rcd([#("fun", v.hole([], value_id))])
  let mod_types =
    v.rcd([#("fun", v.For([], #("$type", v.Typ(0)), tm.hole(type_id)))])
  let ctx = context.push_var(ctx, #("mod", Some(mod_decl), Some(mod_types)))
  let f = core.dot(core.var("mod", s), "fun", s)
  let expr = core.app(f, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(tm.hole(0), [tm.hole(4), tm.int(42)])
  assert type_ == v.hole([v.int(42), mod_decl], 5)
  assert ctx.hole_counter == 6
  // Definitions (solve declarations)
  let mod_expr = core.rcd_values([#("fun", fn_expr)], None, s)
  let #(mod_term, mod_type, ctx) = check(ctx, mod_expr, #(mod_types, s))
  let mod_val = eval(ctx.ffi, ctx.env, mod_term)
  let ctx = unify(ctx, #(mod_decl, s), #(mod_val, s))
  let ctx = resolve.context(ctx)
  // ⚠️ BUG: the polymorphic type gets collapsed into a monomorphic type
  // TODO: The Pi-parameter name should be "x", not "$5"
  let expected_mod_type =
    v.rcd([
      #(
        "fun",
        v.For([], #("$type", v.Typ(0)), tm.Pi(#("$5", tm.Var(0)), tm.Var(0))),
      ),
    ])
  assert resolve.value(ctx.ffi, ctx.subst, mod_type) == expected_mod_type
  assert ctx.types == [#("mod", expected_mod_type)]
  assert ctx.env == [v.rcd([#("fun", fn_val)])]
}
