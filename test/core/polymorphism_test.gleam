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

fn monomorphic_val() {
  // identity: %lam(x: %Int) => x
  v.Lam([], #("x", v.int_t), tm.Var(0))
}

fn polymorphic_fn() {
  // typeof: %for(a: $Type). %lam(x: a) => a
  core.for(
    #("a", Some(core.typ(0, s))),
    core.lam(#("x", Some(core.var("a", s))), core.var("a", s), s),
    s,
  )
}

pub fn polymorphism_monomorphic_lam_test() {
  let ctx = new_ctx
  let f = monomorphic_expr()
  let expr = core.app(f, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(tm.Lam(#("x", tm.int_t), tm.Var(0)), [tm.int(42)])
  assert type_ == v.int_t
  assert ctx.hole_counter == 0
}

pub fn polymorphism_monomorphic_var_test() {
  let ctx = new_ctx
  let ctx = context.push_var(ctx, #("fun", Some(monomorphic_val()), None))
  let f = core.var("fun", s)
  let expr = core.app(f, core.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert term == tm.app(tm.Var(0), [tm.int(42)])
  assert type_ == v.hole([v.int(42), monomorphic_val()], 1)
  assert ctx.hole_counter == 2
}

pub fn polymorphism_monomorphic_declaration_test() {
  let ctx = new_ctx
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
  let mod_expr = core.rcd_values([#("fun", monomorphic_expr())], None, s)
  let #(mod_term, mod_type, ctx) = check(ctx, mod_expr, #(mod_types, s))
  let mod_val = eval(ctx.ffi, ctx.env, mod_term)
  let ctx = unify(ctx, #(mod_decl, s), #(mod_val, s))
  let ctx = resolve.context(ctx)
  assert ctx.types
    == [#("mod", v.rcd([#("fun", v.Pi([], #("$4", v.int_t), tm.int_t))]))]
  assert ctx.env == [v.rcd([#("fun", v.Lam([], #("x", v.int_t), tm.Var(0)))])]
}

pub fn polymorphism_polymorphic_concrete_test() {
  todo
}

pub fn polymorphism_polymorphic_declaration_test() {
  todo
}
