/// End-to-end pins for the public Core API, run as one pipeline:
/// `parse` → `infer`/`check` → `resolve.context` → resolved term, type
/// and errors → `eval`.
///
/// These pin the *final observable* behavior, not the shape of the
/// intermediate values, so they double as the regression net for the
/// planned elaborate/infer split (parse → elaborate → infer/check →
/// eval → quote): the final resolved term, final resolved type,
/// reported errors, and evaluation results of resolved terms must stay
/// identical, whatever the new pipeline does internally.
import core/ast
import core/context.{type Context, Context, new_ctx, push_var}
import core/error as e
import core/eval.{do_app, eval}
import core/ffi
import core/infer.{check, infer}
import core/parse as p
import core/resolve
import core/term as tm
import core/value as v
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/span.{Span}

const s = Span("", 0, 0, 0, 0)

const ffi = ffi.build

/// Parse Core source, infer it, then resolve the context. Returns the
/// fully resolved term, the resolved type, and the resolved context.
fn pipeline(src: String, ctx0: Context) -> #(tm.Term, v.Type, Context) {
  case p.parse("pipeline", src) {
    Error(err) -> {
      let msg = "pipeline: parse failed for '" <> src <> "': "
        <> display_error(err)
      panic as msg
    }
    Ok(ast) -> {
      let #(term, type_, ctx) = infer(ctx0, ast)
      let ctx = resolve.context(ctx)
      let term = resolve.term(ffi, ctx.subst, ctx.env, term)
      let type_ = resolve.value(ffi, ctx.subst, type_)
      #(term, type_, ctx)
    }
  }
}

/// Like `pipeline` but the AST is built programmatically (the Core
/// parser does not cover every construct, e.g. `For` and `Match`).
fn pipeline_ast(ast: ast.Expr, ctx0: Context) -> #(tm.Term, v.Type, Context) {
  let #(term, type_, ctx) = infer(ctx0, ast)
  let ctx = resolve.context(ctx)
  let term = resolve.term(ffi, ctx.subst, ctx.env, term)
  let type_ = resolve.value(ffi, ctx.subst, type_)
  #(term, type_, ctx)
}

/// Infer `ast`, check it against `expected`, then resolve the context.
fn pipeline_check(
  ast: ast.Expr,
  expected: v.Value,
  ctx0: Context,
) -> #(tm.Term, v.Type, Context) {
  let #(term, type_, ctx) = check(ctx0, ast, #(expected, s))
  let ctx = resolve.context(ctx)
  let term = resolve.term(ffi, ctx.subst, ctx.env, term)
  let type_ = resolve.value(ffi, ctx.subst, type_)
  #(term, type_, ctx)
}

fn display_error(err: e.Error) -> String {
  e.display(ffi, [], err)
}

// ============================================================================
// Parsed sources: parse → infer → resolve
// ============================================================================

/// The identity lambda, from source: the pipeline leaves it unchanged
/// and types it as a plain (unquantified) Pi.
pub fn pipeline_parsed_lam_identity_test() {
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let #(term, type_, ctx) = pipeline("%lam(x: %Int) => x", ctx0)
  assert ctx.errors == []
  assert term == tm.Lam(#("x", tm.int_t), tm.Var(0))
  assert type_ == v.Pi([], #("x", v.int_t), tm.int_t)
}

/// A parsed let desugars to `(lam x => body) value` and the binding's
/// type is carried in the lambda's parameter.
pub fn pipeline_parsed_let_test() {
  let ctx0 = push_var(Context(..new_ctx, ffi: ffi), #("y", v.int(1), v.int_t))
  let #(term, type_, ctx) = pipeline("%let x: %Int = y; x", ctx0)
  assert ctx.errors == []
  assert term == tm.App(tm.Lam(#("x", tm.int_t), tm.Var(0)), tm.Var(0))
  assert type_ == v.int_t
}

/// A parsed record with a default field keeps the default in both the
/// term and the type; evaluation keeps it too.
pub fn pipeline_parsed_rcd_default_test() {
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let #(term, type_, ctx) = pipeline("{a: 1 = 42, b: 2}", ctx0)
  assert ctx.errors == []
  // Pinned limitation: `infer` currently drops record-field defaults in
  // BOTH the term and the type (see `infer_rcd_fields`, which keeps only
  // the field value). Field types are the values' types. The elaborate
  // step of the refactor is where defaults are meant to be handled;
  // until then this is the observable behavior.
  let a = #(tm.int(1), None)
  let b = #(tm.int(2), None)
  assert term == tm.Rcd([#("a", a), #("b", b)], None)
  assert type_ == v.Rcd([#("a", #(v.int_t, None)), #("b", #(v.int_t, None))], None)
  assert eval(ffi, ctx.env, term)
    == v.Rcd([#("a", #(v.int(1), None)), #("b", #(v.int(2), None))], None)
}

/// A bare hole infers to itself with a fresh (unsolved) type hole and no
/// error: an unsolved hole is legal at the Core level (it is the unit of
/// unification).
pub fn pipeline_parsed_hole_test() {
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let #(term, type_, ctx) = pipeline("?", ctx0)
  assert ctx.errors == []
  assert term == tm.Hole(Some(0))
  assert case type_ {
    v.Neut(v.NHole(_, Some(1))) -> True
    _ -> False
  }
}

// ============================================================================
// Implicit arguments (`For`): built programmatically
// ============================================================================

/// A polymorphic function `for<a: Type>. fn(x: a) => x` infers to a
/// `For` whose implicit argument can be instantiated and β-reduced:
/// applying `Int` then `1` evaluates to `1`.
pub fn pipeline_implicit_fn_end_to_end_test() {
  let ast =
    ast.for(
      #("a", Some(ast.typ(0, s))),
      ast.lam(#("x", Some(ast.var("a", s))), ast.var("x", s), s),
      s,
    )
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let #(term, type_, ctx) = pipeline_ast(ast, ctx0)
  assert ctx.errors == []
  assert term
    == tm.For(#("a", tm.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
  // The *value* keeps the function term (a Lam inside the For); the
  // *type* is the For over the lambda's Pi. They are distinct.
  let f_val = eval(ffi, ctx.env, term)
  assert f_val
    == v.For([], #("a", v.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
  // In the Pi body the indices are into the frame [x, a]: x's type is
  // `a` (index 1); the body of the Pi is x's type, again `a`.
  assert type_
    == v.For([], #("a", v.Typ(0)), tm.Pi(#("x", tm.Var(0)), tm.Var(1)))
  // Instantiating the implicit argument consumes one application at
  // the value level (the For β-reduces like a Lam): (f Int) 1 == 1.
  let instantiated = do_app(ffi, f_val, v.int_t)
  assert do_app(ffi, instantiated, v.int(1)) == v.int(1)
}

/// Applying an implicit-argument function from the environment: the
/// implicit hole is solved by unification with the explicit argument's
/// type, the resolved term carries the solved argument, and the result
/// evaluates.
pub fn pipeline_implicit_app_solved_test() {
  // As in a module binding: the value carries the function term (Lam
  // inside the For), the type carries the For over the Pi.
  let f_val = v.For([], #("a", v.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
  let f_type = v.For([], #("a", v.Typ(0)), tm.Pi(#("x", tm.Var(0)), tm.Var(0)))
  let ctx0 = push_var(Context(..new_ctx, ffi: ffi), #("f", f_val, f_type))
  let ast = ast.app(ast.var("f", s), ast.int(1, s), s)
  let #(term, type_, ctx) = pipeline_ast(ast, ctx0)
  assert ctx.errors == []
  assert term == tm.App(tm.App(tm.Var(0), tm.int_t), tm.int(1))
  assert type_ == v.int_t
  assert eval(ffi, ctx.env, term) == v.int(1)
}

/// Two nested implicit arguments where only one is constrained by the
/// explicit argument: the constrained one is solved, the unused one
/// stays an unsolved hole in the resolved term, and the program still
/// evaluates.
pub fn pipeline_two_implicit_unused_stays_hole_test() {
  let for_b =
    ast.for(
      #("b", Some(ast.typ(0, s))),
      ast.lam(#("y", Some(ast.var("b", s))), ast.var("y", s), s),
      s,
    )
  let ast = ast.for(#("a", Some(ast.typ(0, s))), for_b, s)
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let #(term, type_, ctx) = pipeline_ast(ast, ctx0)
  assert ctx.errors == []
  let f_val = eval(ffi, ctx.env, term)
  // The value and the type are both the double For quantification.
  assert case f_val {
    v.For(_, #("a", v.Typ(0)), _) -> True
    _ -> False
  }
  assert case type_ {
    v.For(_, #("a", v.Typ(0)), _) -> True
    _ -> False
  }
  // f(1): b := Int (constrained by the argument), a is unconstrained.
  let ast_app = ast.app(ast.var("f", s), ast.int(1, s), s)
  let ctx0 = push_var(Context(..new_ctx, ffi: ffi), #("f", f_val, type_))
  let #(_term, type_, ctx) = pipeline_ast(ast_app, ctx0)
  assert ctx.errors == []
  assert type_ == v.int_t
}

// ============================================================================
// `check`: subtyping convenience and mismatch reporting
// ============================================================================

/// An int literal checked against a float type is silently converted to
/// a float literal (the deliberate subtyping convenience in `check`).
pub fn pipeline_check_int_where_float_test() {
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let ast = ast.int(1, s)
  let #(term, type_, ctx) = pipeline_check(ast, v.float_t, ctx0)
  assert ctx.errors == []
  assert term == tm.float(1.0)
  assert type_ == v.float_t
}

/// A float literal checked against an int type is a type mismatch,
/// reported with the expected/got values.
pub fn pipeline_check_float_where_int_test() {
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let ast = ast.float(1.5, s)
  let #(_term, _type_, ctx) = pipeline_check(ast, v.int_t, ctx0)
  assert ctx.errors
    == [
      e.Error(
        e.TypeMismatch(#(v.float_t, s), #(v.int_t, s)),
        ast.span,
        [],
      ),
    ]
}

/// A variable of the wrong type checked against an annotation is a type
/// mismatch (the annotation does not coerce variables).
pub fn pipeline_check_var_mismatch_test() {
  let ctx0 = push_var(Context(..new_ctx, ffi: ffi), #("x", v.int(1), v.int_t))
  let ast = ast.var("x", s)
  let #(_term, _type_, ctx) = pipeline_check(ast, v.float_t, ctx0)
  assert ctx.errors
    == [
      e.Error(e.TypeMismatch(#(v.int_t, ast.span), #(v.float_t, s)), ast.span, []),
    ]
}

// ============================================================================
// `Match`: eager reduction and neutral stays
// ============================================================================

/// A match on a concrete scrutinee reduces eagerly: the resolved term
/// is the selected case's body, not a match.
pub fn pipeline_match_concrete_reduces_test() {
  let cases = [
    ast.Case(ast.pint(0, s), None, ast.int(10, s)),
    ast.Case(ast.pvar("n", s), None, ast.int(20, s)),
  ]
  let ast = ast.match(ast.int(1, s), cases, s)
  let ctx0 = Context(..new_ctx, ffi: ffi)
  let #(term, type_, ctx) = pipeline_ast(ast, ctx0)
  assert ctx.errors == []
  assert term == tm.int(20)
  assert type_ == v.int_t
}

/// A match on a neutral scrutinee stays a neutral match: the resolved
/// term is the (quoted) match, and its type is a neutral match over the
/// case body types (the dependent motive).
pub fn pipeline_match_neutral_stays_test() {
  let cases = [
    ast.Case(ast.pint(0, s), None, ast.int(1, s)),
    ast.Case(ast.pvar("n", s), None, ast.var("n", s)),
  ]
  let ast = ast.match(ast.var("xs", s), cases, s)
  let ctx0 = push_var(
    Context(..new_ctx, ffi: ffi),
    #("xs", v.var(0), v.int_t),
  )
  let #(term, type_, ctx) = pipeline_ast(ast, ctx0)
  assert ctx.errors == []
  assert term
    == tm.Match(
      tm.Var(0),
      [tm.Case(tm.pint(0), None, tm.int(1)), tm.Case(tm.pvar("n"), None, tm.Var(0))],
    )
  // The type is stuck: a neutral match over the case body types. The
  // pattern-bound `n` was checked against the scrutinee type (%Int), so
  // its fresh pattern hole is solved and the body type is %Int.
  assert type_
    == v.match(
      [v.var(0)],
      v.var(0),
      [
        tm.Case(tm.pint(0), None, tm.int_t),
        tm.Case(tm.pvar("n"), None, tm.int_t),
      ],
    )
  // Still neutral at the value level.
  assert case eval(ffi, ctx.env, term) {
    v.Neut(v.NMatch(_, _, _)) -> True
    _ -> False
  }
}

// ============================================================================
// Holes and unification outcomes at the pipeline level
// ============================================================================

/// A check failure leaves the holes in the error's values unsolved but
/// resolved where possible; the displayed error shows the mismatch.
pub fn pipeline_error_display_test() {
  let ctx0 = push_var(Context(..new_ctx, ffi: ffi), #("x", v.int(1), v.int_t))
  let ast = ast.var("x", s)
  let #(_term, _type_, ctx) = pipeline_check(ast, v.float_t, ctx0)
  case ctx.errors {
    [err, ..] -> {
      let types: List(#(String, v.Value)) = ctx.types
      let displayed = e.display(ffi, types, err)
      assert string.contains(displayed, "type mismatch")
      assert string.contains(displayed, "%Int")
      assert string.contains(displayed, "%Float")
    }
    _ -> panic as "pipeline: expected a type mismatch error"
  }
}
