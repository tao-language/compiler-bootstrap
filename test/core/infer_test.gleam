/// Tests for the Infer module (Bidirectional Type Checking)
///
/// These tests verify core logic only:
/// - Variable lookup via context
/// - Hole generation (fresh ID allocation)
/// - Error handling (undefined vars)
/// - Default value checking in record types
///
/// Trivial data-pass-through tests (Lit, LitT, Typ, Ctr, Rcd, Call)
/// have been removed — they only verify data flows through, not logic.
import core/ast
import core/context.{new_ctx, push_var}
import core/error as e
import core/eval.{eval}
import core/infer.{check, infer}
import core/resolve
import core/term as tm
import core/unify.{unify}
import core/unwrap.{unwrap}
import core/value as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span

const s = span.Span("", 0, 0, 0, 0)

const s1 = span.Span("", 1, 1, 1, 1)

const s2 = span.Span("", 2, 2, 2, 2)

// ============================================================================
//  Typ
// ============================================================================

// ============================================================================
//  Hole
// ============================================================================

// ============================================================================
//  Lit
// ============================================================================

pub fn infer_lit_int_test() {
  let #(term, type_, ctx) = infer(new_ctx, ast.int(1, s))
  assert ctx.errors == []
  assert term == tm.int(1)
  assert type_ == v.int_t
}

pub fn check_lit_int_test() {
  let check_int = fn(ty) {
    let #(term, type_, ctx) = check(new_ctx, ast.int(1, s1), #(ty, s2))
    #(ctx.errors, term, type_)
  }
  assert check_int(v.int_t) == #([], tm.int(1), v.int_t)
  assert check_int(v.i8) == #([], tm.int(1), v.i8)
  assert check_int(v.i16) == #([], tm.int(1), v.i16)
  assert check_int(v.i32) == #([], tm.int(1), v.i32)
  assert check_int(v.i64) == #([], tm.int(1), v.i64)
  assert check_int(v.u8) == #([], tm.int(1), v.u8)
  assert check_int(v.u16) == #([], tm.int(1), v.u16)
  assert check_int(v.u32) == #([], tm.int(1), v.u32)
  assert check_int(v.u64) == #([], tm.int(1), v.u64)
  assert check_int(v.float_t) == #([], tm.float(1.0), v.float_t)
  assert check_int(v.f16) == #([], tm.float(1.0), v.f16)
  assert check_int(v.f32) == #([], tm.float(1.0), v.f32)
  assert check_int(v.f64) == #([], tm.float(1.0), v.f64)
}

pub fn check_lit_float_test() {
  let check_float = fn(ty) {
    let #(term, type_, ctx) = check(new_ctx, ast.float(1.0, s1), #(ty, s2))
    let ctx = resolve.context(ctx)
    #(ctx.errors, term, type_)
  }
  assert check_float(v.int_t)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.int_t, s2)), s1, [])],
      tm.float(1.0),
      v.int_t,
    )
  assert check_float(v.i8)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.i8, s2)), s1, [])],
      tm.float(1.0),
      v.i8,
    )
  assert check_float(v.i16)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.i16, s2)), s1, [])],
      tm.float(1.0),
      v.i16,
    )
  assert check_float(v.i32)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.i32, s2)), s1, [])],
      tm.float(1.0),
      v.i32,
    )
  assert check_float(v.i64)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.i64, s2)), s1, [])],
      tm.float(1.0),
      v.i64,
    )
  assert check_float(v.u8)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.u8, s2)), s1, [])],
      tm.float(1.0),
      v.u8,
    )
  assert check_float(v.u16)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.u16, s2)), s1, [])],
      tm.float(1.0),
      v.u16,
    )
  assert check_float(v.u32)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.u32, s2)), s1, [])],
      tm.float(1.0),
      v.u32,
    )
  assert check_float(v.u64)
    == #(
      [e.Error(e.TypeMismatch(#(v.float_t, s1), #(v.u64, s2)), s1, [])],
      tm.float(1.0),
      v.u64,
    )
  assert check_float(v.float_t) == #([], tm.float(1.0), v.float_t)
  assert check_float(v.f16) == #([], tm.float(1.0), v.f16)
  assert check_float(v.f32) == #([], tm.float(1.0), v.f32)
  assert check_float(v.f64) == #([], tm.float(1.0), v.f64)
}

// ============================================================================
//  LitT
// ============================================================================

// ============================================================================
//  Var
// ============================================================================

pub fn infer_var_undefined_test() {
  let ast = ast.var("x", s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == [e.Error(e.VarUndefined("x"), s, [])]
  assert term == tm.Err
  assert type_ == v.Err
}

pub fn infer_var_defined_test() {
  let ast = ast.var("x", s)
  let ctx0 =
    context.push_var_opt(new_ctx, #("x", Some(v.int(42)), Some(v.int_t)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.Var(0)
  assert type_ == v.int_t
}

// ============================================================================
//  Ctr
// ============================================================================

// ============================================================================
//  Rcd
// ============================================================================

// ============================================================================
//  RcdT
// ============================================================================

// ============================================================================
//  Call
// ============================================================================

// ============================================================================
//  Ann
// ============================================================================

// ============================================================================
//  Lam
// ============================================================================

pub fn infer_lam_simple_test() {
  // $fn(x: $Int) => x
  let ast = ast.lam(#("x", Some(ast.int_t(s))), ast.var("x", s), s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.Lam(#("x", tm.int_t), tm.Var(0))
  assert type_ == v.Pi([], #("x", v.int_t), tm.int_t)
}

pub fn infer_lam_closure_test() {
  // $let y = 3.14; $fn(x: $Int) => y
  let ast = ast.lam(#("x", Some(ast.int_t(s))), ast.var("y", s), s)
  let ctx0 =
    context.push_var_opt(new_ctx, #("y", Some(v.float(3.14)), Some(v.float_t)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.Lam(#("x", tm.int_t), tm.Var(1))
  assert type_ == v.Pi([v.float(3.14)], #("x", v.int_t), tm.float_t)
}

pub fn infer_lam_identity_test() {
  // $fn<a: $Type>(x: a) => x
  let ast =
    ast.for(
      #("a", Some(ast.typ(0, s))),
      ast.lam(#("x", Some(ast.var("a", s))), ast.var("x", s), s),
      s,
    )
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.For(#("a", tm.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
  assert type_
    == v.For([], #("a", v.Typ(0)), tm.Pi(#("x", tm.Var(0)), tm.Var(1)))
}

pub fn infer_lam_typeof_test() {
  // $fn<a: $Type>(x: a) => a
  let ast =
    ast.for(
      #("a", Some(ast.typ(0, s))),
      ast.lam(#("x", Some(ast.var("a", s))), ast.var("a", s), s),
      s,
    )
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.For(#("a", tm.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(1)))
  assert type_
    == v.For([], #("a", v.Typ(0)), tm.Pi(#("x", tm.Var(0)), tm.Typ(0)))
}

// ============================================================================
//  Pi
// ============================================================================

// ============================================================================
//  Fix
// ============================================================================

// ============================================================================
//  App
// ============================================================================

pub fn infer_app_error_not_a_function_test() {
  let ast = ast.app(ast.float(3.14, s1), ast.int(1, s), s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors
    == [e.Error(e.NotAFunction(tm.float(3.14), v.float_t), s1, [])]
  assert term == tm.Err
  assert type_ == v.Err
}

pub fn infer_app_explicit_arg_test() {
  let ast = ast.app(ast.var("f", s), ast.int(42, s), s)
  let pi = v.Pi([], #("x", v.int_t), tm.Var(0))
  let ctx0 = context.push_var_opt(new_ctx, #("f", Some(v.var(0)), Some(pi)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.App(tm.Var(0), tm.int(42))
  assert type_ == v.int_t
}

pub fn infer_app_implicit_arg_test() {
  let ast = ast.app(ast.var("f", s), ast.int(42, s), s)
  let pi = v.For([], #("a", v.int_t), tm.Pi(#("x", tm.int_t), tm.Var(0)))
  let ctx0 = context.push_var_opt(new_ctx, #("f", Some(v.var(0)), Some(pi)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.App(tm.App(tm.Var(0), tm.Hole(Some(0))), tm.int(42))
  assert type_ == v.int_t
}

pub fn infer_app_hole_expansion_test() {
  let ast = ast.app(ast.var("f", s), ast.int(42, s), s)
  let ctx0 =
    context.push_var_opt(new_ctx, #(
      "f",
      Some(v.var(0)),
      Some(v.hole_open([], None)),
    ))
  let #(term, _type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.App(tm.Var(0), tm.int(42))
}

pub fn infer_app_implicit_expansion_test() {
  let pi = v.For([], #("a", v.Typ(0)), tm.Var(0))
  let ctx = context.push_var_opt(new_ctx, #("f", Some(v.var(0)), Some(pi)))
  let expr = ast.app(ast.var("f", s), ast.int(42, s), s)
  let #(term, type_, ctx) = infer(ctx, expr)
  assert ctx.errors == []
  assert ctx.hole_counter > 0
  // For quantifier creates implicit arg hole; app creates return type hole
  assert term == tm.App(tm.App(tm.Var(0), tm.Hole(Some(0))), tm.int(42))
  assert unwrap(ctx.ffi, ctx.subst, type_) == v.hole([v.int(42), v.var(0)], 1)
}

pub fn infer_app_implicit_solve_hole_test() {
  let ast = ast.app(ast.var("identity", s), ast.int(1, s), s)
  let pi = v.For([], #("a", v.Typ(0)), tm.Pi(#("x", tm.Var(0)), tm.Var(1)))
  let ctx0 =
    context.push_var_opt(new_ctx, #("identity", Some(v.var(0)), Some(pi)))
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.App(tm.App(tm.Var(0), tm.Hole(Some(0))), tm.int(1))
  // The implicit hole (id=0) is solved to IntT by unification
  assert unwrap.unwrap(ctx.ffi, ctx.subst, type_) == v.int_t
}

// ============================================================================
//  TypeDef
// ============================================================================

pub fn infer_type_def_bool_test() {
  let tdef =
    ast.TypeDefinition(params: [], arg: ast.rcd_values([], None, s), variants: [
      #(
        "True",
        ast.Variant([], ast.rcd_values([], None, s), ast.ctr0("Bool", s)),
      ),
      #(
        "False",
        ast.Variant([], ast.rcd_values([], None, s), ast.ctr0("Bool", s)),
      ),
    ])
  let ast = ast.Expr(ast.TypeDef(tdef), s, None)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  // A type definition is a value of the universe
  assert type_ == v.Typ(0)
  assert term
    == tm.TypeDef(
      tm.TypeDefinition(params: [], arg: tm.rcd([]), variants: [
        #("True", tm.Variant([], tm.rcd([]), tm.ctr("Bool", []))),
        #("False", tm.Variant([], tm.rcd([]), tm.ctr("Bool", []))),
      ]),
    )
}

pub fn infer_type_def_option_test() {
  let tdef =
    ast.TypeDefinition(
      params: [#("a", ast.hole_open(None, s))],
      arg: ast.rcd_values([#("a", ast.var("a", s))], None, s),
      variants: [
        #(
          "None",
          ast.Variant(
            [],
            ast.rcd_values([], None, s),
            ast.ctr(
              "Option",
              ast.rcd_values([#("a", ast.var("a", s))], None, s),
              s,
            ),
          ),
        ),
        #(
          "Some",
          ast.Variant(
            [],
            ast.rcd_values([#("", ast.var("a", s))], None, s),
            ast.ctr(
              "Option",
              ast.rcd_values([#("a", ast.var("a", s))], None, s),
              s,
            ),
          ),
        ),
      ],
    )
  let ast = ast.Expr(ast.TypeDef(tdef), s, None)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert type_ == v.Typ(0)
  // The untyped parameter is an open hole; the inner terms index into the
  // parameter (de Bruijn 0, the innermost binder).
  assert term
    == tm.TypeDef(
      tm.TypeDefinition(
        params: [#("a", tm.Hole(Some(0)))],
        arg: tm.rcd([#("a", tm.Var(0))]),
        variants: [
          #(
            "None",
            tm.Variant(
              [],
              tm.rcd([]),
              tm.Ctr("Option", tm.rcd([#("a", tm.Var(0))])),
            ),
          ),
          #(
            "Some",
            tm.Variant(
              [],
              tm.rcd([#("", tm.Var(0))]),
              tm.Ctr("Option", tm.rcd([#("a", tm.Var(0))])),
            ),
          ),
        ],
      ),
    )
}

pub fn infer_type_def_gadt_test() {
  let tdef =
    ast.TypeDefinition(
      params: [#("n", ast.int_t(s)), #("a", ast.typ(0, s))],
      arg: ast.rcd_values(
        [#("n", ast.var("n", s)), #("a", ast.var("a", s))],
        None,
        s,
      ),
      variants: [
        #(
          "VNil",
          ast.Variant(
            [],
            ast.rcd_values([], None, s),
            ast.ctr(
              "Vec",
              ast.rcd_values(
                [#("", ast.int(0, s)), #("", ast.var("a", s))],
                None,
                s,
              ),
              s,
            ),
          ),
        ),
        #(
          "VCons",
          ast.Variant(
            [#("m", ast.hole_open(None, s))],
            ast.rcd_values(
              [
                #("x", ast.var("a", s)),
                #(
                  "xs",
                  ast.ctr(
                    "Vec",
                    ast.rcd_values(
                      [#("", ast.var("m", s)), #("", ast.var("a", s))],
                      None,
                      s,
                    ),
                    s,
                  ),
                ),
              ],
              None,
              s,
            ),
            ast.ctr(
              "Vec",
              ast.rcd_values(
                [#("", ast.var("m", s)), #("", ast.var("a", s))],
                None,
                s,
              ),
              s,
            ),
          ),
        ),
      ],
    )
  let ast = ast.Expr(ast.TypeDef(tdef), s, None)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert type_ == v.Typ(0)
  // `n` and `a` are the type's parameters (de Bruijn 1 and 0, last pushed
  // innermost); `m` is VCons's own parameter (de Bruijn 0 within the
  // variant, 1 and 2 for `a` and `n`).
  assert term
    == tm.TypeDef(
      tm.TypeDefinition(
        params: [#("n", tm.int_t), #("a", tm.Typ(0))],
        arg: tm.rcd([#("n", tm.Var(1)), #("a", tm.Var(0))]),
        variants: [
          #(
            "VNil",
            tm.Variant(
              [],
              tm.rcd([]),
              tm.ctr("Vec", [#("", tm.int(0)), #("", tm.Var(0))]),
            ),
          ),
          #(
            "VCons",
            tm.Variant(
              [#("m", tm.Hole(Some(0)))],
              tm.rcd([
                #("x", tm.Var(1)),
                #("xs", tm.ctr("Vec", [#("", tm.Var(0)), #("", tm.Var(1))])),
              ]),
              tm.ctr("Vec", [#("", tm.Var(0)), #("", tm.Var(1))]),
            ),
          ),
        ],
      ),
    )
}

pub fn infer_type_def_gadt_ctor_test() {
  // Infer a type definition and keep it in scope (as the compiler's
  // definition phases do), then check `Some(1)` against `Option(Int)`:
  // the constructor unifies with the type definition via `unify_gadt`,
  // binding the parameter `a` to `IntT`.
  let tdef =
    ast.TypeDefinition(
      params: [#("a", ast.hole_open(None, s))],
      arg: ast.rcd_values([#("a", ast.var("a", s))], None, s),
      variants: [
        #(
          "Some",
          ast.Variant(
            [],
            ast.rcd_values([#("", ast.var("a", s))], None, s),
            ast.ctr(
              "Option",
              ast.rcd_values([#("a", ast.var("a", s))], None, s),
              s,
            ),
          ),
        ),
        #(
          "None",
          ast.Variant(
            [],
            ast.rcd_values([], None, s),
            ast.ctr(
              "Option",
              ast.rcd_values([#("a", ast.var("a", s))], None, s),
              s,
            ),
          ),
        ),
      ],
    )
  let option_def = ast.Expr(ast.TypeDef(tdef), s, None)
  let ctx0 = new_ctx
  let #(option_def_term, _option_def_type, ctx) = infer(ctx0, option_def)
  assert ctx.errors == []
  let option_val = eval(ctx.ffi, ctx.env, option_def_term)
  let ctx = push_var(ctx, #("Option", option_val, v.Typ(0)))
  // The constructor's inferred type (arguments as types) against the
  // expected type's value (the constructor applied to its argument).
  let some_ast =
    ast.ctr("Some", ast.rcd_values([#("", ast.int(1, s))], None, s), s)
  let option_ast =
    ast.ctr("Option", ast.rcd_values([#("", ast.int_t(s))], None, s), s)
  let #(_, some_type, ctx) = infer(ctx, some_ast)
  let #(option_term, _option_type, ctx) = infer(ctx, option_ast)
  let option_val = eval(ctx.ffi, ctx.env, option_term)
  let ctx = unify(ctx, #(some_type, s), #(option_val, s))
  assert ctx.errors == []
  assert some_type == v.Ctr("Some", v.rcd([#("", v.int_t)]))
  // The type's parameter is solved to `IntT` by the unification
  assert list.contains(list.map(ctx.subst, fn(sub) { sub.1.1 }), v.int_t)
}

// ============================================================================
//  Let
// ============================================================================

// ============================================================================
//  Match
// ============================================================================

pub fn infer_match_first_test() {
  let cases = [
    ast.Case(ast.pint(1, s), None, ast.int(42, s)),
    ast.Case(ast.pint(2, s), None, ast.float(3.14, s)),
    ast.Case(ast.pvar("x", s), None, ast.var("x", s)),
  ]
  let ast = ast.match(ast.int(1, s), cases, s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.errors == []
  assert term == tm.int(42)
  assert type_ == v.int_t
}

pub fn infer_match_second_test() {
  let cases = [
    ast.Case(ast.pint(1, s), None, ast.int(42, s)),
    ast.Case(ast.pint(2, s), None, ast.float(3.14, s)),
    ast.Case(ast.pvar("x", s), None, ast.var("x", s)),
  ]
  let ast = ast.match(ast.int(2, s), cases, s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.errors == []
  assert term == tm.float(3.14)
  assert type_ == v.float_t
}

pub fn infer_match_binding_test() {
  let cases = [
    ast.Case(ast.pint(1, s), None, ast.int(42, s)),
    ast.Case(ast.pint(2, s), None, ast.float(3.14, s)),
    ast.Case(ast.pvar("x", s), None, ast.var("x", s)),
  ]
  let ast = ast.match(ast.int(10, s), cases, s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.errors == []
  assert term == tm.int(10)
  // Hole solution is deferred in ctx.subst; unwrap to check the resolved type
  assert unwrap(ctx.ffi, ctx.subst, type_) == v.int_t
}

pub fn infer_match_error_arg_type_mismatch_test() {
  let cases = [
    ast.Case(ast.pint(1, s1), None, ast.int(42, s)),
    ast.Case(ast.pvar("x", s), None, ast.var("x", s)),
  ]
  let ast = ast.match(ast.float(3.14, s2), cases, s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  // assert ctx.errors == [e.TypeMismatch(#(v.int_t, s1), #(v.float_t, s2))]
  assert list.length(ctx.errors) == 1
  assert term == tm.float(3.14)
  // Hole solution is deferred in ctx.subst; unwrap to check the resolved type
  assert unwrap(ctx.ffi, ctx.subst, type_) == v.float_t
}

pub fn infer_match_dependent_motive_test() {
  let cases = [
    ast.Case(ast.pint(1, s), None, ast.int(42, s)),
    ast.Case(ast.pint(2, s), None, ast.float(3.14, s)),
    ast.Case(ast.pvar("x", s), None, ast.var("x", s)),
  ]
  let ctx0 = new_ctx
  let ast = ast.match(ast.hole_open(None, s), cases, s)
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.errors == []
  assert term
    == tm.Match(tm.Hole(Some(0)), [
      tm.Case(tm.pint(1), None, tm.int(42)),
      tm.Case(tm.pint(2), None, tm.float(3.14)),
      tm.Case(tm.pvar("x"), None, tm.Var(0)),
    ])
  assert type_
    == v.match([], v.Neut(v.NHole([], Some(0))), [
      tm.Case(tm.pint(1), None, tm.int_t),
      tm.Case(tm.pint(2), None, tm.float_t),
      tm.Case(tm.pvar("x"), None, tm.Hole(Some(2))),
    ])
  // With deferred substitution, holes 1 and 2 are solved to IntT. The
  // stored env is the frame current when the hole was solved (hole 1 was
  // solved inside the match's guard scope, so its frame holds the pattern
  // binding); quoting is always against the stored frame, so the exact
  // contents matter only via its length — assert the solutions and that
  // each env has the frame length of the solve site.
  let solutions = list.map(ctx.subst, fn(sub) { sub.1.1 })
  let env_sizes = list.map(ctx.subst, fn(sub) { list.length(sub.1.0) })
  assert solutions == [v.int_t, v.int_t]
  assert env_sizes == [1, 0]
}

// ============================================================================
//  Err
// ============================================================================

pub fn infer_err_test() {
  let ast = ast.err(s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert term == tm.Err
  assert type_ == v.Err
}

// ============================================================================
//  Known-soundness-reproduction: a non-exhaustive match on a concrete
//  scrutinee (no case matches) silently yields %error with *no*
//  diagnostics (do_match_case_list falls off the end to v.Err).
//  Exhaustiveness checking (planned, Tao level) should close this.
// ============================================================================
pub fn infer_match_nonexhaustive_concrete_silent_error_test() {
  let cases = [ast.Case(ast.pint(0, s), None, ast.int(1, s))]
  let ast = ast.match(ast.int(1, s), cases, s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  // BUG: no error is reported
  assert ctx.errors == []
  // The match collapses to the %error bottom
  assert term == tm.Err
  assert type_ == v.Err
}

// Same issue via a failing guard on a concrete scrutinee: the guard
// rejects the only case, and do_match falls through to v.Err silently.
pub fn infer_match_guard_fails_concrete_silent_error_test() {
  let cases = [
    ast.Case(
      ast.pvar("n", s),
      Some(#(ast.int(0, s), ast.pint(1, s))),
      ast.int(1, s),
    ),
  ]
  let ast = ast.match(ast.int(1, s), cases, s)
  let ctx0 = new_ctx
  let #(term, type_, ctx) = infer(ctx0, ast)
  // BUG: no error is reported
  assert ctx.errors == []
  // The guard (0 == 1) fails at value level, so the match collapses
  // to the %error bottom
  assert term == tm.Err
  assert type_ == v.Err
}
