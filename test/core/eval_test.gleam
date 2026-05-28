import core/ast
import core/eval.{eval, match_pattern}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("eval_test", 0, 0, 0, 0)

pub fn eval_typ_test() {
  let term = ast.Typ(0, s)
  let result = eval([], [], term)
  assert result == ast.VTyp(0)
}

pub fn eval_hole_test() {
  let term = ast.Hole(0, s)
  let result = eval([], [], term)
  assert result == ast.vhole(0)
}

pub fn eval_lit_test() {
  let term = ast.Lit(ast.Int(1), s)
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_litt_test() {
  let term = ast.LitT(ast.IntT, s)
  let result = eval([], [], term)
  assert result == ast.vint_t
}

pub fn eval_var_undefined_test() {
  let term = ast.Var(0, s)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_var0_test() {
  let term = ast.Var(0, s)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vint_t
}

pub fn eval_var1_test() {
  let term = ast.Var(1, s)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vfloat_t
}

pub fn eval_ctr_test() {
  let term = ast.Ctr("A", ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.VCtr("A", ast.vint_t)
}

pub fn eval_rcd_empty_test() {
  let term = ast.Rcd([], s)
  let result = eval([], [], term)
  assert result == ast.VRcd([])
}

pub fn eval_rcd_fields_test() {
  let term = ast.Rcd([#("x", ast.int_t(s)), #("y", ast.float_t(s))], s)
  let result = eval([], [], term)
  assert result == ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)])
}

pub fn eval_rcdt_empty_test() {
  let term = ast.RcdT([], s)
  let result = eval([], [], term)
  assert result == ast.VRcdT([])
}

pub fn eval_rcdt_fields_test() {
  let term =
    ast.RcdT(
      [
        #("x", ast.int_t(s), Some(ast.int(42, s))),
        #("y", ast.float_t(s), None),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result
    == ast.VRcdT([
      #("x", ast.vint_t, Some(ast.vint(42))),
      #("y", ast.vfloat_t, None),
    ])
}

pub fn eval_call_undefined_test() {
  let term = ast.Call("f", [], ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.vcall("f", [])
}

pub fn eval_call_return_none_test() {
  let ffi = [#("f", fn(_) { None })]
  let term = ast.Call("f", [], ast.int_t(s), s)
  let result = eval(ffi, [], term)
  assert result == ast.vcall("f", [])
}

pub fn eval_call_return_some_test() {
  let ffi = [#("f", fn(_) { Some(ast.vint(42)) })]
  let term = ast.Call("f", [], ast.int_t(s), s)
  let result = eval(ffi, [], term)
  assert result == ast.vint(42)
}

pub fn eval_call_args_test() {
  let term =
    ast.Call("f", [ast.int(42, s), ast.float(3.14, s)], ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.vcall("f", [ast.vint(42), ast.vfloat(3.14)])
}

pub fn eval_ann_test() {
  let term = ast.Ann(ast.int(42, s), ast.int_t(s), s)
  let result = eval([], [], term)
  assert result == ast.vint(42)
}

pub fn eval_lam_explicit_test() {
  // $fn(x: $Int) => x
  let term = ast.Lam(False, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VLam(False, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_lam_implicit_test() {
  // $fn<x: $Type> => x
  let term = ast.Lam(True, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VLam(True, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_lam_closure_test() {
  // let a = $Int; $fn(x: a) => a
  let term = ast.Lam(False, #("x", ast.Var(0, s)), ast.Var(1, s), s)
  let env = [ast.vint_t]
  let result = eval([], env, term)
  assert result == ast.VLam(False, #("x", ast.vint_t), #(env, ast.Var(1, s)))
}

pub fn eval_pi_explicit_test() {
  // $pi(x: $Int) => x
  let term = ast.Pi(False, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VPi(False, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_pi_implicit_test() {
  // $pi<x: $Int> => x
  let term = ast.Pi(True, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let result = eval([], [], term)
  assert result == ast.VPi(True, #("x", ast.vint_t), #([], ast.Var(0, s)))
}

pub fn eval_pi_closure_test() {
  // let a = $Int; $pi(x: a) => a
  let term = ast.Pi(False, #("x", ast.Var(0, s)), ast.Var(1, s), s)
  let env = [ast.vint_t]
  let result = eval([], env, term)
  assert result == ast.VPi(False, #("x", ast.vint_t), #(env, ast.Var(1, s)))
}

pub fn eval_fix_test() {
  let term = ast.Fix("f", ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.VFix("f", #([], ast.int(42, s)))
}

pub fn eval_app_not_a_function_test() {
  let fun = ast.Typ(0, s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_app_neutral_test() {
  // ?10 42 ~> ?10 42
  let fun = ast.Hole(10, s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.vapp(ast.NHole(10), ast.vint(42))
}

pub fn eval_app_beta_reduction_test() {
  // ($fn(x: $Int) => x) 42 ~> 42
  let fun = ast.Lam(False, #("x", ast.int_t(s)), ast.Var(0, s), s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.vint(42)
}

pub fn eval_app_implicit_expansion_test() {
  // ($fn<x: $Type> => ?10 x) 42
  // ~> (?10 $error) 42
  let inner = ast.App(ast.Hole(10, s), ast.Var(0, s), s)
  let fun = ast.Lam(True, #("x", ast.Typ(0, s)), inner, s)
  let term = ast.App(fun, ast.int(42, s), s)
  let result = eval([], [], term)
  assert result == ast.vapp(ast.NApp(ast.NHole(10), ast.VErr), ast.vint(42))
}

// TypeDef( params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )

pub fn eval_match_empty_test() {
  let term = ast.Match(ast.int(42, s), [], s)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_match_first_test() {
  // Match first case with no bindings, base test
  // Match {x: 1, y: 2} { | {x: 1, y: _} => 0 }
  let term =
    ast.Match(
      ast.Rcd([#("x", ast.int(1, s)), #("y", ast.int(2, s))], s),
      [
        ast.Case(
          ast.PRcd([#("x", ast.PLit(ast.Int(1), s)), #("y", ast.PAny(s))], s),
          None,
          ast.int(0, s),
          s,
        ),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result == ast.vint(0)
}

pub fn eval_match_second_test() {
  // Match second case with no bindings, inductive test
  // Match #Some(42) { | #None(_) => 0 | #Some(x) => x }
  let term =
    ast.Match(
      ast.Ctr("Some", ast.int(42, s), s),
      [
        ast.Case(
          ast.PCtr("None", ast.PAny(s), s),
          None,
          ast.int(0, s),
          s,
        ),
        ast.Case(
          ast.PCtr("Some", ast.PAlias("x", ast.PAny(s), s), s),
          None,
          ast.Var(0, s),
          s,
        ),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result == ast.vint(42)
}

pub fn eval_match_bindings_test() {
  // Match case with 2 bindings, DeBruijn/env test
  // Match {x: 1, y: 2} { | {x: x, y: y} => x + y ... but no +, so just return x via Var(0) }
  let term =
    ast.Match(
      ast.Rcd([#("x", ast.int(1, s)), #("y", ast.int(2, s))], s),
      [
        ast.Case(
          ast.PRcd(
            [
              #("x", ast.PAlias("x", ast.PAny(s), s)),
              #("y", ast.PAlias("y", ast.PAny(s), s)),
            ],
            s,
          ),
          None,
          ast.Var(0, s),
          s,
        ),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_match_guard_fail_test() {
  // Match case pattern but fail guard pattern
  // Match #Some(42) { | #Some(x) ? #None(_) ~ #None(_) => 0 | _ => 1 }
  // First case: pattern matches #Some(42), bound x=42, guard: 42 ~ #None(_) -> fails
  // Falls through to wildcard: matches, returns 1
  let term =
    ast.Match(
      ast.Ctr("Some", ast.int(42, s), s),
      [
        ast.Case(
          ast.PCtr("Some", ast.PAlias("x", ast.PAny(s), s), s),
          Some(#(ast.Var(0, s), ast.PCtr("None", ast.PAny(s), s))),
          ast.int(0, s),
          s,
        ),
        ast.Case(ast.PAny(s), None, ast.int(1, s), s),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_match_guard_pass_test() {
  // Match both case and guard patterns
  // Match 42 { | x ? x ~ 42 => 100 | _ => -1 }
  let term =
    ast.Match(
      ast.int(42, s),
      [
        ast.Case(
          ast.PAlias("x", ast.PAny(s), s),
          Some(#(ast.Var(0, s), ast.PLit(ast.Int(42), s))),
          ast.int(100, s),
          s,
        ),
        ast.Case(ast.PAny(s), None, ast.int(-1, s), s),
      ],
      s,
    )
  let result = eval([], [], term)
  assert result == ast.vint(100)
}

pub fn eval_match_guard_bindings_test() {
  // Match case with 1 binding and guard with 2 bindings
  // Match #Some({x: 1, y: 2}) { | #Some(z) ? z ~ {x: a, y: b} => a + b ... no +, so return a via Var(1)
  // The bindings order: guard bindings first, then main env.
  // z = {x: 1, y: 2}, guard term evaluates to {x: 1, y: 2}, guard pattern {x: a, y: b} matches.
  // Bindings from guard: a=1, b=2, prepended to env.
  // Body: Var(1) -> a = 1
  let guard_case =
    ast.Case(
      ast.PCtr("Some", ast.PAlias("z", ast.PAny(s), s), s),
      Some(
        #(
          ast.Var(0, s),
          ast.PRcd(
            [
              #("x", ast.PAlias("a", ast.PAny(s), s)),
              #("y", ast.PAlias("b", ast.PAny(s), s)),
            ],
            s,
          ),
        ),
      ),
      ast.Var(0, s),
      s,
    )
  let term =
    ast.Match(
      ast.Ctr(
        "Some",
        ast.Rcd([#("x", ast.int(1, s)), #("y", ast.int(2, s))], s),
        s,
      ),
      [guard_case],
      s,
    )
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_err_test() {
  let term = ast.Err(s)
  let result = eval([], [], term)
  assert result == ast.VErr
}

// ============================================================================
// match_pattern tests
// ============================================================================

pub fn match_pattern_any_test() {
  // PAny matches any value
  let result = match_pattern(ast.PAny(s), ast.vint(42))
  assert result == Some([])
}

pub fn match_pattern_any_mismatch_test() {
  // PAny still matches even when value doesn't exist (returns None is wrong, PAny always matches)
  let result = match_pattern(ast.PAny(s), ast.vfloat(3.14))
  assert result == Some([])
}

pub fn match_pattern_typ_test() {
  // PTyp matches VTyp with same universe
  let result = match_pattern(ast.PTyp(0, s), ast.VTyp(0))
  assert result == Some([])
}

pub fn match_pattern_typ_mismatch_test() {
  // PTyp doesn't match VTyp with different universe
  let result = match_pattern(ast.PTyp(1, s), ast.VTyp(0))
  assert result == None
}

pub fn match_pattern_typ_wrong_value_test() {
  // PTyp doesn't match non-VTyp values
  let result = match_pattern(ast.PTyp(0, s), ast.vint(42))
  assert result == None
}

pub fn match_pattern_lit_int_test() {
  // PLit matches VLit with same Int literal
  let result = match_pattern(ast.PLit(ast.Int(42), s), ast.vint(42))
  assert result == Some([])
}

pub fn match_pattern_lit_int_mismatch_test() {
  // PLit doesn't match VLit with different Int
  let result = match_pattern(ast.PLit(ast.Int(1), s), ast.vint(42))
  assert result == None
}

pub fn match_pattern_lit_float_test() {
  // PLit matches VLit with same Float literal
  let result = match_pattern(ast.PLit(ast.Float(3.14), s), ast.vfloat(3.14))
  assert result == Some([])
}

pub fn match_pattern_lit_wrong_value_test() {
  // PLit doesn't match non-VLit values
  let result = match_pattern(ast.PLit(ast.Int(42), s), ast.vint(43))
  assert result == None
}

pub fn match_pattern_litt_int_test() {
  // PLitT matches VLitT with same literal type
  let result = match_pattern(ast.PLitT(ast.IntT, s), ast.vint_t)
  assert result == Some([])
}

pub fn match_pattern_litt_int_mismatch_test() {
  // PLitT(IntT) doesn't match VLitT(FloatT)
  let result = match_pattern(ast.PLitT(ast.IntT, s), ast.vfloat_t)
  assert result == None
}

pub fn match_pattern_litt_wrong_value_test() {
  // PLitT doesn't match non-VLitT values
  let result = match_pattern(ast.PLitT(ast.IntT, s), ast.vint(42))
  assert result == None
}

pub fn match_pattern_alias_test() {
  // PAlias binds the value and matches the inner pattern
  let result = match_pattern(
    ast.PAlias("x", ast.PAny(s), s),
    ast.vint(42),
  )
  assert result == Some([ast.vint(42)])
}

pub fn match_pattern_alias_nested_test() {
  // PAlias wrapping another PAlias, each alias binds the value, so 2 copies
  let result = match_pattern(
    ast.PAlias("outer", ast.PAlias("inner", ast.PAny(s), s), s),
    ast.vfloat(3.14),
  )
  // Each PAlias prepends the value: inner binds it, then outer binds it again
  assert result == Some([ast.vfloat(3.14), ast.vfloat(3.14)])
}

pub fn match_pattern_alias_fail_test() {
  // PAlias fails if inner pattern fails
  let result = match_pattern(
    ast.PAlias("x", ast.PCtr("A", ast.PAny(s), s), s),
    ast.vint(42),
  )
  assert result == None
}

pub fn match_pattern_ctr_test() {
  // PCtr matches VCtr with same tag, recurses into inner pattern
  let result = match_pattern(
    ast.PCtr("Some", ast.PAny(s), s),
    ast.VCtr("Some", ast.vint(42)),
  )
  assert result == Some([])
}

pub fn match_pattern_ctr_tag_mismatch_test() {
  // PCtr doesn't match VCtr with different tag
  let result = match_pattern(
    ast.PCtr("None", ast.PAny(s), s),
    ast.VCtr("Some", ast.vint(42)),
  )
  assert result == None
}

pub fn match_pattern_ctr_wrong_value_test() {
  // PCtr doesn't match non-VCtr values
  let result = match_pattern(
    ast.PCtr("Some", ast.PAny(s), s),
    ast.vint(42),
  )
  assert result == None
}

pub fn match_pattern_ctr_nested_test() {
  // Nested PCtr: #Some(#Int(42))
  let inner = ast.PCtr("Int", ast.PLit(ast.Int(42), s), s)
  let result = match_pattern(
    ast.PCtr("Some", inner, s),
    ast.VCtr("Some", ast.VCtr("Int", ast.VLit(ast.Int(42)))),
  )
  assert result == Some([])
}

pub fn match_pattern_ctr_nested_fail_test() {
  // Nested PCtr where inner literal doesn't match
  let inner = ast.PCtr("Int", ast.PLit(ast.Int(99), s), s)
  let result = match_pattern(
    ast.PCtr("Some", inner, s),
    ast.VCtr("Some", ast.VCtr("Int", ast.VLit(ast.Int(42)))),
  )
  assert result == None
}

pub fn match_pattern_rcd_test() {
  // PRcd matches VRcd with same fields and matching values
  let result = match_pattern(
    ast.PRcd([#("x", ast.PLit(ast.Int(1), s)), #("y", ast.PAny(s))], s),
    ast.VRcd([#("x", ast.vint(1)), #("y", ast.vfloat(2.0))]),
  )
  assert result == Some([])
}

pub fn match_pattern_rcd_extra_field_in_pattern_test() {
  // PRcd fails if pattern has field not in value
  let result = match_pattern(
    ast.PRcd([#("x", ast.PAny(s)), #("y", ast.PAny(s)), #("z", ast.PAny(s))], s),
    ast.VRcd([#("x", ast.vint(1)), #("y", ast.vint(2))]),
  )
  assert result == None
}

pub fn match_pattern_rcd_fewer_fields_test() {
  // PRcd succeeds with fewer pattern fields than value fields
  let result = match_pattern(
    ast.PRcd([#("x", ast.PAny(s))], s),
    ast.VRcd([#("x", ast.vint(1)), #("y", ast.vint(2))]),
  )
  assert result == Some([])
}

pub fn match_pattern_rcd_with_bindings_test() {
  // PRcd with alias bindings
  let result = match_pattern(
    ast.PRcd(
      [
        #("x", ast.PAlias("x_val", ast.PAny(s), s)),
        #("y", ast.PAlias("y_val", ast.PAny(s), s)),
      ],
      s,
    ),
    ast.VRcd([#("x", ast.vint(1)), #("y", ast.vint(2))]),
  )
  assert result == Some([ast.vint(1), ast.vint(2)])
}

pub fn match_pattern_rcd_wrong_field_name_test() {
  // PRcd fails if pattern field name doesn't match value field name
  let result = match_pattern(
    ast.PRcd([#("x", ast.PAny(s))], s),
    ast.VRcd([#("y", ast.vint(1))]),
  )
  assert result == None
}

pub fn match_pattern_rcd_value_field_mismatch_test() {
  // PRcd fails if a field value doesn't match the pattern
  let result = match_pattern(
    ast.PRcd([#("x", ast.PLit(ast.Int(99), s))], s),
    ast.VRcd([#("x", ast.vint(42))]),
  )
  assert result == None
}

pub fn match_pattern_error_test() {
  // PError matches VErr
  let result = match_pattern(ast.PError(s), ast.VErr)
  assert result == Some([])
}

pub fn match_pattern_error_wrong_value_test() {
  // PError doesn't match non-error values
  let result = match_pattern(ast.PError(s), ast.vint(42))
  assert result == None
}
