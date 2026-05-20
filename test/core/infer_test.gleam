/// Tests for the Infer module (Bidirectional Type Checking)
import core/ast
import core/infer.{infer}
import core/state.{State, new_state, with_err}
import gleam/list
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

// Helper span constants to verify error reporting.
const s0 = Span("infer_test", 0, 0, 0, 0)

const s1 = Span("infer_test", 1, 1, 1, 1)

const s2 = Span("infer_test", 2, 2, 2, 2)

const s3 = Span("infer_test", 3, 3, 3, 3)

const s4 = Span("infer_test", 4, 4, 4, 4)

const s5 = Span("infer_test", 5, 5, 5, 5)

const s6 = Span("infer_test", 6, 6, 6, 6)

const s7 = Span("infer_test", 7, 7, 7, 7)

const s8 = Span("infer_test", 8, 8, 8, 8)

pub fn infer_typ0_test() {
  let term = ast.Typ(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(1)
}

pub fn infer_typ1_test() {
  let term = ast.Typ(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(2)
}

pub fn infer_hole_concrete_test() {
  let new_state = State(..new_state, hole_counter: 1)
  let term = ast.Hole(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, hole_counter: 2)
  assert result == term
  assert type_ == ast.vhole(1, [])
}

pub fn infer_hole_unknown_test() {
  let new_state = State(..new_state, hole_counter: 10)
  let term = ast.Hole(-1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, hole_counter: 12)
  assert result == ast.Hole(10, s0)
  assert type_ == ast.vhole(11, [])
}

pub fn infer_lit_int_test() {
  let term = ast.int(42, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_lit_float_test() {
  let term = ast.float(3.14, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vfloat_t
}

pub fn infer_litt_intt_test() {
  let term = ast.int_t(s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_floatt_intt_test() {
  let term = ast.float_t(s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_var_undefined_test() {
  let term = ast.Var(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == with_err(new_state, state.VarUndefined(1, s0))
  assert result == term
  assert type_ == ast.VErr
}

pub fn infer_var0_test() {
  let vars = [#("x", ast.vint(42), ast.vint_t)]
  let new_state = State(..new_state, vars: vars)
  let term = ast.Var(0, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_var1_test() {
  let vars = [
    #("x", ast.vint(42), ast.vint_t),
    #("y", ast.vfloat(3.14), ast.vfloat_t),
  ]
  let new_state = State(..new_state, vars: vars)
  let term = ast.Var(1, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vfloat_t
}

pub fn infer_ctr_test() {
  let term = ast.Ctr("A", ast.Typ(0, s0), s1)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VCtr("A", ast.VTyp(1))
}

pub fn infer_rcd0_test() {
  let term = ast.Rcd([], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VRcdT([])
}

pub fn infer_rcd1_test() {
  let term = ast.Rcd([#("x", ast.int(42, s1))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VRcdT([#("x", ast.vint_t, None)])
}

pub fn infer_rcd2_test() {
  let term = ast.Rcd([#("x", ast.int(42, s1)), #("y", ast.float(3.14, s2))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_
    == ast.VRcdT([#("x", ast.vint_t, None), #("y", ast.vfloat_t, None)])
}

pub fn infer_rcdt0_test() {
  let term = ast.RcdT([], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_rcdt1_test() {
  let term = ast.RcdT([#("x", ast.int_t(s1), None)], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_rcdt2_test() {
  let term =
    ast.RcdT([#("x", ast.int_t(s1), None), #("y", ast.float_t(s2), None)], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_rcdt_from_default_value_test() {
  let term = ast.RcdT([#("x", ast.int_t(s1), Some(ast.int(42, s2)))], s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == ast.RcdT([#("x", ast.int_t(s1), Some(ast.int(42, s2)))], s0)
  assert type_ == ast.VTyp(0)
}

pub fn infer_call_test() {
  let term = ast.Call("f", [], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_call_args_test() {
  let term =
    ast.Call("f", [#(ast.float(3.14, s1), ast.float_t(s2))], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_call_arg_type_mismatch_test() {
  let term =
    ast.Call("f", [#(ast.float(3.14, s1), ast.int_t(s2))], ast.int_t(s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  let error = state.TypeMismatch(#(ast.vfloat_t, s1), #(ast.vint_t, s2))
  assert state == with_err(new_state, error)
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_ann_test() {
  let term = ast.Ann(ast.int(42, s1), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == ast.int(42, s1)
  assert type_ == ast.vint_t
}

pub fn infer_ann_type_mismatch_test() {
  let term = ast.Ann(ast.float(3.14, s1), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  let error = state.TypeMismatch(#(ast.vfloat_t, s1), #(ast.vint_t, s2))
  assert state == with_err(new_state, error)
  assert result == ast.float(3.14, s1)
  assert type_ == ast.vfloat_t
}

pub fn infer_ann_hole_type_test() {
  let term = ast.Ann(ast.int(42, s1), ast.Hole(10, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state
    == State(..new_state, subst: [#(10, ast.vint_t)], hole_counter: 1)
  assert result == ast.int(42, s1)
  assert type_ == ast.vint_t
}

pub fn infer_lam_zero_implicits_test() {
  // monomorphic identity
  // $fn(x: $Int) => x
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(0, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi(x: $Int) -> $Int
  assert type_ == ast.VPi([], [], #("x", ast.vint_t), ast.vint_t)
}

pub fn infer_lam_one_implicit_ref_explicit_test() {
  // polymorphic identity
  // $fn<a: $Type>(x: a) => x
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(0, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi<a: $Type>(x: a) -> a
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(0, [])),
      ast.vvar(0, []),
    )
}

pub fn infer_lam_one_implicit_ref_implicit_test() {
  // typeof
  // $fn<a: $Type>(x: a) => a
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(1, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi<a: $Type>(x: a) -> $Type
  assert type_
    == ast.VPi([], [#("a", ast.VTyp(0))], #("x", ast.vvar(0, [])), ast.VTyp(0))
}

pub fn infer_lam_two_implicits_test() {
  // $fn<a: $Type<0>, b: $Type<1>>(pair: ${x: a, y: b}) => {xt: a, yt: b}
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1)), #("b", ast.Typ(1, s2))],
      #(
        "pair",
        ast.RcdT(
          [#("x", ast.Var(1, s4), None), #("y", ast.Var(0, s5), None)],
          s3,
        ),
      ),
      ast.Rcd([#("xt", ast.Var(2, s7)), #("yt", ast.Var(1, s8))], s6),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi<a: $Type<0>, b: $Type<1>>(pair: ${x: a, y: b}) -> ${xt: $Type, yt: $Type}
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0)), #("b", ast.VTyp(1))],
      #(
        "pair",
        ast.VRcdT([#("x", ast.vvar(1, []), None), #("y", ast.vvar(0, []), None)]),
      ),
      ast.VRcdT([#("xt", ast.VTyp(0), None), #("yt", ast.VTyp(1), None)]),
    )
}

pub fn infer_lam_nested_test() {
  // $fn(x: $Int) => $fn(y: $Float) => {a: x, b: y}
  let term =
    ast.Lam(
      [],
      #("x", ast.int_t(s1)),
      ast.Lam(
        [],
        #("y", ast.float_t(s3)),
        ast.Rcd([#("a", ast.Var(1, s5)), #("b", ast.Var(0, s6))], s4),
        s2,
      ),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi(x: $Int) -> $pi(y: $Float) -> ${a: $Int, b: $Float}
  assert type_
    == ast.VPi(
      [],
      [],
      #("x", ast.vint_t),
      ast.VPi(
        [ast.vvar(1, [])],
        [],
        #("y", ast.vfloat_t),
        ast.VRcdT([#("a", ast.vint_t, None), #("b", ast.vfloat_t, None)]),
      ),
    )
}

pub fn infer_lam_closure_test() {
  // $let y: $Float = 3.14; $fn(x: $Int) => y
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(1, s2), s0)
  let var_y = #("y", ast.vfloat(3.14), ast.vfloat_t)
  let new_state = State(..new_state, vars: [var_y])
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi(x: $Int) -> $Float (with env [3.14])
  assert type_
    == ast.VPi([ast.vfloat(3.14)], [], #("x", ast.vint_t), ast.vfloat_t)
}

pub fn infer_lam_closure_shift_test() {
  // $let z = 3.14; $let y = z; $fn(x: $Int) => y
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(1, s2), s0)
  let var_y = #("y", ast.vvar(1, []), ast.vfloat_t)
  let var_z = #("z", ast.vfloat(3.14), ast.vfloat_t)
  let new_state = State(..new_state, vars: [var_y, var_z])
  assert list.map(new_state.vars, fn(var) { var.0 }) == ["y", "z"]
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // $pi(x: $Int) -> $Float (with env [z, 3.14])
  let env = [ast.vvar(2, []), ast.vfloat(3.14)]
  assert type_ == ast.VPi(env, [], #("x", ast.vint_t), ast.vfloat_t)
}

// --- Additional edge cases for infer_lam ---

pub fn infer_lam_implicit_and_closure_test() {
  // $let y = 3.14; $fn<a: $Type>(x: a) => y
  // After pushing a (implicit) and x (param), vars = [x, a, y]
  // Body Var(2) refers to y at index 2
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Var(2, s3),
      s0,
    )
  let var_y = #("y", ast.vfloat(3.14), ast.vfloat_t)
  let new_state = State(..new_state, vars: [var_y])
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // env: [3.14], implicits: [a: $Type], param: (x: a), body_type: $Float
  assert type_
    == ast.VPi(
      [ast.vfloat(3.14)],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(0, [])),
      ast.vfloat_t,
    )
}

pub fn infer_lam_implicit_shadowing_test() {
  // $fn<a: $Type>(x: a) => $fn<a: $Int>(y: a) => y
  // Inner `a` shadows outer `a`
  // Outer vars after push: [x, a_outer]
  // Inner vars after push: [y, a_inner, x, a_outer]
  // Body Var(0) refers to y; body type = a_inner's value = vvar(0, [])
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Lam(
        [#("a", ast.int_t(s4))],
        #("y", ast.Var(0, s5)),
        ast.Var(0, s6),
        s3,
      ),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // Inner vars after full push: [y, a_inner, x, a_outer]
  // Inner VPi context: y=0, a_inner=1, x=2, a_outer=3
  // Inner env: [vvar(2), vvar(3)] = x at level 2, a_outer at level 3
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(0, [])),
      ast.VPi(
        [ast.vvar(2, []), ast.vvar(3, [])],
        [#("a", ast.vint_t)],
        #("y", ast.vvar(0, [])),
        ast.vvar(0, []),
      ),
    )
}

pub fn infer_lam_three_nests_test() {
  // $fn(x: $Int) => $fn(y: $Float) => $fn(z: $Int) => x
  // After outer push x: [x]
  // After middle push y: [y, x]
  // After inner push z: [z, y, x]
  // Body Var(2) refers to x
  let term =
    ast.Lam(
      [],
      #("x", ast.int_t(s1)),
      ast.Lam(
        [],
        #("y", ast.float_t(s3)),
        ast.Lam([], #("z", ast.int_t(s5)), ast.Var(2, s6), s4),
        s2,
      ),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // Inner env: [vvar(1), vvar(2)] = captures y, x from inner VPi's context
  // Middle env: [vvar(1)] = captures x from middle VPi's context
  // Outer env: [] = captures nothing
  assert type_
    == ast.VPi(
      [],
      [],
      #("x", ast.vint_t),
      ast.VPi(
        [ast.vvar(1, [])],
        [],
        #("y", ast.vfloat_t),
        ast.VPi(
          [ast.vvar(1, []), ast.vvar(2, [])],
          [],
          #("z", ast.vint_t),
          ast.vint_t,
        ),
      ),
    )
}

pub fn infer_lam_closure_deeper_test() {
  // $let a = 1; $let b = 2; $fn(x: $Int) => a
  // After push x: [x, b, a]
  // Body Var(2) refers to a at index 2
  let term = ast.Lam([], #("x", ast.int_t(s1)), ast.Var(2, s2), s0)
  let var_a = #("a", ast.vint(1), ast.vint_t)
  let var_b = #("b", ast.vint(2), ast.vint_t)
  let new_state = State(..new_state, vars: [var_b, var_a])
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // env: [vint(2), vint(1)] = [b's value, a's value] (order: innermost first)
  assert type_
    == ast.VPi([ast.vint(2), ast.vint(1)], [], #("x", ast.vint_t), ast.vint_t)
}

pub fn infer_lam_hole_param_type_test() {
  // $fn(x: ?) => x
  // eval on Hole(0, _) returns vhole(0, []) without creating a new hole.
  // So the hole_counter stays at 0.
  let term = ast.Lam([], #("x", ast.Hole(0, s1)), ast.Var(0, s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  // No new holes created during push_param (eval doesn't create holes)
  assert state == new_state
  assert result == term
  // param type value = vhole(0, []), body type = x's type = vhole(0, [])
  assert type_ == ast.VPi([], [], #("x", ast.vhole(0, [])), ast.vhole(0, []))
}

pub fn infer_lam_implicit_and_nested_closure_test() {
  // $let y = 3.14; $fn<a: $Type>(x: a) => $fn<b: $Type>(z: b) => y
  // After outer push a, x: [x, a, y]
  // After inner push b, z: [z, b, x, a, y]
  // Body Var(4) refers to y at index 4
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Lam(
        [#("b", ast.Typ(1, s3))],
        #("z", ast.Var(0, s4)),
        ast.Var(4, s5),
        s6,
      ),
      s0,
    )
  let var_y = #("y", ast.vfloat(3.14), ast.vfloat_t)
  let new_state = State(..new_state, vars: [var_y])
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // Inner vars after full push: [z, b, x, a, y]
  // Inner VPi context: z=0, b=1, x=2, a=3, y=4
  // Inner env: [vvar(2), vvar(3), vfloat(3.14)] = x@2, a@3, y@4
  // Outer env: [vfloat(3.14)] (captures y)
  assert type_
    == ast.VPi(
      [ast.vfloat(3.14)],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(0, [])),
      ast.VPi(
        [ast.vvar(2, []), ast.vvar(3, []), ast.vfloat(3.14)],
        [#("b", ast.VTyp(1))],
        #("z", ast.vvar(0, [])),
        ast.vfloat_t,
      ),
    )
}

pub fn infer_lam_nested_with_both_implicits_test() {
  // $fn<a: $Type>(x: a) => $fn(y: $Float) => x
  let term =
    ast.Lam(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Lam([], #("y", ast.float_t(s4)), ast.Var(1, s5), s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // Inner: VPi([vvar(1), vvar(2)], [], (y: $Float), vvar(1))
  // captures x (vvar(1)), a (vvar(2)) from inner VPi's context
  // Outer: VPi([], [a: $Type], (x: a), inner)  — captures nothing
  assert type_
    == ast.VPi(
      [],
      [#("a", ast.VTyp(0))],
      #("x", ast.vvar(0, [])),
      ast.VPi(
        [ast.vvar(1, []), ast.vvar(2, [])],
        [],
        #("y", ast.vfloat_t),
        ast.vvar(1, []),
      ),
    )
}

// --- Tests for infer_pi (Pi type inference) ---

pub fn infer_pi_simple_test() {
  // $pi<$Int>(x: $Int) -> $Int  (non-dependent)
  let term = ast.Pi([], #("x", ast.int_t(s1)), ast.int_t(s2), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  // Pi types have type $Type (VTyp(0))
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_dependent_ref_implicit_test() {
  // $pi<a: $Type>(x: a) -> a
  // Domain: Var(0) = a (implicit, at index 0 after push)
  // Codomain: Var(1) = a (implicit, at index 1 after pushing x)
  // DeBruijn: after push a then x: [x, a], so a is at index 1
  let term =
    ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), ast.Var(1, s3), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
  // The Pi term's domain is the original term Var(0) (refers to a)
  // The Pi term's codomain is the original term Var(1) (refers to a)
}

pub fn infer_pi_dependent_ref_domain_param_test() {
  // $pi<a: $Type, b: $Type>(x: a) -> b
  // After push a, b: [b, a]
  // After push x: [x, b, a]
  // Domain Var(1) = b (implicit at index 1 after push a)
  // Codomain Var(2) = a (implicit at index 2 after push a, x)
  let term =
    ast.Pi(
      [#("a", ast.Typ(0, s1)), #("b", ast.Typ(1, s2))],
      #("x", ast.Var(1, s4)),
      ast.Var(2, s5),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_closure_capture_test() {
  // $let T = $Type; $pi<a: $Type>(x: a) -> T
  // After push a: [a, T]
  // After push x: [x, a, T]
  // Codomain Var(2) = T (outer var at index 2)
  let term =
    ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), ast.Var(2, s3), s0)
  let var_t = #("T", ast.vvar(0, []), ast.VTyp(1))
  let new_state = State(..new_state, vars: [var_t])
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_two_implicits_test() {
  // $pi<a: $Type<0>, b: $Type<1>>(pair: ${x: a, y: b}) -> $Type
  // After push a: [a]
  // After push b: [b, a]
  // After push pair: [pair, b, a]
  // Domain: RcdT with x: Var(1)=a, y: Var(0)=b
  // Codomain: Rcd with xt: Var(2)=a, yt: Var(1)=b
  let rcd_t =
    ast.RcdT([#("x", ast.Var(1, s4), None), #("y", ast.Var(0, s5), None)], s3)
  let term =
    ast.Pi(
      [#("a", ast.Typ(0, s1)), #("b", ast.Typ(1, s2))],
      #("pair", rcd_t),
      ast.Rcd([#("xt", ast.Var(2, s7)), #("yt", ast.Var(1, s8))], s6),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_nested_test() {
  // $pi<a: $Type>(x: a) -> $pi<b: $Type>(y: b) -> $Type<0>
  // Outer Pi: [a] -> [x, a]
  // Inner Pi (from outer's codomain): [b] -> [y, b]
  // Then push inner's params: [inner_y, inner_b, x, a]
  // Codomain: Var(3) = a, Var(2) = x, Var(1) = inner_b, Var(0) = inner_y
  let inner_codomain = ast.Typ(0, s6)
  let inner_pi =
    ast.Pi([#("b", ast.Typ(1, s4))], #("y", ast.Var(0, s5)), inner_codomain, s3)
  let term =
    ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), inner_pi, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_hole_domain_test() {
  // $pi<<?>(x: a) -> $Int
  // Hole in implicit param type
  let term =
    ast.Pi([#("a", ast.Hole(0, s1))], #("x", ast.Var(0, s2)), ast.int_t(s3), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_hole_codomain_test() {
  // $pi<a: $Type>(x: a) -> ?
  // Hole in codomain
  let new_state = State(..new_state, hole_counter: 0)
  let term =
    ast.Pi(
      [#("a", ast.Typ(0, s1))],
      #("x", ast.Var(0, s2)),
      ast.Hole(0, s3),
      s0,
    )
  let #(result, type_, state) = infer(new_state, term)
  // Hole creates a new hole for the codomain's type
  assert state == State(..new_state, hole_counter: 1)
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_closure_and_implicits_test() {
  // $let T = $Type; $pi<a: $Type>(x: a) -> T
  // After push a: [a, T]
  // After push x: [x, a, T]
  // Codomain Var(2) = T
  let term =
    ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), ast.Var(2, s3), s0)
  let var_t = #("T", ast.vvar(0, []), ast.VTyp(1))
  let new_state = State(..new_state, vars: [var_t])
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_pi_implicit_shadowing_test() {
  // $pi<a: $Type>(x: a) -> $pi<a: $Int>(y: a) -> $Type<1>
  // Inner Pi's codomain: Var(1) = a_inner (the inner implicit)
  let inner_pi =
    ast.Pi([#("a", ast.int_t(s4))], #("y", ast.Var(0, s5)), ast.Typ(1, s6), s3)
  let term =
    ast.Pi([#("a", ast.Typ(0, s1))], #("x", ast.Var(0, s2)), inner_pi, s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == new_state
  assert result == term
  assert type_ == ast.VTyp(0)
}

pub fn infer_fix_const_test() {
  let term = ast.Fix("f", ast.int(42, s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, subst: [#(0, ast.vint_t)], hole_counter: 1)
  assert result == term
  assert type_ == ast.vint_t
}

pub fn infer_fix_unsolved_test() {
  let term = ast.Fix("f", ast.Var(0, s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, subst: [], hole_counter: 1)
  assert result == term
  assert type_ == ast.vhole(0, [])
}

pub fn infer_fix_annotated_test() {
  let term = ast.Fix("f", ast.Ann(ast.Var(0, s2), ast.int_t(s3), s1), s0)
  let #(result, type_, state) = infer(new_state, term)
  assert state == State(..new_state, subst: [#(0, ast.vint_t)], hole_counter: 1)
  assert result == ast.Fix("f", ast.Var(0, s2), s0)
  assert type_ == ast.vint_t
}
//

// pub fn infer_typedef_empty_test() {
//   let term = ast.TypeDef([], [], s0)
//   let #(result, type_, state) = infer(new_state, term)
//   assert result == term
//   assert type_ == ast.VTyp(0)
//   assert state == new_state
// }
//   TypeDef( name: String, params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )

//   Match(arg: Term, cases: List(Case), span: Span)
//   Err(message: String, span: Span)
// --- Tests for infer_fix (fix-point recursion) ---
