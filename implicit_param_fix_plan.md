# Implicit Parameter Fix Plan

## Problem Analysis

### Root Cause
The `term_to_debruijn` function in `ast.gleam` builds the lambda body environment as:
```gleam
let body_env = list.append(implicit_names, [name, ..env])
```

This means De Bruijn indices for the lambda body are:
- **Index 0**: First implicit param `a`
- **Index 1**: Second implicit param (if any)
- **Index n**: Lambda param `x` (where n = number of implicit params)
- **Index n+1+**: Outer scope variables

### The Bug
`infer_lam` only adds the lambda param to the state:
```gleam
let bound_value = ast.VNeut(ast.HVar(0), [])
let state_ext = state.State(
  ..state,
  vars: [#(param_name, #(bound_value, param_val)), ..state.vars],
)
```

This means during body inference:
- `Var(0)` → lambda param `x` ✓ (correct)
- `Var(1)` → outer scope var ✗ (should be implicit param `a`)

The VLam's env only contains the outer scope's variables, not the implicit params.

## Fix Strategy

### Three places need modification:

1. **`infer_lam`** (src/core/infer.gleam)
   - Add implicit params as fresh holes to state BEFORE the lambda param
   - Shift body by n (number of implicit params)
   - Build VLam's env to include: [fresh_holes_for_implicits, lambda_param]

2. **`infer_app` let binding case** (src/core/infer.gleam)  
   - Shift let body by 1 (for let-bound var)
   - Substitute Var(0) with converted arg
   - Extend state with let-bound var

3. **`infer_app` VLam case** (src/core/infer.gleam)
   - Shift let body by 1 (for let binding extension)
   - Create fresh holes for implicits
   - Substitute fresh holes for implicit params in body
   - Substitute Var(0) with converted arg (lambda param)
   - Shift body by n+1 (for let binding + implicits)
   - Extend state with: [let_bound_var, implicit_holes..., lambda_param]

## Detailed Changes

### Change 1: infer_lam

```gleam
fn infer_lam(state, implicits, param, body, _span) -> #(Value, Value, State) {
  let param_name = param.0
  let param_type_term = param.1
  let param_val = evaluate(state, param_type_term)
  
  // Evaluate implicits and add them to state as fresh holes
  let #(implicit_env, implicit_state) = list.fold(
    list.reverse(implicits),
    #( [], state ),
    fn(acc, imp) {
      let #(acc_env, s) = acc
      let ival = evaluate(s, imp.1)
      let fresh_id = s.hole_counter
      let new_s = state.State(..s, hole_counter: fresh_id + 1)
      let hole = ast.VNeut(ast.HHole(fresh_id), [])
      let state_with_imp = def_var(new_s, imp.0, hole, ival)
      #([#(imp.0, hole), ..acc_env], state_with_imp)
    },
  )
  
  // Shift body by n (number of implicit params) to account for implicits in state
  let shifted_body = ast.shift_term(body, list.length(implicits))
  
  // Add lambda param AFTER implicit params (so it's at index n)
  let bound_value = ast.VNeut(ast.HVar(list.length(implicits)), [])
  let param_val = evaluate(implicit_state, param_type_term)
  let state_ext = state.State(
    ..implicit_state,
    vars: [#(param_name, #(bound_value, param_val)), ..implicit_state.vars],
  )
  
  let #(_body_val, body_type, state5) = infer(state_ext, shifted_body)
  
  // VLam env: [implicit_param_values..., lambda_param_bound_value]
  let env = list.append(implicit_env, [bound_value])
  let lam_value = ast.VLam(env, implicit_env, #(param_name, param_val), shifted_body)
  let pi_type = ast.VPi(env, implicit_env, #(param_name, param_val), body_type)
  
  #(lam_value, pi_type, state5)
}
```

### Change 2: infer_app let binding case

```gleam
ast.Lam(implicits, #(param_name, param_type), body, _lam_span) -> {
  let #(arg_val, arg_type, state2) = infer(state, arg)
  let param_val = evaluate(state2, param_type)
  let filled_arg = fill_record_defaults_value(arg_val, param_val)
  let converted_arg = case param_val {
    ast.VLitT(ast.FloatT) ->
      case filled_arg {
        ast.VLit(ast.Int(v)) ->
          case float.parse(int.to_string(v) <> ".0") {
            Ok(f) -> ast.VLit(ast.Float(f))
            Error(_) -> filled_arg
          }
        _ -> filled_arg
      }
    _ -> filled_arg
  }
  let updated_lam = case converted_arg {
    ast.VLam(env, implicits, param, body) ->
      ast.VLam(list.append(env, [converted_arg]), implicits, param, body)
    _ -> converted_arg
  }
  
  // Shift let body by 1 to account for let-bound var
  let shifted_body = ast.shift_term(body, 1)
  // Substitute Var(0) with converted_arg (let-bound var)
  let substituted_body = ast.subst_term_var(0, converted_arg, shifted_body)
  
  let state_ext = def_var(state2, param_name, updated_lam, arg_type)
  let #(body_val, body_type, state_final) = infer(state_ext, substituted_body)
  #(body_val, body_type, state_final)
}
```

### Change 3: infer_app VLam case

```gleam
ast.VLam(lam_env, implicits, #(_pname, param_type), body) -> {
  let filled_arg = fill_record_defaults_value(arg_val, param_type)
  let converted_arg = case param_type {
    ast.VLitT(ast.FloatT) ->
      case filled_arg {
        ast.VLit(ast.Int(v)) ->
          case float.parse(int.to_string(v) <> ".0") {
            Ok(f) -> ast.VLit(ast.Float(f))
            Error(_) -> filled_arg
          }
        _ -> filled_arg
      }
    _ -> filled_arg
  }
  
  // Shift let body by 1 for let binding extension
  let shifted_body = ast.shift_term(body, 1)
  // Substitute Var(0) in shifted body with converted_arg (lambda param)
  let substituted_body = ast.subst_term_var(0, converted_arg, shifted_body)
  
  // Handle implicit params
  let (body_final, state_with_implicits) = case implicits {
    [] -> #(substituted_body, env_to_state([converted_arg], lam_env, state3))
    [_, ..] -> {
      // Create fresh holes for each implicit param
      let #(holes, state_with_holes) = list.fold(
        implicits,
        #( [], state3 ),
        fn(acc, _imp) {
          let #(acc_holes, s) = acc
          let fresh_id = s.hole_counter
          let hole = ast.VNeut(ast.HHole(fresh_id), [])
          let new_s = state.State(..s, hole_counter: fresh_id + 1)
          #([hole, ..acc_holes], new_s)
        },
      )
      let n = list.length(implicits)
      // Shift body by n+1 (let binding + implicits)
      let shifted_body = ast.shift_term(substituted_body, n + 1)
      // Substitute fresh holes for implicit params (Var(1) through Var(n+1))
      let body_with_holes = list.fold(holes, shifted_body, fn(body, hole) {
        ast.subst_term_var(0, hole, body)
      })
      // Build extended env: [let_bound_var, implicit_holes..., lambda_param]
      let env_with_implicits = list.append(lam_env, [converted_arg])
      let env_with_all = list.append(state_with_holes.vars, fn(v) { v.1.0 })
      let env_all = list.append(env_with_all, holes)
      let state_final = env_to_state(env_all, state3.truth_ctr, state3.ffi)
      #(body_with_holes, state_final)
    }
  }
  
  infer(state_with_implicits, body_final)
}
```

Wait, I need to reconsider the VLam case. The state construction is more complex. Let me think about this more carefully...

Actually, the VLam case needs to construct the state correctly:
- State vars should be: [let_bound_var, implicit_holes..., lambda_param, ..outer_state.vars]

But the let binding case already added the let_bound_var to the state. So the VLam case needs to construct a new state with:
- Head: let_bound_var + implicit_holes + lambda_param
- Tail: rest of original state.vars

Let me reconsider the approach. Actually, the simplest approach is:
1. The let binding case adds the let-bound var to the state
2. The VLam case constructs a new state by prepending to the let binding case's state

Let me revise the plan.
