# GADT/TypeDef Refactoring Plan

## Overview
Refactor TypeDef, VTypeDef, and NamedTypeDef to use Term/Value/NamedTerm for constructor
arg_type and return_type (instead of just Values), enabling proper unification and type checking.

## Changes Required

### Phase 1: AST Changes (src/core/ast.gleam)

1. **TypeDef** - Already correct:
   - `params: List(#(String, Term))`
   - `constructors: List(#(String, List(String), Term, Term, Span))`

2. **VTypeDef** - Change return_type from Value to Term:
   ```gleam
   // Before:
   VTypeDef(name: String, params: List(#(String, Value)), constructors: List(#(String, List(String), Value, Value, Span)))
   
   // After:
   VTypeDef(name: String, params: List(#(String, Value)), constructors: List(#(String, List(String), Value, Term, Span)))
   ```

3. **NamedTypeDef** - Already correct:
   - `params: List(#(String, NamedTerm))`
   - `constructors: List(#(String, List(String), NamedTerm, NamedTerm, Span))`

### Phase 2: Unification Changes (src/core/unify.gleam)

1. **Change unify signature** to return `(Value, State)`:
   ```gleam
   pub fn unify(state: State, expected: Value, actual: Value) -> #(Value, State)
   ```

2. **Update match_values** to return `(Value, State)`:
   ```gleam
   fn match_values(state: State, expected: Value, actual: Value) -> #(Value, State)
   ```

3. **Handle VCtr/VTypeDef matching** to return the solved return type:
   ```gleam
   VCtr(tag, arg), VTypeDef(name, params, constructors) ->
     case list.find(constructors, fn(c) { c.0 == tag }) {
       Ok(#(_, bindings, self_type, result_type, _)) -> {
         // Unify arg with self_type, get state
         let (arg, state1) = match_values(state, self_type, arg)
         // result_type is a Term, infer it to get its type
         // Return (result_type_value, state1)
       }
       ...
     }
   ```

### Phase 3: Inference Changes (src/core/infer.gleam)

1. **Add find_type_def** helper:
   ```gleam
   fn find_type_def(env: List(Value), tag: String) -> Option(#(Value, Value))
   ```
   Returns `(type_def, type_arg)` if found.

2. **Update infer_ctr** to use find_type_def:
   ```gleam
   fn infer_ctr(state, tag, arg, span) -> #(Value, Value, State) {
     let (arg_val, arg_type, state1) = infer(state, arg)
     case find_type_def(state1.vars, tag) {
       Some(#(type_def, type_arg)) -> {
         // Use type_def's return type as the inferred type
         // Unify type_def params with type_arg
         // Return (VCtr(tag, arg_val), result_type, state1)
       }
       None -> {
         // Fall back to current behavior
         #(VCtr(tag, arg_val), VCtr(tag, arg_type), state1)
       }
     }
   }
   ```

3. **Update check** to use find_type_def:
   ```gleam
   fn check(state, term, expected_type) -> #(Value, Value, State) {
     let (value, inferred_type, state1) = infer(state, term)
     case find_type_def(state1.vars, expected_type) {
       Some(#(type_def, type_arg)) -> {
         // Unify type_def params with type_arg
         // Unify inferred_type with expected_type
         #(value, expected_type, state1)
       }
       None -> {
         // Current behavior: unify inferred_type with expected_type
       }
     }
   }
   ```

### Phase 4: Parser Changes (src/core/syntax.gleam)

1. **Update parse_type_def** to handle new syntax:
   ```gleam
   // Without parameters (monomorphic)
   $type {
   | #tag(arg_type) -> return_type
   }
   
   // With parameters (polymorphic)
   $type<x: a, y: b> {
   | @m. #tag(arg_type) -> return_type
   }
   ```

### Phase 5: De Bruijn Conversion (src/core/ast.gleam)

1. **Update term_to_debruijn** to handle new TypeDef structure
2. **Update value_to_string** to handle new VTypeDef structure

### Phase 6: Tests

1. Add unit tests for unify, infer, check with new TypeDef system
2. Update existing tests to use new syntax
3. Run full test suite

## Implementation Order

1. AST changes (ast.gleam)
2. Unification changes (unify.gleam)
3. Inference changes (infer.gleam, generalize.gleam, subst.gleam, eval.gleam)
4. Parser changes (syntax.gleam)
5. De Bruijn conversion (ast.gleam)
6. Tests (infer_test.gleam, type_defs_test.gleam, etc.)

## Key Design Decisions

1. **VTypeDef return_type is Term**: Allows inference to evaluate return types
2. **unify returns (Value, State)**: Enables GADT return type resolution
3. **find_type_def in env**: TypeDefs are stored in the environment for lookup
4. **Type param instantiation**: Unify TypeDef params with concrete args before checking
