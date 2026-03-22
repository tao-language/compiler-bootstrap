# Core Language Changes for Tao Integration

> **Goal**: Document core language changes required for Tao integration
> **Status**: 📋 Planned
> **Date**: March 2025

---

## Overview

The Tao high-level language requires several changes to the core language to support:
1. Untyped literals with coercion
2. Pattern guards in match expressions
3. Operator overloading metadata

These changes are **minimal and focused**—they don't require redesigning the core language, just extending it to support Tao's desugaring needs.

---

## Change 1: Untyped Literals (HIGH PRIORITY)

### Current State

```gleam
pub type Literal {
  I32(Int)
  I64(Int)
  U32(Int)
  U64(Int)
  F32(Float)
  F64(Float)
}
```

**Problem**: Tao wants untyped literals (`42`, `3.14`) that can be inferred to any compatible type.

### Proposed Change

```gleam
pub type Literal {
  /// Untyped integer literal (e.g., 42, -1, 0)
  /// Type inference determines: I32, I64, U32, U64, F32, F64
  Int(Int)
  
  /// Untyped float literal (e.g., 3.14, -0.5)
  /// Type inference determines: F32, F64
  Float(Float)
}
```

### Additional Change: Coercion Term

Add a new term form for literal coercion:

```gleam
pub type TermData {
  // ... existing constructors
  
  /// Coerce a literal from one type to another
  /// Inserted by type checker for untyped literals
  Coerce(term: Term, from: LiteralType, to: LiteralType)
}
```

### Type Checker Changes

The type checker needs to insert coercions during inference:

```gleam
fn infer(state: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    Lit(Int(value)) -> {
      // Default to I32, but allow unification to change it
      let i32_type = VLitT(I32T)
      let i32_value = VLit(Int(value))
      #(i32_value, i32_type, state)
    }
    
    Ann(inner, expected_type) -> {
      let #(inner_val, inner_ty, s) = infer(state, inner)
      
      // Check if coercion is needed
      case needs_coercion(inner_ty, expected_type) {
        True -> {
          // Insert coercion
          let coerce_term = Term(Coerce(inner, inner_ty, expected_type), term.span)
          let coerced_val = apply_coercion(inner_val, inner_ty, expected_type)
          #(coerced_val, expected_type, s)
        }
        False -> #(inner_val, inner_ty, s)
      }
    }
    
    // ... other cases
  }
}
```

### Desugaring Example

```tao
// Tao source
let x: Float = 42

// Tao AST
LetDecl("x", None, Annotated(Lit(Int(42)), TPrim(Float)))

// Desugared to Core (with coercion)
Ann(
  Coerce(
    Lit(Int(42)),
    I32T,
    F64T
  ),
  LitT(F64T)
)
```

### Implementation Effort

- **Literal type change**: ~10 lines
- **Coerce term**: ~20 lines
- **Type checker coercion logic**: ~50 lines
- **Evaluator coercion handling**: ~20 lines
- **Tests**: ~30 lines

**Total**: ~100 lines, 1-2 days

---

## Change 2: Pattern Guards (MEDIUM PRIORITY)

### Current State

```gleam
pub type Case {
  Case(pattern: Pattern, body: Term, span: Span)
}
```

**Problem**: Tao supports pattern guards (`match x { | Some(y) if y > 0 -> y }`), but core doesn't.

### Proposed Change

```gleam
pub type Case {
  Case(
    pattern: Pattern,
    guard: Option(Term),  // NEW: Optional guard expression
    body: Term,
    span: Span,
  )
}
```

### Type Checker Changes

Guards are checked as boolean expressions:

```gleam
fn check_case(state: State, case: Case, expected_type: Type) -> #(Value, State) {
  let #(body_val, s) = check(state, case.body, expected_type)
  
  case case.guard {
    Some(guard_term) -> {
      // Check guard as boolean
      let #(guard_val, guard_s) = check(s, guard_term, bool_type)
      #(VCase(case.pattern, guard_val, body_val), guard_s)
    }
    None -> {
      #(VCase(case.pattern, None, body_val), s)
    }
  }
}
```

### Evaluator Changes

Guards are evaluated during pattern matching:

```gleam
fn eval_match(state: State, scrutinee: Value, cases: List(Case)) -> Value {
  case cases {
    [] -> VErr  // No match (should be caught by exhaustiveness)
    [case, ..rest] -> {
      case match_pattern(case.pattern, scrutinee, state) {
        Some(bindings) -> {
          case case.guard {
            Some(guard_term) -> {
              let guard_result = eval(guard_term, extend_state(state, bindings))
              case guard_result {
                VCtr("True", _) => eval(case.body, extend_state(state, bindings))
                _ => eval_match(state, scrutinee, rest)  // Try next case
              }
            }
            None => eval(case.body, extend_state(state, bindings))
          }
        }
        None => eval_match(state, scrutinee, rest)
      }
    }
  }
}
```

### Exhaustiveness Checking

Guards complicate exhaustiveness checking:

```gleam
// Current: All patterns must be covered
// With guards: Guarded patterns are "partial" matches

fn check_exhaustiveness(cases: List(Case), type_info: TypeInfo) -> List(Error) {
  // For guarded patterns, be conservative:
  // - If a guard is present, assume it might fail
  // - Continue checking remaining cases
  
  case cases {
    [] => check_remaining(type_info)  // Check if type is fully covered
    [case, ..rest] => {
      case case.guard {
        Some(_) => {
          // Guarded pattern: check rest as well
          check_exhaustiveness(rest, type_info)
        }
        None => {
          // Unguarded pattern: this case is definitive
          check_exhaustiveness(rest, remove_matched(type_info, case.pattern))
        }
      }
    }
  }
}
```

### Desugaring Example

```tao
// Tao source
match maybe {
  | Some(x) if x > 0 -> x
  | _ -> 0
}

// Tao AST
Match(
  Var("maybe"),
  [
    MatchClause(PCtr("Some", PVar("x")), Some(BinOp(Var("x"), Gt, Lit(0))), Var("x")),
    MatchClause(PAny, None, Lit(0))
  ]
)

// Desugared to Core (with guard)
Match(
  Var("maybe"),
  motive,
  [
    Case(
      PCtr("Some", PAs(PAny, "x")),
      Some(App(App(Var(">"), Var("x")), Lit(0))),  // Guard
      Var("x")
    ),
    Case(PAny, None, Lit(0))
  ]
)
```

### Implementation Effort

- **Case type change**: ~5 lines
- **Type checker guard handling**: ~20 lines
- **Evaluator guard handling**: ~25 lines
- **Exhaustiveness checking update**: ~30 lines
- **Tests**: ~20 lines

**Total**: ~50 lines, 1 day

---

## Change 3: Operator Overloading Metadata (LOW PRIORITY)

### Current State

No tracking of overloaded functions in core.

**Problem**: Tao wants operator overloading (`add(Int, Int)` and `add(Float, Float)`), but core has a single namespace.

### Proposed Change

Add overload tracking to `State`:

```gleam
pub type State {
  State(
    // ... existing fields
    
    /// Overloaded function signatures
    /// Maps function name to list of (type_params, arg_types, return_type)
    overloads: Dict(String, List(OverloadSignature)),
  )
}

pub type OverloadSignature {
  OverloadSignature(
    type_params: List(String),
    arg_types: List(Type),
    return_type: Type,
  )
}
```

### Type Checker Changes

During type checking, resolve overloads by matching argument types:

```gleam
fn infer_call(state: State, name: String, args: List(Term)) -> #(Value, Type, State) {
  case dict.get(state.overloads, name) {
    Ok(signatures) => {
      // Infer argument types
      let #(arg_vals, arg_types, s) = infer_args(state, args)
      
      // Find matching overload
      case find_matching_overload(signatures, arg_types) {
        Ok(signature) => {
          // Inject type applications and call
          let call_term = make_call(name, signature, arg_vals)
          let call_val = eval(call_term, s)
          #(call_val, signature.return_type, s)
        }
        Error(_) => {
          // No matching overload
          let error = NoMatchingOverload(name, arg_types)
          #(VErr, VErr, with_err(s, error))
        }
      }
    }
    Error(_) => {
      // Not overloaded, regular variable lookup
      infer_var(state, name)
    }
  }
}
```

### Name Mangling Approach (Alternative)

Instead of runtime overload resolution, use name mangling during desugaring:

```gleam
// Tao desugaring
fn desugar_binop(left, op, right, span) {
  let op_name = case op {
    OpAdd -> "add"
    // ...
  }
  
  // After type inference, mangle name
  let mangled_name = case inferred_type {
    I32T -> "add_Int_Int"
    F64T -> "add_Float_Float"
    // ...
  }
  
  mk_app2(mk_var(mangled_name, span), left_term, right_term, span)
}
```

**Recommendation**: Use name mangling (simpler, no core changes needed for resolution).

### Implementation Effort

- **State overload field**: ~5 lines
- **OverloadSignature type**: ~10 lines
- **Type checker resolution**: ~40 lines
- **Tests**: ~25 lines

**Total**: ~30 lines (with name mangling), 0.5 days

---

## Implementation Order

### Phase 1: Untyped Literals (HIGH PRIORITY)

1. Change `Literal` type to untyped
2. Add `Coerce` term
3. Update type checker to insert coercions
4. Update evaluator to handle coercions
5. Tests

**Estimated time**: 1-2 days

### Phase 2: Pattern Guards (MEDIUM PRIORITY)

1. Add `guard` field to `Case`
2. Update type checker for guard checking
3. Update evaluator for guard evaluation
4. Update exhaustiveness checking
5. Tests

**Estimated time**: 1 day

### Phase 3: Operator Overloading (LOW PRIORITY)

1. Decide: name mangling vs. runtime resolution
2. If name mangling: update Tao desugaring only
3. If runtime: add overload metadata to State
4. Tests

**Estimated time**: 0.5-1 day

---

## Testing Strategy

### Unit Tests

```gleam
// Untyped literals
pub fn untyped_literal_int_test() {
  let term = Lit(Int(42))
  let #(val, typ, _) = infer(initial_state, term)
  val |> should.equal(VLit(Int(42)))
  typ |> should.equal(VLitT(I32T))  // Defaults to I32
}

// Coercion
pub fn literal_coercion_test() {
  let term = Ann(Lit(Int(42)), LitT(F64T))
  let #(val, typ, _) = infer(initial_state, term)
  typ |> should.equal(VLitT(F64T))
  // val should be coerced
}

// Pattern guards
pub fn pattern_guard_test() {
  let case = Case(PCtr("Some", PAs(PAny, "x")), Some(Var("x")), Var("x"), span)
  // Check guard is preserved
  case.guard |> should.equal(Some(Var("x")))
}
```

### Integration Tests

```gleam
// Tao → Core → Evaluate
pub fn tao_roundtrip_test() {
  let tao_source = "let x: Float = 42"
  let tao_ast = parse_tao(tao_source)
  let core_term = desugar_tao(tao_ast)
  let #(val, _, _) = eval(initial_state, core_term)
  val |> should.equal(VLit(Float(42.0)))
}
```

---

## Risks and Mitigations

### Risk 1: Breaking Existing Code

**Impact**: HIGH - Changes to `Literal` type break existing code

**Mitigation**:
- Update all literal construction sites in single PR
- Provide migration helper functions
- Document changes clearly

### Risk 2: Coercion Performance

**Impact**: MEDIUM - Runtime coercion overhead

**Mitigation**:
- Optimize common coercions (Int → Float)
- Document that coercions are inserted only when needed
- Consider compile-time coercion evaluation

### Risk 3: Guard Exhaustiveness Complexity

**Impact**: MEDIUM - Exhaustiveness checking with guards is complex

**Mitigation**:
- Conservative checking (assume guards might fail)
- Warn on complex guarded patterns
- Document limitations

---

## References

- **[05-comprehensive-analysis.md](../tao/05-comprehensive-analysis.md)** - Full analysis
- **[../../docs/core.md](../../docs/core.md)** - Core language specification
- **[../tao/02-syntax.md](../tao/02-syntax.md)** - Tao syntax specification
