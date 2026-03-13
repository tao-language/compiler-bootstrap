# Tao Overloading Implementation Plan (Revised)

> **Goal**: Implement function and operator overloading through implicit arguments
> **Status**: 📋 **Planned** - Revised with unified implicit argument approach
> **Target**: 6-7 weeks

---

## Revised Design Summary

**Key Changes from Original Plan**:

1. **Unified Lam/App**: Single constructor with implicit flag, not separate TypeApp
2. **Hole-Based Inference**: Tao desugars to normal App, Core inference upgrades to implicit
3. **Forall Types**: Polymorphic types encode implicit parameters
4. **Type Reflection**: Free from implicit argument mechanism

---

## Implementation Phases

### Phase 1: Core AST Extensions (1 week)

**Goal**: Add implicit argument support to Core terms and types

#### Day 1-2: Update Term AST

**File**: `src/core/core.gleam`

```gleam
pub type Term {
  // ... existing constructors
  
  // UPDATED: Lam with implicit params
  Lam(
    params: List(#(String, Bool, Term)),  // name, is_implicit, type_annotation
    body: Term,
    span: Span,
  )
  
  // UPDATED: App with implicit args
  App(
    func: Term,
    args: List(#(Term, Bool)),  // term, is_implicit
    span: Span,
  )
  
  // ... rest unchanged
}
```

**Migration**:
- Existing code: `Lam(name, body, span)` → `Lam([#(name, false, Hole)], body, span)`
- Existing code: `App(func, arg, span)` → `App(func, [#(arg, false)], span)`

**Tests**: `test/core/core_test.gleam`
- [ ] Create Lam with implicit param
- [ ] Create App with implicit arg
- [ ] Backward compatibility (implicit = false)

#### Day 3: Update Type AST

**File**: `src/core/core.gleam`

```gleam
pub type Type {
  // ... existing
  Var(String)
  Fn(List(Type), Type)
  
  // NEW: Polymorphic type
  Forall(List(String), Type)  // ∀a. a → a
}
```

**Tests**:
- [ ] Create Forall type
- [ ] Forall with multiple params
- [ ] Nested Forall

#### Day 4-5: Update All Pattern Matches

Use compiler errors as guide to update all case expressions.

**Files to update**:
- `src/core/core.gleam` (all functions)
- `src/core/syntax.gleam` (format)
- `src/core/error_formatter.gleam`

**Tests**:
- [ ] All existing tests pass
- [ ] No pattern match warnings

**Deliverable**: ✅ Core AST supports implicit arguments

---

### Phase 2: Type Inference with Forall (1-2 weeks)

**Goal**: Instantiate polymorphic functions during inference

#### Day 1-2: Create Holes for Implicit Params

**File**: `src/core/core.gleam` (infer function)

```gleam
fn create_holes(
  params: List(String),
  state: State,
) -> #(List(Term), State) {
  // Create a Hole term for each implicit param
  list.fold(params, #([], state), fn(acc, param_name) {
    let #(holes, state1) = acc
    let hole = Hole(fresh_unification_var(), span)
    (#([hole, ..holes], state1))
  })
}

fn substitute(
  term: Term,
  params: List(String),
  values: List(Term),
) -> Term {
  // Substitute params with values in term
  // Similar to beta reduction
}
```

**Tests**: `test/core/infer_test.gleam`
- [ ] Create holes for single param
- [ ] Create holes for multiple params
- [ ] Substitute preserves structure

#### Day 3-4: Instantiate Forall During Application

**File**: `src/core/core.gleam` (infer function)

```gleam
pub fn infer(state: State, term: Term) -> #(InferResult, State) {
  case term {
    App(func, args, span) => {
      let #(func_result, state1) = infer(state, func)
      
      case func_result.typ {
        Forall(params, body_ty) => {
          // Function has implicit params - instantiate them
          let #(holes, state2) = create_holes(params, state1)
          let instantiated_term = substitute(func_result.term, params, holes)
          let instantiated_ty = substitute_type(body_ty, params, holes)
          
          // Apply with explicit args
          apply(instantiated_term, args, instantiated_ty, span, state2)
        }
        
        _ => {
          // Normal application (no Forall)
          apply(func_result.term, args, func_result.typ, span, state1)
        }
      }
    }
    
    // ... rest unchanged
  }
}

fn apply(
  func: Term,
  args: List(#(Term, Bool)),
  func_ty: Type,
  span: Span,
  state: State,
) -> #(InferResult, State) {
  // Standard function application logic
  // Check arg types match param types
  // Return result type
}
```

**Tests**:
- [ ] Infer application of polymorphic function
- [ ] Infer application of monomorphic function
- [ ] Multiple implicit params

#### Day 5: Unify Holes with Concrete Types

**File**: `src/core/core.gleam` (unification)

```gleam
fn unify(t1: Type, t2: Type, state: State) -> Result(State, Error) {
  case #(t1, t2) {
    #(Hole(id, _), concrete) | #(concrete, Hole(id, _)) => {
      // Bind hole to concrete type
      case occurs_check(id, concrete) {
        True -> Error(InfiniteType)
        False -> Ok(bind_hole(id, concrete, state))
      }
    }
    
    #(Forall(params1, body1), Forall(params2, body2)) => {
      // Unify polymorphic types
      // Alpha-rename to avoid capture
    }
    
    // ... existing cases
  }
}
```

**Tests**:
- [ ] Unify hole with I32
- [ ] Unify hole with function type
- [ ] Occurs check prevents infinite types

**Deliverable**: ✅ Type inference instantiates polymorphic functions

---

### Phase 3: Evaluation with Erasure (1 week)

**Goal**: Evaluate implicit arguments but erase at runtime

#### Day 1-2: Update Evaluation

**File**: `src/core/core.gleam` (eval function)

```gleam
pub fn eval(ffi: Ffi, env: Env, term: Term) -> Value {
  case term {
    App(func, args, span) => {
      // Separate implicit and explicit args
      let implicit_args = list.filter_map(args, fn(#(arg, is_implicit)) {
        case is_implicit {
          True -> Some(eval(ffi, env, arg))
          False -> None
        }
      })
      let explicit_args = list.filter_map(args, fn(#(arg, is_implicit)) {
        case is_implicit {
          True -> None
          False -> Some(eval(ffi, env, arg))
        }
      })
      
      let func_val = eval(ffi, env, func)
      
      case func_val {
        VLam(params, body, closure_env) => {
          // Match params with args (implicit first, then explicit)
          let extended_env = extend_env(
            closure_env,
            params,
            list.append(implicit_args, explicit_args),
          )
          eval(ffi, extended_env, body)
        }
        
        _ => Error(RuntimeError("Not a function"))
      }
    }
    
    Lam(params, body, span) => {
      // Capture environment with param info
      VLam(params, body, env)
    }
    
    // ... rest unchanged
  }
}
```

**Key Insight**: Implicit args are evaluated (for side effects) but not passed to body.

**Tests**: `test/core/eval_test.gleam`
- [ ] Evaluate App with implicit arg
- [ ] Implicit arg erased at runtime
- [ ] Nested implicit apps

#### Day 3: Type Reflection

**File**: `src/core/core.gleam`

```gleam
// typeof example
%let typeof = %fn<a>(x) -> a

// During evaluation:
// typeof<?> (42)  -- Hole created
// typeof<I32>(42) -- Hole filled with I32
// Returns: %I32
```

**Tests**:
- [ ] typeof(42) returns I32
- [ ] typeof("hello") returns String
- [ ] typeof in nested context

#### Day 4-5: Integration Tests

**File**: `test/core/overloading_test.gleam`

```gleam
pub fn neg_overloading_test() {
  let source = "
    %let (-) = %fn<ty>(x) -> %match ty {
      | %I32 -> %i32_neg(x)
      | %F64 -> %f64_neg(x)
    }
    (-)(42)
  "
  
  let result = run(source)
  result |> should.equal(-42)
}

pub fn typeof_reflection_test() {
  let source = "
    %let typeof = %fn<a>(x) -> a
    typeof(42)
  "
  
  let result = run(source)
  result |> should.equal(%I32)  // Type value
}
```

**Deliverable**: ✅ Evaluation erases implicit arguments

---

### Phase 4: Tao Desugaring (1 week)

**Goal**: Desugar Tao to Core with normal applications

#### Day 1-2: Parse Overloaded Functions

**File**: `src/tao/syntax.gleam`

```gleam
// Grammar for overloaded function
// fn (-)(x: I32) -> I32 { ... }
rule("OverloadedFn", [
  alt(
    seq([
      keyword_pattern("fn"),
      ref("OperatorName"),  // (-), (+), etc.
      token_pattern("LParen"),
      ref("Params"),
      token_pattern("RParen"),
      token_pattern("Arrow"),
      ref("Type"),
      ref("Body"),
    ]),
    make_overloaded_fn,
  ),
])
```

**Tests**: `test/tao/syntax_test.gleam`
- [ ] Parse overloaded negation
- [ ] Parse overloaded addition
- [ ] Parse with type annotation

#### Day 3-4: Desugar to Core

**File**: `src/tao/desugar.gleam`

```gleam
pub fn desugar_overloaded_fn(fn_def) -> Term {
  // fn (-)(x: I32) -> I32 { %i32_neg(x) }
  // becomes:
  // %fn<ty>(x) -> %match ty { | %I32 -> %i32_neg(x) }
  
  let implicit_ty_param = #("ty", true, Hole)
  
  let match_arms = list.map(fn_def.overloads, fn(overload) {
    MatchArm(
      pattern: type_to_pattern(overload.param_types),
      body: desugar_expr(overload.body),
    )
  })
  
  Term(
    Lam(
      [implicit_ty_param, #("x", false, Hole)],
      Match(Var("ty"), match_arms, span),
      span,
    ),
    span,
  )
}

pub fn desugar_binop(left, op, right, span) -> Term {
  // (-)(1) desugars to normal App (no implicit info)
  // Core inference will upgrade to implicit app
  Term(
    App(
      Var(op),
      [#(desugar_expr(left), false), #(desugar_expr(right), false)],
      span,
    ),
    span,
  )
}
```

**Key**: Desugar to **normal App**, let Core inference upgrade to implicit.

**Tests**:
- [ ] Desugar overloaded negation
- [ ] Desugar operator usage
- [ ] Desugar preserves structure

#### Day 5: End-to-End Tests

**File**: `test/tao/overloading_test.gleam`

```gleam
pub fn neg_i32_test() {
  let source = "
    fn (-)(x: I32) -> I32 { %i32_neg(x) }
    (-)(42)
  "
  
  let result = run_tao(source)
  result |> should.equal(-42)
}

pub fn neg_f32_test() {
  let source = "
    fn (-)(x: F32) -> F32 { %f32_neg(x) }
    (-)(3.14)
  "
  
  let result = run_tao(source)
  result |> should.equal(-3.14)
}
```

**Deliverable**: ✅ Tao desugars to Core correctly

---

### Phase 5: Formatter + Syntax (1 week)

**Goal**: Print implicit arguments with `<ty>` syntax

#### Day 1-2: Update Formatter

**File**: `src/core/syntax.gleam`

```gleam
pub fn format(term: Term) -> String {
  case term {
    Lam(params, body, _span) => {
      let implicit_params = list.filter_map(params, fn(#(name, is_implicit, _)) {
        case is_implicit {
          True -> Some(name)
          False -> None
        }
      })
      let explicit_params = list.filter_map(params, fn(#(name, is_implicit, _)) {
        case is_implicit {
          True -> None
          False -> Some(name)
        }
      })
      
      let implicit_str = case implicit_params {
        [] -> ""
        _ -> "<" <> string_join(implicit_params, ", ") <> ">"
      }
      let explicit_str = string_join(explicit_params, ", ")
      
      "%fn" <> implicit_str <> "(" <> explicit_str <> ") -> " <> format(body)
    }
    
    App(func, args, _span) => {
      let implicit_args = list.filter_map(args, fn(#(arg, is_implicit)) {
        case is_implicit {
          True -> Some(format(arg))
          False -> None
        }
      })
      let explicit_args = list.filter_map(args, fn(#(arg, is_implicit)) {
        case is_implicit {
          True -> None
          False -> Some(format(arg))
        }
      })
      
      let implicit_str = case implicit_args {
        [] -> ""
        _ -> "<" <> string_join(implicit_args, ", ") <> ">"
      }
      
      format(func) <> implicit_str <> "(" <> string_join(explicit_args, ", ") <> ")"
    }
    
    // ... rest unchanged
  }
}
```

**Tests**:
- [ ] Format Lam with implicit param
- [ ] Format App with implicit arg
- [ ] Format mixed implicit/explicit

#### Day 3: Update Parser (Optional)

For testing, may want to parse Core with implicit syntax:

```gleam
// Parse %fn<a>(x) -> body
rule("Lambda", [
  alt(
    seq([
      keyword_pattern("%fn"),
      opt(implicit_params),  // <a, b>
      token_pattern("LParen"),
      explicit_params,
      token_pattern("RParen"),
      ref("Expr"),
    ]),
    make_lambda,
  ),
])
```

**Tests**:
- [ ] Parse %fn<a>(x) -> x
- [ ] Parse f<T>(x, y)

#### Day 4-5: Documentation + Examples

**File**: `docs/tao-overloading.md`

- [ ] User guide
- [ ] Syntax reference
- [ ] Examples

**Examples**: `examples/tao/overloading/`
- [ ] `01_negation.tao` - Unary negation
- [ ] `02_addition.tao` - Overloaded addition
- [ ] `03_typeof.tao` - Type reflection

**Deliverable**: ✅ Formatter prints implicit syntax

---

### Phase 6: Polish (1 week)

#### Day 1-2: Error Messages

**File**: `src/core/error_formatter.gleam`

```gleam
pub fn type_error_to_diagnostic(error, source, file) -> Diagnostic {
  case error {
    CannotInferImplicit(param_name, span) => {
      // "Cannot infer type parameter 'a'"
      // "Provide explicit type annotation"
    }
    
    AmbiguousImplicit(param_name, candidates, span) => {
      // "Ambiguous type for parameter 'a'"
      // "Candidates: I32, F32"
    }
    
    // ...
  }
}
```

**Tests**:
- [ ] Format cannot infer error
- [ ] Format ambiguous error
- [ ] Include helpful suggestions

#### Day 3: Performance Optimization

- [ ] Profile hole creation
- [ ] Cache substitution results
- [ ] Optimize common cases

#### Day 4-5: Bug Fixes + Testing

- [ ] Fix issues from integration testing
- [ ] Add edge case tests
- [ ] Verify all examples work

**Deliverable**: ✅ Production-ready overloading

---

## Test Plan

### Unit Tests

| Module | Tests | Focus |
|--------|-------|-------|
| `core.gleam` (Term) | 20+ | Implicit Lam/App creation |
| `core.gleam` (Type) | 15+ | Forall type operations |
| `core.gleam` (infer) | 40+ | Forall instantiation, hole filling |
| `core.gleam` (eval) | 25+ | Implicit arg erasure |
| `syntax.gleam` | 20+ | Format/parse implicit syntax |
| `desugar.gleam` | 20+ | Tao → Core desugaring |

### Integration Tests

| Test | Description |
|------|-------------|
| `neg_i32` | Unary negation for I32 |
| `neg_f32` | Unary negation for F32 |
| `add_overload` | Overloaded addition |
| `typeof_i32` | Type reflection for I32 |
| `typeof_list` | Type reflection for List |
| `higher_order` | Map with overloaded function |
| `cross_module` | Overloads from multiple modules |

### Golden File Tests

| File | Description |
|------|-------------|
| `examples/tao/overloading/01_negation.tao` | Negation example |
| `examples/tao/overloading/02_addition.tao` | Addition example |
| `examples/tao/overloading/03_typeof.tao` | Type reflection |

---

## Success Criteria

Overloading is complete when:

- ✅ Core supports implicit arguments in Lam/App
- ✅ Forall types instantiate during inference
- ✅ Implicit args erased at runtime
- ✅ Tao desugars to normal App
- ✅ Type inference upgrades to implicit App
- ✅ Type reflection works (typeof)
- ✅ 150+ tests passing
- ✅ 5+ working examples
- ✅ Clear error messages

---

## Timeline Summary

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| **Phase 1**: Core AST | 1 week | Implicit Lam/App, Forall Type |
| **Phase 2**: Inference | 1-2 weeks | Forall instantiation, hole filling |
| **Phase 3**: Evaluation | 1 week | Implicit arg erasure |
| **Phase 4**: Desugaring | 1 week | Tao → Core with normal App |
| **Phase 5**: Formatter | 1 week | `<ty>` syntax printing |
| **Phase 6**: Polish | 1 week | Docs, examples, tests |

**Total**: 6-7 weeks

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Inference complexity | High | Start simple, add features incrementally |
| Backward compatibility | Medium | Support both old/new syntax during transition |
| Performance (holes) | Low | Profile and optimize if needed |
| Match arm implicit params | Medium | Handle in Phase 2 extension |

---

## Related Documents

- **[10-overloading-design.md](./10-overloading-design.md)** - Design specification
- **[../core/15-type-application.md](../core/15-type-application.md)** - Superseded by this plan
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)

---

**This revised plan leverages implicit arguments for a cleaner, more unified implementation.** 🚀
