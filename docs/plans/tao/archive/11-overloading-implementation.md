# Tao Overloading Implementation Plan (v3)

> **Goal**: Implement function and operator overloading through implicit arguments with single explicit argument
> **Status**: 📋 **Planned** - v3 with recursive implicit handling
> **Target**: 6-7 weeks

---

## Design Summary (v3)

**Key Changes**:

1. **Single Explicit Argument**: `param: #(String, Type)` and `arg: Term`
2. **Recursive Implicit Handling**: Peel off implicit args until base case
3. **Multi-Arg via Records/Currying**: Record for overloading, curried for HOFs
4. **Single Base Case**: `App(func, [], arg)` - same as current implementation

---

## Implementation Phases

### Phase 1: Core AST Extensions (1 week)

**Goal**: Update Core terms to single explicit argument

#### Day 1-2: Update Term AST

**File**: `src/core/core.gleam`

```gleam
pub type Term {
  // ... existing constructors
  
  // UPDATED: Single explicit param
  Lam(
    implicit: List(String),
    param: #(String, Type),
    body: Term,
    span: Span,
  )
  
  // UPDATED: Single explicit arg
  App(
    func: Term,
    implicit: List(Term),
    arg: Term,
    span: Span,
  )
  
  // ... rest unchanged
}
```

**Migration**:
- Existing code: `Lam(name, body, span)` → `Lam([], #(name, Hole), body, span)`
- Existing code: `App(func, [arg], span)` → `App(func, [], arg, span)`

**Tests**: `test/core/core_test.gleam`
- [ ] Create Lam with implicit params
- [ ] Create Lam without implicit params
- [ ] Create App with implicit args
- [ ] Create App without implicit args
- [ ] Backward compatibility (empty implicit list)

#### Day 3: Update Type AST

**File**: `src/core/core.gleam`

```gleam
pub type Type {
  // ... existing
  Var(String)
  Fn(Type, Type)  // UPDATED: Single param type
  
  // NEW: Polymorphic type
  Forall(List(String), Type)  // ∀a. a → a
  
  // Keep for record support
  Record(List(#(String, Type)))
}
```

**Note**: `Fn` now takes single param type (record or curried).

**Tests**:
- [ ] Create Forall type
- [ ] Forall with multiple params
- [ ] Record type for multi-arg

#### Day 4-5: Update All Pattern Matches

Use compiler errors as guide to update all case expressions.

**Files to update**:
- `src/core/core.gleam` (all functions)
- `src/core/syntax.gleam` (format)
- `src/core/error_formatter.gleam`

**Tests**:
- [ ] All existing tests pass
- [ ] No pattern match warnings

**Deliverable**: ✅ Core AST supports single explicit argument

---

### Phase 2: Recursive Type Inference (1-2 weeks)

**Goal**: Instantiate polymorphic functions recursively

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
}
```

**Tests**: `test/core/infer_test.gleam`
- [ ] Create holes for single param
- [ ] Create holes for multiple params
- [ ] Substitute preserves structure

#### Day 3-4: Recursive Inference with Implicit Handling

**File**: `src/core/core.gleam` (infer function)

```gleam
pub fn infer(state: State, term: Term) -> #(InferResult, State) {
  case term {
    App(func, implicit, arg, span) => {
      let #(func_result, state1) = infer(state, func)
      let #(arg_result, state2) = infer(state1, arg)
      
      case func_result.typ {
        Forall(params, body_ty) => {
          // Function has implicit params - instantiate them
          let #(holes, state3) = create_holes(params, state2)
          let instantiated_term = substitute(func_result.term, params, holes)
          let instantiated_ty = substitute_type(body_ty, params, holes)
          
          // Recurse with instantiated function
          infer(state3, App(instantiated_term, implicit, arg, span))
        }
        
        Fn(param_ty, return_ty) => {
          // Base case: check arg matches param type
          case unify(arg_result.typ, param_ty, state2) {
            Ok(state4) => #(InferResult(return_ty, span), state4)
            Error(e) => #(InferResult(Error(e), span), state2)
          }
        }
      }
    }
    
    // ... rest unchanged
  }
}
```

**Tests**:
- [ ] Infer application of polymorphic function
- [ ] Infer application of monomorphic function
- [ ] Multiple implicit params (recursive)
- [ ] Record arg type checking

#### Day 5: Unify Holes with Concrete Types

**File**: `src/core/core.gleam` (unification)

```gleam
fn unify(t1: Type, t2: Type, state: State) -> Result(State, Error) {
  case #(t1, t2) {
    #(Hole(id, _), concrete) | #(concrete, Hole(id, _)) => {
      case occurs_check(id, concrete) {
        True -> Error(InfiniteType)
        False -> Ok(bind_hole(id, concrete, state))
      }
    }
    
    #(Forall(params1, body1), Forall(params2, body2)) => {
      // Unify polymorphic types
    }
    
    #(Record(fields1), Record(fields2)) => {
      // Unify record types
    }
    
    // ... existing cases
  }
}
```

**Tests**:
- [ ] Unify hole with I32
- [ ] Unify hole with record type
- [ ] Occurs check prevents infinite types

**Deliverable**: ✅ Recursive type inference working

---

### Phase 3: Recursive Evaluation (1 week)

**Goal**: Evaluate with recursive implicit handling

#### Day 1-2: Recursive Evaluation

**File**: `src/core/core.gleam` (eval function)

```gleam
pub fn eval(ffi: Ffi, env: Env, term: Term) -> Value {
  case term {
    App(func, [], arg, span) => {
      // BASE CASE: No implicit args
      let func_val = eval(ffi, env, func)
      let arg_val = eval(ffi, env, arg)
      
      case func_val {
        VLam(implicit, param_name, body, closure_env) => {
          let extended_env = extend_env(closure_env, [param_name], [arg_val])
          eval(ffi, extended_env, body)
        }
        _ => Error(RuntimeError("Not a function"))
      }
    }
    
    App(func, [implicit, ..rest], arg, span) => {
      // RECURSIVE CASE: Peel off one implicit arg
      let _implicit_val = eval(ffi, env, implicit)  // Evaluate but erase
      let func_val = eval(ffi, env, func)
      
      case func_val {
        VLam(implicit_params, param_name, body, closure_env) => {
          // Instantiate function with implicit, recurse
          let instantiated = instantiate(func_val, _implicit_val)
          eval(ffi, env, App(instantiated, rest, arg, span))
        }
      }
    }
    
    Lam(implicit, param, body, span) => {
      VLam(implicit, param, body, env)
    }
    
    // ... rest unchanged
  }
}
```

**Key Insight**: Recursive case peels off implicit args until base case.

**Tests**: `test/core/eval_test.gleam`
- [ ] Evaluate App with no implicit (base case)
- [ ] Evaluate App with one implicit
- [ ] Evaluate App with multiple implicit (recursive)
- [ ] Implicit arg erased at runtime

#### Day 3: Type Reflection

**File**: `src/core/core.gleam`

```gleam
// typeof example
%let typeof = %fn<T>(x) -> T

// During evaluation:
// typeof<?>(42)  -- Hole created
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

pub fn record_arg_test() {
  let source = "
    %let (+) = %fn<ty>(args) -> %match ty {
      | {x: %I32, y: %I32} -> %call i32_add(args.x, args.y)
    }
    (+)({x: 1, y: 2})
  "
  
  let result = run(source)
  result |> should.equal(3)
}

pub fn curried_function_test() {
  let source = "
    %let add = %fn(x) -> %fn(y) -> %call i32_add(x, y)
    %call (%call add(1))(2)
  "
  
  let result = run(source)
  result |> should.equal(3)
}
```

**Deliverable**: ✅ Recursive evaluation working

---

### Phase 4: Tao Desugaring (1 week)

**Goal**: Desugar Tao to Core with single explicit arg

#### Day 1-2: Parse Overloaded Functions

**File**: `src/tao/syntax.gleam`

```gleam
// Grammar for overloaded function with record arg
// fn (+)(x: I32, y: I32) -> I32 { ... }
rule("OverloadedFn", [
  alt(
    seq([
      keyword_pattern("fn"),
      ref("OperatorName"),
      token_pattern("LParen"),
      ref("Params"),  // Multiple params become record
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
- [ ] Parse overloaded negation (single param)
- [ ] Parse overloaded addition (multiple params → record)
- [ ] Parse curried function

#### Day 3-4: Desugar to Core

**File**: `src/tao/desugar.gleam`

```gleam
pub fn desugar_overloaded_fn(fn_def) -> Term {
  // fn (-)(x: I32) -> I32 { %i32_neg(x) }
  // becomes: %fn<ty>(x) -> %match ty { | %I32 -> %i32_neg(x) }
  
  let implicit_ty_param = ["ty"]
  
  let match_arms = list.map(fn_def.overloads, fn(overload) {
    MatchArm(
      pattern: type_to_pattern(overload.param_types),
      body: desugar_expr(overload.body),
    )
  })
  
  // Single param (or record for multi-param)
  let param = case fn_def.params {
    [single_param] => #("x", Hole),  // Single param
    multiple_params => {
      // Multiple params become record
      let record_fields = list.map(multiple_params, fn(p) {
        #(p.name, Hole)
      })
      #("args", RecordType(record_fields))
    }
  }
  
  Term(
    Lam(
      implicit: implicit_ty_param,
      param: param,
      body: Match(Var("ty"), match_arms, span),
      span,
    ),
    span,
  )
}

pub fn desugar_binop(left, op, right, span) -> Term {
  // (-)(1) desugars to App with empty implicit
  // Core inference will fill implicit args
  
  // For binary op, create record arg
  let record_arg = Record([("x", desugar_expr(left)), ("y", desugar_expr(right))])
  
  Term(
    App(
      Var(op),
      [],  // Empty implicit - inference will fill
      record_arg,
      span,
    ),
    span,
  )
}

pub fn desugar_regular_fn(fn_def) -> Term {
  // fn double(x: I32) -> I32 { x * 2 }
  // becomes: %fn(x) -> %call i32_mul(x, 2)
  
  Term(
    Lam(
      implicit: [],  // No implicit params
      param: #("x", Hole),
      body: desugar_expr(fn_def.body),
      span,
    ),
    span,
  )
}
```

**Key**: Single explicit arg, empty implicit list (inference fills).

**Tests**:
- [ ] Desugar overloaded negation (single arg)
- [ ] Desugar overloaded addition (record arg)
- [ ] Desugar regular function
- [ ] Desugar curried function

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

pub fn add_record_test() {
  let source = "
    fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
    1 + 2
  "
  
  let result = run_tao(source)
  result |> should.equal(3)
}

pub fn curried_test() {
  let source = "
    fn add(x: I32) -> fn(y: I32) -> I32 { x + y }
    add(1)(2)
  "
  
  let result = run_tao(source)
  result |> should.equal(3)
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
    Lam(implicit, param, body, _span) => {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string_join(implicit, ", ") <> ">"
      }
      let param_str = format_param(param)
      
      "%fn" <> implicit_str <> "(" <> param_str <> ") -> " <> format(body)
    }
    
    App(func, implicit, arg, _span) => {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string_join(list.map(implicit, format), ", ") <> ">"
      }
      
      format(func) <> implicit_str <> "(" <> format(arg) <> ")"
    }
    
    // ... rest unchanged
  }
}

fn format_param(param: #(String, Type)) -> String {
  let #(name, typ) = param
  name <> ": " <> format_type(typ)
}
```

**Tests**:
- [ ] Format Lam with implicit params
- [ ] Format Lam without implicit params
- [ ] Format App with implicit args
- [ ] Format record arg
- [ ] Format curried function

#### Day 3: Update Parser (Optional)

For testing, may want to parse Core with implicit syntax:

```gleam
// Parse %fn<a>(x: I32) -> body
rule("Lambda", [
  alt(
    seq([
      keyword_pattern("%fn"),
      opt(implicit_params),  // <a, b>
      token_pattern("LParen"),
      single_param,          // x: I32 (or record)
      token_pattern("RParen"),
      ref("Expr"),
    ]),
    make_lambda,
  ),
])
```

**Tests**:
- [ ] Parse %fn<a>(x) -> x
- [ ] Parse f<T>({x: 1, y: 2})

#### Day 4-5: Documentation + Examples

**File**: `docs/tao-overloading.md`

- [ ] User guide
- [ ] Syntax reference
- [ ] Examples

**Examples**: `examples/tao/overloading/`
- [ ] `01_negation.tao` - Unary negation (single arg)
- [ ] `02_addition.tao` - Overloaded addition (record arg)
- [ ] `03_typeof.tao` - Type reflection
- [ ] `04_curried.tao` - Curried function

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
    }
    
    RecordFieldMismatch(field, expected, actual, span) => {
      // "Field 'x' has type F32, expected I32"
    }
    
    // ...
  }
}
```

**Tests**:
- [ ] Format cannot infer error
- [ ] Format record field mismatch
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
| `core.gleam` (Term) | 25+ | Single arg Lam/App creation |
| `core.gleam` (Type) | 15+ | Forall, Record types |
| `core.gleam` (infer) | 40+ | Recursive implicit instantiation |
| `core.gleam` (eval) | 25+ | Recursive evaluation, erasure |
| `syntax.gleam` | 25+ | Format/parse implicit syntax |
| `desugar.gleam` | 20+ | Tao → Core with single arg |

### Integration Tests

| Test | Description |
|------|-------------|
| `neg_i32` | Unary negation (single arg) |
| `neg_f32` | Unary negation for F32 |
| `add_record` | Overloaded addition (record arg) |
| `curried_add` | Curried addition |
| `typeof_i32` | Type reflection for I32 |
| `higher_order` | Map with overloaded function |
| `cross_module` | Overloads from multiple modules |

### Golden File Tests

| File | Description |
|------|-------------|
| `examples/tao/overloading/01_negation.tao` | Single arg |
| `examples/tao/overloading/02_addition.tao` | Record arg |
| `examples/tao/overloading/03_typeof.tao` | Type reflection |
| `examples/tao/overloading/04_curried.tao` | Curried |

---

## Success Criteria

Overloading is complete when:

- ✅ Core supports single explicit argument
- ✅ Recursive implicit handling works
- ✅ Forall types instantiate during inference
- ✅ Implicit args erased at runtime
- ✅ Record args for multi-param overloading
- ✅ Curried functions work
- ✅ Type reflection works (typeof)
- ✅ 150+ tests passing
- ✅ 5+ working examples
- ✅ Clear error messages

---

## Timeline Summary

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| **Phase 1**: Core AST | 1 week | Single arg Lam/App |
| **Phase 2**: Inference | 1-2 weeks | Recursive implicit handling |
| **Phase 3**: Evaluation | 1 week | Recursive evaluation |
| **Phase 4**: Desugaring | 1 week | Tao → Core with single arg |
| **Phase 5**: Formatter | 1 week | `<ty>` syntax printing |
| **Phase 6**: Polish | 1 week | Docs, examples, tests |

**Total**: 6-7 weeks

---

## Benefits of v3 Design

| Benefit | Description |
|---------|-------------|
| **Single Base Case** | `App(func, [], arg)` - same as current |
| **Recursive Handling** | Peel off implicit args one by one |
| **Cleaner Code** | No list zipping, simpler pattern matching |
| **Record or Curried** | Flexible multi-arg support |
| **Easier Testing** | One case to test, not multiple arities |

---

## Related Documents

- **[10-overloading-design.md](./10-overloading-design.md)** - Design specification (v3)
- **[../core/15-type-application.md](../core/15-type-application.md)** - Superseded
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)

---

**This v3 design with single explicit argument provides the cleanest recursive implementation.** 🚀
