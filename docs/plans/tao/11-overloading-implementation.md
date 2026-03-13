# Tao Overloading Implementation Plan

> **Goal**: Implement function and operator overloading through dependent types
> **Status**: 📋 **Planned** - After MVP complete
> **Target**: 5-6 weeks

---

## Prerequisites

- ✅ Tao MVP complete (lexer, parser, desugarer, CLI)
- ✅ Basic type checking working
- ⏳ Core type application support (Phase 1)

---

## Phase 1: Core Extensions (1 week)

### Goal: Add type application support to Core

#### Day 1-2: Add TypeApp Constructor

**File**: `src/core/core.gleam`

```gleam
pub type Term {
  // ... existing constructors
  TypeApp(term: Term, types: List(Type), span: Span)  // NEW
}

pub type Value {
  // ... existing constructors
  VTypeApp(value: Value, types: List(Type))  // NEW (or handle in Call)
}
```

**Tests**: `test/core/core_test.gleam`
- [ ] Create TypeApp term
- [ ] TypeApp preserves span
- [ ] TypeApp serializes correctly

#### Day 3: TypeApp Evaluation

**File**: `src/core/core.gleam` (eval function)

```gleam
pub fn eval(ffi, env, term) -> Value {
  case term {
    TypeApp(func, _types, _) -> {
      // Types are erased at runtime
      // Just evaluate the function
      eval(ffi, env, func)
    }
    // ...
  }
}
```

**Tests**: `test/core/eval_test.gleam`
- [ ] TypeApp evaluates to function value
- [ ] Type arguments are erased
- [ ] Nested TypeApp works

#### Day 4: TypeApp Type Checking

**File**: `src/core/core.gleam` (infer function)

```gleam
pub fn infer(state, term) -> #(InferResult, State) {
  case term {
    TypeApp(func, types, span) -> {
      let #(func_result, state1) = infer(state, func)
      // Check that func accepts these type arguments
      // Return instantiated type
      // ...
    }
    // ...
  }
}
```

**Tests**: `test/core/infer_test.gleam`
- [ ] TypeApp type checks correctly
- [ ] Type mismatch detected
- [ ] Polymorphic function application

#### Day 5: Formatter + Polish

**File**: `src/core/syntax.gleam`

```gleam
pub fn format(term) -> String {
  case term {
    TypeApp(func, types, _) -> {
      format(func) <> "(" <> string_join(list.map(types, format_type), ", ") <> ")"
    }
    // ...
  }
}
```

**Tests**: `test/core/syntax_test.gleam`
- [ ] Format TypeApp correctly
- [ ] Round-trip test

**Deliverable**: ✅ Core supports type application

---

## Phase 2: Overload Sets (1 week)

### Goal: Data structures for overload resolution

#### Day 1-2: OverloadSet Data Structure

**File**: `src/tao/overloading/overload_set.gleam`

```gleam
pub type OverloadSet {
  OverloadSet(
    name: String,
    overloads: List(Overload),
  )
}

pub type Overload {
  Overload(
    param_types: List(Type),
    return_type: Type,
    body: Term,  // Core term
    span: Span,
  )
}

pub type Type {
  // Reuse Core Type or define Tao Type
  TInt,
  TFloat,
  TVar(String),
  TApp(String, List(Type)),
  // ...
}
```

**Tests**: `test/tao/overloading/overload_set_test.gleam`
- [ ] Create OverloadSet
- [ ] Add overload to set
- [ ] Lookup by name

#### Day 3: Overload Environment

**File**: `src/tao/overloading/environment.gleam`

```gleam
pub type OverloadEnv {
  OverloadEnv(
    overloads: Dict(String, OverloadSet),
    imports: List(String),
  )
}

pub fn initial_env() -> OverloadEnv { ... }
pub fn add_overload(env, name, overload) -> OverloadEnv { ... }
pub fn get_overloads(env, name) -> Result(OverloadSet, Nil) { ... }
pub fn merge_env(env1, env2) -> OverloadEnv { ... }
```

**Tests**: `test/tao/overloading/environment_test.gleam`
- [ ] Create initial environment
- [ ] Add overloads
- [ ] Merge environments (cross-module)

#### Day 4-5: Cross-Module Merging

**File**: `src/tao/overloading/environment.gleam`

```gleam
pub fn merge_env(env1, env2) -> OverloadEnv {
  // Combine overload sets from both environments
  // Handle conflicts (same signature = error or replace)
}
```

**Tests**: `test/tao/overloading/merge_test.gleam`
- [ ] Merge two environments
- [ ] Detect duplicate overloads
- [ ] Import from multiple modules

**Deliverable**: ✅ Overload sets and environment working

---

## Phase 3: Overload Resolution (1-2 weeks)

### Goal: Resolve overloads based on types

#### Day 1-2: Resolution Algorithm

**File**: `src/tao/overloading/resolution.gleam`

```gleam
pub type ResolutionResult {
  Resolved(overload: Overload, type_args: List(Type))
  NoMatch(available: List(Overload), arg_types: List(Type))
  Ambiguous(matches: List(Overload))
}

pub fn resolve(
  overloads: OverloadSet,
  arg_types: List(Type),
) -> ResolutionResult {
  // Filter overloads by parameter types
  let matches = list.filter(overloads.overloads, fn(overload) {
    types_match(overload.param_types, arg_types)
  })
  
  case matches {
    [match] -> Resolved(match, arg_types)
    [] -> NoMatch(overloads.overloads, arg_types)
    multiple -> Ambiguous(multiple)
  }
}

fn types_match(params: List(Type), args: List(Type)) -> Bool {
  // Check if parameter types match argument types
  // May need unification for polymorphic overloads
}
```

**Tests**: `test/tao/overloading/resolution_test.gleam`
- [ ] Resolve single match
- [ ] No match error
- [ ] Ambiguous error
- [ ] Multiple overloads

#### Day 3-4: Type-Directed Desugaring

**File**: `src/tao/type_check.gleam` (NEW)

```gleam
pub type InferResult {
  InferResult(term: Term, typ: Type)
}

pub fn infer(expr: Expr, env: OverloadEnv) -> Result(#(Term, Type), Error) {
  case expr {
    BinOp(op, left, right) -> {
      let #(left_term, left_ty) = infer(left, env)
      let #(right_term, right_ty) = infer(right, env)
      
      case resolve_operator(op, [left_ty, right_ty], env) {
        Resolved(overload, type_args) -> {
          let term = make_type_app(overload, type_args, [left_term, right_term])
          Ok(#(term, overload.return_type))
        }
        NoMatch(available, arg_types) -> {
          Error(NoMatchingOverload(op, available, arg_types))
        }
        Ambiguous(matches) -> {
          Error(AmbiguousOverload(op, matches))
        }
      }
    }
    // ...
  }
}
```

**Tests**: `test/tao/type_check_test.gleam`
- [ ] Infer type of overloaded operator
- [ ] Error on no match
- [ ] Error on ambiguous

#### Day 5: Error Reporting

**File**: `src/tao/error.gleam` (NEW)

```gleam
pub type Error {
  NoMatchingOverload(
    name: String,
    available: List(Overload),
    arg_types: List(Type),
    span: Span,
  )
  AmbiguousOverload(
    name: String,
    matches: List(Overload),
    span: Span,
  )
  // ...
}
```

**File**: `src/syntax/error_reporter.gleam` (extend)

```gleam
pub fn tao_error_to_diagnostic(error, source, file) -> Diagnostic {
  case error {
    NoMatchingOverload(name, available, arg_types, span) -> {
      // Format: "no matching overload for '+(I32, String)'"
      // List available overloads
    }
    AmbiguousOverload(name, matches, span) -> {
      // Format: "ambiguous overload for '+', candidates:"
      // List matching overloads
    }
  }
}
```

**Tests**: `test/tao/error_test.gleam`
- [ ] Format no-match error
- [ ] Format ambiguous error
- [ ] Include helpful suggestions

**Deliverable**: ✅ Overload resolution working with good errors

---

## Phase 4: Tao Integration (1 week)

### Goal: Wire overloading into Tao pipeline

#### Day 1: Parse Overloaded Functions

**File**: `src/tao/syntax.gleam`

```gleam
// Extend grammar to support overloaded function definitions
// fn (+)(x: I32, y: I32) -> I32 { ... }

pub type MvpExpr {
  // ... existing
  OverloadedFn(
    name: String,
    params: List(Param),
    return_type: Type,
    body: MvpExpr,
    span: Span,
  )
}
```

**Tests**: `test/tao/syntax_test.gleam`
- [ ] Parse overloaded function
- [ ] Parse operator definition
- [ ] Parse type annotation

#### Day 2-3: Desugar Overloaded Functions

**File**: `src/tao/desugar.gleam`

```gleam
pub fn desugar_overloaded_fn(fn_def) -> Term {
  // Convert overloaded function to type-level function
  // fn (+)(x: I32, y: I32) -> I32 { ... }
  // becomes:
  // λ(ty) → match ty { | {x: I32, y: I32} → λ(args) → body }
  
  let match_arms = list.map(fn_def.overloads, fn(overload) {
    make_match_arm(overload)
  })
  
  Term(Lam("ty", Term(Match(...), span)), span)
}
```

**Tests**: `test/tao/desugar_test.gleam`
- [ ] Desugar single overload
- [ ] Desugar multiple overloads
- [ ] Desugar operator

#### Day 4: Desugar Operator Usage

**File**: `src/tao/desugar.gleam`

```gleam
pub fn desugar_binop(left, op, right, env) -> Term {
  // 1 + 2 becomes (+)(I32, I32)(1, 2)
  
  let left_term = desugar(left, env)
  let right_term = desugar(right, env)
  
  let left_ty = infer_type(left_term)
  let right_ty = infer_type(right_term)
  
  // Create type application
  Term(Call(
    Term(Call(Var(op), [TypeApp(left_ty)], span), span),
    [left_term, right_term],
  ), span)
}
```

**Tests**: `test/tao/desugar_test.gleam`
- [ ] Desugar I32 addition
- [ ] Desugar F32 addition
- [ ] Desugar nested operators

#### Day 5: End-to-End Tests

**File**: `test/tao/overloading_integration_test.gleam`

```gleam
pub fn overloaded_add_integration_test() {
  let source = "
    fn (+)(x: I32, y: I32) -> I32 { %i32_add(x, y) }
    fn (+)(x: F32, y: F32) -> F32 { %f32_add(x, y) }
    
    let result = 1 + 2
  "
  
  let result = run_tao(source)
  result |> should.equal(3)
}
```

**Examples**: `examples/tao/overloading/`
- [ ] `01_basic.tao` - Basic overloading
- [ ] `02_vector.tao` - Vector addition
- [ ] `03_cross_module.tao` - Cross-module overloads

**Deliverable**: ✅ End-to-end overloading working

---

## Phase 5: Polish (1 week)

### Goal: Documentation, examples, optimization

#### Day 1-2: Documentation

**File**: `docs/tao-overloading.md` (NEW)

- [ ] User guide
- [ ] Examples
- [ ] Error message guide
- [ ] Performance characteristics

**File**: `docs/plans/tao/10-overloading-design.md` (update)

- [ ] Update with implementation details
- [ ] Add lessons learned

#### Day 3: Examples

**Directory**: `examples/tao/overloading/`

- [ ] Basic overloading example
- [ ] Vector/Matrix example
- [ ] Custom type overloading
- [ ] Cross-module example

#### Day 4: Performance Optimization

- [ ] Profile type application overhead
- [ ] Optimize common cases
- [ ] Consider type erasure strategies

#### Day 5: Bug Fixes + Testing

- [ ] Fix issues found during testing
- [ ] Add edge case tests
- [ ] Verify error messages

**Deliverable**: ✅ Production-ready overloading

---

## Test Plan

### Unit Tests

| Module | Tests | Coverage |
|--------|-------|----------|
| `overload_set.gleam` | 20+ | Data structure operations |
| `environment.gleam` | 15+ | Env operations, merging |
| `resolution.gleam` | 25+ | Resolution algorithm |
| `type_check.gleam` | 30+ | Type-directed desugaring |
| `desugar.gleam` | 20+ | Overload desugaring |

### Integration Tests

| Test | Description |
|------|-------------|
| `overloaded_add` | Basic I32/F32 overloading |
| `vector_add` | Custom type overloading |
| `cross_module` | Import overloads from multiple modules |
| `ambiguous_error` | Ambiguous overload error |
| `no_match_error` | No matching overload error |
| `nested_operators` | Complex expressions |

### Golden File Tests

| File | Description |
|------|-------------|
| `examples/tao/overloading/01_basic.tao` | Basic example |
| `examples/tao/overloading/02_vector.tao` | Vector example |
| `examples/tao/overloading/03_cross_module.tao` | Cross-module |

---

## Success Criteria

Overloading is complete when:

- ✅ Can define overloaded functions in Tao
- ✅ Can define overloaded operators in Tao
- ✅ Overload resolution works based on argument types
- ✅ Cross-module overloads work
- ✅ Clear error messages for no-match and ambiguous
- ✅ 100+ tests passing
- ✅ 5+ working examples
- ✅ Documentation complete

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Type inference complexity | High | Start with explicit types, add inference later |
| Core bloat from type apps | Medium | Profile and optimize if needed |
| Ambiguous overload resolution | Medium | Use specificity rules, clear errors |
| Cross-module conflicts | Medium | Define clear merging rules |

---

## Related Documents

- **[10-overloading-design.md](./10-overloading-design.md)** - Design specification
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - Tao MVP (completed)
- **[../../docs/core.md](../../docs/core.md)** - Core spec (needs update)
- **[../../docs/plans/core/](../../docs/plans/core/)** - Core plans

---

## Timeline Summary

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| **Phase 1**: Core Extensions | 1 week | TypeApp in Core |
| **Phase 2**: Overload Sets | 1 week | OverloadSet data structure |
| **Phase 3**: Resolution | 1-2 weeks | Resolution algorithm + errors |
| **Phase 4**: Integration | 1 week | End-to-end working |
| **Phase 5**: Polish | 1 week | Docs, examples, tests |

**Total**: 5-6 weeks

---

**Let's implement overloading! 🚀**
