# Code Quality Analysis & Refactoring Plan

> **Date**: March 2026
> **Scope**: `src/core/` and `src/tao/`
> **Goal**: Identify improvements before standard library implementation
> **Status**: ✅ **Phase 1 Complete** - All 4/4 tasks done

---

## Progress Status

### Phase 1: Critical (Before Standard Library) - ✅ COMPLETE

| Task | Status | Notes |
|------|--------|-------|
| 1.1 Fix unused parameter warnings | ✅ **Complete** | All source files fixed |
| 1.2 Consolidate builtin implementations | ✅ **Complete** | Added `binop_i32_f64` and `cmp_i32_f64` helpers |
| 1.3 Standardize error type naming | ✅ **Complete** | Renamed fields for consistency |
| 1.4 Extract large `infer` function helpers | ✅ **Complete** | Extracted `infer_app` and `infer_match` |

**Results**:
- **Lines Saved**: ~100 lines from builtin consolidation
- **Code Quality**: All warnings fixed
- **Maintainability**: Error types now consistent, infer function modularized
- **Tests**: 424 passing ✅

---

## Executive Summary

The codebase is **functional and well-tested** (424 tests passing), but has several areas that would benefit from refactoring before implementing the standard library. The main issues are:

1. **Code duplication** in builtin implementations
2. **Inconsistent naming** conventions
3. **Missing abstractions** for common patterns
4. **Overly complex grammar** structure in Tao
5. **Hardcoded type assumptions** throughout

**Priority**: Address critical issues (Phase 1) before standard library, then incremental improvements.

---

## Analysis by File

### `src/core/core.gleam` (2030 lines)

#### ✅ Strengths
- Well-documented with clear type theory foundations
- Good separation of syntax (Terms) vs semantics (Values)
- Error accumulation for IDE support
- Comprehensive type checking with unification

#### ⚠️ Issues

##### 1. **Builtin Implementation Duplication** (HIGH PRIORITY)

**Problem**: 14 nearly identical builtin implementations:

```gleam
pub fn add_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a + b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a +. b)))
    _ -> None
  }
}

pub fn sub_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a - b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a -. b)))
    _ -> None
  }
}
// ... 12 more nearly identical functions
```

**Impact**: 
- Hard to add new numeric types (must update all 14 functions)
- Easy to introduce inconsistencies
- 200+ lines of repetitive code

**Solution**: Create generic helpers:

```gleam
// Generic binary operation helper
fn binop_impl(
  args: List(Value),
  i32_op: fn(Int, Int) -> Int,
  f64_op: fn(Float, Float) -> Float,
) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(i32_op(a, b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(f64_op(a, b))))
    _ -> None
  }
}

// Usage
pub fn add_impl(args: List(Value)) -> Option(Value) {
  binop_impl(args, fn(a, b) { a + b }, fn(a, b) { a +. b })
}

pub fn mul_impl(args: List(Value)) -> Option(Value) {
  binop_impl(args, fn(a, b) { a * b }, fn(a, b) { a *. b })
}
```

**Estimated savings**: ~150 lines, easier to extend

---

##### 2. **Inconsistent Error Type Naming** (MEDIUM PRIORITY)

**Problem**: Error constructors mix naming styles:

```gleam
// PascalCase with underscores
VarUndefined
CtrUndefined
HoleUnsolved

// Mixed styles
PatternMismatch  // PascalCase
TypeMismatch     // PascalCase
DotFieldNotFound  // PascalCase
DotOnNonCtr      // PascalCase but unclear

// Inconsistent argument order
PatternMismatch(pattern: Pattern, expected_ty: Type, s1: Span, s2: Span)
TypeMismatch(expected: Type, got: Type, span1: Span, span2: Span)
```

**Impact**: Harder to pattern match, inconsistent API

**Solution**: Standardize on clear, consistent naming:

```gleam
// All errors: Verb + Noun or Noun + Problem
UndefinedVariable(index: Int, span: Span)
UndefinedConstructor(tag: String, span: Span)
UnsolvedHole(id: Int, span: Span)
TypeMismatch(expected: Type, got: Type, expected_span: Span, got_span: Span)
MissingPattern(span: Span, pattern: Pattern)
RedundantPattern(span: Span)
```

---

##### 3. **Large `infer` Function** (MEDIUM PRIORITY)

**Problem**: The `infer` function is ~200 lines with deeply nested cases:

```gleam
pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    Typ(k) -> ...
    Lit(k) -> ...
    // ... 15 more cases, some with nested cases
    App(fun, implicit, arg) -> {
      let #(fun_val, fun_ty, s) = infer(s, fun)
      case fun_ty {
        VPi(_, _, pi_env, in, out) -> { ... }
        VNeut(HHole(hole_id), []) -> {
          // 40 lines of hole expansion logic
        }
        _ -> ...
      }
    }
  }
}
```

**Solution**: Extract helper functions:

```gleam
pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    Typ(k) -> infer_typ(k, s)
    Lit(k) -> infer_lit(k, s)
    App(fun, implicit, arg) -> infer_app(s, fun, implicit, arg, term.span)
    Match(arg, motive, cases) -> infer_match(s, arg, motive, cases, term.span)
    // ...
  }
}

fn infer_app(s: State, fun: Term, implicit: List(Term), arg: Term, span: Span) 
  -> #(Value, Type, State) {
  // Extracted application logic
}
```

**Benefit**: Easier to test, read, and modify

---

##### 4. **Hardcoded Literal Types** (LOW PRIORITY)

**Problem**: Many functions only handle I32 and F64:

```gleam
pub fn add_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a + b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a +. b)))
    _ -> None  // I64, U32, U64, F32 not supported
  }
}
```

**Impact**: Standard library will need to support all types

**Solution**: Either:
1. Add all 6 types to each function (verbose)
2. Create type-class-like dispatch (more complex but extensible)

Recommend **option 1** for simplicity, with helper:

```gleam
fn map_literal(
  lit: Literal,
  i32_fn: fn(Int) -> a,
  i64_fn: fn(Int) -> a,
  u32_fn: fn(Int) -> a,
  u64_fn: fn(Int) -> a,
  f32_fn: fn(Float) -> a,
  f64_fn: fn(Float) -> a,
) -> a {
  case lit {
    I32(n) -> i32_fn(n)
    I64(n) -> i64_fn(n)
    U32(n) -> u32_fn(n)
    U64(n) -> u64_fn(n)
    F32(n) -> f32_fn(n)
    F64(n) -> f64_fn(n)
  }
}
```

---

### `src/core/syntax.gleam` (1713 lines)

#### ✅ Strengths
- Comprehensive formatter with document algebra
- Good separation of concerns

#### ⚠️ Issues

##### 1. **Repetitive Formatter Cases** (MEDIUM PRIORITY)

**Problem**: Each term constructor has nearly identical formatting logic:

```gleam
fn format_loop(term: Term, parent_prec: Int) -> String {
  case term.data {
    Typ(k) -> "%type_" <> int.to_string(k)
    Lit(lit) -> format_lit(lit)
    Var(i) -> format_var(i)
    // ... 15 more cases, many just delegate to helpers
  }
}
```

**Solution**: Already mostly done, but could be cleaner with pattern matching helpers.

---

### `src/tao/syntax.gleam` (482 lines)

#### ✅ Strengths
- Clear grammar definition
- Good use of grammar DSL

#### ⚠️ Issues

##### 1. **Grammar Rule Duplication** (HIGH PRIORITY)

**Problem**: Each precedence level repeats the same pattern:

```gleam
left_assoc_rule(
  "Logic",
  "Comparison",
  [
    infix_binary("&&", make_and, InfixLeft, 3, " && "),
    infix_binary("||", make_or, InfixLeft, 3, " || "),
  ],
  3,
)
left_assoc_rule(
  "Comparison",
  "Term",
  [
    infix_binary("==", make_eq, InfixLeft, 5, " == "),
    // ... 5 more operators
  ],
  5,
)
```

**Impact**: Adding operators requires understanding the rule structure

**Solution**: Create operator group helper:

```gleam
// Define operator groups declaratively
const operator_groups = [
  OperatorGroup(name: "Logic", precedence: 3, operators: [
    Op("&&", make_and),
    Op("||", make_or),
  ]),
  OperatorGroup(name: "Comparison", precedence: 5, operators: [
    Op("==", make_eq),
    Op("!=", make_neq),
    Op("<", make_lt),
    Op(">", make_gt),
    Op("<=", make_lte),
    Op(">=", make_gte),
  ]),
  // ...
]

// Generate rules from groups
fn generate_rules() -> List(Rule) {
  list.map(operator_groups, fn(group) {
    left_assoc_rule(
      group.name,
      get_lower_level(group.name),
      list.map(group.operators, fn(op) {
        infix_binary(op.symbol, op.constructor, InfixLeft, group.precedence, " " <> op.symbol <> " ")
      }),
      group.precedence,
    )
  })
}
```

---

##### 2. **AST Constructor Explosion** (MEDIUM PRIORITY)

**Problem**: 15+ AST constructors for simple expressions:

```gleam
pub type MvpExpr {
  MvpInt(...)
  MvpVar(...)
  MvpAdd(...)
  MvpSub(...)
  MvpMul(...)
  MvpDiv(...)
  MvpEq(...)
  MvpNeq(...)
  MvpLt(...)
  MvpGt(...)
  MvpLte(...)
  MvpGte(...)
  MvpAnd(...)
  MvpOr(...)
  MvpNot(...)
  OverloadedFn(...)
  OverloadedApp(...)
}
```

**Impact**: Every function must pattern match on all constructors

**Solution**: Consider binary/unary operator enum:

```gleam
pub type BinOp {
  Add | Sub | Mul | Div
  Eq | Neq | Lt | Gt | Lte | Gte
  And | Or
}

pub type UnaryOp {
  Not
}

pub type MvpExpr {
  MvpInt(value: Int, span: Span)
  MvpVar(name: String, span: Span)
  MvpBinOp(left: MvpExpr, op: BinOp, right: MvpExpr, span: Span)
  MvpUnary(op: UnaryOp, expr: MvpExpr, span: Span)
  OverloadedFn(...)
  OverloadedApp(...)
}
```

**Trade-off**: Less constructors, but pattern matching on operators becomes verbose

**Recommendation**: Keep current structure for now (clearer patterns), revisit if it grows beyond 20 constructors.

---

##### 3. **Inconsistent Span Handling** (LOW PRIORITY)

**Problem**: Some functions use `get_span`, others pattern match:

```gleam
fn make_add(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpAdd(left, right, span)
}

fn format_expr_loop(expr: MvpExpr, parent_prec: Int) -> String {
  case expr {
    MvpInt(n, _) -> ...  // Ignores span
    MvpAdd(l, r, _) -> ...  // Ignores span
  }
}
```

**Solution**: Consistent span accessor (already exists as `get_expr_span`), use uniformly.

---

### `src/tao/desugar.gleam` (247 lines)

#### ✅ Strengths
- Clear desugaring logic
- Good context management

#### ⚠️ Issues

##### 1. **Hardcoded Type Assumptions** (HIGH PRIORITY)

**Problem**: All binary ops assume I32:

```gleam
MvpAdd(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_add")
MvpSub(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_sub")
MvpEq(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_eq")
```

**Impact**: Can't handle F32, F64, etc. without type inference

**Solution**: Type-directed desugaring (requires type inference first):

```gleam
fn desugar_binop(left: MvpExpr, right: MvpExpr, span: Span, ctx: DesugarCtx, op: String) -> Term {
  // For now, assume I32
  // TODO: Infer type from context and select appropriate FFI call
  let left_term = desugar_expr(left, ctx)
  let right_term = desugar_expr(right, ctx)
  Term(Call("i32_" <> op, [left_term, right_term]), span)
}
```

This is a **fundamental design issue** - Tao needs type inference before desugaring, or desugaring needs to produce polymorphic Core terms.

**Recommendation**: For now, document limitation. Long-term, consider:
1. Type-directed desugaring (infer first, then desugar)
2. Polymorphic Core terms (desugar to generic ops, resolve in Core)

---

##### 2. **Unused Parameters** (LOW PRIORITY)

**Problem**: Several functions have unused parameters:

```gleam
fn desugar_overloaded_fn(
  name: String,           // Used
  type_param: String,     // Used
  param_name: String,     // Used
  param_type: String,     // Used
  return_type: String,    // UNUSED - should be _return_type
  body: MvpExpr,          // Used
  span: Span,             // Used
) -> Term {
```

**Solution**: Prefix unused with `_` (Gleam convention).

---

## Refactoring Plan

### Phase 1: Critical (Before Standard Library)

**Goal**: Make codebase easier to extend

| Task | Files | Effort | Priority |
|------|-------|--------|----------|
| 1.1 Consolidate builtin implementations | `core.gleam` | 2-3 hours | **HIGH** |
| 1.2 Fix unused parameter warnings | All files | 30 min | **HIGH** |
| 1.3 Standardize error type naming | `core.gleam` | 1-2 hours | **HIGH** |
| 1.4 Extract large `infer` function helpers | `core.gleam` | 2-3 hours | **MEDIUM** |

**Total**: ~6-8 hours

---

### Phase 2: Important (Before Major Features)

| Task | Files | Effort | Priority |
|------|-------|--------|----------|
| 2.1 Operator group abstraction | `tao/syntax.gleam` | 2 hours | MEDIUM |
| 2.2 Fix hardcoded type assumptions | `tao/desugar.gleam` | 3-4 hours | MEDIUM |
| 2.3 Add all literal types to builtins | `core.gleam` | 2 hours | MEDIUM |

**Total**: ~7-8 hours

---

### Phase 3: Nice-to-Have (Incremental)

| Task | Files | Effort | Priority |
|------|-------|--------|----------|
| 3.1 AST constructor consolidation | `tao/syntax.gleam` | 2 hours | LOW |
| 3.2 Consistent span handling | All files | 1 hour | LOW |
| 3.3 Formatter cleanup | `core/syntax.gleam` | 1 hour | LOW |

**Total**: ~4 hours

---

## Recommendations

### Immediate Actions (Do Now)

1. **Fix unused parameter warnings** - Quick win, improves code quality
2. **Consolidate builtin implementations** - Makes adding types easier
3. **Standardize error naming** - Improves API consistency

### Before Standard Library

4. **Extract `infer` helpers** - Makes type checking easier to extend
5. **Address hardcoded types in desugarer** - Critical for multi-type support

### Can Wait

6. **Grammar abstraction** - Current structure works, refactor when adding many operators
7. **AST consolidation** - Only if constructors exceed 20
8. **Formatter cleanup** - Works fine, cosmetic improvements

---

## Risk Assessment

### High Risk Changes
- **Changing AST structure** - Would break parser, formatter, desugarer, tests
- **Changing Core Term/Value types** - Would break type checker, evaluator, everything

### Medium Risk Changes
- **Refactoring `infer` function** - Need comprehensive tests (we have them ✅)
- **Changing error types** - Need to update all error handling (manageable)

### Low Risk Changes
- **Builtin consolidation** - Internal refactoring, no API changes
- **Fixing warnings** - Purely cosmetic

---

## Conclusion

The codebase is in **good shape** but has technical debt that will compound during standard library implementation. 

**Recommendation**: Complete **Phase 1** (6-8 hours) before starting standard library. This will make adding new types and operations significantly easier.

**Phase 2** can be done incrementally as needed during standard library development.

**Phase 3** is optional and can be deferred indefinitely.
