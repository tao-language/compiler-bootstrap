# Error Message Analysis and Improvement Plan

> **Goal**: Comprehensive analysis of current error messages with actionable improvements
> **Status**: 📋 Analysis Complete
> **Date**: March 11, 2026

---

## Executive Summary

This document analyzes all error examples in `examples/core/errors/` and provides a detailed improvement plan for error messages, code snippets, notes, and hints.

### Key Findings

1. **Working Well**: TypeMismatch, HoleUnsolved, NotAFunction have good educational content
2. **Needs Improvement**: Syntax errors are too generic, many errors fall back to E9999
3. **Missing Coverage**: 8 error types have no examples (fall back to generic handler)
4. **Visual Issues**: Code snippets lack inline labels, spans often show 0:0

---

## Current Error Message Analysis

### Type Errors - Working Examples

#### 1. TypeMismatch (01_param_type_mismatch, 02_annotation_mismatch) ✅

**Current Output**:
```
error[E0101]: Type mismatch
  ┌─ input:1:1
1 │ 42 : $Type
    ^^ ----
2 │ 
  = note: $Type(0) and Int are incompatible types
  = note: The expression produces $Type(0) but Int is expected here
  = hint: Check that the expression has the expected type
  = hint: Consider adding a type annotation
  = hint: Did you mean to use a different expression?
```

**Strengths**:
- ✅ Shows both types involved
- ✅ Explains what produces what
- ✅ 3 actionable hints
- ✅ Good code snippet with context

**Weaknesses**:
- ❌ No emoji indicators (❌ 💡 🔧)
- ❌ Inline label "----" is unclear
- ❌ Doesn't show which is expected vs found in the snippet
- ❌ No visual type comparison

**Improvements**:
```
❌ error[E0101]: Type mismatch
error[E0101]: Type mismatch
   ┌─ input:1:5
 1 │ 42 : $Type
   │      ^^^^^ expected $Type(0), found Int
   │
   = note: $Type(0) and Int are incompatible types
   = note: The expression produces Int but $Type(0) is expected here
   🎯 Expected: $Type(0) (a universe type)
   🔍 Found:    Int (a value type)
   💡 $Type is the type of types, not a value type
   💡 42 is a number, not a type
   🔧 Remove the type annotation: 42
   🔧 Or use a value type: 42 : Int
   📚 See: docs/core.md#type-system
```

#### 2. HoleUnsolved (07_hole) ✅

**Current Output**:
```
error[E0106]: Unsolved hole
  ┌─ input:3:2
1 │ // Hole with identifier
2 │ // Used as a placeholder during development
3 │ ?1
     ^
4 │ 
  = note: Hole #1 was not solved during type checking
  = note: Holes are development placeholders that must be replaced before the program is complete
  = hint: Holes are placeholders that must be filled
  = hint: Provide a term of the expected type, or add a type annotation
  = hint: Use holes temporarily during development, then replace them
```

**Strengths**:
- ✅ Excellent educational content
- ✅ Explains what holes are for
- ✅ Clear action items
- ✅ Good span pointing to hole

**Weaknesses**:
- ❌ No emoji indicators
- ❌ Could show expected type if known

**Improvements**:
```
❌ error[E0106]: Unsolved hole
error[E0106]: Unsolved hole
   ┌─ input:3:2
 1 │ // Hole with identifier
 2 │ // Used as a placeholder during development
 3 │ ?1
      ^ Hole #1 not solved
 4 │ 
   │
   = note: Hole #1 was not solved during type checking
   = note: Holes are development placeholders that must be replaced before the program is complete
   💡 Holes are like "TODO" comments for types - they must be filled in
   💡 This hole appears where a value is expected
   🔧 Replace ?1 with a concrete value
   🔧 Add a type annotation: (?1 : Int)
   🔧 Use a wildcard if type can be inferred: _
   📚 See: docs/core.md#holes
```

#### 3. NotAFunction (03_not_a_function) ✅

**Current Output**:
```
error[E0103]: Cannot call non-function value
  ┌─ :0:0
1 │ // Type Error: Not a function
2 │ // Trying to apply a non-function value
3 │ 42(x)
  = note: This value has type Int, which is not callable
  = note: Only function values (created with ->) can be called with parentheses
  = hint: Only functions can be called with parentheses
  = hint: Check that you're calling a function, not a value
  = hint: If you want a function, use a lambda: x -> expression
```

**Strengths**:
- ✅ Shows actual type (Int)
- ✅ Explains what IS callable
- ✅ Provides alternative syntax

**Weaknesses**:
- ❌ Span shows :0:0 (broken - should point to 42)
- ❌ No code snippet highlighting
- ❌ No emoji indicators

**Improvements**:
```
❌ error[E0103]: Cannot call non-function value
error[E0103]: Cannot call non-function value
   ┌─ input:3:1
 1 │ // Type Error: Not a function
 2 │ // Trying to apply a non-function value
 3 │ 42(x)
   │ ^^ cannot call non-function
   │
   = note: This value has type Int, which is not callable
   = note: Only function values (created with ->) can be called with parentheses
   💡 You're trying to call 42 like a function, but it's a number
   💡 Function calls look like: f(x) where f is a function
   🔧 Remove the parentheses if you just want the value: 42
   🔧 Use a function instead: (x -> x)(x)
   🔧 If you meant multiplication, use: 42 * x
   📚 See: docs/core.md#functions
```

---

### Type Errors - Broken Examples (Fall Back to E9999)

#### 4. CtrUndefined (05_constructor) ❌

**Current Output**:
```
error[E9999]: Type error
  ┌─ examples/core/errors/type_errors/05_constructor.core.tao:0:0
1 │ // Constructor Application
2 │ // Constructors are applied like functions: #Tag(argument)
3 │ // Note: Constructors must be defined in the type context
```

**Problems**:
- ❌ Generic E9999 error code
- ❌ Span is 0:0 (not pointing to actual error)
- ❌ Shows comments instead of code with error
- ❌ No notes or hints
- ❌ Doesn't identify the actual issue (#Some is undefined)

**Target Output**:
```
❌ error[E0105]: Constructor not found
error[E0105]: Constructor not found
   ┌─ input:6:18
 4 │ // This example shows valid constructor syntax using Church encoding
 5 │ // since full ADT support requires a prelude/type definition system
 6 │ let some = x -> #Some(x) in
   │                  ^^^^ constructor 'Some' is not defined
 7 │ some(42)
   │
   = note: Constructor `Some` is not defined in the current scope
   = note: Constructors must be defined before use, typically in a data type declaration
   💡 #Some looks like a constructor application
   💡 But no type with constructor 'Some' has been defined
   🔧 Define a type with this constructor first
   🔧 Use an existing constructor from the prelude
   🔧 Check the spelling: did you mean a different constructor?
   📚 See: docs/core.md#constructors
```

#### 5. InfiniteType (10_infinite_type) ❌

**Current Output**:
```
error[E9999]: Type error
  ┌─ examples/core/errors/type_errors/10_infinite_type.core.tao:0:0
...
```

**Problems**:
- ❌ Generic E9999 error
- ❌ Span is 0:0
- ❌ No specific error message
- ❌ No hints about infinite types

**Target Output**:
```
❌ error[E0108]: Infinite type
error[E0108]: Infinite type
   ┌─ input:4:13
 3 │ // Example: applying a function to itself without proper type annotation
 4 │ let f = x -> x(x) in
   │             ^^^^ this would require an infinite type
 5 │ f
   │
   = note: Cannot unify type variable with a type containing itself
   = note: This would create the infinite type: T = T -> ?
   💡 Infinite types are not allowed in this type system
   💡 This happens when a function is applied to itself
   💡 The type checker cannot find a finite type for x
   🔧 Add a type annotation to break the cycle
   🔧 Use a different pattern that doesn't self-apply
   🔧 Consider using a fixpoint combinator instead
   📚 See: docs/core.md#type-inference
```

#### 6. Record Errors (12, 13, 14) ❌

All three record-related errors fall back to E9999:
- `RcdMissingFields` (12_record_missing_fields)
- `DotFieldNotFound` (13_field_not_found)  
- `DotOnNonCtr` (14_dot_on_non_constructor)

**Target Output for RcdMissingFields**:
```
❌ error[E0110]: Field not found
error[E0110]: Field not found
   ┌─ input:5:3
 4 │ // Example: trying to access field 'z' from a record that only has 'x' and 'y'
 5 │ let r = {x: 1, y: 2} in
 6 │ r.z
   │   ^ field 'z' not found
   │
   = note: Record has fields: x, y
   = note: Attempted to access non-existent field: z
   💡 Records only have the fields they were defined with
   💡 Did you misspell the field name?
   🔧 Use an existing field: r.x or r.y
   🔧 Add the field to the record: {x: 1, y: 2, z: 3}
   📚 See: docs/core.md#records
```

#### 7. TODO (16_todo) ❌

**Current Output**: Shows "Undefined variable" for TODO

**Problems**:
- ❌ TODO is being treated as a variable
- ❌ Wrong error type entirely
- ❌ Doesn't recognize TODO as a special form

**Target Output**:
```
❌ error[E9999]: TODO - Incomplete implementation
error[E9999]: TODO - Incomplete implementation
   ┌─ input:5:1
 4 │ // Example: using TODO to mark a function that needs to be implemented
 5 │ TODO("implement this function")
   │ ^^^^ TODO marker found
 6 │ 
   │
   = note: This is a placeholder for incomplete code
   = note: TODO message: "implement this function"
   💡 TODO errors mark incomplete implementations
   💡 They're useful during development but should be fixed
   🔧 Implement the missing functionality
   🔧 Replace TODO with actual implementation
   📚 See: docs/core.md#todo
```

---

### Syntax Errors - All Need Improvement

#### Current Pattern (All Syntax Errors)

**Current Output** (representative example):
```
error[E0001]: Syntax error
  ┌─ input:0:0
1 │ {{{
2 │ 
  = note: Expected: valid alternative
  = note: Got: none
```

**Problems** (apply to ALL syntax errors):
- ❌ Span is always 0:0 (not pointing to actual error location)
- ❌ "Expected: valid alternative" is useless
- ❌ "Got: none" is wrong (we got {{{)
- ❌ No specific information about what went wrong
- ❌ No hints about how to fix
- ❌ Shows comments instead of the actual problematic code
- ❌ No emoji indicators

**Target Pattern**:
```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ input:1:1
 1 │ {{{
   │   ^ unexpected token
   │
   = note: Expected: expression, identifier, or keyword
   = note: Got: { (opening brace)
   💡 The parser encountered unexpected syntax
   💡 This often happens with typos or missing tokens
   🔧 Check for extra or missing brackets
   🔧 Ensure expressions are well-formed
   📚 See: docs/core.md#syntax
```

#### Specific Syntax Error Improvements

##### 01_double_arrow (-> -> x)
```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ input:3:4
 1 │ // Parse Error: Multiple consecutive arrows
 2 │ // This should fail because the grammar doesn't allow multiple arrows in a row
 3 │ -> -> x
   │    ^^ unexpected arrow
   │
   = note: Expected: identifier or expression before arrow
   = note: Got: -> (arrow without left-hand side)
   💡 Lambda arrows must be preceded by a parameter
   💡 Syntax: (parameter) -> body or parameter -> body
   🔧 Add a parameter: x -> x
   🔧 Remove the extra arrow
   📚 See: docs/core.md#lambdas
```

##### 04_bare_hash (#)
```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ input:3:1
 1 │ // Parse Error: Hash without constructor
 2 │ // Hash must be followed by an identifier (constructor name)
 3 │ #
   │ ^ expected constructor name after #
   │
   = note: Expected: identifier (constructor name)
   = note: Got: end of input
   💡 The # symbol starts a constructor application
   💡 Constructors look like: #TagName or #Tag(argument)
   🔧 Add a constructor name: #Some
   🔧 Or remove the # if not using a constructor
   📚 See: docs/core.md#constructors
```

##### 05_bare_dollar ($)
```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ input:3:1
 1 │ // Parse Error: Dollar without type
 2 │ // Dollar must be followed by an identifier (type name)
 3 │ $
   │ ^ expected type name after $
   │
   = note: Expected: identifier (type name)
   = note: Got: end of input
   💡 The $ symbol starts a type reference
   💡 Types look like: $Type, $Int, $MyType
   🔧 Add a type name: $Type
   🔧 Or remove the $ if not referencing a type
   📚 See: docs/core.md#types
```

##### 06_unclosed_paren ((42)
```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ input:2:1
 1 │ // Parse Error: Opening paren without closing
 2 │ (42
   │ ^   unclosed parenthesis
   │
   = note: Expected: ) to close this parenthesis
   = note: Got: end of input
   💡 Every opening ( must have a matching )
   💡 Parentheses group expressions: (expression)
   🔧 Add closing paren: (42)
   🔧 Or remove opening paren: 42
   📚 See: docs/core.md#syntax
```

---

### Syntax Recovery Errors

#### Current Output (01_trailing_operator)
```
error[E0102]: Undefined variable
  ┌─ input:4:1
2 │ // The parser should recover after the unexpected + operator
3 │ // and potentially treat this as just the variable x
4 │ x +
    ^
5 │ 
  = note: Variable at index 0 is not defined in this scope
  = note: Variables must be defined before they are used, typically in a let binding or lambda parameter
  = hint: Check variable name and scope
  = hint: Did you forget to define this variable?
  = hint: Check for typos in the variable name
```

**Analysis**: This is actually decent! The parser recovered and treated `x` as a variable (which is undefined). But we could do better.

**Improvements**:
```
❌ error[E0102]: Undefined variable
error[E0102]: Undefined variable
   ┌─ input:4:1
 2 │ // The parser should recover after the unexpected + operator
 3 │ // and potentially treat this as just the variable x
 4 │ x +
   │ ^ variable 'x' is not defined
   │   ^ unexpected trailing operator
   │
   = note: Variable at index 0 is not defined in this scope
   = note: Variables must be defined before they are used
   ⚠️  Warning: Trailing operator '+' has no right operand
   💡 The parser recovered by treating this as just 'x'
   💡 But 'x' itself is not defined
   🔧 Define x first: let x = 42 in x + 1
   🔧 Remove the trailing operator: x
   🔧 Add a right operand: x + y
   📚 See: docs/core.md#expressions
```

---

## Systematic Issues Identified

### 1. Span Reporting Broken for Many Errors

**Affected**: CtrUndefined, InfiniteType, RcdMissingFields, DotFieldNotFound, DotOnNonCtr, TODO

**Symptom**: Span shows `0:0` or file path instead of `input`

**Cause**: These errors aren't being handled in `error_reporter.gleam`, falling back to generic handler

**Fix**: Add specific handling for each error type in `type_error_to_diagnostic()`

### 2. Syntax Errors Too Generic

**Affected**: All syntax_errors/*

**Symptom**: "Expected: valid alternative, Got: none"

**Cause**: Parse errors aren't extracting useful information from the parser

**Fix**: Improve `parse_error_to_diagnostic()` to show:
- What token was expected
- What token was found
- Specific location of error
- Contextual hints

### 3. No Emoji Indicators

**Affected**: All errors

**Symptom**: No visual scanning aids

**Fix**: Add emoji prefix to diagnostic output:
- ❌ for errors
- 💡 for insights
- 🔧 for fixes
- 📚 for references

### 4. Missing Inline Labels

**Affected**: All errors

**Symptom**: Pointer shows `^` but no explanation of what's wrong at that location

**Fix**: Add inline labels like `^ expected Type, found Int`

### 5. No Visual Type Comparison

**Affected**: TypeMismatch

**Symptom**: Types mentioned in notes but not visually compared

**Fix**: Add formatted type comparison:
```
🎯 Expected: $Type(0)
🔍 Found:    Int
```

---

## Implementation Priority

### Phase 1: Fix Broken Error Types (2 weeks)

| Error Type | File | Priority | Effort |
|------------|------|----------|--------|
| CtrUndefined | 05_constructor | P0 | 1h |
| RcdMissingFields | 12_record_missing_fields | P0 | 1h |
| DotFieldNotFound | 13_field_not_found | P0 | 1h |
| DotOnNonCtr | 14_dot_on_non_constructor | P0 | 1h |
| InfiniteType | 10_infinite_type | P1 | 2h |
| TODO | 16_todo | P1 | 1h |
| PatternMismatch | 08_pattern_mismatch | P1 | 2h |
| SpineMismatch | (need example) | P2 | 2h |

### Phase 2: Improve Syntax Errors (1 week)

| Task | Priority | Effort |
|------|----------|--------|
| Better "expected" messages | P0 | 2h |
| Better "got" messages | P0 | 2h |
| Accurate span reporting | P0 | 3h |
| Contextual hints | P1 | 2h |

### Phase 3: Visual Enhancements (1 week)

| Task | Priority | Effort |
|------|----------|--------|
| Add emoji indicators | P0 | 2h |
| Add inline labels | P1 | 3h |
| Add type comparison | P1 | 2h |
| Improve code snippets | P2 | 2h |

### Phase 4: Educational Content (Ongoing)

| Task | Priority | Effort |
|------|----------|--------|
| Add "why this happens" notes | P1 | 4h |
| Add documentation links | P2 | 2h |
| Add "did you mean?" suggestions | P2 | 4h |

---

## Success Metrics

| Metric | Current | Target |
|--------|---------|--------|
| Errors with specific codes | 6/20 (30%) | 20/20 (100%) |
| Errors with accurate spans | 6/20 (30%) | 20/20 (100%) |
| Errors with 2+ notes | 6/20 (30%) | 20/20 (100%) |
| Errors with 3+ hints | 6/20 (30%) | 20/20 (100%) |
| Errors with emoji indicators | 0/20 (0%) | 20/20 (100%) |
| Errors with inline labels | 0/20 (0%) | 20/20 (100%) |
| Syntax errors with useful messages | 0/9 (0%) | 9/9 (100%) |

---

## Related Documents

- **[05-error-message-improvements.md](./05-error-message-improvements.md)** - Previous improvements
- **[06-error-message-enhancement-plan.md](./06-error-message-enhancement-plan.md)** - Comprehensive enhancement plan
- **[../cli/03-error-reporter.md](../cli/03-error-reporter.md)** - Error reporter spec

---

## References

- [Error Reporter Implementation](../../src/syntax/error_reporter.gleam)
- [Core Error Formatter](../../src/core/error_formatter.gleam)
- [Core Error Types](../../src/core/core.gleam)
- [Rust Compiler Errors](https://github.com/rust-lang/rust/blob/master/compiler/rustc_errors/src)
- [Elm Compiler Errors](https://elm-lang.org/news/compiler-errors-for-humans)
