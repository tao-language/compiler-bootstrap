# Error Message Improvement Plan

> **Goal**: Make error messages more descriptive, actionable, and visual while keeping them succinct
> **Status**: 📋 Planned
> **Date**: March 11, 2026

---

## Executive Summary

This document analyzes all error types in the core language and provides a comprehensive plan for improving error messages. The goal is to provide errors that are:

1. **Descriptive** - Explain what went wrong and why
2. **Actionable** - Tell users exactly how to fix the issue
3. **Visual** - Use emojis and formatting for quick scanning
4. **Succinct** - Get to the point without unnecessary verbosity
5. **Complete** - Cover all error types with consistent quality

---

## Current Error Types Analysis

### Error Types in `core.gleam`

```gleam
pub type Error {
  // Syntax errors
  SyntaxError(span, expected, got, context)

  // Type errors
  PatternMismatch(pattern, expected_ty, s1, s2)
  TypeMismatch(expected, got, span1, span2)
  InfiniteType(hole_id, ty, span1, span2)
  TypeAnnotationNeeded(term)
  NotAFunction(fun, fun_ty)
  VarUndefined(index, span)
  RcdMissingFields(name, span)
  CtrUndefined(tag, span)
  CtrUnsolvedParam(tag, ctr, id, span)
  DotFieldNotFound(name, fields, span)
  DotOnNonCtr(value, name, span)
  HoleUnsolved(id, span)
  SpineMismatch(span1, span2)
  ArityMismatch(span1, span2)
  TODO(message)

  // Exhaustiveness checks
  MatchRedundantCase(Span)
  MatchMissingCase(Span, Pattern)

  // Comptime errors
  ComptimePermissionDenied(operation, span, required)
}
```

### Coverage Analysis

| Error Type | Example Exists? | Golden File? | Quality |
|------------|----------------|--------------|---------|
| **Syntax Errors** | | | |
| SyntaxError | ✅ Multiple | ✅ | 🟡 Medium |
| **Type Errors** | | | |
| TypeMismatch | ✅ 01, 02 | ✅ | 🟢 Good |
| VarUndefined | ✅ (via syntax_recovery) | ✅ | 🟢 Good |
| NotAFunction | ✅ 03 | ✅ | 🟢 Good |
| HoleUnsolved | ✅ 07 | ✅ | 🟢 Good |
| CtrUndefined | ✅ 05 | ✅ | 🟢 Good |
| PatternMismatch | ❌ Missing | ❌ | 🔴 Not covered |
| InfiniteType | ❌ Missing | ❌ | 🔴 Not covered |
| TypeAnnotationNeeded | ❌ Missing | ❌ | 🔴 Not covered |
| RcdMissingFields | ❌ Missing | ❌ | 🔴 Not covered |
| CtrUnsolvedParam | ❌ Missing | ❌ | 🔴 Not covered |
| DotFieldNotFound | ❌ Missing | ❌ | 🔴 Not covered |
| DotOnNonCtr | ❌ Missing | ❌ | 🔴 Not covered |
| SpineMismatch | ❌ Missing | ❌ | 🔴 Not covered |
| ArityMismatch | ❌ Missing | ❌ | 🔴 Not covered |
| TODO | ❌ Missing | ❌ | 🔴 Not covered |
| **Exhaustiveness** | | | |
| MatchRedundantCase | ❌ Missing | ❌ | 🔴 Not covered |
| MatchMissingCase | ❌ Missing | ❌ | 🔴 Not covered |
| **Comptime Errors** | | | |
| ComptimePermissionDenied | ❌ Missing | ❌ | 🔴 Not covered |

**Summary**: Only 6 of 20 error types have examples. We need 14 new examples.

---

## Error Message Format Standard

### Target Format

```
❌ error[E###]: Error Category
error[E###]: Specific error message
   ┌─ file:line:col
   │
 N │ ... context line -2
 N │ ... context line -1
 N │ source code with error
   │       ^^^^ label explaining what's wrong
 N │ ... context line +1
 N │ ... context line +2
   │
   = note: First explanation of the issue
   = note: Second explanation with more detail
   💡 Why this happens (educational)
   🔧 Fix suggestion 1
   🔧 Fix suggestion 2
```

### Emoji Guide

| Emoji | Purpose | Usage |
|-------|---------|-------|
| ❌ | Error indicator | Prefix for error header |
| ⚠️ | Warning indicator | For warnings (future) |
| 💡 | Insight | Explain WHY something is wrong |
| 📝 | Note | Additional context or information |
| 🔧 | Fix | Actionable suggestion to fix |
| 📚 | Reference | Link to documentation |
| 🎯 | Target | Show what was expected |
| 🔍 | Context | Show related information |

### Note Types

```
= note: Technical explanation (what happened)
💡 Insight: Educational explanation (why it happened)
🔧 Fix: Actionable suggestion (how to fix)
📚 See: Reference to documentation
```

---

## Improvement Plans by Error Type

### Phase 1: Missing Error Examples (Priority: High)

#### 1.1 PatternMismatch
**File**: `examples/core/errors/type_errors/08_pattern_mismatch.core.tao`

```gleam
// Pattern Type Mismatch
// Pattern expects a different type than the matched value
// This error occurs when a pattern's type doesn't match the scrutinee
match (42 : Int) {
  | (x : $Type) -> x  // Pattern expects $Type, but value is Int
}
```

**Expected Output**:
```
❌ error[E0107]: Pattern type mismatch
error[E0107]: Pattern type mismatch
   ┌─ input:4:6
 2 │ // This error occurs when a pattern's type doesn't match the scrutinee
 3 │ match (42 : Int) {
 4 │   | (x : $Type) -> x  // Pattern expects $Type, but value is Int
   │       ^^^^^^ pattern has type $Type, but matched value has type Int
 5 │ }
   │
   = note: Pattern type $Type doesn't match value type Int
   = note: Patterns must have the same type as the value being matched
   💡 The pattern tries to match a type ($Type) against a value type (Int)
   💡 $Type is the universe of types, not a value type
   🔧 Remove the type annotation from the pattern
   🔧 Use a value type like Int instead of $Type
   📚 See: docs/core.md#pattern-matching
```

#### 1.2 ArityMismatch
**File**: `examples/core/errors/type_errors/09_arity_mismatch.core.tao`

```gleam
// Arity Mismatch
// Function called with wrong number of arguments
let f = x -> x in
f(1, 2)  // f expects 1 argument, but 2 were provided
```

**Expected Output**:
```
❌ error[E0104]: Arity mismatch
error[E0104]: Arity mismatch
   ┌─ input:3:1
 2 │ // Function called with wrong number of arguments
 3 │ let f = x -> x in
 4 │ f(1, 2)  // f expects 1 argument, but 2 were provided
   │ ^^^^^^^ function expects 1 argument, received 2
   │
   = note: Function has arity 1 (expects 1 argument)
   = note: Call site provides 2 arguments
   💡 Arity is the number of arguments a function expects
   💡 This function was defined with one parameter: x
   🔧 Remove the extra argument
   🔧 Or change the function to accept two parameters: x -> y -> ...
   📚 See: docs/core.md#functions
```

#### 1.3 InfiniteType
**File**: `examples/core/errors/type_errors/10_infinite_type.core.tao`

```gleam
// Infinite Type Error
// Occurs when a type would need to contain itself
// This happens when unification tries to solve a hole with a type containing that hole
let f = x -> x(x) in
f(f)
```

**Expected Output**:
```
❌ error[E0108]: Infinite type
error[E0108]: Infinite type
   ┌─ input:3:13
 2 │ // Occurs when a type would need to contain itself
 3 │ let f = x -> x(x) in
   │             ^^^^ this would require an infinite type
 4 │ f(f)
   │
   = note: Cannot unify type variable with a type containing itself
   = note: This would create the infinite type: T = T -> ?
   💡 Infinite types are not allowed in this type system
   💡 This often happens when applying a function to itself
   🔧 Check if you're accidentally applying a function to itself
   🔧 Add a type annotation to clarify the intended types
   📚 See: docs/core.md#type-inference
```

#### 1.4 TypeAnnotationNeeded
**File**: `examples/core/errors/type_errors/11_type_annotation_needed.core.tao`

```gleam
// Type Annotation Needed
// The type checker cannot infer the type without help
// This happens with polymorphic values or ambiguous expressions
let id = x -> x in
id  // What type should id be?
```

**Expected Output**:
```
❌ error[E0109]: Type annotation needed
error[E0109]: Type annotation needed
   ┌─ input:3:1
 2 │ // The type checker cannot infer the type without help
 3 │ let id = x -> x in
 4 │ id  // What type should id be?
   │ ^^ cannot infer type for this polymorphic value
   │
   = note: The type checker needs more information to determine the type
   = note: This value is polymorphic (works with any type)
   💡 Without a type annotation, the compiler doesn't know which type to use
   💡 This often happens with identity functions or other polymorphic values
   🔧 Add a type annotation: (id : Int -> Int)
   🔧 Use the value in a context where the type is clear
   📚 See: docs/core.md#type-annotations
```

#### 1.5 RcdMissingFields
**File**: `examples/core/errors/type_errors/12_record_missing_fields.core.tao`

```gleam
// Record Missing Fields
// Accessing a field that doesn't exist in the record
let r = {x: 1, y: 2} in
r.z  // z is not a field of r
```

**Expected Output**:
```
❌ error[E0110]: Field not found
error[E0110]: Field not found
   ┌─ input:3:5
 2 │ // Accessing a field that doesn't exist in the record
 3 │ let r = {x: 1, y: 2} in
 4 │ r.z  // z is not a field of r
   │     ^ field 'z' not found in record
   │
   = note: Record has fields: x, y
   = note: Attempted to access non-existent field: z
   💡 Records only have the fields they were defined with
   💡 Did you misspell the field name?
   🔧 Use an existing field: r.x or r.y
   🔧 Add the field to the record: {x: 1, y: 2, z: 3}
   📚 See: docs/core.md#records
```

#### 1.6 DotFieldNotFound (similar to RcdMissingFields but different context)
**File**: `examples/core/errors/type_errors/13_field_not_found.core.tao`

```gleam
// Field Not Found
// Similar to RcdMissingFields but occurs during type checking
let get_x = r -> r.x in
get_x({y: 2})  // Record doesn't have field x
```

**Expected Output**:
```
❌ error[E0111]: Field not found
error[E0111]: Field not found
   ┌─ input:3:11
 2 │ // Similar to RcdMissingFields but occurs during type checking
 3 │ let get_x = r -> r.x in
 4 │ get_x({y: 2})  // Record doesn't have field x
   │           ^^^^ this record doesn't have field 'x'
   │
   = note: Expected record with field 'x'
   = note: Got record with fields: y
   💡 The function requires a record with field 'x'
   💡 The provided record only has field 'y'
   🔧 Add field 'x' to the record: {x: 1, y: 2}
   🔧 Or use a record that already has field 'x'
   📚 See: docs/core.md#records
```

#### 1.7 DotOnNonCtr
**File**: `examples/core/errors/type_errors/14_dot_on_non_constructor.core.tao`

```gleam
// Dot on Non-Constructor
// Trying to project a field from a non-record value
let x = 42 in
x.field  // Cannot project fields from integers
```

**Expected Output**:
```
❌ error[E0112]: Cannot project from non-record
error[E0112]: Cannot project from non-record
   ┌─ input:3:1
 2 │ // Trying to project a field from a non-record value
 3 │ let x = 42 in
 4 │ x.field  // Cannot project fields from integers
   │ ^^^^^^^ cannot project field from value of type Int
   │
   = note: Field projection (.field) only works on records
   = note: This value has type Int, which is not a record
   💡 Only records have named fields that can be projected
   💡 Int is a primitive type, not a record type
   🔧 Use a record instead: {value: 42}.value
   🔧 Or use the value directly without projection
   📚 See: docs/core.md#records
```

#### 1.8 CtrUnsolvedParam
**File**: `examples/core/errors/type_errors/15_constructor_unsolved_param.core.tao`

```gleam
// Constructor Unsolved Parameter
// Constructor parameter type cannot be inferred
// (This is a more advanced error that requires GADT-style constructors)
// Example placeholder - actual error depends on constructor system
let make_pair = #42 in
make_pair  // Constructor parameter unsolved
```

**Expected Output**:
```
❌ error[E0113]: Constructor parameter unsolved
error[E0113]: Constructor parameter unsolved
   ┌─ input:3:1
 2 │ // Constructor parameter type cannot be inferred
 3 │ let make_pair = #42 in
 4 │ make_pair  // Constructor parameter unsolved
   │ ^^^^^^^^^ cannot infer type for constructor parameter
   │
   = note: Constructor parameter type is ambiguous
   = note: Type checker cannot determine the expected type
   💡 Constructor applications need enough context to infer types
   💡 The type checker needs more information
   🔧 Add a type annotation: (make_pair : Pair(Int, Int))
   🔧 Use the constructor in a context with a clear expected type
   📚 See: docs/core.md#constructors
```

#### 1.9 MatchRedundantCase
**File**: `examples/core/errors/exhaustiveness_checks/01_redundant_case.core.tao`

```gleam
// Redundant Match Case
// A case that can never be reached because earlier cases match all possibilities
match (42 : Int) {
  | x -> x      // Matches everything
  | y -> y      // Never reached - redundant!
}
```

**Expected Output**:
```
❌ error[E0202]: Redundant match case
error[E0202]: Redundant match case
   ┌─ input:4:3
 2 │ // A case that can never be reached because earlier cases match all possibilities
 3 │ match (42 : Int) {
 4 │   | x -> x      // Matches everything
   │     ^^^^^ this case matches all values
 5 │   | y -> y      // Never reached - redundant!
   │     ^^^^^ this case is never reached
   │
   = note: Case 2 is redundant because case 1 matches all possible values
   = note: The wildcard pattern (x) matches everything
   💡 Redundant cases indicate dead code that will never execute
   💡 This can hide bugs or indicate a misunderstanding of pattern matching
   🔧 Remove the redundant case
   🔧 Or reorder cases to put specific patterns before wildcards
   📚 See: docs/core.md#pattern-matching
```

#### 1.10 MatchMissingCase
**File**: `examples/core/errors/exhaustiveness_checks/02_missing_case.core.tao`

```gleam
// Missing Match Case
// Pattern match doesn't cover all possible cases
// (This requires an enum/ADT system)
// Example with Bool-like type
match True {
  | True -> 1
  // Missing: False case
}
```

**Expected Output**:
```
❌ error[E0201]: Missing match case
error[E0201]: Missing match case
   ┌─ input:2:1
 2 │ match True {
   │ ^^^^^^^^^^^^ pattern match is not exhaustive
 3 │   | True -> 1
   │     ^^^^^ this matches True
 4 │   // Missing: False case
   │
   = note: Pattern match doesn't cover all constructors
   = note: Missing case for constructor: False
   💡 Exhaustive pattern matching ensures all cases are handled
   💡 Missing cases can lead to runtime errors
   🔧 Add a case for False: | False -> ...
   🔧 Or add a wildcard case: | _ -> ... (less safe)
   📚 See: docs/core.md#exhaustiveness-checking
```

#### 1.11 ComptimePermissionDenied
**File**: `examples/core/errors/comptime/01_permission_denied.core.tao`

```gleam
// Comptime Permission Denied
// Trying to use a restricted operation at compile-time without permission
comptime {
  // This would require AllowRead permission
  // Example placeholder - actual implementation depends on comptime system
  read_file("secret.txt")
}
```

**Expected Output**:
```
❌ error[E0502]: Permission denied
error[E0502]: Permission denied
   ┌─ input:3:3
 2 │ // Trying to use a restricted operation at compile-time without permission
 3 │ comptime {
 4 │   read_file("secret.txt")
   │   ^^^^^^^^^^^^^^^^^^^^^^^ operation 'read_file' requires permission
   │
   = note: Comptime blocks require explicit permission for side effects
   = note: Required permission: AllowRead("secret.txt")
   = note: Granted permissions: none
   💡 Comptime code runs during compilation and needs permission for I/O
   💡 This prevents accidental side effects during type checking
   🔧 Add permission flag: --allow-read=secret.txt
   🔧 Or move the operation to runtime (outside comptime)
   📚 See: docs/core.md#comptime
```

#### 1.12 TODO
**File**: `examples/core/errors/type_errors/16_todo.core.tao`

```gleam
// TODO Error
// Placeholder for incomplete implementation
// This error is used during development
TODO("implement this function")
```

**Expected Output**:
```
❌ error[E9999]: TODO
error[E9999]: TODO
   ┌─ input:3:1
 2 │ // Placeholder for incomplete implementation
 3 │ TODO("implement this function")
   │ ^^^^ TODO: implement this function
   │
   = note: This is a placeholder for incomplete code
   = note: TODOs should be resolved before deployment
   💡 TODO errors mark incomplete implementations
   💡 They're useful during development but should be fixed
   🔧 Implement the missing functionality
   🔧 Replace TODO with actual implementation
   📚 See: docs/core.md#todo
```

---

### Phase 2: Improve Existing Error Messages (Priority: Medium)

#### 2.1 SyntaxError Enhancement

**Current**:
```
error[E0001]: Syntax error
  ┌─ input:0:0
  = note: Expected: valid alternative
  = note: Got: none
```

**Target**:
```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ file:line:col
   │
 N │ {{{
   │   ^ unexpected token
   │
   = note: Expected: expression, identifier, or keyword
   = note: Got: {
   💡 The parser encountered unexpected syntax
   💡 This often happens with typos or missing tokens
   🔧 Check for extra or missing brackets
   🔧 Ensure expressions are well-formed
   📚 See: docs/core.md#syntax
```

#### 2.2 TypeMismatch Enhancement

**Current**:
```
error[E0101]: Type mismatch
  ┌─ input:1:1
1 │ 42 : $Type
  = note: $Type(0) and Int are incompatible types
  = note: The expression produces $Type(0) but Int is expected here
```

**Target** (add visual type comparison):
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

---

### Phase 3: Code Snippet Improvements (Priority: Medium)

#### 3.1 Multi-Line Highlights

**Current**: Highlights only show on the error line

**Target**: Support multi-line error highlighting

```
error[E0101]: Type mismatch
   ┌─ file:2:1
 1 │ let id = 
 2 │   (x : $Type) -> 
   │   ^^^^^^^^^^^^ expected $Type, found Int
 3 │     x
   │     ^ this has type Int
   │
```

#### 3.2 Inline Type Information

**Current**: Types shown in notes only

**Target**: Show types inline with code

```
error[E0101]: Type mismatch
   ┌─ file:1:5
 1 │ 42 : $Type
   │      ━━━━━━ 💡 expected $Type, found Int
   │
```

#### 3.3 Suggestion Inline

**Current**: Suggestions in hints

**Target**: Show "did you mean?" inline

```
error[E0102]: Undefined variable
   ┌─ file:1:1
 1 │ rec(x)
   │ ^^^ did you mean 'rec'?
   │
```

---

### Phase 4: Visual Enhancements (Priority: Low)

#### 4.1 Color Coding

- **Red** (`❌`): Errors
- **Yellow** (`⚠️`): Warnings
- **Blue** (`💡`): Insights
- **Green** (`✅`): Success hints
- **Purple** (`🔧`): Fix suggestions

#### 4.2 Box Drawing Improvements

Use better Unicode box drawing:

```
╭─ error[E0101]: Type mismatch
│    ┌─ file:1:5
│  1 │ 42 : $Type
│    │      ^^^^^ expected $Type, found Int
│    │
│    = note: Types are incompatible
╰─
```

---

## Implementation Checklist

### Phase 1: Missing Examples (2 weeks)

- [ ] Create `08_pattern_mismatch.core.tao`
- [ ] Create `09_arity_mismatch.core.tao`
- [ ] Create `10_infinite_type.core.tao`
- [ ] Create `11_type_annotation_needed.core.tao`
- [ ] Create `12_record_missing_fields.core.tao`
- [ ] Create `13_field_not_found.core.tao`
- [ ] Create `14_dot_on_non_constructor.core.tao`
- [ ] Create `15_constructor_unsolved_param.core.tao`
- [ ] Create `01_redundant_case.core.tao` (exhaustiveness)
- [ ] Create `02_missing_case.core.tao` (exhaustiveness)
- [ ] Create `01_permission_denied.core.tao` (comptime)
- [ ] Create `16_todo.core.tao`

### Phase 2: Error Reporter Updates (2 weeks)

- [ ] Update `type_error_to_diagnostic` for all error types
- [ ] Add educational notes to all errors
- [ ] Add 3 hints per error type
- [ ] Implement type pretty-printing for all types
- [ ] Add inline labels for source snippets

### Phase 3: Source Snippet Improvements (1 week)

- [ ] Support multi-line highlights
- [ ] Add inline type information
- [ ] Implement "did you mean?" suggestions
- [ ] Improve pointer alignment

### Phase 4: Visual Polish (1 week)

- [ ] Add color support (optional, behind flag)
- [ ] Improve box drawing characters
- [ ] Test terminal compatibility

---

## Testing Strategy

1. **Generate golden files** for all new examples
2. **Run full test suite** to ensure no regressions
3. **Manual review** of error message quality
4. **User testing** with sample programs

---

## Success Metrics

| Metric | Target |
|--------|--------|
| Error coverage | 100% (20/20 error types) |
| Examples with golden files | 100% |
| Notes per error | 2+ |
| Hints per error | 3+ |
| Educational content | All errors explain WHY |
| Actionable fixes | All errors suggest HOW |
| Test coverage | 400+ tests |

---

## Related Documents

- **[05-error-message-improvements.md](./05-error-message-improvements.md)** - Previous improvements (Phases 1-3)
- **[03-examples-testing.md](./03-examples-testing.md)** - Examples testing spec
- **[../cli/04-check-run-commands.md](../cli/04-check-run-commands.md)** - CLI commands spec

---

## References

- [Rust Compiler Errors](https://github.com/rust-lang/rust/blob/master/compiler/rustc_errors/src)
- [Elm Compiler Errors](https://elm-lang.org/news/compiler-errors-for-humans)
- [TypeScript Errors](https://www.typescriptlang.org/docs/handbook/error.html)
- [Error Reporter Implementation](../../src/syntax/error_reporter.gleam)
- [Core Error Types](../../src/core/core.gleam)
