# Error Message Design

> **Goal**: Delightfully helpful error messages with excellent visual feedback for both humans and AI assistants
> **Status**: ✅ **Implemented for Core** - 373 tests passing
> **Date**: March 2025 (Updated: March 2026)

---

## Implementation Status

### ✅ Complete (Core Language)

**Module**: `src/core/error_formatter.gleam`, `src/syntax/error_reporter.gleam`

**Features**:
- ✅ Emoji-guided navigation (❌ error, 💡 tip, 📝 note, 🔧 help)
- ✅ Error codes (E0001, E0101-E0113, E0201-E0203, E0502, E9999)
- ✅ Source snippets with 3 lines of context
- ✅ Type information displayed in error messages
- ✅ Educational notes explaining WHY errors occur
- ✅ 3 actionable hints per error type
- ✅ Multi-span error support (type mismatches)
- ✅ Error accumulation (shows all errors, not just first)
- ✅ **373 tests passing**

**Error Types Covered**:
| Code | Error Type | Status |
|------|------------|--------|
| E0001 | SyntaxError | ✅ |
| E0101 | TypeMismatch | ✅ |
| E0102 | VarUndefined | ✅ |
| E0103 | NotAFunction | ✅ |
| E0104 | ArityMismatch | ✅ |
| E0105 | CtrUndefined | ✅ |
| E0106 | HoleUnsolved | ✅ |
| E0107 | InfiniteType | ✅ |
| E0108 | TypeAnnotationNeeded | ✅ |
| E0109 | RcdMissingFields | ✅ |
| E0110 | CtrUnsolvedParam | ✅ |
| E0111 | DotFieldNotFound | ✅ |
| E0112 | DotOnNonCtr | ✅ |
| E0113 | SpineMismatch | ✅ |
| E0201 | MatchMissingCase | ✅ |
| E0202 | MatchRedundantCase | ✅ |
| E0203 | PatternMismatch | ✅ |
| E0502 | ComptimePermissionDenied | ✅ |
| E9999 | TODO | ✅ |

---

## Core Principles

### 1. Instant Visual Recognition

**Every error should be instantly recognizable**:

```
❌ error[E0101]: Type mismatch
   ┌─ src/main.core.tao:5:10
   │
 5 │ let x: %I32 = "hello"
   │          ━━┷┷┷┷┷┷━ expected %I32, found String
   │
   💡 expected because this is %I32
   📝 note: %I32 and String are incompatible types
   🔧 help: Did you mean to use a number? e.g., `let x: %I32 = 42`
```

---

### 2. Emoji-Guided Navigation

| Emoji | Meaning | Usage |
|-------|---------|-------|
| ❌ | Error | Critical issues that prevent compilation |
| ⚠️ | Warning | Issues that don't prevent compilation but should be fixed |
| ℹ️ | Info | Additional information |
| 💡 | Tip | Explanation of why something is wrong |
| 📝 | Note | Additional context or facts |
| 🔧 | Help | Suggested fix with code example |
| 📚 | Reference | Link to documentation |
| 🎯 | Target | Points to exact location |
| 🔍 | Context | Shows related code or definitions |
| ✅ | Success | Shows correct version |

---

### 3. Error Message Structure

**Every error message should answer three questions**:

1. **What went wrong?** - Clear description of the problem
2. **Where is it?** - Precise source location with visual snippet
3. **How do I fix it?** - Actionable suggestion or hint

**Standard Format**:
```
❌ error[E####]: Error Category
   ┌─ file:line:col
   │
 N │ ... context line -3
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
   🔧 Fix suggestion 3
```

---

### 4. Color Coding (Terminal/IDE)

| Element | Color | Purpose |
|---------|-------|---------|
| ❌ Error | Bright Red | Immediate attention |
| ⚠️ Warning | Yellow/Orange | Caution |
| ℹ️ Info | Blue | Information |
| 🔧 Help | Green | Actionable suggestion |
| 📝 Note | Gray | Context |
| Code | Cyan | Code snippets |
| File path | White | Location |

---

## Error Message Examples

### Syntax Errors

#### E0001: Unexpected Token

```core
// ❌ Wrong
let x = 5 +
```

```
❌ error[E0001]: Unexpected token
   ┌─ src/main.core.tao:3:13
   │
 3 │ let x = 5 +
   │             ┷ unexpected end of input
   │
   💡 expected an expression after `+`
   🔧 help: provide the right-hand side:
      │
    3 │ let x = 5 + 10
      │             ++
      │
   🔧 help: or remove the operator:
      │
    3 │ let x = 5
      │         ~
      │
```

---

#### E0002: Missing Closing Brace

```core
// ❌ Wrong
fn add(a: %I32, b: %I32) -> %I32 {
  a + b
```

```
❌ error[E0002]: Missing closing brace
   ┌─ src/main.core.tao:1:32
   │
 1 │ fn add(a: %I32, b: %I32) -> %I32 {
   │                                ┚ unclosed brace
   │
 2 │   a + b
   │
   💡 this opening brace `{` is never closed
   🔧 help: add a closing brace:
      │
    3 │ }
      │
   📝 note: every opening brace `{` needs a matching closing brace `}`
```

---

### Type Errors

#### E0101: Type Mismatch

```core
// ❌ Wrong
let x: %I32 = "hello"
```

```
❌ error[E0101]: Type mismatch
   ┌─ src/main.core.tao:3:14
   │
 3 │ let x: %I32 = "hello"
   │     ┬      ━━━┷━━━
   │     │      │
   │     │      expected %I32, found String
   │     expected because this is %I32
   │
   📝 note: %I32 and String are incompatible types
   🔧 help: use a number instead:
      │
    3 │ let x: %I32 = 42
      │              ~~
      │
   🔧 help: or change the type annotation:
      │
    3 │ let x: String = "hello"
      │         ~~~~~~
      │
   📚 reference: docs/core.md#types
```

---

#### E0102: Undefined Variable

```core
// ❌ Wrong
fn increment() -> %I32 {
  count + 1
}
```

```
❌ error[E0102]: Undefined variable
   ┌─ src/main.core.tao:4:3
   │
 4 │   count + 1
   │   ━━┷━━
   │   │
   │   this variable is not defined
   │
   📝 note: `count` is not defined in this scope
   🔍 context: function `increment` defined at line 3
   🔧 help: did you forget to define it?
      │
    3 │ fn increment() -> %I32 {
    4 │   let count = 0
      │   +++++++++++++
    5 │   count + 1
      │
   🔧 help: or pass it as a parameter:
      │
    3 │ fn increment(count: %I32) -> %I32 {
      │              ~~~~~~~~~~
      │
   📚 reference: docs/core.md#variables
```

---

#### E0103: Not a Function

```core
// ❌ Wrong
let x = 5
let y = x(10)
```

```
❌ error[E0103]: Cannot call non-function value
   ┌─ src/main.core.tao:4:11
   │
 4 │ let y = x(10)
   │           ━┛━ cannot call value of type %I32
   │
   📝 note: `x` has type %I32, which is not callable
   💡 only functions can be called with parentheses
   🔧 help: did you mean to use a different variable?
   🔧 help: or define `x` as a function:
      │
    2 │ let x = fn(n: %I32) -> %I32 { n * 2 }
      │         ++++++++++++++++++++++++++
      │
   📚 reference: docs/core.md#functions
```

---

#### E0104: Arity Mismatch

```core
// ❌ Wrong
fn add(a: %I32, b: %I32) -> %I32 {
  a + b
}

let result = add(5)
```

```
❌ error[E0104]: Wrong number of arguments
   ┌─ src/main.core.tao:6:16
   │
 6 │ let result = add(5)
   │              ━━┛━
   │              │
   │              expected 2 arguments, got 1
   │
   📝 note: function signature is `fn add(a: %I32, b: %I32) -> %I32`
   🔍 context: function defined at line 3
   🔧 help: provide the missing argument:
      │
    6 │ let result = add(5, 10)
      │                    ++++
      │
   📚 reference: docs/core.md#functions#arguments
```

---

#### E0105: Constructor Undefined

```core
// ❌ Wrong
let x = #Just(5)
```

```
❌ error[E0105]: Constructor not found
   ┌─ src/main.core.tao:3:9
   │
 3 │ let x = #Just(5)
   │         ━━┛━ constructor not found
   │
   📝 note: `#Just` is not a defined constructor
   🔍 available constructors:
   │
   │   ✅ #True
   │   ✅ #False
   │   ✅ #Some
   │   ✅ #None
   │
   💡 you might be thinking of `#Some` from the Option type
   🔧 help: use the correct constructor:
      │
    3 │ let x = #Some(5)
      │         ~~~~
      │
   📚 reference: docs/core.md#constructors
```

---

#### E0106: Unsolved Hole

```core
// ❌ Wrong
fn incomplete(x) -> ? {
  ?
}
```

```
❌ error[E0106]: Unsolved hole
   ┌─ src/main.core.tao:3:3
   │
 3 │   ?
   │   ┷ hole not solved
   │
   📝 note: hole #1 was not solved during type checking
   📝 note: holes are development placeholders that must be replaced
   💡 holes are placeholders that must be inferred or provided
   🔧 help: provide an implementation:
      │
    3 │   x  // return the input
      │   ~
      │
   🔧 help: or use a typed hole:
      │
    3 │   ?(x: %I32)
      │
   📚 reference: docs/core.md#holes
```

---

### Pattern Matching Errors

#### E0201: Match Missing Case

```core
// ❌ Wrong
fn unwrap(result) -> {
  %match result {
    | #Ok(x) -> x
  }
}
```

```
❌ error[E0201]: Pattern match not exhaustive
   ┌─ src/main.core.tao:6:3
   │
 6 │ ╭   %match result {
 7 │ │     | #Ok(x) -> x
 8 │ │   }
   │ ╰───┚ not all cases are covered
   │
   📝 note: type has 2 constructors
   📝 note: you've covered 1 constructor: `#Ok`
   🔍 missing constructors:
   │
   │   ❌ #Err
   │
   🔧 help: add the missing case:
      │
    8 │     | #Err(e) -> panic("unwrap called on Err")
      │
   🔧 help: or add a wildcard case:
      │
    8 │     | _ -> panic("unhandled case")
      │
   📚 reference: docs/core.md#pattern-matching
```

---

#### E0202: Match Redundant Case

```core
// ❌ Wrong
fn process(m) -> {
  %match m {
    | #Some(x) if x > 0 -> x
    | #Some(x) if x > 0 -> 0  // Redundant!
    | _ -> 0
  }
}
```

```
⚠️ warning[W0202]: Redundant pattern
   ┌─ src/main.core.tao:7:5
   │
 7 │     | #Some(x) if x > 0 -> 0  // Redundant!
   │       ━━━━━━━━━━━━━━ this case is already handled
   │
   📝 note: this pattern matches the same values as a previous case
   🔍 previous case:
   │
 6 │     | #Some(x) if x > 0 -> x
   │       ━━━━━━━━━━━━━━
   │
   🔧 help: remove the redundant case, or use a different guard:
      │
    7 │     | #Some(x) if x <= 0 -> 0
      │                ~~~~~~
      │
   💡 redundant cases are safe to remove and won't change behavior
```

---

### Comptime Errors

#### E0502: Permission Denied

```core
// ❌ Wrong
@permission(Read("/etc/passwd"))
fn read_config() -> {
  comptime {
    read_file("/etc/shadow")  // Not allowed!
  }
}
```

```
❌ error[E0502]: Permission denied
   ┌─ src/main.core.tao:5:5
   │
 5 │     read_file("/etc/shadow")
   │     ━━━━━━━━━━━━━━━━━━━━━━━━ this operation requires Write("/etc/shadow")
   │
   📝 note: comptime code requires explicit permissions
   🔍 current permissions:
   │
   │   ✅ Read("/etc/passwd")
   │   ❌ Write("/etc/shadow")  ← missing!
   │
   🔧 help: add the required permission:
      │
    2 │ @permission(Read("/etc/passwd"), Write("/etc/shadow"))
      │                                +++++++++++++++++++++++
      │
   🔧 help: or use a file you have permission for:
      │
    5 │     read_file("/etc/passwd")
      │                 ~~~~~~~~~~~
      │
   📚 reference: docs/core.md#comptime
```

---

## Error Code Reference

| Code | Severity | Category | Description |
|------|----------|----------|-------------|
| E0001 | ❌ Error | Syntax | Unexpected token |
| E0002 | ❌ Error | Syntax | Missing closing brace |
| E0003 | ❌ Error | Syntax | Invalid identifier |
| E0101 | ❌ Error | Type | Type mismatch |
| E0102 | ❌ Error | Type | Undefined variable |
| E0103 | ❌ Error | Type | Not a function |
| E0104 | ❌ Error | Type | Arity mismatch |
| E0105 | ❌ Error | Type | Constructor undefined |
| E0106 | ❌ Error | Type | Unsolved hole |
| E0107 | ❌ Error | Type | Infinite type |
| E0108 | ❌ Error | Type | Type annotation needed |
| E0109 | ❌ Error | Type | Record missing fields |
| E0110 | ❌ Error | Type | Constructor unsolved param |
| E0111 | ❌ Error | Type | Dot field not found |
| E0112 | ❌ Error | Type | Dot on non-constructor |
| E0113 | ❌ Error | Type | Spine mismatch |
| E0201 | ❌ Error | Pattern | Match missing case |
| E0202 | ⚠️ Warning | Pattern | Match redundant case |
| E0203 | ❌ Error | Pattern | Invalid pattern |
| E0502 | ❌ Error | Comptime | Permission denied |
| E9999 | ❌ Error | General | TODO / Unknown error |

---

## Implementation Details

### Module Structure

```
src/
├── core/
│   └── error_formatter.gleam  # Core error to diagnostic conversion
└── syntax/
    ├── error_reporter.gleam   # Error reporting with source snippets
    └── source_snippet.gleam   # Source snippet formatting
```

### Diagnostic Type

```gleam
pub type Diagnostic {
  Diagnostic(
    code: String,           // e.g., "E0101"
    severity: Severity,     // Error, Warning, Info
    message: String,        // Short description
    location: Location,     // File, line, column
    highlights: List(Highlight),  // Pointers in source
    notes: List(String),    // Additional context
    hints: List(String),    // Actionable suggestions
  )
}
```

### Error Flow

```
Parse Error / Type Error
         ↓
error_reporter.parse_error_to_diagnostic()
         ↓
source_snippet.format_diagnostic()
         ↓
CLI Output (with emojis, colors)
```

---

## Testing

All error messages are tested via golden file comparison:

```bash
# Run all tests
gleam test

# Result: 373 tests passing ✅
```

**Golden Files**:
- Location: `examples/core/errors/**/*.output.txt`
- Format: Exact CLI output
- Update: `./scripts/generate_golden_files.sh`

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Error reporting overview
- **[02-error-types.md](./02-error-types.md)** - Error type specifications
- **[03-source-snippets.md](./03-source-snippets.md)** - Source snippet formatting
- **[04-cli-integration.md](./04-cli-integration.md)** - CLI integration
- **[05-parse-error-panic-fix.md](./05-parse-error-panic-fix.md)** - Parse error panic fix
- **[../testing/01-overview.md](../testing/01-overview.md)** - Testing overview
- **[../testing/05-error-message-improvements.md](../testing/05-error-message-improvements.md)** - Error improvements (complete)
- **[../../docs/cli.md](../../docs/cli.md)** - CLI documentation
- **[../../docs/core-syntax.md](../../docs/core-syntax.md)** - Core syntax reference

---

## References

- [Error Reporter Implementation](../../src/syntax/error_reporter.gleam)
- [Core Error Formatter](../../src/core/error_formatter.gleam)
- [Source Snippet](../../src/syntax/source_snippet.gleam)
- [Rust Compiler Errors](https://github.com/rust-lang/rust/blob/master/compiler/rustc_errors/src)
- [Elm Compiler Errors](https://elm-lang.org/news/compiler-errors-for-humans)
- [TypeScript Errors](https://www.typescriptlang.org/docs/handbook/error.html)
