# Code Style Guide

> **Project**: Compiler Bootstrap
> **Language**: Gleam
> **Date**: March 2025

---

## Documentation Style

### Code Comments

**Principle**: Brief comments in code, detailed docs in `docs/`

```gleam
/// Bound variable (De Bruijn index). Index = distance to binder.
/// See docs/core.md for details.
Var(index: Int)
```

**DO**:
- Use `///` for public-facing documentation
- Keep inline comments brief
- Link to `docs/core.md` for detailed explanations
- Explain **why**, not just **what**

**DON'T**:
- Write multi-paragraph comments in code
- Duplicate documentation from `docs/`
- State the obvious (e.g., `// increment x` for `x = x + 1`)

---

## Module Headers

**Principle**: Minimal, consistent headers

```gleam
/// Module name
///
/// Brief description (1-2 sentences).
///
/// For detailed documentation see:
/// - [Link to docs](../docs/module.md)
import module

// ============================================================================
// Section Name
// ============================================================================
```

**Section headers**: Use consistent format with `// ============`

---

## Type Annotations

**Principle**: Annotate public APIs, infer locally

**DO annotate**:
- Public function signatures
- Module-level constants
- Complex types where inference fails

```gleam
/// Public function - annotate
pub fn infer(state: State, term: Term) -> #(Value, Type, State) {
  ...
}

/// Module constant - annotate  
pub const initial_state: State = State(...)
```

**DON'T annotate**:
- Private helper functions
- Let bindings with obvious types
- Test helper functions
- Lambda parameters in stubs

```gleam
/// Private helper - infer
fn helper(x) { x + 1 }

/// Test helper - infer  
fn make_term() { Term(Var(0), span) }

/// Stub formatter - use underscores for unused
fn stub_formatter(_ast, _prec) { formatter.text("") }
```

---

## Variable Naming

**Principle**: Clear names, underscore unused

**Prefix with `_`**:
- Unused function parameters
- Unused let bindings
- Span variables in patterns (when genuinely unused)
- Test variables that are bookkeeping

```gleam
/// Unused parameter - prefix with _
fn format_stub(_ast: Term, _prec: Int) -> Doc {
  formatter.text("<stub>")
}

/// Unused span in pattern
case term {
  Var(index, _span) -> ...  // span not used
}

/// Test bookkeeping
let #(_val, _s) = comptime_eval(state, term)
```

**DON'T prefix**:
- Variables that are actually used
- Loop counters that matter
- Error values that should be handled

---

## Error Messages

**Principle**: Clear, consistent, professional

**Format**:
```
<error type>: <message>
  <location hint>
```

**Examples**:
```
Parse error: expected identifier, got "42"
Type error: mismatch between Int and String
Runtime error: division by zero
File not found: path/to/file.tao
```

**DON'T**:
- Use emojis in error messages (✗ ✓)
- Be cryptic ("error 42")
- Blame the user ("you messed up")

---

## Function Style

**Principle**: Small, focused, composable

**DO**:
- One function = one responsibility
- Short parameter lists (< 4 params)
- Clear names that describe intent

**DON'T**:
- Functions > 50 lines (consider splitting)
- Boolean flags as parameters (use separate functions)
- Nested case expressions > 2 levels

---

## Pattern Matching

**Principle**: Exhaustive, clear, no redundancy

**DO**:
- Cover all cases explicitly
- Use `_` for genuine catch-alls
- Order patterns from specific to general

**DON'T**:
- Add unreachable `_` cases
- Duplicate patterns
- Use case when if/else suffices

---

## Imports

**Principle**: Only import what you use

**DO**:
- Remove unused imports
- Group imports: stdlib, project, local
- Use specific imports: `import list.{map, filter}`

**DON'T**:
- Import entire modules "just in case"
- Duplicate imports
- Import types you don't use

---

## Testing Style

**Principle**: Tests as documentation

**DO**:
- One assertion per test
- Descriptive test names
- Check structural equality
- Test error cases

```gleam
pub fn parse_number_single_digit_test() {
  parse_ok("42") |> should.equal(Int(42))
}

pub fn parse_add_left_associative_test() {
  // 1 + 2 + 3 should parse as (1 + 2) + 3
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}
```

**DON'T**:
- Multiple assertions per test
- Generic names (`test1`, `foo_test`)
- Test only success cases

See `test/README.md` for complete testing guide.

---

## Error Handling

**Principle**: Accumulate errors, don't panic

**DO**:
- Return `Result` or `ParseResult` with error list
- Continue checking after errors (IDE support)
- Include source locations in errors

**DON'T**:
- Use `panic` for user errors
- Stop at first error
- Return bare `Error` without context

---

## Naming Conventions

**Types**: `PascalCase`
```gleam
pub type TermData { ... }
pub type LiteralType { ... }
```

**Functions**: `snake_case`
```gleam
pub fn infer_type() { ... }
fn helper_function() { ... }
```

**Variables**: `snake_case`
```gleam
let current_state = ...
let term_data = ...
```

**Modules**: `snake_case` file names
```
src/core/core.gleam
src/syntax/grammar.gleam
```

---

## File Organization

**Principle**: Mirror directory structure

```
src/
├── core/
│   ├── core.gleam      # Core language
│   └── syntax.gleam    # Core parser/formatter
├── syntax/
│   ├── grammar.gleam   # Grammar DSL
│   ├── lexer.gleam     # Lexer
│   └── formatter.gleam # Formatter
└── tao/
    ├── ast.gleam       # Tao AST
    ├── desugar.gleam   # Tao → Core
    └── ...
```

**Test files**: Mirror src with `_test` suffix
```
test/
├── core/
│   ├── core_test.gleam
│   └── syntax_test.gleam
└── syntax/
    ├── grammar_test.gleam
    └── lexer_test.gleam
```

---

## Documentation Links

- [Testing Guide](../../test/README.md)
- [Core Language](../../docs/core.md)
- [Syntax Library](../../docs/syntax-library.md)
- [Tao Language](../../docs/plans/tao/01-overview.md)
- [Maintenance Plans](../../docs/plans/maintenance/01-overview.md)
