# CLI Golden File Format

> **Goal**: Define the exact format of golden files for CLI output
> **Status**: 📋 Planned
> **Date**: March 11, 2026

---

## Overview

Golden files (`.output.txt`) capture the exact output of running the CLI on an example file. They serve as:
1. **Regression tests** - Catch unintended output changes
2. **Living documentation** - Show what users actually see
3. **Expected behavior** - Define what the CLI should output

---

## File Naming

Golden files use the same base name as the source file:

```
examples/core/programs/add.core.tao       → add.output.txt
examples/core/terms/identity.core.tao     → identity.output.txt
examples/core/errors/type_errors/mismatch.core.tao → mismatch.output.txt
```

---

## Success Example Format

### Source
```gleam
// examples/core/programs/i32_add.core.tao
%call i32_add(1, 2)
```

### Golden File
```
3
```

**Characteristics**:
- Just the normalized term
- No headers or footers
- No "Result:" prefix
- Single line (for simple terms)

### Complex Term Example

### Source
```gleam
// examples/core/programs/function_composition.core.tao
let compose = f -> g -> x -> f(g(x)) in
compose(x -> x + 1)(x -> x * 2)
```

### Golden File
```
fn(x) { fn(x) { x * 2 + 1 } }
```

**Note**: The exact format depends on the `term_to_string` implementation.

---

## Error Example Format

### Source
```gleam
// examples/core/errors/type_errors/type_mismatch.core.tao
// This type annotation doesn't match the value's type.
1 : $Type
```

### Golden File
```
❌ error[E0101]: Type mismatch
error[E0101]: Type mismatch
   ┌─ examples/core/errors/type_errors/type_mismatch.core.tao:2:5
   │
 1 │ // This type annotation doesn't match the value's type.
 2 │ 1 : $Type
   │     ^~~~~ value is Int, but it should be $Type
 3 │ 
   │
   💡 The value 1 is of type Int
   💡 The type annotation expects a value of type $Type
   📝 note: Int and $Type are incompatible types
   🔧 help: Did you mean? `1 : Int`
-----------------------------------------------------------
1
```

**Characteristics**:
1. **Error header** with emoji and code
2. **Duplicate header** for terminal visibility
3. **Source span** with file path, line, column
4. **Source snippet** with context (2-3 lines before/after)
5. **Inline message** explaining the issue
6. **Hints** with emojis (💡, 📝, 🔧)
7. **Delimiter** (59 dashes)
8. **Result** (even with errors)

---

## Output Streams

### stderr (Errors)
```
❌ error[E0101]: Type mismatch
error[E0101]: Type mismatch
   ┌─ ...
   │
   │
   💡 ...
   📝 ...
   🔧 ...
```

### stdout (Result)
```
-----------------------------------------------------------
1
```

**Note**: Golden files combine both streams with errors first.

---

## Normalization Rules

For golden file comparison, normalize:

### DO Normalize
- ✅ Strip ANSI color codes
- ✅ Trim trailing whitespace per line
- ✅ Trim leading/trailing blank lines
- ✅ Normalize line endings (`\r\n` → `\n`)

### DO NOT Normalize
- ❌ Error codes (E0101, etc.)
- ❌ Line numbers
- ❌ Column numbers
- ❌ File paths
- ❌ Error messages
- ❌ Emoji characters
- ❌ Delimiter

### Rationale

**Normalize**: Things that vary by environment (colors, line endings, whitespace)

**Don't normalize**: Things that are part of the error semantics (codes, locations, messages)

---

## Multiple Errors

When multiple errors exist, show all of them:

```
❌ error[E0101]: Type mismatch
error[E0101]: Type mismatch
   ┌─ file:3:5
   │
 2 │ let x = 1
 3 │ let y = x : $Type
   │             ^^^^^
   │
   💡 ...
   🔧 ...

❌ error[E0102]: Undefined variable
error[E0102]: Undefined variable
   ┌─ file:5:10
   │
 4 │ let z = w
   │          ^
   │
   💡 ...
   🔧 ...
-----------------------------------------------------------
<result>
```

**Order**: Errors in order encountered (parse errors first, then type errors)

---

## Special Cases

### Parse Errors Only

When only parse errors exist (no type checking):

```
❌ error[E0001]: Syntax error
error[E0001]: Syntax error
   ┌─ file:1:5
   │
 1 │ {{{
   │     ^
   │
   = Expected: expression
   = Got: }
   │
   📝 note: ...
   🔧 help: ...
-----------------------------------------------------------
Err(Parse error)
```

**Note**: Result shows `Err(...)` for parse failures.

### Holes (Unsolved Metavariables)

```
❌ error[E0106]: Unsolved hole
error[E0106]: Unsolved hole
   ┌─ file:3:2
   │
 3 │ ?1
   │  ^
   │
   = note: Hole #1 was not solved
   💡 ...
   🔧 ...
-----------------------------------------------------------
?1
```

**Note**: Result shows the hole as-is.

---

## Updating Golden Files

### When to Update
- ✅ CLI output format changes intentionally
- ✅ Error messages improved
- ✅ New examples added
- ✅ Bug fixes that change output

### When NOT to Update
- ❌ To make tests pass (fix the code instead)
- ❌ Without reviewing the diff
- ❌ Without running full test suite

### Process
```bash
# 1. Make code changes
# 2. Regenerate golden files
./scripts/generate_golden_files.sh

# 3. Review changes
git diff examples/core/

# 4. Run tests
gleam test

# 5. Commit both code and golden file changes
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Testing overview
- **[03-examples-testing.md](./03-examples-testing.md)** - Examples testing spec
- **[04-cli-golden-files.md](./04-cli-golden-files.md)** - This file
- **[../cli/04-check-run-commands.md](../cli/04-check-run-commands.md)** - CLI commands spec

---

## References

- [Golden File Script](../../scripts/generate_golden_files.sh)
- [E2E Tests](../../test/core/examples_test.gleam)
- [Examples Directory](../../examples/core/)
