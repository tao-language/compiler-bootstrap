# Lessons Learned

> **Purpose**: Capture hard-won insights from building the Compiler Bootstrap project
> **Audience**: Future maintainers, contributors, and AI assistants
> **Status**: Living document - update as we learn
> **Last Updated**: March 2025 (Warning cleanup: 45 → 0)

---

## Core Principles

### 1. Correctness Over Cleanliness

**Lesson**: A warning is a hint, not a command. Never apply fixes without understanding.

**Example**: We had 45 compiler warnings. After careful analysis:
- 20 were safe to fix (unused stub parameters)
- 2 were genuinely unused parameters (removed entirely)
- 5 test variables looked unused but were actually used in case expressions
- **Attempting to "fix" test variables broke a test**

**Takeaway**: 
```gleam
// ❌ Wrong: Blindly applying warning
let #(_val, _s) = comptime_eval(state, term)  // Broke test - val used below!

// ✅ Right: Understand first, then decide
let #(val, s) = comptime_eval(state, term)
case val {
  VCall(name, args) -> { ... }  // val IS used!
}
```

**Rule**: If a warning seems suspicious, read 10 lines before and after before changing anything.

---

### 2. Some "Dead Code" is Essential

**Lesson**: What looks unused may be critical for correctness.

**Example**: `EMatch` constructor in `Elim` type
```gleam
pub type Elim {
  EDot(name: String)
  EApp(arg: Value)
  EMatch(env: Env, motive: Value, cases: List(Case))  // ← Looks unused!
}
```

The compiler warned about unused code, but `EMatch` is **ESSENTIAL** for normalization by evaluation. It stores pending match operations on neutral terms.

**Takeaway**: Core algorithm components often look "unused" because they're part of deferred computation.

**Rule**: Before removing "unused" code in compilers/interpreters:
1. Understand the evaluation strategy
2. Check for deferred computation patterns
3. Ask: "Is this part of a spine/spine-like structure?"

---

### 3. Type Aliases Can Be Semantic

**Lesson**: `pub type Type = Value` is not redundancy - it's documenting dependent type theory.

**Example**:
```gleam
pub type Value = ...
pub type Type = Value  // ← Looks redundant!
```

In dependent type theory, types ARE values (they inhabit universes). This alias documents that fundamental property.

**Takeaway**: In PL implementation, type aliases often encode semantic equivalences, not just convenience.

**Rule**: Before removing type aliases:
1. Check if it documents a semantic equivalence
2. Look for comments explaining the relationship
3. Ask: "Is this encoding a type theory concept?"

---

### 4. Read The Full Warning Message

**Lesson**: Gleam's warnings are smarter than they first appear.

**Example**: We initially thought `env` parameter was essential:
```gleam
// ❌ Wrong analysis - added comment but kept parameter
/// Note: env is passed recursively for nested patterns (not used in base cases)
fn named_pattern_to_de_bruijn(pattern: NamedPattern, env: List(String)) -> Pattern {
```

But the full warning said:
```
This argument is passed to the function when recursing, but it's never used
for anything.
```

**Key insight**: "Never used for anything" means it's not consulted in ANY branch - not even passed to other functions. It's just being passed to itself pointlessly.

**Takeaway**: There's a difference between:
- **False positive**: Parameter used in some branches (like `env` in pattern matching with binders)
- **Genuinely unused**: Parameter passed recursively but never consulted anywhere

**Rule**: Read the ENTIRE warning message. Gleam distinguishes between:
- "This variable is never used" → Safe to prefix with `_`
- "This argument is passed when recursing, but never used for anything" → Safe to REMOVE entirely

---

### 5. Unreachable Code After Panic Indicates a Bug

**Lesson**: Unreachable code warnings after `panic` often indicate contradictory logic.

**Example**:
```gleam
// ❌ Wrong: Both panicking AND returning a value
Error(_) ->
  ParseResult(ast: panic as "No start rule", errors: [
    ParseError(position: 0, expected: "start rule", got: "none"),
  ])
```

This tries to both panic and return a `ParseResult` - the return is unreachable.

**Fix**:
```gleam
// ✅ Right: Panic is the return value
let rule = case dict.get(grammar.rules, grammar.start) {
  Ok(rule) -> rule
  Error(_) -> panic as "Grammar missing start rule"
}
```

**Takeaway**: Unreachable code after panic means you're trying to do two incompatible things.

**Rule**: When you see "unreachable code after panic":
1. Check if you're both panicking and returning
2. Restructure so panic IS the return value of that branch
3. Don't wrap panic in constructors

---

### 6. Test Variables Need Context

**Lesson**: Test variables that look unused may be used in pattern matching.

**Example that broke**:
```gleam
// ❌ This broke the test:
let #(_val, _s) = comptime_eval(state, term)  // val used below!

// ✅ The actual usage:
let #(val, s) = comptime_eval(state, term)
case val {  // ← val used here!
  VCall(name, args) -> { ... }
}
```

**Takeaway**: Gleam's pattern matching means variables can be "used" in ways that aren't obvious from the binding site.

**Rule**: For test variables:
1. Read the entire test function
2. Check for `case` expressions using the variable
3. Check for subsequent function calls using the variable
4. Only prefix with `_` if genuinely unused throughout

---

### 7. Documentation Strategy Matters

**Lesson**: Verbose inline comments clutter code; separate detailed docs are better.

**Before** (too verbose):
```gleam
/// Bound variable using De Bruijn index
/// 
/// Index represents DISTANCE to binding site (counting outward):
/// - `Var(0)` = innermost binder (λx. x)
/// - `Var(1)` = next outer binder (λx. λy. x)
/// 
/// Advantage: No variable capture during substitution.
/// Disadvantage: Must shift indices when moving terms.
Var(index: Int)
```

**After** (clean + link):
```gleam
/// Bound variable (De Bruijn index). Index = distance to binder.
/// See docs/core.md for details.
Var(index: Int)
```

**Takeaway**: Code should be scannable; details belong in dedicated docs.

**Rule**: 
- Inline comments: 1-2 lines max, explain WHY not WHAT
- Complex topics: Link to `docs/` for full explanation
- Algorithms: Comment the invariant, not every step

---

### 8. Gleam Has No `if`

**Lesson**: Gleam only has `case` expressions - this is by design for explicit pattern matching.

**Wrong assumption**:
```gleam
// ❌ This doesn't exist in Gleam:
if condition {
  do_something()
}
```

**Correct**:
```gleam
// ✅ Gleam uses case for everything:
case condition {
  True -> do_something()
  False -> Nil
}
```

**Takeaway**: Don't try to apply patterns from other languages blindly.

**Rule**: When learning Gleam:
1. Read the language tour first
2. Understand what constructs exist (and don't exist)
3. Don't assume features from similar languages

---

### 9. Compiler Warnings Have Blind Spots

**Lesson**: The compiler can't see:
- Indirect usage (via recursion, higher-order functions)
- Usage in pattern matching (case expressions)
- Semantic importance (algorithm correctness)

**Takeaway**: Warnings are suggestions from a dumb (but helpful) assistant.

**Rule**: For each warning:
1. **Understand** why it's triggered
2. **Verify** it's genuinely an issue
3. **Decide** based on context, not blindly

---

## Project-Specific Lessons

### Parser/Compiler Implementation

1. **Spine structures store deferred computation** - Don't remove "unused" spine constructors
2. **Neutral terms are critical for NbE** - They represent "stuck" computations
3. **De Bruijn conversion needs environment threading** - `env` parameters are essential (when actually used!)
4. **Stubs are intentional** - Formatter stubs returning placeholder text are placeholders, not bugs
5. **Pattern formatting doesn't need bindings** - Patterns don't bind variables, only match them
6. **Warning cleanup is achievable** - We went from 45 warnings to 0!

### Testing

1. **One assertion per test** - Makes failures easier to debug
2. **Check structural equality** - Not just success/failure
3. **Test error cases** - Not just happy paths
4. **Read the full test** - Variables may be used in pattern matching

### Documentation

1. **Tests are documentation** - They should teach how to use the API
2. **Link, don't duplicate** - Code comments link to `docs/`, not repeat content
3. **Living documents** - Update lessons learned as you learn
4. **Document false positives** - If a warning is genuinely a false positive, comment why

### Warning Cleanup

1. **Read the full warning** - Gleam provides context about WHY something is unused
2. **Distinguish false positives from real issues** - Some parameters really are useless
3. **Unreachable code after panic = bug** - Indicates contradictory logic
4. **Measure progress** - Track warning count reduction (we went from 45 to 0!)

---

## How to Use This Document

### For Contributors

1. Read this before making "cleanup" changes
2. When in doubt, ask rather than assume
3. Update this document when you learn something new

### For AI Assistants

1. Reference this document when suggesting changes
2. Be extra cautious with "unused" code in compilers
3. Always read context before applying fixes
4. Read the FULL warning message, not just the first line

### For Future Maintainers

1. Add your own lessons as you encounter them
2. Link to specific examples when possible
3. Note when lessons were learned (date/context)

---

## Related Documents

- **[src/README.md](../src/README.md)** - Code style guide
- **[test/README.md](../test/README.md)** - Testing guide
- **[docs/plans/maintenance/](./plans/maintenance/)** - Maintenance plans
- **[docs/plans/maintenance/04-unused-variable-safety-review.md](./plans/maintenance/04-unused-variable-safety-review.md)** - Safety-critical review
- **[docs/plans/maintenance/03-warning-analysis.md](./plans/maintenance/03-warning-analysis.md)** - Warning categorization
- **[docs/plans/maintenance/05-warning-cleanup-complete.md](./plans/maintenance/05-warning-cleanup-complete.md)** - Final cleanup report

---

## Changelog

| Date | Lesson | Context |
|------|--------|---------|
| 2026-03 | Gleam has no `string.find` | Implemented custom substring search |
| 2026-03 | Reserved keywords matter | `test` is reserved - use `test_item` |
| 2026-03 | Constructor imports needed | Pattern match needs `Skip` not `type Skip` |
| 2026-03 | Record field access limits | Destructure before case arm returns |
| 2026-03 | Duplicate imports error | Combine into single import line |
| 2026-03 | Option vs Result unwrap | Different signatures, check docs |
| 2025-03 | Read full warning message | `env` parameter looked essential but was genuinely unused |
| 2025-03 | Unreachable code = bug | Panic + return is contradictory |
| 2025-03 | Warning cleanup complete | 45 → 0 warnings (100% reduction) |
| 2025-03 | Don't blindly fix warnings | Test variables broke test |
| 2025-03 | EMatch is essential | Looked unused but critical for NbE |
| 2025-03 | Type aliases can be semantic | `Type = Value` documents type theory |
| 2025-03 | Documentation belongs in docs/ | Verbose comments clutter code |
| 2025-03 | Gleam has no `if` | Language design choice |

---

## Gleam-Specific Implementation Lessons (2026)

### 1. String API Limitations

**Lesson**: `gleam/string` lacks common functions like `find` and `drop_left`.

**Example**:
```gleam
// ❌ Doesn't exist:
string.find(text, substring)
string.drop_left(text, 2)

// ✅ Workaround:
fn find_substring(text: String, substring: String) -> Option(Int) {
  find_index(text, substring, 0)
}

fn find_index(text: String, substring: String, offset: Int) -> Option(Int) {
  case string.starts_with(text, substring) {
    True -> Some(offset)
    False -> find_index(string.drop_start(text, 1), substring, offset + 1)
  }
}
```

**Takeaway**: Check stdlib API before assuming functions exist. Implement helpers when needed.

---

### 2. Reserved Keywords

**Lesson**: `test` is a reserved keyword in Gleam (used for test blocks).

**Example**:
```gleam
// ❌ Syntax error:
list.filter(tests, fn(test) { test.name == "foo" })

// ✅ Works:
list.filter(tests, fn(test_item) { test_item.name == "foo" })
```

**Takeaway**: When variable names conflict with Gleam keywords, use descriptive alternatives.

---

### 3. Constructor Imports for Pattern Matching

**Lesson**: To pattern match on custom type variants, import constructors unqualified.

**Example**:
```gleam
// ❌ Can't pattern match:
import tao/test_parser.{type Annotation}
case ann {
  Annotation.Skip(_) -> ...  // Error: Annotation not in scope
}

// ✅ Works:
import tao/test_parser.{type Annotation, Skip, Timeout, Group}
case ann {
  Skip(_) -> ...  // Works!
}
```

**Takeaway**: Import both `type TypeName` and constructor names for pattern matching.

---

### 4. Record Field Access in Case Arms

**Lesson**: Can't use `acc.field` expressions directly in case arm return values.

**Example**:
```gleam
// ❌ Syntax error:
case ann {
  Skip(_) -> AnnotationCounts(acc.total + 1, acc.skip + 1, ...)
}

// ✅ Works:
case ann {
  Skip(_) -> {
    let AnnotationCounts(total, skip, timeout, group, io) = acc
    AnnotationCounts(total + 1, skip + 1, timeout, group, io)
  }
}
```

**Takeaway**: Destructure records before using fields in case expressions.

---

### 5. Duplicate Import Errors

**Lesson**: Can't import same module twice, even for different things.

**Example**:
```gleam
// ❌ Duplicate import error:
import gleam/option.{Some, None}
import gleam/option.{type Option}

// ✅ Works:
import gleam/option.{Some, None, type Option}
```

**Takeaway**: Combine all imports from same module into one line.

---

### 6. Option vs Result for unwrap

**Lesson**: `option.unwrap` and `result.unwrap` have different signatures.

**Example**:
```gleam
// ❌ Wrong:
first_span |> result.unwrap(default)  // result.unwrap expects Error type
first_span |> option.unwrap(default)  // Wrong argument order

// ✅ Correct:
option.unwrap(first_span, default)  // Function form, not pipe
```

**Takeaway**: Check function signatures - some use pipe, some don't.
