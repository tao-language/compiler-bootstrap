# Lessons Learned

> **Purpose**: Capture hard-won insights from building the Compiler Bootstrap project
> **Audience**: Future maintainers, contributors, and AI assistants
> **Status**: Living document - update as we learn

---

## Core Principles

### 1. Correctness Over Cleanliness

**Lesson**: A warning is a hint, not a command. Never apply fixes without understanding.

**Example**: We had 45 compiler warnings. After careful analysis:
- 20 were safe to fix (unused stub parameters)
- 1 was a false positive (`env` parameter passed recursively)
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

### 4. Recursive Parameters Look Unused

**Lesson**: Parameters passed recursively but not used in base cases trigger false positives.

**Example**:
```gleam
fn named_pattern_to_de_bruijn(pattern: NamedPattern, env: List(String)) -> Pattern {
  case pattern {
    NPAny(_span) -> PAny  // env not used - WARNING!
    NPAs(inner, name, _span) -> {
      let inner_db = named_pattern_to_de_bruijn(inner, env)  // ← env USED here!
      PAs(inner_db, name)
    }
  }
}
```

The `env` parameter is essential - it's threaded through recursive calls for nested patterns.

**Takeaway**: Compiler can't see that a parameter is used indirectly via recursion.

**Rule**: For recursive functions:
1. Check if parameter is used in ANY branch
2. Check if parameter is passed to recursive calls
3. If yes to both: it's a false positive, add comment explaining

---

### 5. Test Variables Need Context

**Lesson**: Test variables that look unused may be used in pattern matching.

**Example that broke**:
```gleam
// ❌ This broke the test:
let #(_val, _s) = c.comptime_eval(state, term)

// ✅ The actual usage:
let #(val, s) = c.comptime_eval(state, term)
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

### 6. Documentation Strategy Matters

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

### 7. Gleam Has No `if`

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

### 8. Compiler Warnings Have Blind Spots

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
3. **De Bruijn conversion needs environment threading** - `env` parameters are essential
4. **Stubs are intentional** - Formatter stubs returning placeholder text are placeholders, not bugs

### Testing

1. **One assertion per test** - Makes failures easier to debug
2. **Check structural equality** - Not just success/failure
3. **Test error cases** - Not just happy paths
4. **Read the full test** - Variables may be used in pattern matching

### Documentation

1. **Tests are documentation** - They should teach how to use the API
2. **Link, don't duplicate** - Code comments link to `docs/`, not repeat content
3. **Living documents** - Update lessons learned as you learn

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

### For Future Maintainers

1. Add your own lessons as you encounter them
2. Link to specific examples when possible
3. Note when lessons were learned (date/context)

---

## Related Documents

- **[src/README.md](../src/README.md)** - Code style guide
- **[test/README.md](../test/README.md)** - Testing guide
- **[docs/plans/maintenance/](./plans/maintenance/)** - Maintenance plans
- **[docs/core.md](./core.md)** - Core language specification

---

## Changelog

| Date | Lesson | Context |
|------|--------|---------|
| 2025-03 | Don't blindly fix warnings | Test variables broke test |
| 2025-03 | EMatch is essential | Looked unused but critical for NbE |
| 2025-03 | Type aliases can be semantic | `Type = Value` documents type theory |
| 2025-03 | Recursive parameters look unused | `env` parameter false positive |
| 2025-03 | Documentation belongs in docs/ | Verbose comments clutter code |
| 2025-03 | Gleam has no `if` | Language design choice |
