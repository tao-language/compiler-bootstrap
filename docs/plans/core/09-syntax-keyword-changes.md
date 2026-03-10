# Syntax Keyword Changes

> **Goal**: Replace bare keywords with `%` prefixed keywords to avoid namespace conflicts
> **Status**: ✅ Implemented - Lexer and grammar updated
> **Priority**: High
> **Date**: March 2025

---

## Implementation Status

### ✅ Complete

**Lexer Changes:**
- ✅ `%match` → `PercentMatch` token
- ✅ `%call` → `PercentCall` token
- ✅ `%comptime` → `PercentComptime` token
- ✅ `%` → `Percent` token (for other uses)
- ✅ `~` → `Tilde` token
- ✅ `|` → `Pipe` token
- ✅ `?` → `Question` token (already exists for holes, will be reused for guards)

**Grammar Changes:**
- ✅ Match expression: `%match arg ~ motive { | pat -> body }`
- ✅ Call expression: `%call name(args)`
- ✅ Comptime expression: `%comptime term`
- ✅ Cases: `| pat -> body` (single case supported, multiple cases pending)
- ⏳ Guard syntax: `| pat ? guard -> body` (documented, implementation pending)

**Formatter Changes:**
- ✅ Match formatting with new syntax
- ✅ Call formatting with new syntax
- ✅ Comptime formatting with new syntax

### ⏳ Testing

- ✅ Existing tests pass (401 tests)
- ⏳ New syntax examples need verification

---

## Motivation

### Current Problem

Bare keywords (`match`, `call`, `comptime`) conflict with variable names:

```gleam
// Is this a match expression or a variable named "match"?
match -> match(match)

// Shadowing keywords is confusing
let match = 42
match(match)  // What does this mean?
```

### Solution

Use `%` prefix for all keywords, consistent with existing syntax:

| Prefix | Usage | Example |
|--------|-------|---------|
| `$` | Types | `$Type`, `$I32` |
| `#` | Constructors | `#True`, `#Some(x)` |
| `%` | Keywords | `%match`, `%call`, `%comptime` |

---

## Syntax Changes

### 1. Pattern Matching

**Old Syntax**:
```gleam
match value with motive returning
  pattern -> body,
  pattern -> body
```

**New Syntax**:
```gleam
%match value ~ motive {
  | pattern ? guard -> body
  | pattern -> body
}
```

**Changes**:
- `match` → `%match`
- `with` → `~` (tilde separator)
- `returning` → removed (use `{` directly)
- Cases enclosed in `{ }` instead of comma-separated
- Each case starts with `|` (pipe)
- Optional `? guard` after pattern (uses `?` instead of `if` keyword)

**Benefits**:
- No keyword conflicts (`if` is not a keyword)
- Clearer visual structure with `{ }` and `|`
- Guard support built-in with concise `?` syntax
- Consistent with pattern matching in other languages (Rust, OCaml, Haskell)

### 2. Built-in Call

**Old Syntax**:
```gleam
call prim.add(x, y)
```

**New Syntax**:
```gleam
%call prim.add(x, y)
```

**Changes**:
- `call` → `%call`

**Benefits**:
- `call` can be used as variable name
- Consistent with other keywords

### 3. Comptime

**Old Syntax**:
```gleam
comptime { term }
```

**New Syntax**:
```glem
%comptime term
```

**Changes**:
- `comptime` → `%comptime`
- Braces optional (only if needed for grouping)

**Benefits**:
- `comptime` can be used as variable name
- Simpler syntax

---

## Grammar Changes

### Token Changes

**Add Token**:
```gleam
"%" -> "Percent"
```

### Match Expression Grammar

**Old**:
```gleam
|> grammar.rule("Match", [
  grammar.alt(
    grammar.seq([
      grammar.keyword_pattern("match"),
      grammar.ref("Expr"),
      grammar.keyword_pattern("with"),
      grammar.ref("Expr"),
      grammar.keyword_pattern("returning"),
      grammar.ref("Cases"),
    ]),
    make_match,
    fn(v, p) { format_value(v, p) },
  ),
])

|> grammar.rule("Cases", [
  grammar.alt(
    grammar.seq([
      grammar.ref("Pattern"),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
    ]),
    make_single_case,
    fn(_, _) { formatter.text("") },
  ),
  grammar.alt(
    grammar.seq([
      grammar.ref("Pattern"),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
      grammar.token_pattern("Comma"),
      grammar.ref("Cases"),
    ]),
    make_case_cons,
    fn(_, _) { formatter.text("") },
  ),
])
```

**New**:
```gleam
|> grammar.rule("Match", [
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Percent"),
      grammar.token_pattern("Ident"),  // "match"
      grammar.ref("Expr"),
      grammar.token_pattern("Tilde"),
      grammar.ref("Expr"),
      grammar.token_pattern("LBrace"),
      grammar.ref("Cases"),
      grammar.token_pattern("RBrace"),
    ]),
    make_match,
    fn(v, p) { format_value(v, p) },
  ),
])

|> grammar.rule("Cases", [
  // Single case: | pattern ? guard -> body
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Pipe"),
      grammar.ref("Pattern"),
      grammar.opt(grammar.seq([  // Optional guard
        grammar.token_pattern("Question"),
        grammar.ref("Expr"),
      ])),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
    ]),
    make_single_case,
    fn(_, _) { formatter.text("") },
  ),
  // Multiple cases
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Pipe"),
      grammar.ref("Pattern"),
      grammar.opt(grammar.seq([
        grammar.token_pattern("Question"),
        grammar.ref("Expr"),
      ])),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
      grammar.ref("Cases"),
    ]),
    make_case_cons,
    fn(_, _) { formatter.text("") },
  ),
])
```

### Call Expression Grammar

**Old**:
```gleam
|> grammar.rule("Call", [
  grammar.alt(
    grammar.seq([
      grammar.keyword_pattern("call"),
      grammar.token_pattern("Ident"),
      grammar.token_pattern("LParen"),
      grammar.ref("ArgList"),
      grammar.token_pattern("RParen"),
    ]),
    make_call,
    fn(v, p) { format_value(v, p) },
  ),
])
```

**New**:
```gleam
|> grammar.rule("Call", [
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Percent"),
      grammar.token_pattern("Ident"),  // "call"
      grammar.token_pattern("LParen"),
      grammar.ref("ArgList"),
      grammar.token_pattern("RParen"),
    ]),
    make_call,
    fn(v, p) { format_value(v, p) },
  ),
])
```

### Comptime Expression Grammar

**Old**:
```gleam
|> grammar.rule("Comptime", [
  grammar.alt(
    grammar.seq([
      grammar.keyword_pattern("comptime"),
      grammar.token_pattern("LBrace"),
      grammar.ref("Expr"),
      grammar.token_pattern("RBrace"),
    ]),
    make_comptime,
    fn(v, p) { format_value(v, p) },
  ),
])
```

**New**:
```gleam
|> grammar.rule("Comptime", [
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Percent"),
      grammar.token_pattern("Ident"),  // "comptime"
      grammar.ref("Expr"),
    ]),
    make_comptime,
    fn(v, p) { format_value(v, p) },
  ),
])
```

---

## Lexer Changes

### Add Tokens

```gleam
// In tokenize_char or tokenize_operator
"%" -> "Percent"
"~" -> "Tilde"
"|" -> "Pipe"
// Note: "?" already exists for holes, reused for guards
```

### Remove Keywords

```gleam
// Remove from keyword list
- "match"
- "with"
- "returning"
- "call"
- "comptime"
// Note: "if" was never a keyword, guards use "?" instead
```

These are now just regular identifiers that follow `%`.

---

## Migration Guide

### Update Existing Code

**Before**:
```gleam
match x with $Type returning
  #Some(y) -> y,
  _ -> #None
```

**After**:
```gleam
%match x ~ $Type {
  | #Some(y) -> y
  | _ -> #None
}
```

**Before**:
```gleam
call prim.add(1, 2)
```

**After**:
```gleam
%call prim.add(1, 2)
```

**Before**:
```gleam
comptime { 1 + 2 }
```

**After**:
```gleam
%comptime 1 + 2
```

### Variable Names Now Available

```gleam
// These are now valid!
match -> match(match)
call -> call(call)
comptime -> comptime(comptime)
```

---

## Example Programs

### Identity with Match

```gleam
%match x ~ $Type {
  | y -> y
}
```

### Option Handling

```gleam
%match opt ~ $Type {
  | #Some(x) -> x
  | #None -> 0
}
```

### With Guard

```gleam
%match n ~ $Type {
  | x ? x > 0 -> #Positive(x)
  | x ? x < 0 -> #Negative(x)
  | _ -> #Zero
}
```

### Built-in Call

```gleam
%call prim.add(%call prim.mul(2, 3), 1)
```

### Comptime

```gleam
%comptime %call prim.add(1, 2)
```

---

## Implementation Checklist

- [ ] Update lexer to recognize `%`, `~`, `|` tokens
- [ ] Remove `match`, `with`, `returning`, `call`, `comptime` from keywords
- [ ] Update `Match` grammar rule
- [ ] Update `Call` grammar rule
- [ ] Update `Comptime` grammar rule
- [ ] Update `Cases` grammar rule (add `|` and `if` support)
- [ ] Update constructors to handle new syntax
- [ ] Update formatters for new syntax
- [ ] Update all examples
- [ ] Update all tests
- [ ] Update documentation

---

## Files to Modify

| File | Changes |
|------|---------|
| `src/syntax/lexer.gleam` | Add `%`, `~`, `|` tokens; remove keywords |
| `src/core/syntax.gleam` | Update grammar rules for match, call, comptime |
| `src/core/core.gleam` | Update any keyword references |
| `test/core/syntax_test.gleam` | Update all tests |
| `examples/core/*.core.tao` | Update all examples |
| `examples/core/errors/**/*.core.tao` | Update error examples |
| `docs/**/*.md` | Update documentation |

---

## Benefits Summary

1. **No Keyword Conflicts**: `match`, `call`, `comptime` can be variable names
2. **Cleaner Syntax**: `%` prefix makes keywords visually distinct
3. **Better Match Syntax**: `{ }` and `|` provide clearer structure
4. **Guard Support**: `if guard` in patterns
5. **Consistent Design**: Matches `$Type` and `#Constructor` patterns
6. **Easier Parsing**: No keyword table needed
7. **Future-Proof**: Easy to add new `%keyword` features

---

## Estimated Effort

**Time**: 4-8 hours

**Complexity**: Medium

**Risk**: Medium (breaking change, requires updating all examples/tests)

---

## Related Documents

- **[06-production-ready.md](./06-production-ready.md)** - Production ready plan
- **[07-fix-match-parsing.md](./07-fix-match-parsing.md)** - Fix match parsing (this change supersedes)
- **[02-syntax.md](./02-syntax.md)** - Syntax specification (will be updated)

---

## References

- [Lexer](../../src/syntax/lexer.gleam)
- [Core Syntax](../../src/core/syntax.gleam)
- [Examples](../../examples/core/)
