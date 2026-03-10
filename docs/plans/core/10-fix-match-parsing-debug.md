# %match Parsing Debug Plan

> **Goal**: Diagnose and fix the `%match` expression parsing failure
> **Status**: 🔍 Investigation in progress
> **Date**: March 2025

---

## Problem Summary

The `%match` expression fails to parse with error:
```
Parse error at position 0: expected valid alternative, got none
```

**Working:**
- ✅ `%call f(x)` - parses successfully
- ✅ `%comptime 1` - parses successfully
- ✅ Lexer produces correct `PercentMatch` token

**Failing:**
- ❌ `%match x ~ $Type { | y -> y }` - fails at position 0

---

## Current Implementation

### Lexer Output (Verified Correct)
```
%match x ~ $Type { | y -> y }

[PercentMatch(%match)
, Ident(x)
, Tilde(~)
, Dollar($)
, Ident(Type)
, LBrace({)
, Pipe(|)
, Ident(y)
, Arrow(->)
, Ident(y)
, RBrace(})
]
```

### Grammar Rule
```gleam
|> grammar.rule("Match", [
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("PercentMatch"),
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
```

### Handler Function
```gleam
fn make_match(values) -> ParseValue {
  case values {
    [_, AstValue(AsTerm(arg)), _, AstValue(AsTerm(motive)), _, AstValue(AsCases(cases)), _] ->
      AsTerm(NMatch(arg, motive, cases, get_span(arg)))
    _ -> panic as "Expected match expression"
  }
}
```

---

## Hypothesis Analysis

### Hypothesis 1: Expr Rule Ordering Issue

**Theory**: The `Expr` rule tries alternatives in order. If `Match` is tried but fails deep in the parse (e.g., in `Cases`), backtracking might not work correctly.

**Evidence**:
- `Match` is listed first in `Expr` alternatives
- `Cases` references `Pattern` which references `Expr` - potential left recursion?

**Test**: Move `Match` to after `Atom` in `Expr` rule.

**Status**: ⏳ Not yet tested

---

### Hypothesis 2: Cases Rule Conflict

**Theory**: The `Cases` rule might be conflicting with something, or the `Pattern` rule inside it is failing.

**Current Cases Rule**:
```gleam
|> grammar.rule("Cases", [
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Pipe"),
      grammar.ref("Pattern"),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
    ]),
    make_single_case_list,
    fn(_, _) { formatter.text("") },
  ),
])
```

**Evidence**:
- Only supports single case currently
- `Pattern` rule might be too restrictive

**Test**: Simplify `Cases` to just accept `Pipe` and see if that parses.

**Status**: ⏳ Not yet tested

---

### Hypothesis 3: Pattern Rule Issue

**Theory**: The `Pattern` rule might not be recognizing `y` as a valid pattern.

**Current Pattern Rule**:
```gleam
|> grammar.rule("Pattern", [
  // Wildcard: _
  grammar.alt(grammar.token_pattern("Underscore"), make_pattern_any, ...),
  // As-pattern: x @ pat
  grammar.alt(grammar.seq([...]), make_pattern_as, ...),
  // Constructor: #Name(pat)
  grammar.alt(grammar.seq([...]), make_pattern_ctr, ...),
  // Literal: 42
  grammar.alt(grammar.token_pattern("Number"), make_pattern_lit, ...),
])
```

**Evidence**:
- No variable pattern (`Ident`) in the rule!
- This is likely the bug!

**Status**: ✅ **FOUND THE BUG!**

---

## Root Cause

The `Pattern` rule is missing a clause for variable patterns (identifiers). When parsing:
```
| y -> y
```

The parser tries to match `y` against `Pattern`, but `Pattern` only accepts:
- `_` (wildcard)
- `x @ pat` (as-pattern)
- `#Name(pat)` (constructor)
- `42` (literal)

It does NOT accept plain identifiers like `y`!

---

## Fix Plan

### Step 1: Add Variable Pattern to Pattern Rule

Add a new alternative for identifier patterns:

```gleam
|> grammar.rule("Pattern", [
  // Variable pattern: x
  grammar.alt(
    grammar.token_pattern("Ident"),
    make_pattern_var,
    fn(_, _) { formatter.text("") },
  ),
  // ... existing patterns ...
])
```

### Step 2: Implement make_pattern_var Handler

```gleam
fn make_pattern_var(values) -> ParseValue {
  case values {
    [TokenValue(token)] ->
      AsPattern(NPAs(NPAny(grammar.span_from_token(token, "input")), token.value))
    _ -> panic as "Expected identifier"
  }
}
```

### Step 3: Test

```bash
gleam run -- check examples/core/11_match_single.core.tao
```

---

## Additional Work

### Multiple Cases Support

Once single-case match works, implement multiple cases:

```gleam
|> grammar.rule("Cases", [
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Pipe"),
      grammar.ref("Pattern"),
      grammar.opt(  // Optional guard
        grammar.seq([
          grammar.token_pattern("Question"),
          grammar.ref("Expr"),
        ]),
      ),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
      grammar.many(  // Zero or more additional cases
        grammar.seq([
          grammar.token_pattern("Pipe"),
          grammar.ref("Pattern"),
          grammar.opt(
            grammar.seq([
              grammar.token_pattern("Question"),
              grammar.ref("Expr"),
            ]),
          ),
          grammar.token_pattern("Arrow"),
          grammar.ref("Expr"),
        ]),
      ),
    ]),
    make_cases_with_guards,
    fn(_, _) { formatter.text("") },
  ),
])
```

### Guard Support

The grammar already supports guards with `?`, but the handler ignores them. Need to:
1. Store guard in `NamedCase` type
2. Use guard during type checking/evaluation

---

## Testing Checklist

- [ ] Single case: `%match x ~ $Type { | y -> y }`
- [ ] Multiple cases: `%match x ~ $Type { | a -> a | b -> b }`
- [ ] With guard: `%match x ~ $Type { | y ? y > 0 -> y | _ -> 0 }`
- [ ] Constructor pattern: `%match opt ~ $Type { | #Some(x) -> x | #None -> 0 }`
- [ ] Wildcard pattern: `%match x ~ $Type { | _ -> 0 }`
- [ ] As-pattern: `%match x ~ $Type { | y @ #Some(z) -> y }`
- [ ] Nested patterns: `%match x ~ $Type { | #Some(#Some(y)) -> y }`

---

## Files to Modify

1. `src/core/syntax.gleam` - Add variable pattern to `Pattern` rule
2. `src/core/syntax.gleam` - Add `make_pattern_var` handler
3. `examples/core/11_match_single.core.tao` - Test file
4. `test/core/syntax_test.gleam` - Add match parsing tests

---

## Success Criteria

- ✅ `%match` expressions parse without errors
- ✅ Round-trip: parse → format → parse produces identical output
- ✅ All 401 existing tests continue to pass
- ✅ New match expression tests pass
