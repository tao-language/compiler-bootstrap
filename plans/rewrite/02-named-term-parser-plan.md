# Plan: Parser → NamedTerm → term_to_debruijn → Term

## Problem
The parser currently manages De Bruijn indices directly via an environment stack.
This causes subtle bugs when fixpoint variables aren't properly added to the env,
leading to incorrect De Bruijn indices for recursive references.

## Solution
Separate parsing from index calculation:
1. **Parser** → produces `NamedTerm` (variables as string names, no env tracking)
2. **term_to_debruijn** → converts `NamedTerm` → `Term` (De Bruijn indices)

## Architecture

```
Source string
  → tokenize()
  → parse_tokens() → NamedTerm    (parser: string names)
  → term_to_debruijn() → Term     (conversion: De Bruijn indices)
  → infer() → Type               (type checking)
  → evaluate() → Value           (normalization)
```

## Changes Required

### 1. `src/core/ast.gleam` — Add NamedFix
- Add `NamedFix(name: String, body: NamedTerm, span: Span)` to NamedTerm type
- Add `NamedFix` → `Fix` conversion in `named_term_to_debruijn`

### 2. `src/core/syntax.gleam` — Rewrite parser to produce NamedTerm
- Change all `parse_*` functions to return `NamedTerm` instead of `Term`
- Remove `add_binding` function and `env` from Parser type (no longer needed)
- Remove `term_span` helper (not needed for NamedTerm)
- Update `parse_tokens` to call `term_to_debruijn` at the end
- Update all imports

### 3. `src/cli/debug_core.gleam` — Show NamedTerm in output
- Add "NAMED" section between PARSING and DEBRUIJN
- Show the NamedTerm representation

### 4. `src/core/ast.gleam` — Update term_to_string for Fix
- Add `Fix` case to `term_to_string` for proper display

### 5. Tests
- Update existing syntax_test.gleam assertions for NamedTerm
- Add new tests for NamedTerm → De Bruijn conversion
- Add tests for fixpoint variable binding correctness

### 6. tour_test.gleam
- No changes needed — uses `parse` which will still return `#(Term, List(ParseError))`

## Implementation Order
1. Add NamedFix to ast.gleam + term_to_debruijn conversion
2. Rewrite parse_tokens / parse_tokens_acc to use NamedTerm
3. Rewrite parse_term → NamedTerm (the big one)
4. Rewrite parse_var, parse_match, parse_fix, parse_let, parse_lambda → NamedTerm
5. Rewrite remaining helpers (parse_app, parse_app_chain, parse_ffi_call, etc.)
6. Remove env from Parser type, remove add_binding
7. Update debug_core.gleam
8. Update/add tests
9. Fix all compilation errors

## Key Design Decisions
- Parser doesn't track variable bindings at all — it just records variable names as strings
- term_to_debruijn is the single source of truth for De Bruijn index calculation
- NamedLet is desugared by term_to_debruijn (not by the parser)
- NamedFix is desugared by term_to_debruijn (body is the lambda, no separate body)
