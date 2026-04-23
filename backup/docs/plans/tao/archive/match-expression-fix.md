# Match Expression Fix Plan

## Problem Analysis

### Root Cause

The match expression grammar rule is correctly structured, but the value extraction logic is broken. The issue is in how `make_match` and the clause extraction functions handle the grammar's value structure.

### Grammar Value Structure

For the match rule:
```gleam
seq([
  keyword_pattern("match"),      // [KeywordValue(match_kw)]
  ref("Expr"),                   // [AstValue(scrutinee)]
  opt(seq([...]))),              // [] or [TokenValue(arrow), TokenValue(ident)]
  token_pattern("LBrace"),       // [TokenValue(lbrace)]
  many(seq([...]))),             // [ListValue(clause1_items), ListValue(clause2_items), ...]
  token_pattern("RBrace"),       // [TokenValue(rbrace)]
])
```

Expected values structure:
```
[KeywordValue(match_kw), AstValue(scrutinee), opt_result, TokenValue(lbrace), ListValue(clause1_items), ListValue(clause2_items), ..., TokenValue(rbrace)]
```

Where each `ListValue(clause_items)` contains:
```
[TokenValue(pipe), AstValue(pattern), opt_guard, TokenValue(arrow), AstValue(body)]
```

### Issues Identified

1. **`make_match` value extraction**: The function expects values in a specific order but the `opt(seq([...]))` can return an empty list `[]` which shifts subsequent values.

2. **Clause extraction**: The `extract_clauses_after_lbrace` function looks for `ListValue` items after `LBrace`, but the values structure has multiple `ListValue` items (one per clause), not a single wrapped list.

3. **Pattern conversion**: The `pattern_ast_to_pattern` function needs to handle `Ctr` expressions for constructor patterns.

## Solution

### Step 1: Fix `make_match` Value Extraction

Update `make_match` to correctly handle the optional type annotation and extract clauses:

```gleam
fn make_match(values) -> Expr {
  // values = [match_kw, scrutinee, opt_type_annotation, lbrace, clause1, clause2, ..., rbrace]
  // where opt_type_annotation is either [] or [TokenValue(arrow), TokenValue(ident)]
  // and each clause is a ListValue containing [pipe, pattern, opt_guard, arrow, body]
  
  // Extract scrutinee (second element, AstValue)
  // Skip optional type annotation (could be 0 or 2 elements)
  // Find LBrace and collect all ListValue clauses until RBrace
}
```

### Step 2: Fix Clause Extraction

Update `extract_clauses_after_lbrace` to handle the flat structure where each clause is a separate `ListValue`:

```gleam
fn extract_clauses_after_lbrace(values, in_braces, acc) {
  case values {
    [] -> list.reverse(acc)
    [TokenValue(t), ..rest] if t.kind == "LBrace" -> 
      extract_clauses_after_lbrace(rest, True, acc)
    [TokenValue(t), ..rest] if t.kind == "RBrace" -> 
      list.reverse(acc)
    [ListValue(clause_items), ..rest] if in_braces ->
      case extract_single_clause_from_list(clause_items) {
        Some(clause) -> extract_clauses_after_lbrace(rest, in_braces, [clause, ..acc])
        None -> extract_clauses_after_lbrace(rest, in_braces, acc)
      }
    [_v, ..rest] -> 
      extract_clauses_after_lbrace(rest, in_braces, acc)
  }
}
```

### Step 3: Fix Single Clause Extraction

Update `extract_single_clause_from_list` to correctly extract pattern and body:

```gleam
fn extract_single_clause_from_list(items) {
  // items = [pipe, pattern, opt_guard, arrow, body]
  // Find pipe position, then extract pattern (next item)
  // Find arrow position after pattern, then extract body (next item)
  // Handle optional guard
}
```

### Step 4: Fix Pattern Conversion

Update `pattern_ast_to_pattern` to handle `Ctr` expressions:

```gleam
pub fn pattern_ast_to_pattern(expr) -> Pattern {
  case expr {
    Var("_", span) -> PWild(span)
    Var(name, span) -> PVar(name, span)
    Int(value, span) -> PLit(value, span)
    Ctr(name, args, span) -> {
      let pattern_args = list.map(args, pattern_ast_to_pattern)
      PCtr(name, pattern_args, span)
    }
    _ -> PWild(Span("error", 0, 0, 0, 0))
  }
}
```

### Step 5: Fix Match Rule Pattern Reference

Change the match rule to use `ref("Primary")` or `ref("Application")` instead of `ref("Expr")` for patterns to avoid circular reference issues and greedy matching:

```gleam
many(seq([
  token_pattern("Pipe"),
  ref("Application"),  // Use Application to match constructor applications
  opt(seq([
    keyword_pattern("if"),
    ref("Expr"),  // guard
  ])),
  token_pattern("Arrow"),
  ref("Expr"),  // body
]))
```

## Testing

After implementing the fix:
1. Test simple match: `match 1 { | 0 -> 1 | _ -> 0 }`
2. Test constructor pattern: `match Some(42) { | Some(x) -> x | None -> 0 }`
3. Test constructor without args: `match True { | True -> 1 | False -> 0 }`
4. Run all tests and verify pass count increases

## Timeline

- Step 1-3: Fix value extraction and clause parsing (2-3 hours)
- Step 4: Fix pattern conversion (30 minutes)
- Step 5: Fix grammar rule (30 minutes)
- Testing: 1 hour

Total: ~4-5 hours
