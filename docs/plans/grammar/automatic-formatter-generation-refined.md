# Automatic Formatter Generation - Refined Plan

> **Status**: Phase 1 complete (grammar-guided formatting), Phase 2 in progress
> **Date**: March 2025

---

## Current Implementation Status

### ✅ Phase 1: Grammar-Guided Formatting (Complete)

**What works:**
- Grammar stores formatting metadata (precedence, separator, associativity, layout)
- Generic `format_binary_op` helper uses grammar metadata
- Precedence-based parenthesization automatic
- **238 tests passing**

**What's manual:**
- Formatter still pattern matches on AST constructors
- Manual mapping: `Add(l, r)` → `"+"` operator keyword

```gleam
// Current approach (manual pattern matching)
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> grammar.format_binary_op(grammar, "+", l, r, parent_prec, format_expr)
    // Manual mapping: Add → "+"
  }
}
```

### ⏳ Phase 2: Automatic Operator Lookup (In Progress)

**Goal:** Eliminate manual pattern matching for operators.

**Approach:** Store AST constructor → operator mapping in grammar.

```gleam
// Future approach (automatic lookup)
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case format_by_operator(grammar, ast, parent_prec) {
    Some(doc) -> doc
    None -> format_atom(ast)  // Fallback for atoms
  }
}
```

---

## Phase 2 Implementation Plan

### Step 1: Add AST Tag to Operator

```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
    separator: String,
    // NEW: AST tag for lookup
    ast_tag: String,  // e.g., "Add", "Sub", "Mul", "Div"
  )
}
```

### Step 2: Add Operator Registry by Tag

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: Dict(String, Operator(a)),  // keyword → Operator
    // NEW: Operator lookup by AST tag
    operators_by_tag: Dict(String, Operator(a)),  // "Add" → Operator
  )
}
```

### Step 3: Update Operator Helper

```gleam
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  separator: String,
  ast_tag: String,  // NEW parameter
) -> Operator(a) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    precedence: precedence,
    associativity: Left,
    layout: Inline,
    separator: separator,
    ast_tag: ast_tag,
  )
}
```

### Step 4: Build Operator-by-Tag Registry

```gleam
fn to_grammar(builder: GrammarBuilder(a)) -> Grammar(a) {
  // ... existing code ...
  
  let operators_dict =
    list.fold(builder.operators, dict.new(), fn(acc, op) {
      dict.insert(acc, op.keyword, op)
    })
  
  // NEW: Build operator-by-tag registry
  let operators_by_tag_dict =
    list.fold(builder.operators, dict.new(), fn(acc, op) {
      dict.insert(acc, op.ast_tag, op)
    })
  
  Grammar(
    name: builder.name,
    start: builder.start,
    rules: rules_dict,
    tokens: builder.tokens,
    keywords: builder.keywords,
    operators: operators_dict,
    operators_by_tag: operators_by_tag_dict,  // NEW
  )
}
```

### Step 5: Implement Automatic Formatter

```gleam
pub fn format(grammar: Grammar(a), ast: a) -> String {
  let doc = format_ast(grammar, ast, -1)
  formatter.render(doc, 80)
}

fn format_ast(grammar: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  // Try automatic operator formatting first
  case format_by_operator(grammar, ast, parent_prec) {
    Some(doc) -> doc
    None -> format_atom(ast)  // Fallback for atoms
  }
}

fn format_by_operator(grammar: Grammar(a), ast: a, parent_prec: Int) -> Option(Doc) {
  // Get AST tag (user-provided function)
  case get_ast_tag(ast) {
    Some(tag) -> {
      case dict.get(grammar.operators_by_tag, tag) {
        Ok(op) -> {
          // Extract operands using operator deconstructor
          let #(left, right) = extract_operands(op, ast)
          Some(do_format_binary_op(op, left, right, parent_prec, format_ast))
        }
        Error(_) -> None
      }
    }
    None -> None
  }
}

fn get_ast_tag(ast: a) -> Option(String) {
  // User-provided function to get AST tag
  // For calc: Add(_) → "Add", Sub(_) → "Sub", etc.
}

fn extract_operands(op: Operator(a), ast: a) -> #(a, a) {
  // Use operator deconstructor to extract operands
  // This still requires deconstructors, but only for operators
}
```

### Step 6: Update Calc Grammar

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10, " + ", "Add"),  // NEW: ast_tag
    grammar.op("-", Sub, 10, " - ", "Sub"),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op("*", Mul, 20, " * ", "Mul"),
    grammar.op("/", Div, 20, " / ", "Div"),
  ])
  // ...
}

// User-provided tag function
fn get_expr_tag(ast: Expr) -> Option(String) {
  case ast {
    Int(_) -> None  // Not an operator
    Add(_, _) -> Some("Add")
    Sub(_, _) -> Some("Sub")
    Mul(_, _) -> Some("Mul")
    Div(_, _) -> Some("Div")
  }
}
```

### Step 7: Automatic Formatter Usage

```gleam
// Fully automatic - no pattern matching on operators!
fn format_ast(grammar: Grammar(Expr), ast: Expr, parent_prec: Int) -> Doc {
  case grammar.format_by_operator(grammar, ast, parent_prec, get_expr_tag) {
    Some(doc) -> doc
    None -> format_atom(ast)
  }
}

fn format_atom(ast: Expr) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    _ -> formatter.text("<unknown>")
  }
}
```

---

## Trade-offs

### Current Approach (Phase 1)

**Pros:**
- ✅ Simple, works now
- ✅ No deconstructors needed
- ✅ Type-safe (pattern matching is exhaustive)

**Cons:**
- ❌ Manual pattern matching for every AST constructor
- ❌ Duplicates AST structure in formatter

### Automatic Approach (Phase 2)

**Pros:**
- ✅ No manual pattern matching for operators
- ✅ Single source of truth (grammar has all formatting info)
- ✅ Less boilerplate in formatter

**Cons:**
- ❌ Still need `get_ast_tag` function (pattern matching on AST)
- ❌ Still need deconstructors for operators (or use `get_ast_tag` to extract operands)
- ❌ More complex grammar definition (ast_tag parameter)

---

## Recommendation

**Phase 1 (current)** is the right balance for now:
- Grammar is single source of truth for formatting rules
- Formatter is minimal (just pattern matching + helper calls)
- No deconstructors needed
- Type-safe

**Phase 2** can be implemented later if:
- You want to eliminate operator pattern matching
- You're willing to add `ast_tag` to grammar definition
- You're okay with `get_ast_tag` function (still some pattern matching)

**Full automation** (no pattern matching at all) would require:
- Gleam macros to auto-generate `get_ast_tag` and deconstructors
- Or runtime type inspection (not available in Gleam)

---

## Implementation Checklist

### Phase 1 (Complete ✅)

- [x] Add `separator` field to `Operator` type
- [x] Update `op()` helper to include separator
- [x] Implement `format_binary_op()` generic helper
- [x] Update calc grammar with separators
- [x] Update calc formatter to use grammar metadata
- [x] All 238 tests passing

### Phase 2 (Optional)

- [ ] Add `ast_tag` field to `Operator` type
- [ ] Add `operators_by_tag` registry to `Grammar`
- [ ] Update `op()` helper to include ast_tag
- [ ] Build `operators_by_tag` registry in `to_grammar()`
- [ ] Implement `format_by_operator()` helper
- [ ] Implement `get_ast_tag()` for calc
- [ ] Update calc formatter to use automatic lookup
- [ ] Add tests for automatic formatting

---

## Summary

**Current state:** Grammar-guided formatting with manual pattern matching.

**Next step (optional):** Add AST tag lookup to eliminate operator pattern matching.

**Full automation:** Requires Gleam macros or runtime type inspection (not available).
