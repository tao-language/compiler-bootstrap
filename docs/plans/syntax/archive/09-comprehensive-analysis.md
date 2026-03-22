# Syntax Library Comprehensive Analysis

> **Date**: March 2025
> **Purpose**: Analyze the syntax library architecture, identify issues, and propose simplifications
> **Status**: Analysis Complete

---

## Executive Summary

The syntax library is **mostly well-designed** but has several architectural issues that create unnecessary complexity and maintenance burden. The core insight (grammar as single source of truth) is correct, but the implementation has drifted from this principle.

### Key Findings

| Category | Status | Action Required |
|----------|--------|-----------------|
| Grammar DSL | ⚠️ Overcomplicated | Replace Builder with direct record |
| Lexer | ⚠️ Problematic | Replace with grammar-based tokenization |
| Formatter | ⚠️ Disconnected | Should extract metadata from grammar |
| Error Reporting | ✅ Good | No changes needed |
| Deconstructor | ❌ Broken | Remove (DONE) |
| Layout System | ⚠️ Partially implemented | Complete or simplify |
| Precedence Handling | ❌ Duplicated | Extract from grammar, don't hardcode |

### Recommended Actions

1. **Remove the standalone lexer** - Tokenization should be grammar-defined
2. **Remove the deconstructor stub** - It's not feasible and creates false expectations (DONE)
3. **Simplify layout system** - Remove unused layout hints
4. **Replace Builder pattern** - Use direct record construction for Grammar
5. **Fix formatter integration** - Extract precedence from grammar, don't hardcode
6. **Add grammar validation** - Catch common mistakes at grammar definition time

---

## Architecture Analysis

### Current Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                        User defines                              │
│  ┌─────────────┐  ┌──────────────┐  ┌─────────────────────┐    │
│  │   AST Type  │  │   Grammar    │  │ Manual Formatter    │    │
│  │             │  │  (DSL)       │  │                     │    │
│  └──────┬──────┘  └──────┬───────┘  └──────────┬──────────┘    │
│         │                │                      │               │
└─────────┼────────────────┼──────────────────────┼───────────────┘
          │                │                      │
          ▼                ▼                      ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Syntax Library                              │
│  ┌─────────────┐  ┌──────────────┐  ┌─────────────────────┐    │
│  │    Lexer    │  │   Grammar    │  │    Formatter        │    │
│  │  (hardcoded)│  │   DSL        │  │  Combinators        │    │
│  │             │  │   Parser     │  │                     │    │
│  └──────┬──────┘  └──────┬───────┘  └──────────┬──────────┘    │
│         │                │                      │               │
└─────────┼────────────────┼──────────────────────┼───────────────┘
          │                │                      │
          ▼                ▼                      ▼
     ┌─────────┐     ┌──────────┐          ┌──────────┐
     │ Tokens  │────▶│   AST    │─────────▶│   Doc    │
     └─────────┘     └──────────┘          └──────────┘
```

### Problems

1. **Lexer is hardcoded** - Not grammar-defined, breaks "single source of truth" principle
2. **Deconstructor is a stub** - Creates false expectation of automatic formatting
3. **Layout hints are partially implemented** - `break_before`, `indent_rhs` defined but not used
4. **Formatter stubs in grammar** - `fn(_ast, _prec) { formatter.text("") }` serves no purpose
5. **Duplication between grammar and formatter** - Precedence defined in grammar, repeated in formatter

---

## Detailed Analysis

### 1. Lexer: Should Be Grammar-Defined ❌

**Current State**:
```gleam
// src/syntax/lexer.gleam - Hardcoded tokenizer
pub fn tokenize(source: String) -> List(Token) {
  // 400+ lines of hardcoded tokenization logic
  // Handles: whitespace, comments, numbers, strings, operators
}
```

**Problem**: The lexer is completely separate from the grammar. This means:
- Token kinds are hardcoded, not grammar-defined
- Comment handling is hardcoded, not configurable
- Language-specific tokenization (indentation for Python/Haskell) not supported
- Breaks "single source of truth" principle

**Solution**: Grammar should define tokenization patterns:

```gleam
// Proposed: Grammar-defined tokenization
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.token("Number", pattern: "[0-9]+")  // Regex or combinator
  |> grammar.token("Ident", pattern: "[a-zA-Z_][a-zA-Z0-9_]*")
  |> grammar.skip("Whitespace", pattern: "[ \\t\\n\\r]+")
  |> grammar.skip("LineComment", pattern: "//[^\\n]*")
  |> grammar.skip("BlockComment", pattern: "/\\*[^*]*\\*/")
  // ... rest of grammar
}
```

**Benefits**:
- Tokenization is part of grammar (single source of truth)
- Easy to add new token types
- Configurable comment handling
- Supports indentation-based languages

**Implementation Effort**: ~200-300 lines (replace lexer with grammar-based tokenization)

---

### 2. Deconstructor: Not Feasible, Should Be Removed ❌

**Current State**:
```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    deconstructor: fn(a) -> List(Value(a)),  // STUB!
    formatter: fn(a, Int) -> Doc,
  )
}

// All destructors panic:
deconstructor: fn(_) { panic as "Deconstructor not implemented" }
```

**Problem**: As analyzed in `docs/plans/syntax/06-automatic-formatter-analysis.md`:
- Parser is many-to-one (can't be inverted)
- AST doesn't preserve formatting information
- Precedence/layout info lost after construction
- **Fundamentally not feasible** without major architectural changes

**Solution**: Remove the deconstructor field entirely:

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    formatter: fn(a, Int) -> Doc,
  )
}
```

**Benefits**:
- Honest about what's possible
- Reduces confusion
- Simplifies API
- Removes 14 lines of stub code per alternative

**Implementation Effort**: ~50 lines (remove deconstructor from all alternatives)

---

### 3. Layout System: Partially Implemented ⚠️

**Current State**:
```gleam
pub type OperatorLayout {
  OperatorLayout(
    separator: String,
    break_before: Bool,      // Defined but not used
    break_after: Bool,       // Defined but not used
    indent_rhs: Bool,        // Defined but not used
  )
}

pub fn default_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: False,  // Ignored
    break_after: False,   // Ignored
    indent_rhs: False,    // Ignored
  )
}
```

**Problem**: Layout fields are defined but not used in formatting. This creates:
- False expectations
- Unused API surface
- Confusion for users

**Solution**: Either complete the implementation OR simplify to what's actually used:

**Option A: Complete Implementation** (~100 lines)
- Implement layout breaking in formatter
- Thread layout info through formatting
- Support `break_before`, `break_after`, `indent_rhs`

**Option B: Simplify** (~20 lines)
```gleam
pub type OperatorLayout {
  OperatorLayout(
    separator: String,
    // That's it - everything else is handled by formatter combinators
  )
}
```

**Recommendation**: Option B - Formatter combinators already handle layout well:
```gleam
// Current approach works fine:
format_binop_auto(format_expr, l, r, "+", 10, parent_prec)
// Layout handled by formatter, not grammar
```

---

### 4. Formatter Stubs in Grammar: Serve No Purpose ❌

**Current State**:
```gleam
grammar.alt(
  grammar.token_pattern("Number"),
  fn(values) { Int(...) },  // Constructor
  fn(_ast, _prec) { formatter.text("") },  // STUB!
)
```

**Problem**: The formatter in grammar alternatives is never called! The actual formatting is done by manual formatters:

```gleam
// Actual formatter (separate from grammar):
pub fn format(ast: Expr) -> String {
  format_expr(ast, 0) |> formatter.render_default
}

fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n, _) -> text(int.to_string(n))  // Real formatting
    // ...
  }
}
```

**Solution**: Remove formatter from grammar alternatives:

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    // No formatter here - it's separate
  )
}

// Usage:
grammar.alt(
  grammar.token_pattern("Number"),
  fn(values) { Int(...) },  // Just the constructor
)
```

**Benefits**:
- Honest separation of concerns
- Grammar = parsing only
- Formatter = formatting only
- Reduces confusion

---

### 5. Precedence Duplication: Grammar vs Formatter ⚠️

**Current State**:
```gleam
// Grammar defines precedence:
grammar.op("+", make_add, 10, grammar.default_op_layout("+"))

// Formatter repeats precedence:
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  Add(l, r, _) ->
    format_binop_auto(format_expr, l, r, "+", 10, parent_prec)
    //                                                  ^^
    //                                          Precedence repeated!
}
```

**Problem**: Precedence is defined twice, which can lead to inconsistencies.

**Current Mitigation**: `format_binop_auto` helps, but still requires manual precedence.

**Better Solution**: Extract precedence from grammar automatically:

```gleam
// Grammar defines precedence ONCE:
grammar.op("+", make_add, 10, ...)

// Formatter extracts it:
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  Add(l, r, _) -> {
    let prec = get_precedence(calc_grammar(), "add")  // Extract from grammar
    format_binop_auto(format_expr, l, r, "+", prec, parent_prec)
  }
}
```

**Implementation**: Already exists as `extract_precedence_table`, but not well integrated.

---

### 6. Grammar API: Overcomplicated Builder Pattern ❌

**Current State**:
```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.left_assoc("Expr", "Term", [...], 10)
  |> grammar.left_assoc("Term", "Factor", [...], 20)
  |> grammar.rule("Factor", [...])
}
```

**Assessment**: The Builder pattern is overcomplicated for what it does:
- ❌ Requires ~100 lines of builder infrastructure
- ❌ Uses pipe-heavy style that obscures the grammar structure
- ❌ Builder functions (`grammar.name`, `grammar.start`, etc.) add indirection
- ❌ List accumulation in builder is inefficient (repeated list prepends)

**Better Approach**: Direct record construction

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  Grammar(
    name: "Calc",
    start: "Expr",
    tokens: ["Number", "LParen", "RParen"],
    keywords: [],
    rules: [
      Rule(
        name: "Expr",
        alternatives: left_assoc_alts("Term", [
          Operator("+", make_add, 10, default_op_layout()),
          Operator("-", make_sub, 10, default_op_layout()),
        ]),
        precedence: 10,
      ),
      Rule(
        name: "Term",
        alternatives: left_assoc_alts("Factor", [
          Operator("*", make_mul, 20, default_op_layout()),
          Operator("/", make_div, 20, default_op_layout()),
        ]),
        precedence: 20,
      ),
      Rule(
        name: "Factor",
        alternatives: [
          alt(token_pattern("Number"), make_int),
          alt(parenthesized("Expr"), unwrap_parens),
        ],
        precedence: 0,
      ),
    ],
    operators: [
      Operator("+", make_add, 10, Left, default_op_layout()),
      Operator("-", make_sub, 10, Left, default_op_layout()),
      Operator("*", make_mul, 20, Left, default_op_layout()),
      Operator("/", make_div, 20, Left, default_op_layout()),
    ],
  )
}
```

**Benefits**:
- ✅ More declarative - grammar structure is visible at a glance
- ✅ No builder infrastructure (~100 lines removed)
- ✅ Type system ensures all fields are provided
- ✅ Easier to understand and maintain
- ✅ Explicit about defaults (e.g., `keywords: []`)

**Trade-offs**:
- More verbose for simple grammars (but clearer)
- Requires listing operators twice (in rules and operators list) - can be mitigated with helper functions

---

### 6b. Formatter Precedence Duplication ❌

**Current State**:
```gleam
// Grammar defines precedence ONCE:
grammar.op("+", make_add, 10, grammar.default_op_layout("+"))

// Formatter repeats precedence:
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  Add(l, r, _) ->
    format_binop_auto(format_expr, l, r, "+", 10, parent_prec)
    //                                                  ^^
    //                                          Precedence DUPLICATED!
}
```

**Problem**: Precedence is defined in the grammar but hardcoded in the formatter. This violates the "single source of truth" principle and leads to:
- Inconsistencies when precedence is updated in grammar but not formatter
- Maintenance burden - every precedence change requires two updates
- Error-prone - easy to mistype precedence numbers

**Solution**: Extract precedence from grammar

```gleam
// Grammar defines precedence ONCE:
Operator("+", make_add, 10, Left, default_op_layout())

// Formatter extracts it:
fn format_expr(ast: Expr, parent_prec: Int, grammar: Grammar(Expr)) -> Doc {
  case ast {
    Add(l, r, _) -> {
      let prec = get_operator_precedence(grammar, "Add")  // Returns 10
      format_binop_auto(format_expr, l, r, "+", prec, parent_prec, grammar)
    }
  }
}

// Helper that extracts precedence from grammar
fn get_operator_precedence(grammar: Grammar(a), constructor: String) -> Int {
  case dict.get(grammar.operators_by_constructor, constructor) {
    Ok(op) -> op.precedence
    Error(_) -> 0  // Default for non-operator constructors
  }
}
```

**Better Solution**: Operator lookup includes formatter combinator

```gleam
// Grammar defines operator with all metadata:
Operator(
  symbol: "+",
  constructor: make_add,
  precedence: 10,
  associativity: Left,
  layout: default_op_layout(),
)

// Formatter uses grammar to get operator info:
fn format_expr(ast: Expr, parent_prec: Int, grammar: Grammar(Expr)) -> Doc {
  case ast {
    Add(l, r, _) -> {
      case get_operator_by_constructor(grammar, "Add") {
        Ok(op) -> format_binop_auto(format_expr, l, r, op.symbol, op.precedence, parent_prec)
        Error(_) -> text("<Add>")  // Fallback for unknown constructors
      }
    }
  }
}
```

**Benefits**:
- ✅ Precedence defined ONCE in grammar
- ✅ Formatter can't get out of sync
- ✅ Adding new operators is single-change
- ✅ Type-safe operator lookup

---

### 7. Error Handling: Good ✅

**Current State**:
```gleam
pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

// Never panics, accumulates errors
```

**Assessment**: This is excellent! Error handling is:
- ✅ Error-resilient (never panics)
- ✅ Accumulates multiple errors
- ✅ Position tracking
- ✅ Source snippets with diagnostics

**No changes needed.**

---

### 8. Formatter Combinators: Good but Could Be Better ✅

**Current State**:
```gleam
// 16+ combinators available:
format_binop_auto(format_fn, left, right, sep, prec, parent_prec)
format_unary(op, operand)
format_wrapped(open, content, close)
format_list(items, sep)
format_application(fun, args)
format_lambda(params, body)
format_record(fields)
format_record_auto(fields, width)
format_match(scrutinee, cases)
format_case(pattern, guard, body)
// ... and more
```

**Assessment**: This is excellent! Reduces boilerplate by ~70%.

**Minor Improvements**:
- Add `format_if(condition, then_doc, else_doc)`
- Add `format_indented(doc)` helper
- Add `format_nested(current_indent, doc)` helper

---

## Recommended Architecture

### Proposed Changes

```
┌─────────────────────────────────────────────────────────────────┐
│                        User defines                              │
│  ┌─────────────┐  ┌──────────────────────────────────────┐     │
│  │   AST Type  │  │   Grammar (includes tokenization)    │     │
│  │             │  │                                      │     │
│  └──────┬──────┘  └──────────────────┬───────────────────┘     │
│         │                            │                         │
└─────────┼────────────────────────────┼─────────────────────────┘
          │                            │
          ▼                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Syntax Library                              │
│  ┌────────────────────────────────┐  ┌─────────────────────┐   │
│  │   Grammar-Based Tokenizer      │  │   Formatter         │   │
│  │   (generated from grammar)     │  │   Combinators       │   │
│  │                                │  │                     │   │
│  └────────────┬───────────────────┘  └──────────┬──────────┘   │
│               │                                  │              │
└───────────────┼──────────────────────────────────┼──────────────┘
                │                                  │
                ▼                                  ▼
          ┌──────────┐                      ┌──────────┐
          │   AST    │─────────────────────▶│   Doc    │
          └──────────┘     Manual           └──────────┘
                       Pattern Match
```

### Key Changes

1. **Remove standalone lexer** - Tokenization is grammar-defined
2. **Remove deconstructor** - Honest about what's possible
3. **Remove formatter from grammar** - Separate concerns
4. **Simplify layout system** - Remove unused fields
5. **Improve precedence extraction** - Better integration

---

## Implementation Plan

### Phase 1: Cleanup (1-2 days)

**Remove unused features**:
- [ ] Remove `deconstructor` field from `Alternative`
- [ ] Remove formatter stubs from grammar alternatives
- [ ] Remove unused layout fields (`break_before`, `break_after`, `indent_rhs`)
- [ ] Update all examples and tests

**Estimated effort**: ~100 lines removed, ~50 lines updated

---

### Phase 2: Grammar-Based Tokenization (2-3 days)

**Replace lexer with grammar-defined tokenization**:
- [ ] Add `grammar.token_pattern(kind, pattern)` API
- [ ] Add `grammar.skip(kind, pattern)` for whitespace/comments
- [ ] Implement grammar-based tokenizer
- [ ] Remove hardcoded lexer
- [ ] Update all examples

**Estimated effort**: ~300 lines new, ~400 lines removed

---

### Phase 3: Better Integration (1-2 days)

**Improve precedence/layout integration**:
- [ ] Better `extract_precedence_table` integration
- [ ] Add `get_precedence(grammar, constructor)` helper
- [ ] Add more formatter combinators
- [ ] Update documentation

**Estimated effort**: ~100 lines

---

### Phase 4: Documentation (1 day)

**Update all documentation**:
- [ ] Update `docs/syntax-library.md`
- [ ] Update `docs/plans/syntax/*.md`
- [ ] Add migration guide
- [ ] Add more examples

**Estimated effort**: ~200 lines of docs

---

## Summary

### What's Good (Keep As-Is)

✅ Grammar DSL - Declarative, type-safe, composable
✅ Formatter combinators - 16+ helpers reduce boilerplate
✅ Error handling - Error-resilient with source snippets
✅ Source location tracking - Full span propagation

### What Needs Cleanup

❌ Standalone lexer - Should be grammar-defined
❌ Deconstructor stub - Not feasible, creates false expectations
❌ Formatter stubs in grammar - Serve no purpose
❌ Unused layout fields - Create confusion

### Net Impact

- **Lines removed**: ~600
- **Lines added**: ~400
- **Net reduction**: ~200 lines
- **Complexity reduction**: Significant
- **User experience**: Improved (clearer API)

---

## Related Documents

- **[docs/plans/syntax/06-automatic-formatter-analysis.md](docs/plans/syntax/06-automatic-formatter-analysis.md)** - Why full automation not feasible
- **[docs/plans/syntax/08-grammar-derived-formatter-plan.md](docs/plans/syntax/08-grammar-derived-formatter-plan.md)** - Grammar-derived metadata approach
- **[docs/syntax-library.md](docs/syntax-library.md)** - Current syntax library documentation

---

## Conclusion

The syntax library is **80% correct**. The core insight (grammar as single source of truth) is right, but the implementation has some historical baggage that should be cleaned up. The recommended changes will:

1. Make the library more honest about what's automatic vs manual
2. Reduce code size by ~200 lines
3. Improve user experience with clearer API
4. Better align with the "single source of truth" principle
