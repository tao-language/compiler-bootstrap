# Automatic Formatter Generation Analysis

> **Goal**: Analyze feasibility of generating formatters automatically from grammar
> **Status**: 📋 Analysis Complete
> **Date**: March 2025

---

## Executive Summary

**Fully automatic formatter generation is NOT feasible** with the current architecture without significant changes. However, **significant UX improvements are possible** that reduce manual formatter boilerplate by ~60-70%.

**Recommendation**: Implement UX improvements (formatter combinators, boilerplate generation) rather than pursuing full automation.

---

## Current Architecture

### Grammar Structure

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),       // What to parse
    constructor: fn(List(Value(a))) -> a,  // values → AST
    deconstructor: fn(a) -> List(Value(a)), // AST → values (STUB!)
    formatter: fn(a, Int) -> Doc,  // AST → Doc (MANUAL)
  )
}
```

### Current Approach

1. **Grammar defines**: Pattern + Constructor + (stub) Deconstructor + (manual) Formatter
2. **Parser uses**: Pattern + Constructor
3. **Formatter uses**: Manual pattern matching on AST

**Example** (Calculator):
```gleam
// Grammar defines constructor
grammar.alt(
  grammar.token_pattern("Number"),
  fn(values) { Int(int.parse(token.value)) },  // Constructor
  fn(ast, _) { case ast { Int(n) -> text(n) } },  // Manual formatter
)

// Separate manual formatter
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> text(n)
    Add(l, r) -> format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    // ... manual for each constructor
  }
}
```

---

## Why Full Automation is NOT Feasible

### Problem 1: Lossy Conversion (Fundamental)

**Parser**: `TokenValue → AST` (many-to-one)
**Formatter**: `AST → TokenValue` (one-to-many)

**Example**:
```
Source: "1 + 2 + 3"
AST:    Add(Add(Int(1), Int(2)), Int(3))

Formatting options:
- "1 + 2 + 3"      ← Preferred (no redundant parens)
- "(1 + 2) + 3"    ← Technically correct but verbose
- "((1 + 2) + 3)"  ← Correct but ugly
```

**Problem**: AST doesn't preserve original formatting. Formatter must **reconstruct** appropriate parentheses based on precedence.

**Why automation fails**: Grammar knows precedence, but deconstructor only produces values, not formatting decisions.

---

### Problem 2: Precedence Information Loss

**Grammar has precedence**:
```gleam
grammar.left_assoc("Expr", "Term", [
  grammar.op("+", Add, 10, ...),
  grammar.op("*", Mul, 20, ...),
], 10)
```

**AST does NOT**:
```gleam
pub type Expr {
  Add(Expr, Expr)  // No precedence info!
  Mul(Expr, Expr)
}
```

**Formatter needs precedence**:
```gleam
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Add(l, r) -> {
      // Must know: Add has prec 10
      format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    }
    Mul(l, r) -> {
      // Must know: Mul has prec 20
      format_binop(format_expr(l, 20), format_expr(r, 21), " * ", 20, parent_prec)
    }
  }
}
```

**Why automation fails**: Precedence is in grammar, not in AST. Automatic formatter would need to carry grammar metadata through to formatting, which requires significant architectural changes.

---

### Problem 3: Layout Information Mismatch

**Grammar has layout per-alternative**:
```gleam
grammar.op("+", Add, 10, grammar.default_op_layout("+"))
// default_op_layout has: break_after, indent_rhs, etc.
```

**Formatter needs layout per-node**:
```gleam
fn format_binop(left, right, op, prec, parent_prec) -> Doc {
  // Needs to know: should we break after op? indent RHS?
  // This info is in grammar but not accessible here
}
```

**Why automation fails**: Layout hints are attached to grammar rules, not AST nodes. Formatter would need to thread layout info through the entire AST.

---

### Problem 4: Deconstructor Complexity

**Simple case works**:
```gleam
// Constructor
fn(values) { Int(n) }

// Deconstructor (theoretical)
fn(ast) { case ast { Int(n) -> [TokenValue(n)] } }
```

**Complex case fails**:
```gleam
// Constructor for left_assoc
fn(first, rest) { fold_operators(first, rest, operators) }

// Deconstructor (impossible to auto-generate)
fn(ast) { 
  // How do we know which operators were used?
  // Add(Add(1, 2), 3) could be from "1 + 2 + 3" or "(1 + 2) + 3"
  // Need to reconstruct the exact sequence
}
```

**Why automation fails**: `fold_operators` is a many-to-one function. Inverting it requires solving an ambiguous reconstruction problem.

---

### Problem 5: AST Structure Mismatch

**Grammar defines flat structure**:
```gleam
// left_assoc creates: Add(Add(1, 2), 3)
grammar.left_assoc("Expr", "Term", [...])
```

**Formatter needs tree structure**:
```gleam
// Must know: this Add came from left_assoc at prec 10
// Not just: this is an Add
```

**Why automation fails**: Grammar combinators (`left_assoc`, `right_assoc`) create specific AST structures, but that information is lost after construction.

---

## What IS Possible: UX Improvements

While full automation is not feasible, we can significantly improve the UX:

### Improvement 1: Formatter Combinators (HIGH VALUE)

**Current** (manual everything):
```gleam
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    // ... repetitive for each constructor
  }
}
```

**Improved** (combinators mirroring grammar):
```gleam
// Define formatter once, reuse for all types
pub fn format_with(grammar: Grammar(a), ast: a) -> Doc {
  format_by_rule(grammar, grammar.start, ast, 0)
}

// Helper that handles precedence automatically
fn format_binop_auto(
  grammar: Grammar(a),
  op_name: String,  // e.g., "add"
  left: a,
  right: a,
  parent_prec: Int,
) -> Doc {
  let op = dict.get(grammar.operators, op_name) |> option.unwrap(...)
  let left_doc = format_with(grammar, left)
  let right_doc = format_with(grammar, right)
  format_binop(left_doc, right_doc, op.layout.separator, op.precedence, parent_prec)
}
```

**Benefit**: ~40% reduction in formatter boilerplate

---

### Improvement 2: Boilerplate Generation (HIGH VALUE)

**Generate formatter skeleton from AST type**:

```gleam
// Run: gleam run generate-formatter --type Expr

// Generated:
pub fn format_Expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> todo("format Int")
    Add(l, r) -> todo("format Add")
    Sub(l, r) -> todo("format Sub")
    Mul(l, r) -> todo("format Mul")
    Div(l, r) -> todo("format Div")
  }
}

// Developer fills in todos:
pub fn format_Expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))  // ✓ Filled
    Add(l, r) -> format_binop_auto(..., "add", l, r, parent_prec)  // ✓ Filled
    // ...
  }
}
```

**Benefit**: ~30% reduction in initial setup time

---

### Improvement 3: Precedence Metadata in AST (MEDIUM VALUE)

**Add precedence info to AST**:

```gleam
// Current
pub type Expr {
  Add(Expr, Expr)
}

// Improved (with precedence metadata)
pub type Expr {
  Add(Expr, Expr, precedence: Int)  // Carries precedence
}

// Or: wrapper type
pub type Preceded(a) {
  Preceded(value: a, precedence: Int)
}

// Grammar produces:
fn(values) { Preceded(Add(l, r), 10) }
```

**Benefit**: Formatter can access precedence without manual threading

**Cost**: AST becomes more complex, all code must unwrap `Preceded`

---

### Improvement 4: Grammar-Derived Formatter Registry (MEDIUM VALUE)

**Store formatter functions in grammar**:

```gleam
pub type Grammar(a) {
  Grammar(
    // ... existing fields
    formatters: Dict(String, fn(a, Int) -> Doc),  // NEW
  )
}

// When defining grammar:
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define
  
  g
  |> grammar.rule("Expr", [
    grammar.alt_with_formatter(
      pattern,
      constructor,
      deconstructor,
      formatter,  // Registered in grammar
    ),
  ])
}

// Formatter uses registry:
pub fn format(ast: Expr) -> Doc {
  format_by_rule(calc_grammar(), "Expr", ast, 0)
}

fn format_by_rule(grammar, rule_name, ast, parent_prec) -> Doc {
  let formatter = dict.get(grammar.formatters, rule_name) |> option.unwrap(...)
  formatter(ast, parent_prec)
}
```

**Benefit**: Centralizes formatter logic, enables composition

**Cost**: More complex grammar API

---

### Improvement 5: Better Default Formatters (LOW VALUE)

**Provide smarter defaults**:

```gleam
// Current default (useless)
formatter: fn(_ast, _) { formatter.text("<ast>") }

// Improved default (uses inspect)
formatter: fn(ast, _) { formatter.text(inspect(ast)) }

// Even better: structural formatting
formatter: fn(ast, _) { format_structural(ast) }

fn format_structural(ast: a) -> Doc {
  // Generic structural formatting (like inspect but prettier)
  // Doesn't handle precedence, but works for debugging
}
```

**Benefit**: Works out-of-the-box for debugging

**Cost**: Doesn't solve precedence/layout

---

## Recommended Approach

### Phase 1: Formatter Combinators (1-2 days)

**Goal**: Reduce formatter boilerplate by ~40%

**Implementation**:
```gleam
// src/syntax/formatter.gleam

/// Format binary operator with automatic precedence handling
pub fn format_binop(
  left: Doc,
  right: Doc,
  op: String,
  prec: Int,
  parent_prec: Int,
) -> Doc {
  let doc = concat([left, text(op), right])
  case prec < parent_prec {
    True -> parens(doc)
    False -> doc
  }
}

/// Format unary operator
pub fn format_unary(op: String, operand: Doc) -> Doc {
  concat([text(op), operand])
}

/// Format wrapped (parens, braces, etc.)
pub fn format_wrapped(open: String, content: Doc, close: String) -> Doc {
  concat([text(open), content, text(close)])
}

/// Format list with separator
pub fn format_list(items: List(Doc), sep: Doc) -> Doc {
  join(sep, items)
}

/// Format with layout (soft breaks)
pub fn format_with_layout(
  items: List(#(Doc, LayoutHint)),
  indent: Int,
) -> Doc {
  // Implementation using soft/hard breaks
}
```

**Usage**:
```gleam
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) ->
      formatter.format_binop(
        format_expr(l, 10),
        format_expr(r, 11),
        " + ",
        10,
        parent_prec,
      )
  }
}
```

---

### Phase 2: Boilerplate Generator (2-3 days)

**Goal**: Reduce initial formatter setup time by ~30%

**Implementation**:
```gleam
// src/codegen/formatter_gen.gleam

pub fn generate_formatter_skeleton(ast_type: String) -> String {
  // Parse AST type definition
  // Generate case expression with todos
  // Output to file
}

// CLI command:
// gleam run generate-formatter --type Expr --output src/mylang/formatter.gleam
```

**Generated Output**:
```gleam
// Generated by: gleam run generate-formatter --type Expr

pub fn format_Expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> todo("format Int: use formatter.text(int.to_string(n))")
    Add(l, r) -> todo("format Add: use formatter.format_binop(...)")
    Sub(l, r) -> todo("format Sub: use formatter.format_binop(...)")
    Mul(l, r) -> todo("format Mul: use formatter.format_binop(...)")
    Div(l, r) -> todo("format Div: use formatter.format_binop(...)")
  }
}
```

---

### Phase 3: Documentation & Examples (1 day)

**Goal**: Make manual formatters easier to write

**Implementation**:
- Document formatter best practices
- Provide more examples (lambda calculus, let-language, etc.)
- Create formatter cookbook (common patterns)

---

## Why NOT Pursue Full Automation

### Technical Reasons

1. **Information loss is fundamental** - Can't recover what wasn't preserved
2. **Precedence handling requires AST changes** - Significant architectural impact
3. **Layout threading is complex** - Would require major refactoring
4. **Deconstructor inversion is ambiguous** - Many-to-one functions can't be inverted

### Practical Reasons

1. **Manual formatters are better** - More control, better output
2. **Cost/benefit is poor** - ~80% of the work for ~20% gain
3. **Existing approach works** - Manual formatters are working well
4. **UX improvements give 80% benefit** - For ~20% of the effort

---

## Conclusion

**Full automatic formatter generation is NOT feasible** without:
- Major architectural changes (precedence in AST, layout threading)
- Solving ambiguous reconstruction problems
- Accepting lower-quality output

**UX improvements ARE feasible** and provide ~60-70% of the benefit:
- Formatter combinators (1-2 days)
- Boilerplate generator (2-3 days)
- Better documentation (1 day)

**Recommendation**: Implement UX improvements, document manual formatter patterns, accept that some manual work is necessary for high-quality formatting.

---

## Related Documents

- **[syntax-library.md](../syntax-library.md)** - Syntax library documentation
- **[plans/grammar/04-formatter-library.md](plans/grammar/04-formatter-library.md)** - Formatter library status
- **[plans/grammar/02-grammar-dsl.md](plans/grammar/02-grammar-dsl.md)** - Grammar DSL specification

---

## References

- [Formatter Implementation](../src/syntax/formatter.gleam)
- [Grammar Implementation](../src/syntax/grammar.gleam)
- [Calculator Example](../src/examples/calc.gleam)
- [Wadler's "A Prettier Printer"](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf)
