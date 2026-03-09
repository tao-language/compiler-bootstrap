# Automatic Formatter Generation Design

> **Goal**: Generate formatter automatically from grammar definition
> **Status**: Revised design based on prior implementation
> **Date**: March 2025

---

## Problem Analysis

The user correctly identified the issue with the deconstructor approach:

> "Wouldn't this approach require you to define the deconstructors + the grammar? With this approach each deconstructor must handle all cases, otherwise it won't compile. This will be significantly more verbose."

**Yes, this is correct.** Requiring deconstructors defeats the purpose of automatic generation.

### Key Insight

The formatter is **AST-directed** (traverses AST), but should get formatting metadata from the **grammar** (precedence, separators, layout). The grammar is the single source of truth for formatting rules, not the formatter implementation.

---

## Revised Approach: Grammar-Guided Formatting

### Core Idea

Instead of trying to match AST nodes to grammar rules (which requires deconstructors), we:

1. **Store formatting metadata in the grammar** (precedence, separators, layout)
2. **Formatter is still written manually** but is minimal - just pattern matching on AST
3. **Formatter queries grammar for formatting rules** based on AST structure

This is a **hybrid approach**:
- Grammar: Single source of truth for formatting rules (precedence, separators)
- Formatter: Minimal pattern matching that uses grammar metadata

### Benefits

1. **No deconstructors needed** - formatter pattern matches on AST directly
2. **Single source of truth** - precedence, separators defined once in grammar
3. **Type-safe** - no runtime type inspection needed
4. **Minimal boilerplate** - formatter is just pattern matching + grammar lookups

---

## Design

### Grammar Stores Formatting Metadata

```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
    // Formatting metadata
    separator: String,        // e.g., " + "
    left_prec_offset: Int,    // 0 for left-assoc, 1 for right-assoc
    right_prec_offset: Int,   // 1 for left-assoc, 0 for right-assoc
  )
}

pub type Rule(a) {
  Rule(
    name: String,
    precedence: Int,
    // Formatting metadata for this rule
    format_kind: FormatKind,
  )
}

pub type FormatKind {
  /// Atom: just format the value (e.g., numbers, identifiers)
  FormatAtom
  /// Sequence: format children with separators
  FormatSeq(separators: List(String))
  /// Parenthesized: wrap in parens
  FormatParens
  /// Custom: user-provided format function
  FormatCustom(fn(a) -> String)
}
```

### Formatter Uses Grammar Metadata

```gleam
pub fn format(grammar: Grammar(a), ast: a) -> String {
  let doc = format_ast(grammar, ast, -1)
  formatter.render(doc, 80)
}

fn format_ast(grammar: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  // Formatter pattern matches on AST (AST-directed)
  case ast {
    // Atoms: use grammar's format_kind
    Int(n) -> format_atom(grammar, ast, int.to_string(n), parent_prec)
    
    // Binary ops: use grammar's operator metadata
    Add(l, r) -> format_binary_op(grammar, "add", l, r, parent_prec)
    Sub(l, r) -> format_binary_op(grammar, "sub", l, r, parent_prec)
    Mul(l, r) -> format_binary_op(grammar, "mul", l, r, parent_prec)
    Div(l, r) -> format_binary_op(grammar, "div", l, r, parent_prec)
    
    // Unknown: fallback
    _ -> formatter.text("<unknown>")
  }
}

fn format_binary_op(
  grammar: Grammar(a),
  op_name: String,
  left: a,
  right: a,
  parent_prec: Int,
) -> Doc {
  // Get operator metadata from grammar
  case dict.get(grammar.operators, op_name) {
    Ok(op) -> {
      let left_doc = format_ast(grammar, left, op.precedence + op.left_prec_offset)
      let right_doc = format_ast(grammar, right, op.precedence + op.right_prec_offset)
      
      let inner = formatter.concat([
        left_doc,
        formatter.text(op.separator),
        right_doc,
      ])
      
      // Add parens if needed based on precedence
      case op.precedence < parent_prec {
        True -> formatter.parens(inner)
        False -> inner
      }
    }
    Error(_) -> formatter.text("<unknown op>")
  }
}
```

### Grammar Definition

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10, " + "),  // keyword, constructor, prec, separator
    grammar.op("-", Sub, 10, " - "),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op("*", Mul, 20, " * "),
    grammar.op("/", Div, 20, " / "),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}
```

### Formatter Implementation

```gleam
pub fn format(ast: Expr) -> String {
  format_ast(calc_grammar(), ast, -1) |> formatter.render_default
}

fn format_ast(grammar: Grammar(Expr), ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    
    // Use grammar metadata for operators
    Add(l, r) -> format_binary_op(grammar, "add", l, r, parent_prec)
    Sub(l, r) -> format_binary_op(grammar, "sub", l, r, parent_prec)
    Mul(l, r) -> format_binary_op(grammar, "mul", l, r, parent_prec)
    Div(l, r) -> format_binary_op(grammar, "div", l, r, parent_prec)
  }
}
```

---

## Key Differences from Prior Approaches

### Prior Approach (Deconstructors)

```gleam
// Verbose - requires deconstructors for every AST constructor
grammar.op_full("+", Add, fn(ast) { case ast { Add(l, r) -> #(l, r) } }, 10)
```

**Problem**: Every AST constructor needs a deconstructor, which is verbose and error-prone.

### Revised Approach (Grammar Metadata)

```gleam
// Simple - just provide formatting metadata
grammar.op("+", Add, 10, " + ")

// Formatter pattern matches on AST (no deconstructors needed)
fn format_ast(grammar, ast, parent_prec) {
  case ast {
    Add(l, r) -> format_binary_op(grammar, "add", l, r, parent_prec)
    // ...
  }
}
```

**Benefit**: Formatter is minimal pattern matching, grammar has all formatting rules.

---

## Implementation Steps

### Step 1: Add Formatting Metadata to Operator

```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    precedence: Int,
    associativity: Associativity,
    // NEW: Formatting metadata
    separator: String,
  )
}
```

### Step 2: Update Operator Helper

```gleam
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  separator: String,
) -> Operator(a) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    precedence: precedence,
    associativity: Left,
    separator: separator,
  )
}
```

### Step 3: Add Operator Registry to Grammar

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
    // NEW: Operator registry for formatting
    operators: Dict(String, Operator(a)),  // "add" → Operator
  )
}
```

### Step 4: Implement Generic Formatter Helpers

```gleam
pub fn format_binary_op(
  grammar: Grammar(a),
  op_name: String,
  left: a,
  right: a,
  parent_prec: Int,
) -> Doc {
  case dict.get(grammar.operators, op_name) {
    Ok(op) -> {
      let left_prec = op.precedence + case op.associativity {
        Left -> 0
        Right -> 1
        NonAssoc -> 1
      }
      let right_prec = op.precedence + case op.associativity {
        Left -> 1
        Right -> 0
        NonAssoc -> 1
      }
      
      let left_doc = format_ast(grammar, left, left_prec)
      let right_doc = format_ast(grammar, right, right_prec)
      
      let inner = formatter.concat([
        left_doc,
        formatter.text(op.separator),
        right_doc,
      ])
      
      case op.precedence < parent_prec {
        True -> formatter.parens(inner)
        False -> inner
      }
    }
    Error(_) -> formatter.text("<unknown>")
  }
}
```

### Step 5: Update Calc Formatter

```gleam
// Old: Manual formatting with hardcoded precedence
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 11), format_expr(r, 10), " + ", 10, parent_prec)
    // ...
  }
}

// New: Use grammar metadata
fn format_ast(grammar: Grammar(Expr), ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binary_op(grammar, "add", l, r, parent_prec)
    Sub(l, r) -> format_binary_op(grammar, "sub", l, r, parent_prec)
    Mul(l, r) -> format_binary_op(grammar, "mul", l, r, parent_prec)
    Div(l, r) -> format_binary_op(grammar, "div", l, r, parent_prec)
  }
}
```

---

## Benefits

### Code Comparison

**Old (Manual Formatter)**:
```gleam
// 40 lines grammar + 40 lines manual formatter
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 11), format_expr(r, 10), " + ", 10, parent_prec)
    Sub(l, r) -> format_binop(format_expr(l, 11), format_expr(r, 10), " - ", 10, parent_prec)
    Mul(l, r) -> format_binop(format_expr(l, 21), format_expr(r, 20), " * ", 20, parent_prec)
    Div(l, r) -> format_binop(format_expr(l, 21), format_expr(r, 20), " / ", 20, parent_prec)
  }
}
```

**New (Grammar-Guided)**:
```gleam
// 40 lines grammar + 15 lines formatter
fn format_ast(grammar: Grammar(Expr), ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binary_op(grammar, "add", l, r, parent_prec)
    Sub(l, r) -> format_binary_op(grammar, "sub", l, r, parent_prec)
    Mul(l, r) -> format_binary_op(grammar, "mul", l, r, parent_prec)
    Div(l, r) -> format_binary_op(grammar, "div", l, r, parent_prec)
  }
}
```

**Reduction**: 80 lines → 55 lines (31% reduction)

### Single Source of Truth

| Aspect | Old | New |
|--------|-----|-----|
| Precedence | Hardcoded in formatter | Defined in grammar |
| Separators | Hardcoded in formatter | Defined in grammar |
| Associativity | Implicit in formatter | Defined in grammar |
| AST pattern matching | Manual | Manual (unchanged) |

**Key win**: Formatting rules (precedence, separators) are defined once in grammar, not duplicated in formatter.

---

## Future: Full Automatic Generation

The next step is to eliminate the manual pattern matching entirely. This requires:

1. **AST tags**: Each AST constructor has a tag (e.g., `AddTag`, `MulTag`)
2. **Tag-based lookup**: Grammar maps tags to operators
3. **Generic formatter**: No pattern matching needed

```gleam
// AST with tags
pub type Expr {
  Int(Int)
  Add(Expr, Expr)
  // ...
}

pub fn expr_tag(ast: Expr) -> ExprTag {
  case ast {
    Int(_) -> IntTag
    Add(_, _) -> AddTag
    // ...
  }
}

// Grammar maps tags to operators
pub type Grammar(a) {
  Grammar(
    // ...
    operator_by_tag: Dict(ExprTag, Operator(a)),
  )
}

// Generic formatter - no pattern matching!
pub fn format_ast(grammar: Grammar(a), ast: a, parent_prec: Int) -> Doc {
  let tag = get_tag(ast)  // User-provided tag function
  case dict.get(grammar.operator_by_tag, tag) {
    Some(op) -> {
      let #(left, right) = op.deconstructor(ast)  // Still need deconstructor
      // ... format as binary op
    }
    None => format_atom(grammar, ast, parent_prec)
  }
}
```

But this still requires deconstructors. The **true** automatic generation requires:

1. **Gleam macros** to auto-generate deconstructors from AST type
2. **Or**: Store both constructor and deconstructor in grammar (verbose)

For now, the **grammar-guided** approach is the best balance of simplicity and maintainability.

---

## Summary

The revised approach:

1. **Grammar stores formatting metadata** (precedence, separators, layout)
2. **Formatter is minimal** - just pattern matching on AST + grammar lookups
3. **No deconstructors needed** - formatter pattern matches directly on AST
4. **Single source of truth** - formatting rules defined once in grammar

This is the simplest and most maintainable approach given Gleam's type system limitations.
