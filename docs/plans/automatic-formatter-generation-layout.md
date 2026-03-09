# Automatic Formatter Generation - Layout-Aware Design

> **Goal**: Single source of truth for grammar that generates both parser and formatter with full layout control
> **Status**: Design analysis and recommendations
> **Date**: March 2025

---

## Key Requirement: Two Layouts Per Definition

Every grammar rule should support:
1. **Single-line layout** - Compact, for short expressions
2. **Multi-line layout** - Expanded with newlines/indentation, for long expressions

The `formatter.gleam` library provides:
- `Line` - Soft line break (space when flat, newline when broken)
- `HardLine` - Always a newline
- `Group` - Try flat first, break if doesn't fit width

---

## Layout Metadata in Grammar

### Current LayoutStyle Type

```gleam
pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}
```

### Enhanced Layout Configuration

```gleam
pub type LayoutConfig {
  LayoutConfig(
    /// Single-line separator (e.g., " + ")
    inline_separator: String,
    /// Multi-line separator (e.g., "\n  + " with leading newline + indent)
    multiline_separator: String,
    /// When to break: Auto (based on width), Always, Never
    break_mode: BreakMode,
    /// Width threshold for Auto break mode
    break_width: Int,
    /// Indentation for multi-line layout
    indent: Int,
    /// Layout style: Inline, BreakAfter, BreakBefore, Block
    style: LayoutStyle,
  )
}

pub type BreakMode {
  BreakAuto      // Break based on width
  BreakAlways    // Always use multi-line layout
  BreakNever     // Always use single-line layout
}
```

### Usage in Grammar

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op_with_layout(
      "+", Add, 
      10, 
      LayoutConfig(
        inline_separator: " + ",
        multiline_separator: "\n  + ",  // Newline + 2-space indent
        break_mode: BreakAuto,
        break_width: 60,
        indent: 2,
        style: BreakAfterOperator(2),
      ),
    ),
  ])
}
```

---

## Layout Hints for Complex Cases

### Soft vs Hard Newlines

```gleam
pub type LayoutHint {
  /// Use soft newline (space when flat, newline when broken)
  SoftNewline
  /// Use hard newline (always newline)
  HardNewline
  /// Use space only (never break)
  SpaceOnly
  /// No separator (concat directly)
  NoSeparator
}

pub type LayoutConfig {
  LayoutConfig(
    // ... existing fields ...
    /// Separator hints for each position in sequence
    sequence_hints: List(LayoutHint),
  )
}
```

### Example: Function Definition with Mixed Layout

```gleam
// Function: fn(x: Int, y: Int) -> Int { x + y }
// Multi-line:
// fn(
//   x: Int,
//   y: Int,
// ) -> Int {
//   x + y
// }

grammar.rule("FnDef", [
  grammar.seq_with_layout([
    grammar.keyword("fn"),
    grammar.token("LParen"),
    grammar.sep1("Param", "Comma"),
    grammar.token("RParen"),
    grammar.token("Arrow"),
    grammar.ref("Type"),
    grammar.token("LBrace"),
    grammar.ref("Body"),
    grammar.token("RBrace"),
  ], LayoutConfig(
    sequence_hints: [
      SpaceOnly,       // "fn"
      NoSeparator,     // "("
      SoftNewline,     // params (break after each comma)
      SpaceOnly,       // ")"
      SpaceOnly,       // "->"
      SpaceOnly,       // type
      SoftNewline,     // "{"
      HardNewline,     // body (always on new line)
      NoSeparator,     // "}"
    ],
    break_mode: BreakAuto,
    break_width: 80,
    indent: 2,
  )),
])
```

---

## Phase 1 vs Phase 2: Trade-off Analysis

### Phase 1: Grammar-Guided Formatting (Current)

**Implementation:**
```gleam
// Grammar defines formatting metadata
grammar.op("+", Add, 10, LayoutConfig(
  inline_separator: " + ",
  multiline_separator: "\n  + ",
  break_mode: BreakAuto,
  break_width: 60,
  indent: 2,
  style: BreakAfterOperator(2),
))

// Formatter manually pattern matches
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> grammar.format_binary_op(grammar, "+", l, r, parent_prec, format_expr)
  }
}
```

**User Experience:**
- ✅ Clear what's happening (explicit pattern matching)
- ✅ Type-safe (exhaustive pattern matching)
- ✅ Easy to customize per-AST-constructor
- ❌ Repetitive (pattern match + operator keyword for each constructor)
- ❌ Easy to make mistakes (wrong operator keyword)

**Lines of Code:**
```
Grammar: 20 lines (with layout config)
Formatter: 15 lines (pattern matching + helper calls)
Total: 35 lines
```

### Phase 2: Automatic Operator Lookup

**Implementation:**
```gleam
// Grammar defines formatting metadata + AST tag
grammar.op("+", Add, 10, LayoutConfig(...), ast_tag: "Add")

// Formatter uses automatic lookup
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case grammar.format_by_operator(grammar, ast, parent_prec, get_expr_tag) {
    Some(doc) -> doc
    None => format_atom(ast)
  }
}

// Still need tag function (pattern matching)
fn get_expr_tag(ast: Expr) -> Option(String) {
  case ast {
    Add(_, _) -> Some("Add")
    Sub(_, _) -> Some("Sub")
    Int(_) -> None
  }
}
```

**User Experience:**
- ✅ Less repetitive in main formatter
- ✅ Centralized operator metadata in grammar
- ❌ Still need `get_expr_tag()` function (pattern matching)
- ❌ More complex grammar definition (ast_tag parameter)
- ❌ Harder to customize per-AST-constructor (need to override automatic behavior)

**Lines of Code:**
```
Grammar: 25 lines (with layout config + ast_tag)
Formatter: 10 lines (automatic lookup)
Tag function: 10 lines (pattern matching)
Total: 45 lines
```

### Phase 3: Full Automation with Macros (Future)

**Implementation:**
```gleam
// Grammar defines everything
grammar.op("+", Add, 10, LayoutConfig(...))

// Formatter is fully automatic (no pattern matching)
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  grammar.format_ast(grammar, ast, parent_prec)
}

// Macro auto-generates:
// - get_ast_tag() function
// - Operand extractors
// - Default layout configs
```

**User Experience:**
- ✅ Minimal boilerplate
- ✅ Single source of truth (grammar)
- ❌ Requires Gleam macros (not stable)
- ❌ Less control over edge cases

**Lines of Code:**
```
Grammar: 20 lines (with layout config)
Formatter: 5 lines (fully automatic)
Total: 25 lines
```

---

## Recommendation: Enhanced Phase 1

Based on the trade-offs, I recommend **Enhanced Phase 1**:

### Keep Manual Pattern Matching, But Improve Layout Support

**Rationale:**
1. **Pattern matching is explicit and clear** - Users know exactly what's happening
2. **Type-safe** - Compiler checks exhaustiveness
3. **Easy to customize** - Special cases handled naturally in pattern matching
4. **Layout metadata in grammar** - Single source of truth for formatting rules

### Enhance Layout Configuration

Add rich layout metadata to grammar:

```gleam
pub fn op_with_layout(
  keyword: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
  layout: LayoutConfig,
) -> Operator(a)

pub type LayoutConfig {
  LayoutConfig(
    inline_separator: String,
    multiline_separator: String,
    break_mode: BreakMode,
    break_width: Int,
    indent: Int,
    style: LayoutStyle,
  )
}
```

### Provide Helper Functions

```gleam
// Default layout for binary operators
pub fn default_op_layout(separator: String) -> LayoutConfig {
  LayoutConfig(
    inline_separator: separator,
    multiline_separator: "\n  " <> separator,
    break_mode: BreakAuto,
    break_width: 60,
    indent: 2,
    style: BreakAfterOperator(2),
  )
}

// Compact layout (never break)
pub fn compact_layout(separator: String) -> LayoutConfig {
  LayoutConfig(
    inline_separator: separator,
    multiline_separator: separator,
    break_mode: BreakNever,
    break_width: 9999,
    indent: 0,
    style: Inline,
  )
}

// Block layout (always break)
pub fn block_layout(open: String, close: String, indent: Int) -> LayoutConfig {
  LayoutConfig(
    inline_separator: " ",
    multiline_separator: "\n",
    break_mode: BreakAlways,
    break_width: 0,
    indent: indent,
    style: Block(open, close, indent),
  )
}
```

### Example: Complete Calc Grammar with Layout

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op_with_layout("+", Add, 10, grammar.default_op_layout(" + ")),
    grammar.op_with_layout("-", Sub, 10, grammar.default_op_layout(" - ")),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op_with_layout("*", Mul, 20, grammar.default_op_layout(" * ")),
    grammar.op_with_layout("/", Div, 20, grammar.default_op_layout(" / ")),
  ])
  |> grammar.rule_with_layout("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ], LayoutConfig(
    inline_separator: "",
    multiline_separator: "",
    break_mode: BreakNever,  // Atoms never break
    break_width: 9999,
    indent: 0,
    style: Inline,
  ))
}

// Formatter uses layout metadata
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  let grammar = calc_grammar()
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> grammar.format_binary_op(grammar, "+", l, r, parent_prec, format_expr)
    Sub(l, r) -> grammar.format_binary_op(grammar, "-", l, r, parent_prec, format_expr)
    Mul(l, r) -> grammar.format_binary_op(grammar, "*", l, r, parent_prec, format_expr)
    Div(l, r) -> grammar.format_binary_op(grammar, "/", l, r, parent_prec, format_expr)
  }
}
```

---

## Summary

| Aspect | Phase 1 (Current) | Phase 2 (Auto Lookup) | Phase 3 (Macros) | Enhanced Phase 1 (Recommended) |
|--------|-------------------|----------------------|------------------|-------------------------------|
| Pattern matching | Manual | Manual (tag function) | None | Manual |
| Layout metadata | Basic | Basic | Auto-generated | **Rich** |
| Lines of code | 35 | 45 | 25 | 40 |
| Type safety | ✅ Full | ✅ Full | ⚠️ Depends on macro | ✅ Full |
| Customization | ✅ Easy | ⚠️ Harder | ❌ Limited | ✅ Easy |
| User experience | Good | Worse | Best (future) | **Best (now)** |

**Recommendation:** Implement **Enhanced Phase 1** with rich layout configuration. This gives the best balance of:
- ✅ Single source of truth (grammar has all formatting rules)
- ✅ Type-safe (pattern matching is exhaustive)
- ✅ Flexible layout control (soft/hard newlines, break modes)
- ✅ Easy to customize per-AST-constructor
- ✅ Works now (no macros needed)

Phase 2 (automatic operator lookup) adds complexity without significant UX improvement. Save it for later if users request it.
