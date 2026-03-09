# Layout-Aware Grammar Design - Refined

> **Goal**: Flexible layout configuration that separates global settings from AST-specific hints
> **Status**: Refined design based on feedback
> **Date**: March 2025

---

## Key Insights

### 1. Separate Global vs AST-Specific Settings

**Global formatter settings** (apply to all rules):
- `width`: Max line width before breaking (e.g., 80)
- `indent_string`: Indentation unit (e.g., `"  "` or `"\t"`)

**AST-specific layout hints** (per rule/operator):
- Where breaks are allowed
- Break preference (soft vs hard)
- Separator strings (without hardcoded indentation)

### 2. Layout Hints in Grammar Structure

Instead of hardcoding `multiline_separator: "\n  + "`, specify **where breaks can occur**:

```gleam
// Instead of:
LayoutConfig(
  inline_separator: " + ",
  multiline_separator: "\n  + ",  // Hardcoded indent!
)

// Use layout hints in sequence:
[Expr, SoftBreak, "+", Expr]
```

### 3. Support Complex Layouts

Ternary operators, pattern matching, function definitions need fine-grained control:

```gleam
// Ternary: cond ? then : else
// Multi-line:
// cond
//   ? then
//   : else

[Cond, SoftBreak, "?", Then, SoftBreak, ":", Else]

// Function definition:
// fn(x: Int, y: Int) -> Int { body }
// Multi-line:
// fn(
//   x: Int,
//   y: Int,
// ) -> Int {
//   body
// }

["fn", "(", Params, SoftBreak, ")", "->", Type, SoftBreak, "{", HardBreak, Body, HardBreak, "}"]
```

---

## Refined Data Structures

### Global Formatter Configuration

```gleam
pub type FormatterConfig {
  FormatterConfig(
    /// Maximum line width before breaking (global)
    width: Int,
    /// Indentation string (global): "  " or "\t"
    indent_string: String,
    /// Indentation level (number of indent_string units)
    indent_level: Int,
  )
}

pub fn default_formatter_config() -> FormatterConfig {
  FormatterConfig(
    width: 80,
    indent_string: "  ",
    indent_level: 0,
  )
}
```

### Layout Hints

```gleam
pub type LayoutHint {
  /// Allow soft break here (space when flat, newline+indent when broken)
  SoftBreak
  /// Always break here (newline+indent, even in short expressions)
  HardBreak
  /// Never break, always use space
  Space
  /// No separator (concat directly)
  None
}
```

### Sequence with Layout Hints

```gleam
pub type SeqItem(a) {
  SeqItem(
    pattern: Pattern(a),
    layout_hint: LayoutHint,
  )
}

pub type Pattern(a) {
  // ... existing patterns ...
  /// Sequence with layout hints between elements
  SeqWithLayout(items: List(SeqItem(a)))
}
```

### Operator Layout Configuration

```gleam
pub type OperatorLayout {
  OperatorLayout(
    /// Separator string (no indentation - added automatically)
    separator: String,
    /// Where breaks are allowed relative to operator
    break_before: Bool,  // Can break before operator?
    break_after: Bool,   // Can break after operator?
    /// Indent additional level for RHS when broken
    indent_rhs: Bool,
  )
}

pub fn default_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: False,
    break_after: True,   // Break after operator (like " +\n")
    indent_rhs: True,    // Indent RHS when broken
  )
}

pub fn break_before_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: True,  // Break before operator (like "\n+ ")
    break_after: False,
    indent_rhs: False,
  )
}
```

### Enhanced Operator Type

```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    precedence: Int,
    associativity: Associativity,
    layout: OperatorLayout,
  )
}
```

---

## Grammar Definition API

### Sequence with Layout Hints

```gleam
pub fn seq_with_layout<A>(
  items: List(#(Pattern(A), LayoutHint)),
) -> Pattern(A) {
  SeqWithLayout(
    list.map(items, fn(#(pattern, hint)) {
      SeqItem(pattern, hint)
    })
  )
}

// Usage:
grammar.seq_with_layout([
  #(grammar.ref("Cond"), Space),
  #(grammar.token("Question"), SoftBreak),
  #(grammar.ref("Then"), SoftBreak),
  #(grammar.token("Colon"), Space),
  #(grammar.ref("Else"), None),
])
```

### Operator with Layout

```gleam
pub fn op_with_layout<A>(
  keyword: String,
  constructor: fn(A, A) -> A,
  precedence: Int,
  layout: OperatorLayout,
) -> Operator(A) {
  Operator(
    keyword: keyword,
    constructor: constructor,
    precedence: precedence,
    associativity: Left,
    layout: layout,
  )
}

// Usage:
grammar.left_assoc("Expr", "Term", [
  grammar.op_with_layout("+", Add, 10, default_op_layout(" + ")),
  grammar.op_with_layout("-", Sub, 10, break_before_op_layout("\n- ")),
])
```

---

## Formatter Implementation

### Generic Sequence Formatter

```gleam
pub fn format_sequence_with_layout<A>(
  grammar: Grammar(A),
  items: List(SeqItem(A)),
  values: List(Value(A)),
  config: FormatterConfig,
  format_value: fn(Value(A), FormatterConfig) -> Doc,
) -> Doc {
  format_sequence_loop(items, values, config, format_value, [])
}

fn format_sequence_loop<A>(
  items: List(SeqItem(A)),
  values: List(Value(A)),
  config: FormatterConfig,
  format_value: fn(Value(A), FormatterConfig) -> Doc,
  docs: List(Doc),
) -> Doc {
  case items, values {
    [item, ..rest_items], [value, ..rest_values] -> {
      let doc = format_value(value, config)
      let separator = case item.layout_hint {
        SoftBreak -> formatter.line()
        HardBreak -> formatter.hardline()
        Space -> formatter.space()
        None -> formatter.empty()
      }
      format_sequence_loop(
        rest_items,
        rest_values,
        config,
        format_value,
        list.append(docs, [doc, separator])
      )
    }
    [], [] -> formatter.concat(docs)
    _, _ -> formatter.concat(docs)  // Mismatch, just format what we have
  }
}
```

### Binary Operator Formatter

```gleam
pub fn format_binary_op<A>(
  grammar: Grammar(A),
  op_name: String,
  left: A,
  right: A,
  parent_prec: Int,
  format_ast: fn(A, Int, FormatterConfig) -> Doc,
  config: FormatterConfig,
) -> Doc {
  case dict.get(grammar.operators, op_name) {
    Ok(op) -> {
      // Calculate precedence for operands
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
      
      let left_doc = format_ast(left, left_prec, config)
      
      // Format separator with potential line break
      let separator = case op.layout.break_before {
        True -> formatter.concat([formatter.line(), formatter.text(op.layout.separator)])
        False -> formatter.text(op.layout.separator)
      }
      
      // Format right side with potential indentation
      let right_config = case op.layout.indent_rhs {
        True -> FormatterConfig(..config, indent_level: config.indent_level + 1)
        False -> config
      }
      let right_doc = format_ast(right, right_prec, right_config)
      
      let inner = formatter.concat([
        left_doc,
        separator,
        case op.layout.break_after {
          True -> formatter.line()
          False -> formatter.empty()
        },
        right_doc,
      ])
      
      // Add parentheses if needed
      case op.precedence < parent_prec {
        True -> formatter.parens(inner)
        False => inner
      }
    }
    Error(_) => formatter.text("<unknown op: " <> op_name <> ">")
  }
}
```

---

## Complete Examples

### Example 1: Calculator with Layout Hints

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op_with_layout("+", Add, 10, default_op_layout(" + ")),
    grammar.op_with_layout("-", Sub, 10, default_op_layout(" - ")),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op_with_layout("*", Mul, 20, default_op_layout(" * ")),
    grammar.op_with_layout("/", Div, 20, default_op_layout(" / ")),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(
      grammar.seq_with_layout([
        #(grammar.token("LParen"), None),
        #(grammar.ref("Expr"), Space),
        #(grammar.token("RParen"), None),
      ]),
      fn([_, expr, _]) { expr },
    ),
  ])
}

// Usage:
// Short: "1 + 2 * 3"
// Long (breaks after operator):
// "1 +
//   2 * 3"
```

### Example 2: Ternary Operator

```gleam
grammar.rule("Ternary", [
  grammar.alt(
    grammar.seq_with_layout([
      #(grammar.ref("Cond"), Space),
      #(grammar.token("Question"), SoftBreak),
      #(grammar.ref("Then"), SoftBreak),
      #(grammar.token("Colon"), Space),
      #(grammar.ref("Else"), None),
    ]),
    fn([cond, _, then_, _, else_]) { Ternary(cond, then_, else_) },
  ),
])

// Short: "cond ? then : else"
// Long:
// "cond
//   ? then
//   : else"
```

### Example 3: Function Definition

```gleam
grammar.rule("FnDef", [
  grammar.alt(
    grammar.seq_with_layout([
      #(grammar.keyword("fn"), None),
      #(grammar.token("LParen"), None),
      #(grammar.sep1("Param", "Comma"), SoftBreak),
      #(grammar.token("RParen"), SoftBreak),
      #(grammar.token("Arrow"), Space),
      #(grammar.ref("ReturnType"), SoftBreak),
      #(grammar.token("LBrace"), HardBreak),
      #(grammar.ref("Body"), HardBreak),
      #(grammar.token("RBrace"), None),
    ]),
    fn([_, _, params, _, _, ret, _, body, _]) { FnDef(params, ret, body) },
  ),
])

// Short: "fn(x: Int, y: Int) -> Int { x + y }"
// Long:
// "fn(
//   x: Int,
//   y: Int,
// ) -> Int {
//   x + y
// }"
```

---

## Implementation Checklist

### Phase 1: Core Layout Support

- [ ] Add `FormatterConfig` type with `width`, `indent_string`, `indent_level`
- [ ] Add `LayoutHint` type (`SoftBreak`, `HardBreak`, `Space`, `None`)
- [ ] Add `SeqItem` type with pattern + layout hint
- [ ] Add `SeqWithLayout` pattern variant
- [ ] Add `seq_with_layout()` helper function
- [ ] Add `OperatorLayout` type
- [ ] Update `Operator` type to include `layout: OperatorLayout`
- [ ] Add `op_with_layout()` helper function
- [ ] Implement `format_sequence_with_layout()` generic helper
- [ ] Update `format_binary_op()` to use `OperatorLayout`
- [ ] Update calc grammar with layout hints
- [ ] Add tests for layout breaking

### Phase 2: Advanced Layout Features

- [ ] Add `break_width` per-rule (override global width)
- [ ] Add `always_break` flag for forcing multi-line
- [ ] Add nested indentation tracking
- [ ] Add layout hints for choice/alternative patterns
- [ ] Add tests for complex layouts (ternary, functions)

---

## Benefits of Refined Design

| Aspect | Old Design | Refined Design |
|--------|------------|----------------|
| **Indent handling** | Hardcoded in separator | Global `indent_string` + `indent_level` |
| **Break control** | Per-operator config | Layout hints in sequence |
| **Flexibility** | Limited to operators | Works for any sequence |
| **Composability** | Each rule needs full config | Hints compose naturally |
| **Complex layouts** | Hard to express | Natural with hints |

### Example Comparison

**Old Design:**
```gleam
LayoutConfig(
  inline_separator: " + ",
  multiline_separator: "\n  + ",  // Hardcoded indent!
)
```

**Refined Design:**
```gleam
[Expr, SoftBreak, "+", Expr]
// Uses global indent_string automatically
```

The refined design is more flexible, composable, and doesn't hardcode indentation.
