# Operator Metadata Query API Plan

> **Goal**: Single source of truth for operator metadata with minimal, composable structure
> **Status**: 📋 Plan
> **Date**: March 2025 (Updated: Postfix pattern approach)

---

## Core Insight

**All operators are one of four kinds**: `Prefix`, `Postfix`, `InfixLeft`, `InfixRight`

**Ternary, slice, index, call are NOT new kinds** - they're **Infix operators with structured RHS**.

The pattern for infix operators:
```
lhs <infix_op> rhs_expr <postfix_structure>
```

Examples:
| Operator | lhs | infix_op | rhs | postfix |
|----------|-----|----------|-----|-----------|
| `x + y` | x | `+` | y | (nothing) |
| `a[i]` | a | `[` | i | `]` |
| `f(x)` | f | `(` | x | `)` |
| `a ? b : c` | a | `?` | b | `: c` |
| `a[b:c]` | a | `[` | b | `:c]` |
| `if a then b else c` | a | `then` | b | `else c` |

**Postfix structure is recursive**:
- Nothing (binary ops)
- Closing token (index, call)
- Separator + expr + more (ternary, slice)

---

## Type Definitions

### OperatorKind

```gleam
/// Only 4 operator kinds
pub type OperatorKind {
  Prefix      // -x, !x, ~x
  Postfix     // x!, x++, x--
  InfixLeft   // x + y, a[i], a ? b : c (left-associative)
  InfixRight  // x = y, x -> y (right-associative)
}
```

### PostfixPattern

```gleam
/// Describes what comes AFTER the rhs expression in an infix operator
/// 
/// This is recursive to handle ternary, slice, etc.
pub type PostfixPattern {
  /// Nothing after rhs: x + y, x * y
  None
  
  /// Just a closing token: a[i] → "]", f(x) → ")"
  Close(token: String)
  
  /// Separator + expr + more postfix
  /// Examples:
  /// - a ? b : c   → Continue(sep: ":", rest: None)
  /// - a[b:c]      → Continue(sep: ":", rest: Close("]"))
  /// - a[b:c:d]    → Continue(sep: ":", rest: Continue(sep: ":", rest: Close("]")))
  Continue(separator: String, rest: PostfixPattern)
}
```

### Operator

```gleam
/// Complete operator metadata
/// 
/// Infix operators contain everything needed to format:
/// - infix_op: the operator symbol between lhs and rhs
/// - postfix: what comes after rhs (nothing, closing, or recursive)
pub type Operator(a) {
  /// Prefix operator: <symbol> <expr>
  /// Example: -x, !x, ~x
  Prefix(
    precedence: Int,
    symbol: String,
    constructor: fn(a) -> a,
  )
  
  /// Postfix operator: <expr> <symbol>
  /// Example: x!, x++, x--
  Postfix(
    precedence: Int,
    symbol: String,
    constructor: fn(a) -> a,
  )
  
  /// Infix operator: lhs <infix_op> rhs <postfix>
  /// Examples:
  /// - x + y: infix_op="+", postfix=None
  /// - a[i]: infix_op="[", postfix=Close("]")
  /// - a ? b : c: infix_op="?", postfix=Continue(":", None)
  /// - a[b:c]: infix_op="[", postfix=Continue(":", Close("]"))
  Infix(
    associativity: OperatorKind,  // InfixLeft or InfixRight
    precedence: Int,
    infix_op: String,
    postfix: PostfixPattern,
    constructor: fn(...) -> a,  // arity varies by postfix
  )
}
```

### Grammar

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: List(Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: List(#(String, Operator(a))),  // Keyed by primary symbol
  )
}
```

---

## PostfixPattern Examples

### Binary Operators (None)

```gleam
// x + y
postfix: None

// x = y
postfix: None

// x |> y
postfix: None
```

### Index/Call (Close)

```gleam
// a[i]
postfix: Close("]")

// f(x)
postfix: Close(")")

// <x> (XML-style)
postfix: Close(">")

// {x} (brace-style)
postfix: Close("}")
```

### Ternary (Continue + None)

```gleam
// a ? b : c
// Structure: a ? b : c
//            ↑ ↑ ↑ └─ None (nothing after "c")
//              │ └─────── "c" is rhs, then ":" then None
//              └───────── "?" is infix_op
postfix: Continue(":", None)

// if a then b else c
postfix: Continue("else ", None)
```

### Slice (Continue + Close)

```gleam
// a[b:c]
// Structure: a [ b : c ]
//            ↑ ↑ ↑ └─ Close("]") (after "c")
//              │ └─────── "b" is rhs, then ":" then Close("]")
//              └───────── "[" is infix_op
postfix: Continue(":", Close("]"))

// a[b:c:d] (hypothetical multi-slice)
// Structure: a [ b : c : d ]
postfix: Continue(":", Continue(":", Close("]")))

// a[b..c] (range slice)
postfix: Continue("..", Close("]"))
```

### Optional Chaining (Continue + Close)

```gleam
// x?.y (JS-style optional member)
// Parsed as: x ? . y
//            (optional chain with "." as separator)
postfix: Continue(".", None)

// x?.[i] (optional index)
postfix: Continue(".", Close("]"))
```

---

## Formatter Combinators

### 1. format_prefix

```gleam
/// Format prefix operator: <symbol> <expr>
pub fn format_prefix(
  format_fn: fn(a, Int) -> Doc,
  operand: a,
  operator: Operator(a),
  parent_prec: Int,
) -> Doc {
  case operator {
    Prefix(precedence, symbol, _) -> {
      let operand_doc = format_fn(operand, precedence + 1)
      let doc = concat([text(symbol), operand_doc])
      
      case precedence < parent_prec {
        True -> parens(doc)
        False -> doc
      }
    }
    _ -> text("<expected-prefix>")  // Should not happen
  }
}
```

---

### 2. format_postfix

```gleam
/// Format postfix operator: <expr> <symbol>
pub fn format_postfix(
  format_fn: fn(a, Int) -> Doc,
  operand: a,
  operator: Operator(a),
  parent_prec: Int,
) -> Doc {
  case operator {
    Postfix(precedence, symbol, _) -> {
      let operand_doc = format_fn(operand, precedence + 1)
      let doc = concat([operand_doc, text(symbol)])
      
      case precedence < parent_prec {
        True -> parens(doc)
        False -> doc
      }
    }
    _ -> text("<expected-postfix>")  // Should not happen
  }
}
```

---

### 3. format_infix

```gleam
/// Format infix operator: lhs <infix_op> rhs <postfix>
/// 
/// Handles ALL infix operators:
/// - Binary: x + y (postfix=None)
/// - Index: a[i] (postfix=Close("]"))
/// - Ternary: a ? b : c (postfix=Continue(":", None))
/// - Slice: a[b:c] (postfix=Continue(":", Close("]")))
pub fn format_infix(
  format_fn: fn(a, Int) -> Doc,
  lhs: a,
  rhs: a,
  operator: Operator(a),
  parent_prec: Int,
) -> Doc {
  case operator {
    Infix(associativity, precedence, infix_op, postfix, _) -> {
      let lhs_doc = format_fn(lhs, precedence)
      let rhs_prec = case associativity {
        InfixLeft -> precedence + 1
        InfixRight -> precedence
        _ -> precedence + 1
      }
      let rhs_doc = format_fn(rhs, rhs_prec)
      
      // Format: lhs <infix_op> rhs <postfix>
      let doc = format_infix_with_postfix(
        format_fn,
        lhs_doc,
        rhs_doc,
        infix_op,
        postfix,
        precedence,
      )
      
      case precedence < parent_prec {
        True -> parens(doc)
        False -> doc
      }
    }
    _ -> text("<expected-infix>")  // Should not happen
  }
}

/// Helper: format infix with postfix structure
fn format_infix_with_postfix(
  format_fn: fn(a, Int) -> Doc,
  lhs_doc: Doc,
  rhs_doc: Doc,
  infix_op: String,
  postfix: PostfixPattern,
  prec: Int,
) -> Doc {
  case postfix {
    None => {
      // x + y
      concat([lhs_doc, text(infix_op), rhs_doc])
    }
    Close(token) => {
      // a[i], f(x)
      concat([lhs_doc, text(infix_op), rhs_doc, text(token)])
    }
    Continue(sep, rest) => {
      // a ? b : c  or  a[b:c]
      // rhs is "b", then we have ":c" (sep + rhs2 + rest)
      // But we need rhs2... this is the tricky part.
      // 
      // The issue: rhs in format_infix is just "b", but we need "b : c"
      // Solution: for Continue patterns, the "rhs" passed in should
      // already include the full structure (b : c), formatted by caller.
      //
      // Alternative: format_infix_ternary takes 3 operands directly.
      // 
      // Let's go with: Continue means caller handles the extra structure.
      // This function just adds the separator and rest.
      concat([lhs_doc, text(infix_op), rhs_doc, text(sep), format_postfix_rest(rest)])
    }
  }
}

/// Format the rest of a Continue postfix
fn format_postfix_rest(postfix: PostfixPattern) -> Doc {
  case postfix {
    None -> empty()
    Close(token) -> text(token)
    Continue(sep, rest) -> {
      // This shouldn't happen - Continue in rest means we need another expr
      // which the caller should have handled
      concat([text(sep), format_postfix_rest(rest)])
    }
  }
}
```

---

### 4. format_infix_ternary (Special Case)

```gleam
/// Format ternary operator (special case: 3 operands)
/// 
/// Ternary needs 3 operands, so it gets a dedicated combinator.
/// The operator metadata provides precedence and delimiters.
pub fn format_infix_ternary(
  format_fn: fn(a, Int) -> Doc,
  cond: a,
  then: a,
  else: a,
  operator: Operator(a),
  parent_prec: Int,
) -> Doc {
  case operator {
    Infix(associativity, precedence, infix_op, postfix, _) -> {
      let cond_doc = format_fn(cond, precedence)
      let then_doc = format_fn(then, precedence + 1)
      let else_doc = format_fn(else, precedence + 1)
      
      // Extract separators from postfix
      let (sep1, sep2) = case postfix {
        Continue(s1, Close(s2)) -> #(s1, s2)
        Continue(s1, None) -> #(s1, "")
        _ -> #(" ?", " :")  // Fallback
      }
      
      let doc = concat([
        cond_doc,
        text(infix_op),
        text(" "),
        then_doc,
        text(sep1),
        text(" "),
        else_doc,
        text(sep2),
      ])
      
      case precedence < parent_prec {
        True -> parens(doc)
        False -> doc
      }
    }
    _ -> text("<expected-infix>")
  }
}
```

---

## Operator Construction Helpers

```gleam
/// Create prefix operator
pub fn prefix(
  symbol: String,
  constructor: fn(a) -> a,
  precedence: Int,
) -> #(String, Operator(a)) {
  #(symbol, Prefix(precedence, symbol, constructor))
}

/// Create postfix operator
pub fn postfix(
  symbol: String,
  constructor: fn(a) -> a,
  precedence: Int,
) -> #(String, Operator(a)) {
  #(symbol, Postfix(precedence, symbol, constructor))
}

/// Create binary infix operator (no postfix)
pub fn infix_binary(
  symbol: String,
  constructor: fn(a, a) -> a,
  associativity: OperatorKind,
  precedence: Int,
  separator: String,
) -> #(String, Operator(a)) {
  #(symbol, Infix(associativity, precedence, separator, None, constructor))
}

/// Create wrapped infix operator (index, call)
pub fn infix_wrapped(
  symbol: String,
  constructor: fn(a, a) -> a,
  associativity: OperatorKind,
  precedence: Int,
  open: String,
  close: String,
) -> #(String, Operator(a)) {
  // infix_op = open, postfix = Close(close)
  #(symbol, Infix(associativity, precedence, open, Close(close), constructor))
}

/// Create ternary infix operator
pub fn infix_ternary(
  infix_symbol: String,
  constructor: fn(a, a, a) -> a,
  associativity: OperatorKind,
  precedence: Int,
  sep1: String,
  sep2: String,
) -> #(String, Operator(a)) {
  // infix_op = infix_symbol, postfix = Continue(sep1, Close(sep2))
  #(infix_symbol, Infix(associativity, precedence, infix_symbol, Continue(sep1, Close(sep2)), constructor))
}

/// Create slice infix operator
pub fn infix_slice(
  open: String,
  constructor: fn(a, a, a) -> a,
  associativity: OperatorKind,
  precedence: Int,
  sep: String,
  close: String,
) -> #(String, Operator(a)) {
  #(open, Infix(associativity, precedence, open, Continue(sep, Close(close)), constructor))
}
```

---

## Operator Examples

### Binary Infix (`+`, `-`, `*`, `/`)

```gleam
// Grammar
operators: [
  infix_binary("+", make_add, InfixLeft, 10, " + "),
  infix_binary("*", make_mul, InfixLeft, 20, " * "),
]

// Operator structure:
// Add: Infix(InfixLeft, 10, " + ", None, make_add)

// Formatter
Add(l, r, _) -> {
  case list.key_find(grammar.operators, "+") {
    Ok(op) -> format_infix(format_expr, l, r, op, parent_prec)
    Error(_) -> text("<unknown>")
  }
}

// Output: 1 + 2
// Format: lhs " + " rhs <nothing>
```

---

### Index (`a[i]`, `a!i`, `<i>a`)

```gleam
// C-style: a[i]
operators: [
  infix_wrapped("[", make_index, InfixLeft, 1000, "[", "]"),
]
// Operator: Infix(InfixLeft, 1000, "[", Close("]"), make_index)

// F#-style: a!i
operators: [
  infix_wrapped("!", make_index, InfixLeft, 1000, "!", ""),
]
// Operator: Infix(InfixLeft, 1000, "!", Close(""), make_index)

// Formatter (same for both)
Index(arr, idx, _) -> {
  case list.key_find(grammar.operators, key) {
    Ok(op) -> format_infix(format_expr, arr, idx, op, parent_prec)
    Error(_) -> text("<unknown>")
  }
}

// Output (C): arr[0]
// Format: lhs "[" rhs "]"

// Output (F#): arr!0
// Format: lhs "!" rhs ""
```

---

### Call (`f(x)`, `f!x`)

```gleam
// C-style: f(x)
operators: [
  infix_wrapped("(", make_call, InfixLeft, 1000, "(", ")"),
]

// F#-style: f!x
operators: [
  infix_wrapped("!", make_call, InfixLeft, 1000, "!", ""),
]

// Formatter
Call(f, args, _) -> {
  let args_doc = format_args(args)
  case list.key_find(grammar.operators, key) {
    Ok(op) -> format_infix(format_expr, f, args_doc, op, parent_prec)
    Error(_) -> text("<unknown>")
  }
}

// Output (C): f(1, 2)
// Output (F#): f!(1, 2)
```

---

### Ternary (`a ? b : c`, `if a then b else c`)

```gleam
// C-style: a ? b : c
operators: [
  infix_ternary("?", make_if, InfixRight, 3, " : ", ""),
]
// Operator: Infix(InfixRight, 3, "?", Continue(" : ", Close("")), make_if)

// ML-style: if a then b else c
operators: [
  infix_ternary("then", make_if, InfixRight, 3, " else ", ""),
]
// Operator: Infix(InfixRight, 3, "then", Continue(" else ", Close("")), make_if)

// Formatter (needs 3 operands)
If(c, t, e, _) -> {
  case list.key_find(grammar.operators, key) {
    Ok(op) -> format_infix_ternary(format_expr, c, t, e, op, parent_prec)
    Error(_) -> text("<unknown>")
  }
}

// Output (C): cond ? then : else
// Format: cond "?" " " then " : " " " else ""

// Output (ML): if cond then then else else
```

---

### Slice (`a[b:c]`, `a[b..c]`)

```gleam
// Python-style: a[b:c]
operators: [
  infix_slice("[", make_slice, InfixLeft, 1000, ":", "]"),
]
// Operator: Infix(InfixLeft, 1000, "[", Continue(":", Close("]")), make_slice)

// Range-style: a[b..c]
operators: [
  infix_slice("[", make_slice, InfixLeft, 1000, "..", "]"),
]

// Formatter (needs 3 operands: arr, start, end)
Slice(arr, start, end, _) -> {
  // Build the "rhs" structure: start : end ]
  let rhs_content = concat([
    format_expr(start, 1000),
    text(":"),
    format_expr(end, 1000),
  ])
  
  case list.key_find(grammar.operators, "[") {
    Ok(op) -> format_infix(format_expr, arr, rhs_content, op, parent_prec)
    Error(_) -> text("<unknown>")
  }
}

// Output: arr[1:5]
// Format: lhs "[" rhs_content (which is "1:5") → "arr[1:5]"
// Wait, that's wrong... let me reconsider.
```

**Issue**: Slice formatting needs adjustment. The `infix_op` is `[`, but we're double-printing it.

**Fix**: For slice, the formatter should handle the brackets differently:

```gleam
// Alternative: slice uses special pattern
pub fn infix_slice(...) {
  // Use empty infix_op, put everything in postfix
  #(open, Infix(assoc, prec, "", Continue(sep, Close(close)), constructor))
}

// Then format_infix produces: lhs "" rhs_content → lhs + rhs_content
// Where rhs_content = "start:end]"
// Result: arrstart:end]  (still wrong, missing "[")

// Better fix: format_infix_with_postfix handles Continue specially
fn format_infix_with_postfix(...) {
  case postfix {
    Continue(sep, rest) => {
      // For Continue, infix_op is the OPEN bracket
      // rhs is the first expr, then sep, then more, then rest
      concat([lhs_doc, text(infix_op), rhs_doc, text(sep), format_postfix_rest(rest)])
    }
    // ...
  }
}

// Output: arr[1:5]
// Format: lhs "[" rhs ":" rest
//         arr "[" "1"  ":"  "5]"
//         = arr[1:5]  ✓
```

---

### Pipeline (`x |> f`)

```gleam
operators: [
  infix_binary("|>", make_pipe, InfixLeft, 5, " |> "),
]

// Output: x |> f |> g
```

---

### Range (`1..5`, `1..<5`)

```gleam
// Inclusive: 1..5
operators: [
  infix_binary("..", make_range, InfixLeft, 10, ".."),
]

// Exclusive: 1..<5
operators: [
  infix_binary("..<", make_range_excl, InfixLeft, 10, "..<"),
]

// Output: 1..5, 1..<5
```

---

### Optional Chaining (`x?.y`, `x?.[i]`)

```gleam
// Optional member: x?.y
// Parsed as: x ? .y  (optional with "." separator)
operators: [
  infix_ternary("?", make_optional, InfixLeft, 1000, ".", ""),
]
// Hmm, this doesn't quite work because optional has 2 operands, not 3...

// Better: treat as binary with postfix
operators: [
  infix_wrapped("?", make_optional, InfixLeft, 1000, "?", ""),
]
// But then it formats as x?y, not x?.y

// Best: use Continue with empty first part
operators: [
  Infix(InfixLeft, 1000, "?", Continue(".", None), make_optional),
]

// Formatter for 2-operand optional:
OptionalMember(x, field, _) -> {
  // This is tricky - Continue expects 3 operands
  // But optional member is really just 2: x and field
  // The "." is part of the operator syntax, not a separator between operands
  
  // Solution: treat optional as binary with special separator
  case list.key_find(grammar.operators, "?") {
    Ok(op) -> {
      // Custom handling for optional
      let x_doc = format_expr(x, 1000)
      let field_doc = format_expr(field, 1000)
      concat([x_doc, text("?."), field_doc])
    }
    Error(_) -> text("<unknown>")
  }
}
```

**Note**: Optional chaining is a bit of an edge case. It might be better handled as a special binary operator with separator `"?."` instead of using Continue.

---

## Summary Table

| Operator | Example | Kind | infix_op | postfix |
|----------|---------|------|----------|---------|
| Binary | `x + y` | InfixLeft | `" + "` | None |
| Assign | `x = y` | InfixRight | `" = "` | None |
| Index (C) | `a[i]` | InfixLeft | `"["` | Close("]") |
| Index (F#) | `a!i` | InfixLeft | `"!"` | Close("") |
| Call (C) | `f(x)` | InfixLeft | `"("` | Close(")") |
| Ternary (C) | `a ? b : c` | InfixRight | `"?"` | Continue(" : ", Close("")) |
| Ternary (ML) | `if a then b else c` | InfixRight | `"then"` | Continue(" else ", Close("")) |
| Slice | `a[b:c]` | InfixLeft | `"["` | Continue(":", Close("]")) |
| Pipeline | `x |> f` | InfixLeft | `" |> "` | None |
| Range | `1..5` | InfixLeft | `".."` | None |
| Prefix | `-x` | Prefix | N/A | N/A |
| Postfix | `x!` | Postfix | N/A | N/A |

---

## Implementation Plan

### Phase 1: Add PostfixPattern Type

```gleam
pub type PostfixPattern {
  None
  Close(token: String)
  Continue(separator: String, rest: PostfixPattern)
}
```

---

### Phase 2: Update Operator Type

```gleam
pub type Operator(a) {
  Prefix(precedence: Int, symbol: String, constructor: fn(a) -> a)
  Postfix(precedence: Int, symbol: String, constructor: fn(a) -> a)
  Infix(
    associativity: OperatorKind,
    precedence: Int,
    infix_op: String,
    postfix: PostfixPattern,
    constructor: fn(...) -> a,
  )
}
```

---

### Phase 3: Update Grammar Type

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: List(Rule(a)),
    tokens: List(String),
    keywords: List(String),
    operators: List(#(String, Operator(a))),
  )
}
```

---

### Phase 4: Add Helper Functions

```gleam
pub fn prefix(...) -> #(String, Operator(a))
pub fn postfix(...) -> #(String, Operator(a))
pub fn infix_binary(...) -> #(String, Operator(a))
pub fn infix_wrapped(...) -> #(String, Operator(a))
pub fn infix_ternary(...) -> #(String, Operator(a))
pub fn infix_slice(...) -> #(String, Operator(a))
```

---

### Phase 5: Update Rule Functions

Update parsing to handle postfix patterns.

---

### Phase 6: Add Query API

```gleam
pub fn get_operator(grammar: Grammar(a), symbol: String) -> Result(Operator(a), Nil)
```

---

### Phase 7: Add Formatter Combinators

```gleam
pub fn format_prefix(...) -> Doc
pub fn format_postfix(...) -> Doc
pub fn format_infix(...) -> Doc
pub fn format_infix_ternary(...) -> Doc
```

---

### Phase 8: Update calc.gleam Example

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  grammar.Grammar(
    name: "Calc",
    operators: [
      infix_binary("+", make_add, InfixLeft, 10, " + "),
      infix_binary("-", make_sub, InfixLeft, 10, " - "),
      infix_binary("*", make_mul, InfixLeft, 20, " * "),
      infix_binary("/", make_div, InfixLeft, 20, " / "),
    ],
    rules: [...],
  )
}
```

---

## Testing Plan

```gleam
// Binary
pub fn format_binary_test() {
  format(Add(Int(1), Int(2))) |> should.equal("1 + 2")
}

// Wrapped (index)
pub fn format_index_test() {
  format(Index(Var("arr"), Int(0))) |> should.equal("arr[0]")
}

// Ternary
pub fn format_ternary_test() {
  format(If(Var("c"), Int(1), Int(2))) |> should.equal("c ? 1 : 2")
}

// Slice
pub fn format_slice_test() {
  format(Slice(Var("arr"), Int(1), Int(5))) |> should.equal("arr[1:5]")
}

// Prefix
pub fn format_prefix_test() {
  format(Negate(Int(5))) |> should.equal("-5")
}

// Postfix
pub fn format_postfix_test() {
  format(Force(Int(5))) |> should.equal("5!")
}

// Precedence
pub fn format_precedence_test() {
  format(Mul(Add(Int(1), Int(2)), Int(3))) |> should.equal("(1 + 2) * 3")
}
```

---

## Success Criteria

| Criterion | Status |
|-----------|--------|
| Only 4 operator kinds | ✅ `Prefix`, `Postfix`, `InfixLeft`, `InfixRight` |
| PostfixPattern is recursive | ✅ `None`, `Close`, `Continue` |
| Ternary/slice use same pattern | ✅ Both use `Continue` |
| Only 4 formatter combinators | ✅ `format_prefix`, `format_postfix`, `format_infix`, `format_infix_ternary` |
| Language-agnostic delimiters | ✅ Any delimiters via `PostfixPattern` |
| Precedence defined ONCE | ✅ In grammar only |
| Simple query API | ✅ `list.key_find(operators, symbol)` |

---

## Related Documents

- **[08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)** - Previous plan
- **[../syntax-library.md](../syntax-library.md)** - Syntax library documentation

---

## Implementation Checklist

- [ ] **Phase 1**: Add `PostfixPattern` type
- [ ] **Phase 2**: Update `Operator` type (sum type with 3 constructors)
- [ ] **Phase 3**: Update `Grammar` type
- [ ] **Phase 4**: Add helper functions (`prefix`, `postfix`, `infix_*`)
- [ ] **Phase 5**: Update rule functions for parsing
- [ ] **Phase 6**: Add query API
- [ ] **Phase 7**: Add 4 formatter combinators
- [ ] **Phase 8**: Update `calc.gleam` example
- [ ] **Phase 9**: Add tests
- [ ] **Phase 10**: Update documentation

---

## Estimated Effort

| Phase | Complexity | Time |
|-------|------------|------|
| Phase 1-3: Types | Low | 30 min |
| Phase 4: Helpers | Medium | 45 min |
| Phase 5: Rules | Medium | 1 hour |
| Phase 6: Query API | Low | 15 min |
| Phase 7: Formatters | Medium | 1 hour |
| Phase 8: Example | Medium | 45 min |
| Phase 9: Tests | Medium | 1 hour |
| **Total** | | **~4.5 hours** |

---

## Conclusion

This plan provides a **minimal, composable operator system**:

**Four operator kinds**: `Prefix`, `Postfix`, `InfixLeft`, `InfixRight`

**Recursive postfix pattern**:
- `None` - Binary ops (`x + y`)
- `Close(token)` - Index/call (`a[i]`, `f(x)`)
- `Continue(sep, rest)` - Ternary/slice (`a ? b : c`, `a[b:c]`)

**Four formatter combinators**:
- `format_prefix` - Prefix operators
- `format_postfix` - Postfix operators
- `format_infix` - Binary, index, call, slice
- `format_infix_ternary` - Ternary (3 operands)

**Key insight**: Ternary and slice are the same pattern (`Continue`) with different delimiters. All "custom" structure lives in `PostfixPattern`, not the formatter.
