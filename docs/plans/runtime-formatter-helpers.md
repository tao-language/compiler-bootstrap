# Runtime Formatter Helpers - No Code Generation

## Constraint

**Gleam has no code generation/preprocessing.** We cannot:
- ❌ Generate source files before compilation
- ❌ Use comptime macros
- ❌ Run a pre-compilation step

**We MUST use runtime data structures.**

---

## Revised Approach: Runtime Lookup Tables

Instead of generating constants and functions, we store them **in the grammar itself**:

### Before (Code Generation - Won't Work)
```gleam
// ❌ Generated source file
pub const PREC_ADD = 10
pub fn format_add(...) { ... }
```

### After (Runtime Data - Will Work)
```gleam
// ✅ Stored in grammar at runtime
pub type OperatorInfo(a) {
  OperatorInfo(
    precedence: Int,
    associativity: Associativity,
    separator: String,
    layout: LayoutStyle,
    format_fn: fn(a, a, Int, fn(a, Int) -> Doc) -> Doc,  // ← Function stored as value!
  )
}

// Grammar contains lookup table
pub type Grammar(a) {
  Grammar(
    // ... existing fields
    operator_info: Dict(String, OperatorInfo(a)),
  )
}
```

---

## Implementation

### 1. Operator Info Type

```gleam
pub type Associativity {
  Left
  Right
  None
}

pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
  Custom
}

pub type OperatorInfo(a) {
  OperatorInfo(
    precedence: Int,
    associativity: Associativity,
    separator: String,
    layout: LayoutStyle,
    format_fn: fn(a, a, Int, fn(a, Int) -> Doc) -> Doc,
  )
}
```

### 2. Grammar Construction

```gleam
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  separator: String,
  precedence: Int,
  associativity: Associativity,
  layout: LayoutStyle,
) -> Operator(a) {
  // Create format function that handles precedence & parens
  let format_fn = fn(left: a, right: a, parent_prec: Int, format_child: fn(a, Int) -> Doc) {
    let doc = case associativity {
      Left -> {
        let l_doc = format_child(left, precedence + 1)
        let r_doc = format_child(right, precedence)
        format_binop(l_doc, r_doc, separator, precedence, parent_prec, layout)
      }
      Right -> {
        let l_doc = format_child(left, precedence)
        let r_doc = format_child(right, precedence + 1)
        format_binop(l_doc, r_doc, separator, precedence, parent_prec, layout)
      }
      None -> {
        let l_doc = format_child(left, precedence)
        let r_doc = format_child(right, precedence)
        format_binop(l_doc, r_doc, separator, precedence, parent_prec, layout)
      }
    }
    doc
  }
  
  Operator(
    keyword,
    constructor,
    separator,
    precedence,
    associativity,
    layout,
    format_fn,  // ← Store function as value!
  )
}
```

### 3. Grammar Stores Operator Info

```gleam
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
    // NEW: Operator info for formatting
    operator_info: Dict(String, OperatorInfo(a)),
  )
}

pub fn left_assoc(
  g: Grammar(a),
  name: String,
  first: Symbol,
  ops: List(Operator(a)),
  precedence: Int,
  layout: LayoutStyle,
) -> Grammar(a) {
  // Build operator info dict
  let operator_info = list.fold(ops, g.operator_info, fn(acc, op) {
    dict.insert(acc, op.keyword, OperatorInfo(
      op.precedence,
      op.associativity,
      op.separator,
      op.layout,
      op.format_fn,  // ← Store the function!
    ))
  })
  
  Grammar(..g, operator_info: operator_info)
}
```

### 4. Generic Format Combinators (Not Generated)

```gleam
// In grammar.gleam - NOT generated, just regular functions

/// Generic binary operator formatter
pub fn format_binop(
  left: Doc,
  right: Doc,
  separator: String,
  precedence: Int,
  parent_prec: Int,
  layout: LayoutStyle,
) -> Doc {
  let doc = case layout {
    Inline -> {
      formatter.concat([formatter.text(left), formatter.text(separator), formatter.text(right)])
    }
    BreakAfterOperator(indent) -> {
      formatter.group(
        formatter.concat([
          left,
          formatter.text(separator),
          formatter.line,
          formatter.nest(indent, right),
        ])
      )
    }
    BreakBeforeOperator(indent) -> {
      formatter.group(
        formatter.concat([
          left,
          formatter.line,
          formatter.nest(indent, formatter.concat([formatter.text(separator), right])),
        ])
      )
    }
    _ -> formatter.concat([left, formatter.text(separator), right])
  }
  wrap_parens(doc, precedence < parent_prec)
}

/// Wrap in parens if precedence is lower than parent
pub fn wrap_parens(doc: Doc, condition: Bool) -> Doc {
  case condition {
    True -> formatter.concat([formatter.text("("), doc, formatter.text(")")])
    False -> doc
  }
}

/// Block formatter
pub fn format_block(
  open: String,
  children: List(Doc),
  close: String,
  separator: String,
  indent: Int,
  parent_prec: Int,
) -> Doc {
  let children_doc = case children {
    [] -> formatter.text("")
    [first, ..rest] -> {
      formatter.concat(
        list.append(
          [first],
          list.map(rest, fn(c) { formatter.concat([formatter.text(separator), formatter.line, c]) })
        )
      )
    }
  }
  formatter.group(
    formatter.concat([
      formatter.text(open),
      formatter.nest(indent, formatter.concat([formatter.line, children_doc])),
      formatter.line,
      formatter.text(close),
    ])
  )
}
```

### 5. AST-Specific Formatter (Uses Grammar at Runtime)

```gleam
// In calc/syntax.gleam

pub fn format(ast: Expr) -> String {
  let g = calc_grammar()  // Get grammar with operator info
  let doc = format_expr(g, ast, -1)
  formatter.render(doc, formatter.default_config())
}

fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    
    Add(l, r) -> {
      // Look up operator info from grammar at runtime!
      case dict.get(g.operator_info, "+") {
        Ok(op_info) -> op_info.format_fn(l, r, parent_prec, fn(e, prec) { format_expr(g, e, prec) })
        Error(_) -> formatter.text("<unknown operator>")
      }
    }
    
    Mul(l, r) -> {
      case dict.get(g.operator_info, "*") {
        Ok(op_info) -> op_info.format_fn(l, r, parent_prec, fn(e, prec) { format_expr(g, e, prec) })
        Error(_) -> formatter.text("<unknown operator>")
      }
    }
    
    // Non-operator constructs still need manual formatting
    Rcd(fields) -> format_record(g, fields, parent_prec),
  }
}

fn format_record(g: Grammar(Expr), fields: List(#(String, Expr)), parent_prec: Int) -> Doc {
  let field_docs = list.map(fields, fn(f) {
    formatter.concat([
      formatter.text(f.0),
      formatter.text(": "),
      format_expr(g, f.1, 0),
    ])
  })
  format_block("{", field_docs, "}", ",", 2, parent_prec)
}
```

---

## Hybrid Approach: Best of Both Worlds

For operators: **Runtime lookup** (generated automatically from grammar)
For non-operators: **Manual formatting** (records, match, etc.)

### Grammar Definition (Same as Before)

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  |> grammar.with_token("Operator")
  
  |> grammar.left_assoc(
    "Expr",
    grammar.ref("Term"),
    [
      grammar.op(
        "+",
        fn(l, r) { Add(l, r) },
        " + ",
        10,
        grammar.Left,
        grammar.BreakAfterOperator(2),  // ← Layout hint stored in grammar
      ),
    ],
    10,
    grammar.BreakAfterOperator(2),
  )
  
  |> grammar.left_assoc(
    "Term",
    grammar.ref("Factor"),
    [
      grammar.op(
        "*",
        fn(l, r) { Mul(l, r) },
        " * ",
        20,
        grammar.Left,
        grammar.BreakAfterOperator(2),
      ),
    ],
    20,
    grammar.BreakAfterOperator(2),
  )
}
```

### Formatter (Uses Grammar at Runtime)

```gleam
pub fn format(ast: Expr) -> String {
  let g = calc_grammar()
  let doc = format_expr(g, ast, -1)
  formatter.render(doc, formatter.default_config())
}

fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    
    // Operators use grammar lookup
    Add(l, r) -> format_op(g, "+", l, r, parent_prec, format_expr)
    Mul(l, r) -> format_op(g, "*", l, r, parent_prec, format_expr)
    
    // Non-operators use manual formatting
    Rcd(fields) -> format_record(g, fields, parent_prec),
  }
}
```

**Note**: The pattern match is intentional and beneficial:
- ✅ **Exhaustiveness checking** - Gleam compiler warns if you miss a constructor
- ✅ **Type-safe** - No runtime errors from missing cases
- ✅ **Clear control flow** - Easy to see what's formatted how
- ✅ **Custom formatting** - Complex constructs (Match, etc.) can have special handling

/// Generic helper - looks up operator from grammar and formats it
fn format_binop_from_grammar(
  g: Grammar(a),
  op: String,
  left: a,
  right: a,
  parent_prec: Int,
  format_child: fn(a, Int) -> Doc,
) -> Doc {
  case dict.get(g.operator_info, op) {
    Ok(op_info) -> op_info.format_fn(left, right, parent_prec, format_child)
    Error(_) -> formatter.text("<unknown operator: " <> op <> ">")  // ← Includes op name for debugging!
  }
}
```

---

## Further Optimization: Reduce Boilerplate

We can make the formatter even simpler:

### Helper for Operator Formatting

```gleam
/// Format any binary operator from grammar
pub fn format_op(
  g: Grammar(a),
  op: String,
  left: a,
  right: a,
  parent_prec: Int,
  format_child: fn(a, Int) -> Doc,
) -> Doc {
  case dict.get(g.operator_info, op) {
    Ok(info) -> info.format_fn(left, right, parent_prec, format_child)
    Error(_) -> formatter.text("<unknown operator: " <> op <> ">")  // ← Includes op name!
  }
}
```

### Formatter Becomes Trivial

```gleam
fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_op(g, "+", l, r, parent_prec, format_expr)
    Mul(l, r) -> format_op(g, "*", l, r, parent_prec, format_expr)
    Rcd(fields) -> format_record(g, fields, parent_prec),
  }
}
```

---

## Default Formatting for Common Structures

For common AST structures, we can provide **default formatters** inferred from grammar:

### Lists, Tuples, Records

```gleam
// Grammar knows these are block structures
grammar.block_rule("List", "[", grammar.sep(grammar.ref("Item"), grammar.token("Comma")), "]")
grammar.block_rule("Tuple", "(", grammar.sep(grammar.ref("Item"), grammar.token("Comma")), ")")
grammar.block_rule("Record", "{", grammar.sep(grammar.ref("Field"), grammar.token("Comma")), "}")
```

### Generic Block Formatter

```gleam
/// Default formatter for block structures
pub fn format_block_default(
  children: List(a),
  open: String,
  close: String,
  separator: String,
  indent: Int,
  parent_prec: Int,
  format_child: fn(a, Int) -> Doc,
) -> Doc {
  let child_docs = list.map(children, fn(c) { format_child(c, 0) })
  format_block(open, child_docs, close, separator, indent, parent_prec)
}
```

### Usage in Formatter

```gleam
fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_op(g, "+", l, r, parent_prec, format_expr)
    Mul(l, r) -> format_op(g, "*", l, r, parent_prec, format_expr)
    
    // Use default block formatter for records
    Rcd(fields) -> format_block_default(
      fields,
      "{",
      "}",
      ", ",
      2,
      parent_prec,
      fn(f) { format_field(g, f) },
    ),
    
    // Custom formatting for complex constructs
    Match(arg, motive, cases) -> format_match(g, arg, motive, cases, parent_prec),
  }
}
```

### Benefits

- ✅ **Less boilerplate** - Common structures use generic formatter
- ✅ **Consistent** - All block structures formatted same way
- ✅ **Still flexible** - Can override with custom formatter when needed
- ✅ **Grammar-driven** - Open/close/separator from grammar

---

## Trade-offs

### Pros ✅

1. **No code generation** - Works with standard Gleam compilation
2. **Single source of truth** - Grammar defines everything
3. **Type-safe** - All functions type-checked at compile time
4. **Flexible** - Can override formatting when needed
5. **Runtime introspection** - Can query grammar for operator info

### Cons ❌

1. **Runtime cost** - Dict lookup for each operator (minor)
2. **Function closures** - Stored in grammar (minor memory overhead)
3. **Still need pattern match** - Can't fully auto-generate the case expression
4. **Non-operators need manual formatting** - Records, match, etc.

**However**, the pattern match approach has benefits:
- ✅ **Exhaustiveness checking** - Gleam compiler warns if you miss a constructor
- ✅ **Type-safe** - No runtime errors from missing cases
- ✅ **Clear control flow** - Easy to see what's formatted how
- ✅ **Custom formatting** - Complex constructs (Match, etc.) can have special handling

---

## Future Enhancement: Macro-like Helpers

If Gleam adds macros in the future, we could generate the case expression:

```gleam
// Future possibility (not available now)
@derive_formatter
pub type Expr {
  Int(Int)
  Add(Expr, Expr)  // @op("+", precedence: 10, layout: BreakAfter(2))
  Mul(Expr, Expr)  // @op("*", precedence: 20, layout: BreakAfter(2))
  Rcd(List(#(String, Expr)))
}
```

For now, we manually write the case expression but use runtime helpers.

---

## Implementation Plan

### Phase 1: Add Operator Info Types
- [ ] `OperatorInfo(a)` type with `format_fn` field
- [ ] Update `Operator` type to include layout, precedence, etc.
- [ ] Update `Grammar(a)` to include `operator_info` dict

### Phase 2: Update Grammar Construction
- [ ] Update `op()` to create format function
- [ ] Update `left_assoc()` to populate operator_info dict
- [ ] Add `format_binop()`, `format_block()`, `wrap_parens()` helpers

### Phase 3: Add Default Formatters
- [ ] Implement `format_block_default()` for block structures
- [ ] Implement `format_list_default()` for list-like structures
- [ ] Document which constructs use defaults vs custom formatting

### Phase 4: Update calc/syntax.gleam
- [ ] Add layout hints to grammar definition
- [ ] Implement `format_op()` helper with error messages
- [ ] Update formatter to use grammar lookup
- [ ] Use default formatters for records/lists
- [ ] Test pretty-printing output

### Phase 5: Documentation
- [ ] Document how to add new operators
- [ ] Document how to format non-operator constructs
- [ ] Add examples of different layout styles
- [ ] Show when to use defaults vs custom formatting

---

## Conclusion

**Yes, we can do this at runtime!** The key insights:

1. **Store format functions as values** in the grammar (higher-order functions)
2. **Use Dict lookup** to get operator info at runtime
3. **Provide generic combinators** that handle precedence/parens/layout
4. **Formatter pattern matches** and calls helpers (exhaustiveness-checked!)
5. **Default formatters** for common structures (lists, records, tuples)
6. **Custom formatters** for complex constructs (Match, etc.)
7. **Error messages include operator name** for easy debugging

### What's Automated ✅

- **Operators** - Precedence, associativity, layout all from grammar
- **Block structures** - Lists, tuples, records use default formatter
- **Parenthesization** - Automatic based on precedence
- **Line breaking** - Automatic based on layout hints
- **Indentation** - Automatic based on layout hints

### What's Manual ✍️

- **Pattern match** - One case per AST constructor (exhaustiveness-checked!)
- **Complex constructs** - Match, Let, etc. need custom formatting
- **Field formatting** - Record fields, match cases, etc.

This is the **sweet spot**: maximum automation where it matters (operators), flexibility where needed (complex constructs), and Gleam's type system ensuring correctness!
