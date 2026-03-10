# Formatter UX Improvement Plan (SUPERSEDED)

> **Status**: ⚠️ SUPERSEDED by [08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)
> **Date**: March 2025

---

## Note

This plan has been **superseded** by **[08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)** which provides a better solution:

- **This plan**: Manual formatter with combinators (60-70% boilerplate reduction)
- **New plan**: Grammar-derived metadata + combinators (70-80% reduction, zero precedence duplication)

The new plan solves the critical issue of **precedence duplication** by generating metadata tables from the grammar, ensuring precedence is defined ONCE.

---

## Original Plan (For Reference)

This plan implemented **practical UX improvements** for manual formatters, reducing boilerplate while maintaining full control over formatting output.

**Estimated Effort**: 4-6 days
**Expected Benefit**: 60-70% reduction in formatter boilerplate

See **[08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)** for the updated approach.

---

## Phase 1: Formatter Combinators (1-2 days)

### 1.1 Add Combinator Functions

**File**: `src/syntax/formatter.gleam`

**Implementation**:

```gleam
// ============================================================================
// FORMATTER COMBINATORS
// ============================================================================

/// Format binary operator with automatic precedence-based parenthesization
///
/// Example:
/// ```gleam
/// format_binop(
///   format_expr(left, 10),
///   format_expr(right, 11),
///   " + ",
///   10,  // Operator precedence
///   parent_prec,
/// )
/// ```
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

/// Format unary operator (prefix)
///
/// Example:
/// ```gleam
/// format_unary("-", format_expr(operand, 90))
/// ```
pub fn format_unary(op: String, operand: Doc) -> Doc {
  concat([text(op), operand])
}

/// Format unary operator (postfix)
///
/// Example:
/// ```gleam
/// format_unary_postfix(format_expr(operand, 90), "!")
/// ```
pub fn format_unary_postfix(operand: Doc, op: String) -> Doc {
  concat([operand, text(op)])
}

/// Format wrapped expression (parens, braces, brackets, etc.)
///
/// Example:
/// ```gleam
/// format_wrapped("(", format_expr(inner, 0), ")")
/// format_wrapped("{", format_fields(fields), "}")
/// ```
pub fn format_wrapped(open: String, content: Doc, close: String) -> Doc {
  concat([text(open), content, text(close)])
}

/// Format list of items with separator
///
/// Example:
/// ```gleam
/// format_list(
///   [format_expr(a, 0), format_expr(b, 0), format_expr(c, 0)],
///   text(", "),
/// )
/// ```
pub fn format_list(items: List(Doc), sep: Doc) -> Doc {
  join(sep, items)
}

/// Format list with trailing separator (for multi-line)
///
/// Example:
/// ```gleam
/// format_list_trailing(
///   [field1, field2, field3],
///   concat([text(","), line()]),
/// )
/// ```
pub fn format_list_trailing(items: List(Doc), sep: Doc) -> Doc {
  case items {
    [] -> empty
    _ -> {
      let separated = join(sep, items)
      concat([separated, sep])
    }
  }
}

/// Format function application
///
/// Example:
/// ```gleam
/// format_application(
///   format_expr(fun, 85),
///   [format_expr(arg1, 0), format_expr(arg2, 0)],
/// )
/// ```
pub fn format_application(fun: Doc, args: List(Doc)) -> Doc {
  concat([
    fun,
    text("("),
    format_list(args, concat([text(","), line()])),
    text(")"),
  ])
}

/// Format lambda abstraction
///
/// Example:
/// ```gleam
/// format_lambda(
///   ["x", "y"],
///   format_expr(body, 0),
/// )
/// ```
pub fn format_lambda(params: List(String), body: Doc) -> Doc {
  concat([
    text("fn("),
    format_list(params |> list.map(text), concat([text(","), line()])),
    text(") -> "),
    body,
  ])
}

/// Format with optional layout (soft breaks)
///
/// Example:
/// ```gleam
/// format_with_layout([
/// #(text("let"), SoftBreak),
/// #(text("x"), Space),
/// #(text("="), SoftBreak),
/// #(format_expr(value, 0), NoSeparator),
/// ])
/// ```
pub fn format_with_layout(
  items: List(#(Doc, LayoutHint)),
  indent: Int,
) -> Doc {
  format_to_string_with_layout(items, indent, True)
}

fn format_to_string_with_layout(
  items: List(#(Doc, LayoutHint)),
  indent: Int,
  flat: Bool,
) -> Doc {
  case items {
    [] -> empty
    [#(doc, hint), ..rest] -> {
      let sep = case hint {
        SoftBreak -> {
          case flat {
            True -> text(" ")
            False -> concat([hardline, text(string.repeat(" ", indent))])
          }
        }
        HardBreak -> concat([hardline, text(string.repeat(" ", indent))])
        Space -> text(" ")
        NoSeparator -> empty
      }
      concat([doc, sep, format_to_string_with_layout(rest, indent, flat)])
    }
  }
}

/// Format record with fields
///
/// Example:
/// ```gleam
/// format_record([
/// #("x", format_expr(x, 0)),
/// #("y", format_expr(y, 0)),
/// #("z", format_expr(z, 0)),
/// ])
/// ```
pub fn format_record(fields: List(#(String, Doc))) -> Doc {
  let field_docs = fields |> list.map(fn(f) {
    let #(name, value) = f
    concat([text(name), text(": "), value])
  })
  format_wrapped(
    "{ ",
    format_list(field_docs, concat([text(", "), line()])),
    " }",
  )
}

/// Format match expression
///
/// Example:
/// ```gleam
/// format_match(
///   format_expr(scrutinee, 85),
///   [
///     format_case(pattern1, guard1, body1),
///     format_case(pattern2, guard2, body2),
///   ],
/// )
/// ```
pub fn format_match(scrutinee: Doc, cases: List(Doc)) -> Doc {
  concat([
    text("match "),
    scrutinee,
    text(" {"),
    hardline,
    format_list(cases, hardline),
    hardline,
    text("}"),
  ])
}

/// Format single match case
///
/// Example:
/// ```gleam
/// format_case(
///   format_pattern(pattern),
///   Some(format_expr(guard, 0)),
///   format_expr(body, 0),
/// )
/// ```
pub fn format_case(pattern: Doc, guard: Option(Doc), body: Doc) -> Doc {
  let guard_doc = case guard {
    Some(g) -> concat([text(" if "), g])
    None -> empty
  }
  concat([
    text("| "),
    pattern,
    guard_doc,
    text(" -> "),
    body,
  ])
}
```

**Tests**: Add 20+ tests for each combinator

---

### 1.2 Update Documentation

**File**: `docs/syntax-library.md`

**Add section**:

```markdown
## Formatter Combinators

The formatter library provides combinators that reduce boilerplate:

### Binary Operators

```gleam
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
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

### Records

```gleam
fn format_record(fields: List(#(String, Expr))) -> Doc {
  let field_docs = fields |> list.map(fn(f) {
    let #(name, value) = f
    #(name, format_expr(value, 0))
  })
  formatter.format_record(field_docs)
}
```

### Match Expressions

```gleam
fn format_match(scrutinee: Expr, cases: List(Case)) -> Doc {
  formatter.format_match(
    format_expr(scrutinee, 85),
    cases |> list.map(format_case),
  )
}
```

See `src/syntax/formatter.gleam` for all available combinators.
```

---

## Phase 2: Boilerplate Generator (2-3 days)

### 2.1 Generator Implementation

**File**: `src/codegen/formatter_gen.gleam` (NEW)

**Implementation**:

```gleam
// ============================================================================
// FORMATTER BOILERPLATE GENERATOR
// ============================================================================
import gleam/io
import gleam/result
import gleam/string
import simplifile

pub type GenerateError {
  ParseError(message: String)
  FileError(simplifile.FileError)
}

/// Generate formatter skeleton from AST type definition
///
/// Usage: gleam run generate-formatter --type Expr --output src/mylang/formatter.gleam
pub fn generate_formatter_skeleton(
  ast_type: String,
  output_path: String,
) -> Result(Nil, GenerateError) {
  // Read AST type definition from source file
  let ast_source = simplifile.read(ast_type <> ".gleam")
    |> result.map_error(GenerateError.FileError)
  
  // Parse AST type (simple parser for type definitions)
  let constructors = parse_ast_constructors(ast_source)
  
  // Generate formatter skeleton
  let skeleton = generate_skeleton(ast_type, constructors)
  
  // Write to output file
  simplifile.write(output_path, skeleton)
    |> result.map_error(GenerateError.FileError)
  
  io.println("Generated formatter skeleton: " <> output_path)
  Ok(Nil)
}

fn parse_ast_constructors(source: String) -> List(Constructor) {
  // Simple parser for: pub type Expr { Int(Int) Add(Expr, Expr) ... }
  // Returns list of constructor names and argument types
}

fn generate_skeleton(type_name: String, constructors: List(Constructor)) -> String {
  let case_clauses = constructors |> list.map(fn(c) {
    generate_case_clause(c)
  })
  
  "
// Generated by: gleam run generate-formatter --type " <> type_name <> "
// TODO: Fill in the todo() calls with actual formatting logic

import syntax/formatter.{type Doc}
import syntax/formatter
import mylang/ast.{type " <> type_name <> "}

pub fn format_" <> type_name <> "(ast: " <> type_name <> ", parent_prec: Int) -> Doc {
  case ast {
" <> string.join(case_clauses, "\n") <> "
  }
}

// TODO: Implement helper functions as needed
// - format_binop for binary operators
// - format_unary for unary operators
// - format_record for records
// - format_match for match expressions
"
}

fn generate_case_clause(constructor: Constructor) -> String {
  let pattern = constructor.name <> "(" <> string.join(constructor.args, ", ") <> ")"
  let todo_msg = "format " <> constructor.name <> ": use formatter.format_* combinators"
  "    " <> pattern <> " -> todo(\"" <> todo_msg <> "\")"
}
```

---

### 2.2 CLI Integration

**File**: `src/compiler_bootstrap.gleam`

**Add command**:

```gleam
pub fn main() {
  let args = command_line_args()
  
  case parse_args(args) {
    Ok(GenerateFormatter(type, output)) -> {
      case formatter_gen.generate_formatter_skeleton(type, output) {
        Ok(_) -> io.exit(0)
        Error(err) -> {
          io.println("Error: " <> format_error(err))
          io.exit(1)
        }
      }
    }
    // ... other commands
  }
}

fn parse_args(args: List(String)) -> Result(Command, String) {
  case args {
    ["generate-formatter", "--type", type, "--output", output] ->
      Ok(GenerateFormatter(type, output))
    // ... other commands
  }
}
```

---

### 2.3 Usage Documentation

**File**: `docs/syntax-library.md`

**Add section**:

```markdown
## Generating Formatter Boilerplate

Instead of writing formatters from scratch, generate a skeleton:

```bash
gleam run generate-formatter --type Expr --output src/mylang/formatter.gleam
```

This generates:

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

Then fill in the `todo()` calls with actual formatting logic using the formatter combinators.
```

---

## Phase 3: Examples & Documentation (1 day)

### 3.1 Add More Examples

**Files to create**:

1. `src/examples/lambda.gleam` - Lambda calculus formatter
2. `src/examples/let.gleam` - Let-language formatter
3. `src/examples/tao_expr.gleam` - Tao expression formatter

**Example** (Lambda calculus):

```gleam
// src/examples/lambda.gleam
import syntax/formatter.{type Doc}
import syntax/formatter

pub type Expr {
  Var(String)
  Lam(String, Expr)
  App(Expr, Expr)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, 0) |> formatter.render_default
}

fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Var(name) -> formatter.text(name)
    Lam(param, body) ->
      formatter.format_lambda([param], format_expr(body, 0))
    App(fun, arg) ->
      formatter.format_application(
        format_expr(fun, 85),
        [format_expr(arg, 0)],
      )
  }
}
```

---

### 3.2 Formatter Cookbook

**File**: `docs/formatter-cookbook.md` (NEW)

**Content**:

```markdown
# Formatter Cookbook

Common formatting patterns and how to implement them.

## Binary Operators

```gleam
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
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

## Records with Layout

```gleam
fn format_record(fields: List(#(String, Expr))) -> Doc {
  let field_docs = fields |> list.map(fn(f) {
    let #(name, value) = f
    #(name, format_expr(value, 0))
  })
  formatter.format_record(field_docs)
}
```

## Match Expressions

```gleam
fn format_match(scrutinee: Expr, cases: List(Case)) -> Doc {
  formatter.format_match(
    format_expr(scrutinee, 85),
    cases |> list.map(fn(c) {
      formatter.format_case(
        format_pattern(c.pattern),
        c.guard |> option.map(format_expr(_, 0)),
        format_expr(c.body, 0),
      )
    }),
  )
}
```

## Function Application

```gleam
fn format_call(fun: Expr, args: List(Expr)) -> Doc {
  formatter.format_application(
    format_expr(fun, 85),
    args |> list.map(format_expr(_, 0)),
  )
}
```

## Lists

```gleam
fn format_list(items: List(Expr)) -> Doc {
  formatter.format_wrapped(
    "[",
    formatter.format_list(
      items |> list.map(format_expr(_, 0)),
      formatter.concat([formatter.text(","), formatter.line()]),
    ),
    "]",
  )
}
```
```

---

## Timeline

| Phase | Component | Days | Tests | Deliverables |
|-------|-----------|------|-------|--------------|
| 1 | Formatter Combinators | 1-2 | 20+ | 12 new combinator functions |
| 2 | Boilerplate Generator | 2-3 | 10+ | CLI command, generator |
| 3 | Examples & Docs | 1 | - | 3 examples, cookbook |
| **Total** | | **4-6** | **30+** | **Complete UX improvement** |

---

## Success Criteria

**After implementation**:

1. ✅ Formatter boilerplate reduced by 60-70%
2. ✅ New formatters can be created in ~1 hour (vs. ~3 hours)
3. ✅ 3+ working examples (lambda, let, tao)
4. ✅ Cookbook with common patterns
5. ✅ 30+ tests passing
6. ✅ Documentation updated

**Metrics**:
- Lines of manual formatter code: -60%
- Time to create new formatter: -66%
- Test coverage: 30+ new tests

---

## Risks & Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Combinators don't cover all cases | Low | Medium | Keep manual formatter option |
| Generator too complex | Medium | Low | Start simple, iterate |
| Documentation outdated | Low | Low | Keep examples in sync |

---

## Related Documents

- **[06-automatic-formatter-analysis.md](./06-automatic-formatter-analysis.md)** - Why full automation is not feasible
- **[04-formatter-library.md](./04-formatter-library.md)** - Current formatter status
- **[../syntax-library.md](../syntax-library.md)** - Syntax library documentation

---

## References

- [Formatter Implementation](../../src/syntax/formatter.gleam)
- [Grammar Implementation](../../src/syntax/grammar.gleam)
- [Calculator Example](../../src/examples/calc.gleam)
