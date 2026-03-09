# Core Language Implementation Plan

> **Status**: Grammar system complete, core language grammar pending
> **Date**: March 2025

---

## Current Status

### ✅ Complete and Working

1. **Lexer** - Tokenizes all core language tokens
2. **Grammar DSL** - Full layout-aware grammar definition
3. **Parser** - Handles all grammar constructs
4. **Formatter** - Layout-aware formatting with precedence
5. **Tests** - 238 tests passing for grammar system
6. **FFI/Comptime** - 263 tests passing

### ⏳ Pending

1. **Core Language Grammar Definition** - Create `src/core/grammar.gleam`
2. **Constructor/Deconstructor Functions** - Map parsed values to `Term`
3. **Core Formatter** - Implement `format_term()` for all `Term` variants
4. **De Bruijn Conversion** - Handle name ↔ index conversion
5. **Integration** - Wire up with existing core module

---

## Implementation Phases

### Phase 1: Minimal Core Grammar (2-4 hours)

Start with the simplest working subset:

**Grammar rules:**
- `Expr` → `Atom` | `App`
- `Atom` → `Ident` | `Number` | `Hole` | `Paren`
- `App` → `Atom ( ExprList )`

**Constructors:**
- `make_var(token)` → `Term(Var(name), span)`
- `make_lit(token)` → `Term(Lit(value), span)`
- `make_hole(token)` → `Term(Hole(id), span)`
- `make_app(fun, args)` → `Term(App(fun, arg), span)`

**Tests:**
- Parse variable: `x`
- Parse number: `42`
- Parse hole: `?`
- Parse application: `f(x)`
- Parse nested app: `f(g(x))`
- Parse multi-arg: `f(x, y)`

### Phase 2: Lambda and Pi Types (4-6 hours)

Add function types:

**Grammar rules:**
- `Expr` → `Lambda` | `PiType` | ...
- `Lambda` → `λ LambdaParams . Expr`
- `PiType` → `( Ident : Type ) → Type`

**Constructors:**
- `make_lambda(params, body)` → Nested `Term(Lam(name, body), span)`
- `make_pi(name, in_, out)` → `Term(Pi(name, in_, out), span)`

**Tests:**
- Parse lambda: `λx. x`
- Parse multi-param lambda: `λx y. x + y`
- Parse Pi type: `(x: A) → B`
- Parse arrow type: `A → B`

### Phase 3: Records and Field Access (4-6 hours)

Add record types:

**Grammar rules:**
- `Atom` → `Record` | `Dot`
- `Record` → `{ FieldList }`
- `Dot` → `Atom . Ident`

**Constructors:**
- `make_record(fields)` → `Term(Rcd(fields), span)`
- `make_dot(obj, field)` → `Term(Dot(obj, field), span)`

**Tests:**
- Parse record: `{x: 1, y: 2}`
- Parse field access: `r.x`
- Parse nested access: `r.x.y`

### Phase 4: Type Annotations (2-4 hours)

Add type annotations:

**Grammar rules:**
- `Expr` → `App : Type`

**Constructors:**
- `make_annotation(term, typ)` → `Term(Ann(term, typ), span)`

**Tests:**
- Parse annotation: `x: Int`
- Parse annotated app: `f(x): Int`

### Phase 5: Match Expressions (6-8 hours)

Add pattern matching:

**Grammar rules:**
- `Expr` → `match Expr MatchBody`
- `MatchBody` → `{ CaseList }`
- `Case` → `Pattern → Expr`

**Constructors:**
- `make_match(arg, motive, cases)` → `Term(Match(arg, motive, cases), span)`

**Tests:**
- Parse match: `match x {A → 1}`
- Parse with patterns: `match x {Cons(h, t) → h}`

### Phase 6: Constructors (2-4 hours)

Add algebraic data types:

**Grammar rules:**
- `Atom` → `Constructor`
- `Constructor` → `Ident ( [ExprList] )`

**Constructors:**
- `make_constructor(name, args)` → `Term(Ctr(name, arg), span)`

**Tests:**
- Parse nullary: `Nil`
- Parse unary: `Cons(1)`
- Parse multi-arg: `Cons(1, Nil)`

### Phase 7: Comptime Integration (4-6 hours)

Integrate with existing comptime system:

**Grammar rules:**
- `Expr` → `comptime Expr`

**Constructors:**
- `make_comptime(expr)` → `Term(Comptime(expr), span)`

**Tests:**
- Parse comptime: `comptime add(1, 2)`
- Test constant folding

### Phase 8: Formatter (6-8 hours)

Implement complete formatter:

**Functions:**
- `format_term(term, parent_prec)` → `Doc`
- `format_atom(term)` → `Doc`
- `format_lambda(name, body, parent_prec)` → `Doc`
- `format_app(fun, args, parent_prec)` → `Doc`
- etc.

**Tests:**
- Format variable: `x`
- Format application: `f(x)`
- Format lambda: `λx. x`
- Round-trip: `parse(format(parse(s))) == parse(s)`

### Phase 9: De Bruijn Conversion (4-6 hours)

Handle name/index conversion:

**Parser:**
- Maintain symbol table during parsing
- Convert names to De Bruijn indices

**Formatter:**
- Convert indices back to names (when possible)
- Show as indices when no name available

**Tests:**
- Parse `λx. x` → `Lam(0)`
- Format `Lam(0)` → `λx. x`

### Phase 10: Polish (4-8 hours)

Final touches:

- Better error messages
- Performance optimization
- Documentation
- Integration with existing core module

---

## Key Design Decisions

### 1. Bidirectional Grammar

Each grammar rule needs both constructor and deconstructor:

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,      // Parse: values → AST
    deconstructor: fn(a) -> List(Value(a)),    // Format: AST → values
  )
}
```

### 2. Formatter Generation Algorithm

```
format_ast(grammar, ast, parent_prec):
  1. Find which rule/alternative produced this AST
     - Try each rule's deconstructor until one succeeds

  2. Deconstruct AST into values
     - values = alternative.deconstructor(ast)

  3. Format each value based on pattern
     - For TokenValue: output the token text
     - For AstValue(child): recursively format_ast(child, child_prec)

  4. Join formatted values with layout hints from pattern
     - Use SoftBreak/HardBreak/Space from SeqWithLayout

  5. Add parentheses if precedence requires
```

### 3. Token Values in Deconstructors

**Problem**: Deconstructors need to return `TokenValue` for punctuation, but we don't have actual tokens when formatting.

**Solution**: Create "synthetic" tokens with just the text:

```gleam
fn make_lparen() -> Token {
  Token(kind: "LParen", value: "(", start: pos(0), end: pos(0))
}
```

### 4. Finding Matching Alternative

**Problem**: How to find which alternative produced an AST?

**Solution**: Try each deconstructor until one succeeds (doesn't panic):

```gleam
fn find_matching_alternative(grammar, ast) {
  list.find_map(grammar.rules, fn(rule) {
    list.find_map(rule.alternatives, fn(alt) {
      try {
        alt.deconstructor(ast)
        Some(#(rule, alt))
      } catch panic {
        None  // This alternative doesn't match
      }
    })
  })
}
```

### 5. Precedence for Complex Patterns

**Problem**: How to determine child precedence for non-operator patterns?

**Solution**: Each pattern type has a default precedence:
- Atoms: 100 (highest)
- Application: 85
- Lambda: 70
- Pi type: 65
- etc.

---

## Challenges and Solutions

### Challenge 1: Application Parsing

**Problem**: Core language application is C-style only, but needs curried semantics.

**Solution**: Parse `f(x, y)` as left-associative: `((f x) y)`

### Challenge 2: Lambda Syntax

**Problem**: Lambda uses `λx. body` with Unicode character.

**Solution**: Lexer handles Unicode λ, grammar treats it as keyword.

### Challenge 3: Record Fields

**Problem**: Record fields are `name: value` pairs with nested structure.

**Solution**: Use `sep1` with custom field pattern.

### Challenge 4: Pattern Matching

**Problem**: Match expressions have complex syntax with patterns and guards.

**Solution**: Separate grammar rules for patterns and cases.

### Challenge 5: De Bruijn Indices

**Problem**: Surface syntax uses names, internal representation uses indices.

**Solution**: Symbol table during parsing, context during formatting.

---

## File Structure

```
src/
├── syntax/
│   ├── grammar.gleam      # Grammar DSL + parser + formatter generators
│   ├── formatter.gleam    # Document algebra (unchanged)
│   └── lexer.gleam        # Tokenizer (unchanged)
├── core/
│   ├── core.gleam         # Term types, evaluator, type checker (unchanged)
│   ├── grammar.gleam      # Core language grammar definition ← MAIN WORK
│   ├── parser.gleam       # Thin wrapper: grammar.parse(core_grammar(), src)
│   └── formatter.gleam    # Thin wrapper: grammar.format(core_grammar(), ast)
└── ...
```

---

## Test Plan

### Parser Tests

```gleam
pub fn parse_var_test() {
  let result = parser.parse(core_grammar(), "x")
  result.ast |> should.equal(Term(Var(0), _))
}

pub fn parse_app_test() {
  let result = parser.parse(core_grammar(), "f(x)")
  result.ast |> should.equal(Term(App(Var(0), Var(1)), _))
}

pub fn parse_lambda_test() {
  let result = parser.parse(core_grammar(), "λx. x")
  result.ast |> should.equal(Term(Lam(0, Var(0)), _))
}
```

### Formatter Tests

```gleam
pub fn format_var_test() {
  let term = Term(Var(0), _)
  formatter.format(term) |> should.equal("x")
}

pub fn format_app_test() {
  let term = Term(App(Var(0), Var(1)), _)
  formatter.format(term) |> should.equal("f(x)")
}
```

### Round-Trip Tests

```gleam
pub fn roundtrip_var_test() {
  let source = "x"
  let result = parser.parse(core_grammar(), source)
  let formatted = formatter.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_app_test() {
  let source = "f(x)"
  let result = parser.parse(core_grammar(), source)
  let formatted = formatter.format(result.ast)
  formatted |> should.equal(source)
}
```

---

## Estimated Effort

| Phase | Description | Hours |
|-------|-------------|-------|
| 1 | Minimal grammar (atoms + app) | 2-4 |
| 2 | Lambda and Pi types | 4-6 |
| 3 | Records and field access | 4-6 |
| 4 | Type annotations | 2-4 |
| 5 | Match expressions | 6-8 |
| 6 | Constructors | 2-4 |
| 7 | Comptime integration | 4-6 |
| 8 | Formatter | 6-8 |
| 9 | De Bruijn conversion | 4-6 |
| 10 | Polish | 4-8 |
| **Total** | | **34-54 hours** |

---

## Summary

The grammar system is complete and tested. Implementing the core language grammar is a matter of:

1. Defining grammar rules following calculator example patterns
2. Writing constructor/deconstructor functions for each `Term` variant
3. Implementing formatter that uses grammar metadata
4. Adding comprehensive tests for each construct

**Key insight**: Both parser and formatter are generated from the same grammar - it's truly the single source of truth.

| Direction | Grammar Provides | Generated By |
|-----------|-----------------|--------------|
| Source → AST | Pattern + Constructor | Parser |
| AST → Source | Pattern + Deconstructor | Formatter |

---

## See Also

- [Core Language Overview](./01-overview.md)
- [Syntax Specification](./02-syntax.md)
- [FFI and Comptime](./03-ffi-comptime.md)
- [Grammar DSL](../grammar/02-grammar-dsl.md)
