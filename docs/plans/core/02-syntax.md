# Core Language Syntax Specification

> **Goal**: TypeScript-like syntax with full Term coverage
> **Status**: ✅ **Complete** - All 13 Term variants implemented with proper variable shadowing
> **Date**: March 2025 (Updated)

---

## Status

### ✅ What's Working

**Complete Syntax Implementation:**
- ✅ All 13 Term variants implemented
- ✅ Variables: `x` → `Var(0)` with proper De Bruijn conversion
- ✅ Literals: `42` → `Lit(I32(42))`
- ✅ Lambda: `x -> x` → `Lam("x", body)` (ASCII syntax)
- ✅ Pi types: `(x : A) -> B` → `Pi("x", in, out)` (ASCII syntax)
- ✅ Application: `f(x)` → `App(fun, arg)`
- ✅ Type annotations: `x : $I32` → `Ann(term, typ)`
- ✅ Field access: `record.field` → `Dot(arg, field)`
- ✅ Constructors: `#True`, `#Some(x)` → `Ctr(tag, arg)`
- ✅ Records: `{}`, `{x: 1}`, `{x: 1, y: 2}` → `Rcd(fields)`
- ✅ Type universes: `$Type`, `$Type(1)` → `Typ(level)`
- ✅ Literal types: `$I32`, `$F64` → `LitT(typ)`
- ✅ Holes: `?`, `?1` → `Hole(id)`
- ✅ Pattern matching: `match x with ... returning ...` → `Match(arg, motive, cases)`
- ✅ Built-in calls: `call name(args)` → `Call(name, args)`
- ✅ Comptime: `comptime { term }` → `Comptime(term)`

**Advanced Features:**
- ✅ **Two-pass parsing** - NamedTerm AST → De Bruijn conversion with proper variable shadowing
- ✅ **Variable shadowing** - `x -> y -> x` correctly preserves outer `x` reference
- ✅ **Pattern syntax** - Wildcards, as-patterns, constructor patterns
- ✅ **Full formatter** - All terms format correctly with precedence
- ✅ **Source locations** - Full span tracking from tokens
- ✅ **Round-trip tests** - Parse → format → verify
- ✅ **401 tests passing**

**Implementation:**
- ✅ Single file: `src/core/syntax.gleam`
- ✅ Grammar-derived parser and formatter
- ✅ NamedTerm intermediate AST for proper name resolution

### Key Implementation Details

#### Two-Pass Parsing (Variable Shadowing Fix)

```gleam
// Pass 1: Parse to NamedTerm (with string names)
pub type NamedTerm {
  NVar(name: String, span: Span)
  NLam(name: String, body: NamedTerm, span: Span)
  NPi(name: String, in: NamedTerm, out: NamedTerm, span: Span)
  // ... 12 variants total
}

// Pass 2: Convert to Term (De Bruijn indices)
fn named_to_de_bruijn_loop(term: NamedTerm, env: List(String)) -> Term {
  case term {
    NVar(name, span) -> {
      case find_in_env(env, name, 0) {
        Ok(index) -> Term(Var(index), span)  // Found binding
        Error(_) -> Term(Var(0), span)       // Free variable
      }
    }
    NLam(name, body, span) -> {
      let body_db = named_to_de_bruijn_loop(body, [name, ..env])
      Term(Lam(name, body_db), span)
    }
    // ... other cases
  }
}
```

This allows `x -> y -> x` to correctly reference the outer `x` (index 1), not the inner `y`.

#### Pattern AST

```gleam
pub type NamedPattern {
  NPAny(span: Span)                          // _
  NPAs(pattern: NamedPattern, name: String, span: Span)  // x @ pat
  NPTyp(level: Int, span: Span)              // $Type
  NPLit(value: Literal, span: Span)          // 42
  NPLitT(typ: LiteralType, span: Span)       // $I32
  NPRcd(fields: List(#(String, NamedPattern)), span: Span)  // {x: pat}
  NPCtr(tag: String, arg: NamedPattern, span: Span)  // #Name(pat)
}
```

### Syntax Reference

```gleam
// Variables and literals
x
42

// Lambda (ASCII)
x -> x
x -> y -> x  // Correctly preserves outer x!

// Pi types (ASCII)
(x : $I32) -> $I32
(x : $Type(1)) -> $Type(1)

// Constructors with # prefix
#True
#Some
#Maybe(x)

// Type universes and literal types
$Type
$Type(1)
$I32
$F64

// Records with fields
{}
{x: 1}
{x: 1, y: 2, z: 3}

// Holes with optional IDs
?
?1
?2

// Pattern matching
match x with $Type returning
  _ -> #True,
  #Some(y) -> y

// Built-in calls
call prim.add(x, y)

// Compile-time evaluation
comptime { 1 + 2 }

// Type annotations
x : $I32

// Field access
record.field
```

### Test Coverage

**401 tests passing** covering:
- Round-trip tests for all term types
- Variable shadowing scenarios
- Pattern matching syntax
- Precedence and parenthesization
- Lexer token recognition
- Formatter output

---

## Grammar Summary

### Tokens

| Token | Example | Description |
|-------|---------|-------------|
| `Ident` | `x`, `foo` | Identifier |
| `Number` | `42` | Integer literal |
| `Arrow` | `->` | Function/PI arrow |
| `Dollar` | `$` | Type/literal type prefix |
| `Hash` | `#` | Constructor prefix |
| `Question` | `?` | Hole marker |
| `Underscore` | `_` | Wildcard |
| `At` | `@` | As-pattern marker |

### Keywords

- `match` - Pattern matching
- `with` - Match clause introducer
- `returning` - Match return type introducer
- `call` - Built-in call
- `comptime` - Compile-time evaluation

### Grammar Rules

```
Expr = Lambda | Pi | Ann | App | Dot | Match | Call | Comptime | Atom
Atom = Constructor | Type | Hole | Record | Var | Lit | Parens
Constructor = #Ident | #Ident(Expr)
Type = $Ident | $Ident(Number)
Hole = ? | ?Number
Record = {} | {FieldList}
FieldList = Ident : Expr | Ident : Expr , FieldList
Lambda = Ident -> Expr
Pi = (Ident : Expr) -> Expr
Ann = Atom : Atom
App = Atom(Expr)
Dot = Atom.Ident
Match = match Expr with Expr returning Cases
Cases = Pattern -> Expr | Pattern -> Expr , Cases
Pattern = _ | Ident @ Pattern | #Ident(Pattern) | Number
Call = call Ident(ArgList)
ArgList = Expr | Expr , ArgList
Comptime = comptime { Expr }
```

---

## Implementation Pattern

### Two-Pass Architecture

```gleam
// Pass 1: Grammar builds NamedTerm
fn make_lambda(values) -> ParseValue {
  case values {
    [TokenValue(name_token), _, AstValue(AsTerm(body))] ->
      AsTerm(NLam(name_token.value, body, span))
    _ -> panic as "Expected lambda"
  }
}

// Pass 2: Convert to Term with De Bruijn indices
fn named_to_de_bruijn_loop(term: NamedTerm, env: List(String)) -> Term {
  // Environment tracks bound variable names
  // Index 0 = innermost binder
}

// Public API composes both passes
pub fn parse(source: String) -> ParseResult(Term) {
  let parsed = grammar.parse(core_grammar(), source)
  case parsed {
    Ok(AsTerm(named_term)) -> Ok(named_to_de_bruijn(named_term))
    // ...
  }
}
```

### Formatter with Pattern Support

```gleam
fn format_term(term: Term, parent_prec: Int, bindings: List(String)) -> formatter.Doc {
  case term.data {
    Var(index) -> {
      case get_binding(bindings, index) {
        Ok(name) -> formatter.text(name)
        Error(_) -> formatter.text("var" ++ int.to_string(index))
      }
    }
    Match(arg, motive, cases) -> {
      let case_docs = cases |> list.map(fn(c) {
        let Case(pattern, body, _) = c
        formatter.concat([
          format_pattern(pattern, bindings),
          formatter.text(" -> "),
          format_term(body, 70, bindings),
        ])
      })
      // ... format full match expression
    }
    // ... other cases
  }
}

fn format_pattern(pattern: Pattern, bindings: List(String)) -> formatter.Doc {
  case pattern {
    PAny -> formatter.text("_")
    PAs(inner, name) -> formatter.concat([
      formatter.text(name),
      formatter.text(" @ "),
      format_pattern(inner, bindings),
    ])
    PCtr(tag, arg) -> formatter.concat([
      formatter.text("#"),
      formatter.text(tag),
      formatter.text("("),
      format_pattern(arg, bindings),
      formatter.text(")"),
    ])
    // ... other cases
  }
}
```

---

## Precedence Levels

| Construct | Precedence | Associativity |
|-----------|------------|---------------|
| Atoms (Var, Lit, etc.) | 100 | N/A |
| Application | 85 | Left |
| Lambda | 70 | Right |
| Pi type | 65 | Right |
| Comptime | 50 | N/A |
| Match | 40 | N/A |

Lower precedence = looser binding = more likely to need parens.

---

## File Structure

```
src/core/
├── syntax.gleam         # Complete syntax implementation (~1150 lines)
│   ├── NamedTerm        # Intermediate AST with named variables
│   ├── NamedPattern     # Pattern AST with named variables
│   ├── NamedCase        # Match case AST
│   ├── ParseValue       # Wrapper type for multi-type grammar
│   ├── core_grammar()   # Complete grammar definition
│   ├── parse()          # Two-pass parser
│   ├── format()         # Full formatter
│   ├── named_to_de_bruijn_loop/2  # Name → index conversion
│   ├── format_pattern/2 # Pattern formatter
│   └── 50+ constructors # make_lambda, make_pi, etc.
└── core.gleam           # Term types, evaluator, type checker

test/core/
├── syntax_test.gleam    # 40+ syntax round-trip tests
└── core_test.gleam      # 263 core module tests
```

---

## Test Examples

### Variable Shadowing

```gleam
pub fn roundtrip_lambda_shadowing_test() {
  // x -> y -> x should preserve reference to outer x
  let source = "x -> y -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)  // Passes!
}

pub fn roundtrip_lambda_self_shadowing_test() {
  // x -> x -> x shows shadowing behavior
  let source = "x -> x -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)  // Inner x refers to middle lambda
}
```

### Pattern Matching

```gleam
pub fn roundtrip_match_test() {
  let source = "match x with $Type returning _ -> #True, #Some(y) -> y"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}
```

### Records

```gleam
pub fn roundtrip_record_multiple_fields_test() {
  let source = "{x: 1, y: 2, z: 3}"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}
```

---

## Implementation Challenges (Resolved)

### 1. Variable Shadowing ✅

**Problem**: Surface syntax uses names (`x`), but internal representation uses De Bruijn indices (`Var(0)`).

**Solution**: Two-pass parsing with `NamedTerm` intermediate AST:
- Pass 1: Parse to `NamedTerm` with string names
- Pass 2: Convert to `Term` with environment tracking

**Result**: `x -> y -> x` correctly preserves outer `x` reference.

### 2. Multi-Type Grammar ✅

**Problem**: Grammar DSL requires all rules to return same type, but field lists need `List(#(String, Term))`.

**Solution**: `ParseValue` wrapper type:
```gleam
pub type ParseValue {
  AsTerm(NamedTerm)
  AsFields(List(#(String, NamedTerm)))
  AsCases(List(NamedCase))
  AsPattern(NamedPattern)
  AsArgs(List(NamedTerm))
}
```

**Result**: Full record syntax `{x: 1, y: 2}` works correctly.

### 3. Pattern Grammar ✅

**Problem**: Match expressions need complex pattern grammar with wildcards, as-patterns, constructor patterns.

**Solution**: Dedicated `Pattern` rule with `NamedPattern` AST:
- `NPAny` for `_`
- `NPAs` for `x @ pat`
- `NPCtr` for `#Name(pat)`

**Result**: Full pattern matching syntax works.

---

## See Also

- [Core Language Overview](./01-overview.md)
- [Variable Shadowing Plan](./03-variable-shadowing.md)
- [FFI and Comptime](./03-ffi-comptime.md)
- [Syntax Library Documentation](../../syntax-library.md)
- [Grammar DSL](../grammar/02-grammar-dsl.md)
