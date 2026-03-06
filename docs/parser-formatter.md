# Parser and Formatter Guide

This document explains the parser and formatter implementation for the core language.

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Lexer](#lexer)
4. [Parser](#parser)
5. [Formatter](#formatter)
6. [Usage Examples](#usage-examples)
7. [API Reference](#api-reference)

---

## Overview

The parser and formatter provide bidirectional conversion between source code and the core language AST (`Term`).

```
Source Code ←→ Lexer → Tokens ←→ Parser → Term ←→ Formatter → Source Code
```

### Design Goals

- **Simplicity**: Straightforward recursive descent parsing, no complex frameworks
- **Clarity**: Clear separation between lexing, parsing, and formatting
- **Error Recovery**: Parser continues on errors where possible
- **Round-trip**: Parsing then formatting should produce equivalent source

---

## Architecture

The parser and formatter provide bidirectional conversion between source code and the core language AST (`Term`).

```
src/core/
├── core.gleam       # Core language types and type checker
├── parser.gleam     # Lexer and parser
└── formatter.gleam  # Pretty printer
```

The `src/core/` directory contains all core language-specific code. This structure allows:
- Adding new high-level languages in separate directories
- Reusing parser/formatter patterns for other languages
- Clear separation between language-agnostic and language-specific code

### Data Flow

1. **Lexer**: Source string → List of tokens
2. **Parser**: List of tokens → Term AST
3. **Formatter**: Term AST → Source string

---

## Lexer

The lexer converts source code into a stream of tokens.

### Token Types

```gleam
pub type Token {
  TokIdent(String)        // x, foo, bar
  TokConstructor(String)  // Cons, Nil, True
  TokInteger(Int)         // 42, 100
  TokType(Int)            // Type, Type0, Type1
  TokLitType(LiteralType) // I32, F64
  TokMatch                // match
  TokWith                 // with
  TokArrow                // =>
  TokColon                // :
  TokComma                // ,
  TokLParen               // (
  TokRParen               // )
  TokLBrace               // {
  TokRBrace               // }
  TokUnderscore           // _
  TokHole                 // ?
  TokEOF                  // End of file
}
```

### Lexical Rules

| Pattern | Token | Example |
|---------|-------|---------|
| `[a-z][a-z0-9]*` | `TokIdent` or keyword | `x`, `match`, `with` |
| `[A-Z][a-z0-9]*` | `TokConstructor` or `TokType` | `Cons`, `Type`, `Type0` |
| `[0-9]+` | `TokInteger` | `42`, `100` |
| `=>` | `TokArrow` | `=>` |
| `:` | `TokColon` | `:` |
| `_` | `TokUnderscore` | `_` |
| `?` | `TokHole` | `?` |
| `//.*` | (ignored) | `// comment` |

### Implementation

The lexer works directly with UTF codepoint integers for efficiency:

```gleam
pub fn tokenize(source: String) -> List(Token) {
  let chars = 
    string.to_utf_codepoints(source) 
    |> list.map(string.utf_codepoint_to_int)
  do_tokenize(chars, []) |> list.reverse
}
```

---

## Parser

The parser uses recursive descent to convert tokens into a `Term` AST.

### Parsing Strategy

1. **Peek**: Look at current token without consuming
2. **Expect**: Consume token, error if unexpected
3. **Recurse**: Call appropriate parsing function for construct

### Grammar (Informal)

```
term       ::= match_expr | lambda_expr
match_expr ::= "match" term "with" "{" cases "}"
lambda_expr ::= "(" ident ":" term ")" "=>" term
app_expr   ::= atom_expr "(" term ")"
atom_expr  ::= record | constructor | "(" term ":" term ")" 
             | hole | literal_type | literal | type | ident

record     ::= "{" fields "}"
fields     ::= (ident ":" term ("," term)*)?

constructor ::= ident "(" term ")"

pattern    ::= "_" | ident | literal | type | "{" pattern_fields "}" | constructor
```

### Error Handling

The parser returns `Result(Term, String)` with simple error messages:

```gleam
fn expect(parser: Parser, expected: Token) -> Result(Parser, String) {
  case peek(parser) {
    Some(t) if t == expected -> Ok(advance(parser))
    Some(_) -> Error("Unexpected token")
    None -> Error("Unexpected end of input")
  }
}
```

---

## Formatter

The formatter converts a `Term` AST back to source code.

### Formatting Rules

| Term | Output |
|------|--------|
| `Typ(k)` | `"Type"` or `"Type" <> k` |
| `Lit(I32(n))` | `int.to_string(n)` |
| `Hole(_)` | `"?"` |
| `Lam(name, body)` | `"(" <> name <> ": A) => " <> format(body)` |
| `App(fun, arg)` | `format(fun) <> "(" <> format(arg) <> ")"` |
| `Rcd(fields)` | `"{ " <> join(fields) <> " }"` |
| `Match(arg, _, cases)` | `"match " <> format(arg) <> " with { " <> join(cases) <> " }"` |

### Implementation

Simple recursive formatting:

```gleam
pub fn format(term: core.Term) -> String {
  case term.data {
    core.Typ(k) -> format_type(k)
    core.Lit(lit) -> format_literal(lit)
    core.Lam(name, body) -> format_lambda(name, body)
    // ... etc
  }
}
```

---

## Usage Examples

### Parsing Source Code

```gleam
import parser

pub fn example() {
  // Parse a type
  parser.parse_source("Type")
  // Returns: Ok(Term(Typ(0), Span("parsed", 0, 0)))
  
  // Parse a lambda
  parser.parse_source("(x: Type) => x")
  // Returns: Ok(Term(Lam("x", ...), ...))
  
  // Parse a record
  parser.parse_source("{ x: 1, y: 2 }")
  // Returns: Ok(Term(Rcd(...), ...))
  
  // Parse with error
  parser.parse_source("invalid syntax")
  // Returns: Error("Unexpected token")
}
```

### Formatting Terms

```gleam
import formatter
import core

pub fn example() {
  let span = core.Span("test", 0, 0)
  
  // Format a type
  formatter.format(core.Term(core.Typ(0), span))
  // Returns: "Type"
  
  // Format a literal
  formatter.format(core.Term(core.Lit(core.I32(42)), span))
  // Returns: "42"
  
  // Format a hole
  formatter.format(core.Term(core.Hole(0), span))
  // Returns: "?"
}
```

### Round-Trip

```gleam
import parser
import formatter

pub fn roundtrip(source: String) -> Result(String, String) {
  use term <- result.map_error(parser.parse_source(source), fn(e) {
    "Parse error: " <> e
  })
  Ok(formatter.format(term))
}

// roundtrip("Type") returns Ok("Type")
// roundtrip("42") returns Ok("42")
```

---

## API Reference

### Parser Module

#### `tokenize(source: String) -> List(Token)`

Convert source code to tokens.

```gleam
parser.tokenize("x")
// Returns: [TokIdent("x"), TokEOF]
```

#### `parse_source(source: String) -> Result(core.Term, String)`

Parse source code into a Term AST.

```gleam
parser.parse_source("Type")
// Returns: Ok(Term(Typ(0), Span("parsed", 0, 0)))

parser.parse_source("invalid")
// Returns: Error("Unexpected token")
```

### Formatter Module

#### `format(term: core.Term) -> String`

Format a Term to source code.

```gleam
formatter.format(core.Term(core.Typ(0), span))
// Returns: "Type"
```

#### `format_pattern(pattern: core.Pattern) -> String`

Format a Pattern to source code.

```gleam
formatter.format_pattern(core.PAny)
// Returns: "_"
```

---

## Supported Syntax

### Types

```typescript
Type      // Type at level 0
Type0     // Type at level 0
Type1     // Type at level 1
```

### Literals

```typescript
42        // Integer
I32       // Literal type
```

### Terms

```typescript
x         // Variable
?         // Hole (metavariable)
(x: A) => x          // Lambda
f(x)      // Application
{ x: 1 }  // Record
Cons(x)   // Constructor
(x: Type) // Annotation
match x with { A => 1 }  // Match
```

### Patterns

```typescript
_         // Wildcard
x         // Variable pattern
42        // Literal pattern
{ x: p }  // Record pattern
Cons(p)   // Constructor pattern
```

---

## Limitations

### Current Limitations

1. **No floating point literals** - Only integers supported
2. **No nested comments** - `//` comments only
3. **No pretty printing** - Simple formatting, no line breaking
4. **No error recovery** - Parser stops at first error
5. **No source positions** - Spans are placeholders

### Future Improvements

1. Add floating point literal support
2. Implement block comments `/* */`
3. Add pretty printing with line breaking
4. Implement error recovery for better IDE support
5. Track proper source positions through parsing

---

## Testing

Run the parser and formatter tests:

```bash
gleam test
```

Test coverage includes:

- Tokenization of all token types
- Parsing of all term forms
- Formatting of all term forms
- Round-trip (parse then format)

---

## See Also

- [`docs/core.md`](core.md) - Core language specification
- [`src/parser.gleam`](../src/parser.gleam) - Parser implementation
- [`src/formatter.gleam`](../src/formatter.gleam) - Formatter implementation
