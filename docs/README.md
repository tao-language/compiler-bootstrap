# Compiler Bootstrap Documentation

This documentation covers the compiler bootstrap project, which provides a dependently typed core language with language-agnostic parser and formatter libraries.

## Table of Contents

1. [Project Overview](#project-overview)
2. [Directory Structure](#directory-structure)
3. [Core Language](#core-language)
4. [Unified Grammar System](#unified-grammar-system)
5. [Language-Agnostic Libraries](#language-agnostic-libraries)
6. [Adding New Languages](#adding-new-languages)
7. [Testing](#testing)

---

## Project Overview

The compiler bootstrap project provides:

1. **A dependently typed core language** with:
   - Normalization by evaluation
   - Bidirectional type checking
   - Exhaustiveness checking
   - Fast, context-free parsing

2. **Language-agnostic parser library** supporting:
   - C-style syntax (braces, semicolons)
   - Python-style syntax (indentation-based)
   - OCaml-style syntax (begin/end blocks)
   - Parser combinators for building custom parsers

3. **Language-agnostic formatter library** supporting:
   - Multiple brace styles (K&R, Allman, etc.)
   - Configurable indentation
   - Automatic line breaking
   - Document algebra for flexible formatting

---

## Directory Structure

```
src/
├── parser.gleam          # Language-agnostic parser combinator library
├── formatter.gleam       # Language-agnostic pretty printer library
└── core/
    ├── core.gleam        # Core language types and type checker
    ├── parser.gleam      # Core language-specific parser
    └── formatter.gleam   # Core language-specific formatter

test/
├── core_test.gleam                    # Core language type checker tests
├── core_parser_formatter_test.gleam   # Core language parser/formatter tests
└── types_test.gleam.backup            # Backup of type system tests

docs/
├── core.md              # Core language specification
└── parser-formatter.md  # Parser and formatter library documentation
```

---

## Core Language

The core language is a minimal dependently typed calculus designed for:

- **Fast parsing**: Context-free grammar for efficient parsing
- **Type safety**: Bidirectional type checking with inference
- **Extensibility**: Foundation for higher-level languages

### Syntax

```typescript
// Types
Type0
Type1
I32
F64

// Terms
x                    // Variable
42                   // Literal
?                    // Hole (metavariable)
(x: Type) => x       // Lambda
f(x)                 // Application
{ x: 1, y: 2 }       // Record
Cons(1)              // Constructor
(x: Type)            // Annotation
match x with { A => 1 }  // Match
```

### Documentation

See [`docs/core.md`](core.md) for the complete core language specification.

---

## Unified Grammar System

The unified grammar system allows defining a language grammar once and deriving both parsers and formatters from it.

### Benefits

- **Consistency**: Parser and formatter always agree on syntax
- **Maintainability**: Change syntax in one place
- **Correctness**: Round-trip (parse → format → parse) is guaranteed
- **Simplicity**: No duplicate parser/formatter logic

### Example

```gleam
import grammar

// Define grammar
let expr_grammar = grammar.grammar("Expr", [
  grammar.rule("Expr", grammar.choice([
    grammar.seq([
      grammar.token("let"),
      grammar.pattern("Ident"),
      grammar.token("="),
      grammar.ref_rule("Expr"),
    ]),
    grammar.ref_rule("Term"),
  ])),
  grammar.rule("Term", grammar.choice([
    grammar.pattern("Ident"),
    grammar.pattern("Number"),
  ])),
])

// Generate parser
let parse = grammar.to_parser(expr_grammar)

// Generate formatter
let format = grammar.to_formatter(expr_grammar)

// Use them
let tree = parse("let x = 42")
let source = format(tree)
```

### Documentation

See [`docs/grammar.md`](grammar.md) for the complete grammar system documentation.

---

## Language-Agnostic Libraries

### Parser Library (`src/parser.gleam`)

A combinator-based parser library supporting multiple syntax styles.

#### Features

- **Token-based parsing**: Work with pre-tokenized input
- **Parser combinators**: Build complex parsers from simple ones
- **Error handling**: Graceful error recovery and reporting
- **Multiple syntax styles**: Support for braces, indentation, or custom delimiters

#### Configuration

```gleam
// C-style (TypeScript, Java, C++)
parser.c_style_config()
// - Braces: { }
// - Statement separator: ;
// - Indentation: 2 spaces

// Python-style
parser.python_style_config()
// - Indentation-based blocks
// - Indentation width: 4 spaces
// - No statement separator

// OCaml-style
parser.ocaml_style_config()
// - Block delimiters: begin/end
// - Statement separator: ;;
// - Indentation: 2 spaces
```

#### Parser Combinators

```gleam
// Basic parsers
parser.token(match_fn)      // Match token by predicate
parser.token_eq(token)      // Match specific token
parser.pure(value)          // Always succeed with value
parser.fail(message)        // Always fail

// Sequencing
parser.seq2(p1, p2)         // Parse two values
parser.seq3(p1, p2, p3)     // Parse three values
parser.ignore_right(p1, p2) // Parse both, keep first
parser.ignore_left(p1, p2)  // Parse both, keep second
parser.between(open, p, close) // Parse delimited value

// Choice
parser.or(p1, p2)           // Try p1, then p2
parser.choice([p1, p2, p3]) // Try multiple parsers

// Repetition
parser.many(p)              // Zero or more
parser.many1(p)             // One or more
parser.sep_by(p, sep)       // Separated list
parser.sep_by1(p, sep)      // Non-empty separated list

// Optional
parser.opt(p)               // Optional parser

// Transformation
parser.map(p, f)            // Transform result
parser.and_then(p, f)       // Transform with error handling

// Error handling
parser.with_context(p, msg) // Add error context
parser.recover(p)           // Error recovery
```

### Formatter Library (`src/formatter.gleam`)

A pretty-printing library using document algebra.

#### Features

- **Document algebra**: Build formatted output from combinators
- **Automatic line breaking**: Wrap lines at configured width
- **Configurable indentation**: Support for different styles
- **Multiple output styles**: C-style, Python-style, etc.

#### Configuration

```gleam
// C-style (K&R)
formatter.c_style_config()
// - Max width: 80
// - Indent: 2 spaces
// - Brace style: SameLine

// K&R style
formatter.kr_style_config()
// - Max width: 100
// - Indent: 4 spaces
// - Brace style: SameLine

// Allman style
formatter.allman_style_config()
// - Max width: 100
// - Indent: 4 spaces
// - Brace style: NextLine

// Python-style
formatter.python_style_config()
// - Max width: 88
// - Indent: 4 spaces
// - Brace style: None

// OCaml-style
formatter.ocaml_style_config()
// - Max width: 100
// - Indent: 2 spaces
// - Brace style: SameLine
```

#### Document Combinators

```gleam
// Basic documents
formatter.text(s)           // Plain text
formatter.space             // Space character
formatter.empty             // Empty document
formatter.line              // Soft line break
formatter.hard_line         // Hard line break

// Combining documents
formatter.concat([d1, d2])  // Concatenate documents
formatter.append(d1, d2)    // Append two documents
formatter.nest(n, d)        // Increase indentation
formatter.group(d)          // Group for line breaking
formatter.if_broken(b, f)   // Different doc when broken

// Separators
formatter.join(sep, docs)   // Join with separator
formatter.comma_sep(docs)   // Comma-separated
formatter.space_sep(docs)   // Space-separated
formatter.line_sep(docs)    // Line-separated

// Blocks
formatter.braces(d)         // { d }
formatter.parens(d)         // ( d )
formatter.brackets(d)       // [ d ]
formatter.block(d, config)  // Style-aware block

// Lists
formatter.list(docs)        // Formatted list
formatter.flex_list(docs)   // Flexible list (flat or broken)

// Utilities
formatter.from_string(s)    // String to document
formatter.from_int(i)       // Int to document
formatter.from_list(xs, f)  // Map list to documents
formatter.surround(l, d, r) // Surround document
formatter.parenthesize(d)   // Add parentheses
```

---

## Adding New Languages

To add a new high-level language:

1. **Create a new directory**: `src/<language>/`

2. **Define language-specific types**:
   ```gleam
   // src/mylang/types.gleam
   pub type Expr {
     Var(String)
     Lam(String, Expr)
     App(Expr, Expr)
   }
   ```

3. **Create a lexer**:
   ```gleam
   // src/mylang/lexer.gleam
   pub type Token {
     Ident(String)
     Arrow
     LParen
     RParen
     // ...
   }
   
   pub fn tokenize(source: String) -> List(Token) {
     // Tokenize source
   }
   ```

4. **Create a parser** using the language-agnostic library:
   ```gleam
   // src/mylang/parser.gleam
   import parser
   
   pub fn parse_expr() -> parser.Parser(Token, Expr) {
     parser.or(
       parse_lam(),
       parse_app(),
     )
   }
   ```

5. **Create a formatter**:
   ```gleam
   // src/mylang/formatter.gleam
   import formatter
   
   pub fn format_expr(expr: Expr) -> String {
     let doc = format_expr_doc(expr)
     formatter.render(doc, formatter.python_style_config())
   }
   ```

---

## Testing

### Running Tests

```bash
gleam test
```

### Test Structure

Tests are organized by component:

- `test/core_test.gleam` - Core language type checker tests
- `test/core_parser_formatter_test.gleam` - Core language parser/formatter tests

### Writing Tests

```gleam
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn my_test() {
  let result = my_function()
  result |> should.equal(expected_value)
}
```

### Test Coverage

Current test coverage:
- **Core language**: Type checking, normalization, exhaustiveness
- **Parser**: Tokenization, parsing all constructs
- **Formatter**: All document combinators, rendering

---

## References

- [Core Language Specification](core.md)
- [Parser and Formatter Guide](parser-formatter.md)
