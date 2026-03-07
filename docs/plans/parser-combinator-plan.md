# Generic Parser Combinator Library - Implementation Plan

## Overview

This document outlines the plan for implementing a **generic parser combinator library** in Gleam that can be used for any programming language, not just the core language. The library should be completely generic and composable, similar to the Haskell reference implementation.

## Design Goals

1. **Generic**: The library should not assume any specific language features (keywords, operators, etc.)
2. **Composable**: Parsers should be composable using combinators
3. **Type-safe**: Leverage Gleam's type system for type-safe parsing
4. **Good UX**: Easy to use and extend for new languages
5. **Error Recovery**: Support for error recovery and recovery strategies
6. **Location Tracking**: Track source locations for error messages

## Core Types

### Parser Type

```gleam
/// A parser that produces a value of type `a`
pub type Parser(a) {
  Parser(fn(State) -> Result(#(a, State), State))
}

/// Parser state with remaining input and location tracking
pub type State {
  State(
    remaining: String,
    filename: String,
    pos: Position,
    index: Int,
    expected: String,
    committed: String,
  )
}

/// Source position
pub type Position {
  Position(row: Int, col: Int)
}

/// Source location with filename and range
pub type Location {
  Location(filename: String, range: Range)
}

/// Range of positions
pub type Range {
  Range(start: Position, end: Position)
}
```

## Core Combinators

### Basic Parsers

```gleam
/// Parser that succeeds with a value
pub fn ok(a: a) -> Parser(a)

/// Parser that always fails
pub fn fail() -> Parser(a)

/// Get current state
pub fn state() -> Parser(State)

/// Get current position
pub fn position() -> Parser(Position)
```

### Character Parsers

```gleam
/// Parse any character
pub fn any_char() -> Parser(String)

/// Parse a specific character
pub fn char(c: String) -> Parser(String)

/// Parse a character satisfying a predicate
pub fn char_if(pred: fn(String) -> Bool) -> Parser(String)

/// Parse one of several characters
pub fn char_of(chars: List(String)) -> Parser(String)

/// Parse a letter
pub fn letter() -> Parser(String)

/// Parse a digit
pub fn digit() -> Parser(String)

/// Parse a letter or digit
pub fn alphanumeric() -> Parser(String)

/// Parse whitespace
pub fn space() -> Parser(String)
pub fn spaces() -> Parser(String)

/// Parse whitespace including newlines
pub fn whitespace() -> Parser(String)
pub fn whitespaces() -> Parser(String)
```

### Text Parsers

```gleam
/// Parse specific text
pub fn text(str: String) -> Parser(String)

/// Parse one of several texts
pub fn text_of(texts: List(String)) -> Parser(String)

/// Parse a word (alphanumeric sequence)
pub fn word() -> Parser(String)

/// Parse a specific word with word boundary
pub fn word_boundary(txt: String) -> Parser(String)
```

### Sequence Combinators

```gleam
/// Chain parsers in sequence
pub fn chain(parsers: List(Parser(a))) -> Parser(List(a))

/// Parse zero or one
pub fn zero_or_one(parser: Parser(a)) -> Parser(Option(a))

/// Parse zero or more
pub fn zero_or_more(parser: Parser(a)) -> Parser(List(a))

/// Parse one or more
pub fn one_or_more(parser: Parser(a)) -> Parser(List(a))

/// Parse exactly n times
pub fn exactly(n: Int, parser: Parser(a)) -> Parser(List(a))

/// Parse at least n times
pub fn at_least(n: Int, parser: Parser(a)) -> Parser(List(a))

/// Parse at most n times
pub fn at_most(n: Int, parser: Parser(a)) -> Parser(List(a))

/// Parse between min and max times
pub fn between(min: Int, max: Int, parser: Parser(a)) -> Parser(List(a))
```

### Choice Combinators

```gleam
/// Try parsers in order, return first success
pub fn one_of(parsers: List(Parser(a))) -> Parser(a)

/// Commit to first successful parse
pub fn commit_one_of(parsers: List(Parser(a))) -> Parser(a)

/// Choose based on a comparison function
pub fn choose(
  f: fn(a, a) -> Result(Nil, Nil),
  parsers: List(Parser(a))
) -> Parser(a)
```

### Padding and Delimiters

```gleam
/// Pad parser on the left
pub fn padded_l(padding: Parser(a), parser: Parser(b)) -> Parser(b)

/// Pad parser on the right
pub fn padded_r(padding: Parser(a), parser: Parser(b)) -> Parser(b)

/// Pad parser on both sides
pub fn padded(padding: Parser(a), parser: Parser(b)) -> Parser(b)

/// Parse between delimiters
pub fn inbetween(
  start: Parser(a),
  end: Parser(a),
  parser: Parser(b)
) -> Parser(b)

/// Parse delimited by open and close
pub fn delimited_by(
  open: Parser(a),
  close: Parser(a),
  parser: Parser(b)
) -> Parser(b)

/// Parse separated by delimiter
pub fn separated_by(
  sep: Parser(a),
  parser: Parser(b)
) -> Parser(List(b))
```

### Lookahead and Assertions

```gleam
/// Lookahead without consuming
pub fn lookahead(parser: Parser(a)) -> Parser(a)

/// Negative lookahead
pub fn lookahead_not(parser: Parser(a)) -> Parser(Nil)

/// Assert a condition
pub fn assert(pred: fn(a) -> Bool, parser: Parser(a)) -> Parser(a)

/// Negate a parser
pub fn not(parser: Parser(a)) -> Parser(Nil)
```

## Error Handling and Recovery

Error handling is **critical** for user experience. The parser should **never fail completely** - instead, it should always return a (possibly partial) AST along with a list of errors. This allows:

1. **Multiple error reporting**: Show all errors at once, not just the first one
2. **Partial AST**: Continue parsing even after errors to provide partial results
3. **Better UX**: Users can fix multiple errors in one iteration

### Error Types

```gleam
/// Parse error with location and message
pub type ParseError {
  ParseError(
    location: Location,
    message: String,
    expected: List(String),
    severity: ErrorSeverity,
  )
}

/// Error severity
pub type ErrorSeverity {
  Error      // Must be fixed
  Warning    // Should be fixed but parsing can continue
  Info       // Informational
}

/// Parser result - always succeeds with AST and errors
pub type ParseResult(a) {
  ParseResult(
    ast: a,
    errors: List(ParseError),
  )
}
```

### Error Recovery Strategies

```gleam
/// Sync to a synchronization point
pub fn sync_to(sync_points: List(Parser(a))) -> Parser(Nil)

/// Skip until end of line
pub fn sync_to_eol() -> Parser(Nil)

/// Skip until next statement
pub fn sync_to_next_stmt() -> Parser(Nil)

/// Skip current token
pub fn skip_token() -> Parser(Nil)

/// Insert a missing token
pub fn insert_token(token: a) -> Parser(a)

/// Delete tokens until a predicate is satisfied
pub fn delete_until(pred: fn(a) -> Bool) -> Parser(Nil)
```

### Error Recovery Combinators

```gleam
/// Parse with recovery - always returns a result
pub fn recover(
  parser: Parser(a),
  recovery: Parser(a),
  error_msg: String
) -> Parser(ParseResult(a))

/// Parse with sync points - skip to sync points on error
pub fn recover_with_sync(
  parser: Parser(a),
  sync_points: List(Parser(Nil)),
  error_msg: String
) -> Parser(ParseResult(a))

/// Parse and collect errors
pub fn with_error_recovery(parser: Parser(a)) -> Parser(ParseResult(a))

/// Convert parser to always succeed with errors
pub fn recover_all(parser: Parser(a), default: a) -> Parser(ParseResult(a))
```

### Error Reporting

```gleam
/// Format a single error
pub fn format_error(error: ParseError, source: String) -> String

/// Format multiple errors
pub fn format_errors(errors: List(ParseError), source: String) -> String

/// Format error with source snippet
pub fn format_error_with_snippet(
  error: ParseError,
  source: String,
  context_lines: Int
) -> String
```

### Usage Example with Error Recovery

```gleam
// Define expression parser with error recovery
let expr = recover(
  precedence(ops, 0),
  sync_to([char(';'), char('\n'), char('}')]),
  "Expected expression"
)

// Parse entire file with error recovery
let parse_file(source: String) -> ParseResult(Module) {
  let result = with_error_recovery(module_parser())
  
  case parse(result, "main.gleam", source) {
    Ok(parse_result) -> parse_result
    Error(state) -> 
      ParseResult(
        ast: empty_module(),
        errors: [ParseError(
          location: Location(state.filename, Range state.pos state.pos),
          message: "Failed to parse",
          expected: [state.expected],
          severity: Error
        )]
      )
  }
}

// Format errors for display
let formatted = format_errors(result.errors, source)
io.println(formatted)

// Use the AST even if there were errors
case result.ast {
  Some(module) -> compile_module(module)
  None -> io.println("Could not parse file")
}
```

### Error Recovery Strategies

1. **Panic Mode**: Skip tokens until a synchronization point (statement separator, closing brace, etc.)
2. **Phrase Level**: Insert/delete/replace tokens to recover from specific errors
3. **Global Recovery**: Use multiple strategies based on error type

### Best Practices

1. **Always return AST**: Even with errors, return a partial AST
2. **Collect all errors**: Don't stop at the first error
3. **Meaningful messages**: Provide clear, actionable error messages
4. **Source locations**: Include precise source locations
5. **Context**: Show surrounding source code for context
6. **Suggestions**: Suggest fixes when possible

### Example Error Output

```
error: Expected expression
  ┌─ main.gleam:5:10
  │
5 │ let x = + y;
  │          ^ Expected expression after operator

  Hint: Try adding a value after the operator

warning: Missing semicolon
  ┌─ main.gleam:10:15
   │
10 │ let y = 42
   │               ^ Expected ';'

   Hint: Add ';' at the end of the statement

Found 2 errors, 1 warning
```
```

### Expression Parsers (Pratt Parsing)

```gleam
/// Expression parser type for Pratt parsing
pub type ExprParser(a) {
  Atom(fn(Parser(a)) -> Parser(a))
  Prefix(Int, fn(Parser(a)) -> Parser(a))
  InfixL(Int, fn(a, Parser(a)) -> Parser(a))
  InfixR(Int, fn(a, Parser(a)) -> Parser(a))
}

/// Atom parser
pub fn atom(
  f: fn(a) -> b,
  parser: Parser(a)
) -> ExprParser(b)

/// Group parser
pub fn group(
  open: Parser(a),
  close: Parser(a),
  spaces: Parser(b),
) -> ExprParser(c)

/// Prefix operator
pub fn prefix(
  precedence: Int,
  f: fn(Location, op, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Suffix operator
pub fn suffix(
  precedence: Int,
  f: fn(Location, op, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Left-associative infix operator
pub fn infix_l(
  precedence: Int,
  f: fn(Location, op, a, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Right-associative infix operator
pub fn infix_r(
  precedence: Int,
  f: fn(Location, op, a, a) -> a,
  spaces: Parser(a),
  op: Parser(op)
) -> ExprParser(a)

/// Build expression parser with precedence
pub fn precedence(ops: List(ExprParser(a)), min_prec: Int) -> Parser(a)
```

## Usage Example

Here's how the library would be used to define a simple expression language:

```gleam
import parser.{type Parser, Parser}
import parser.{atom, infix_l, prefix, precedence}

// Define operators
let ops = [
  // Atoms
  atom(fn(x) -> x, integer()),
  atom(fn(x) -> x, float()),
  atom(fn(x) -> x, identifier()),
  
  // Prefix operators
  prefix(100, fn(loc, op, x) -> Neg(loc, x), spaces(), char("-")),
  
  // Infix operators (left-associative)
  infix_l(50, fn(loc, op, x, y) -> Add(loc, x, y), spaces(), char("+")),
  infix_l(50, fn(loc, op, x, y) -> Sub(loc, x, y), spaces(), char("-")),
  infix_l(60, fn(loc, op, x, y) -> Mul(loc, x, y), spaces(), char("*")),
  infix_l(60, fn(loc, op, x, y) -> Div(loc, x, y), spaces(), char("/")),
  
  // Right-associative operators
  infix_r(70, fn(loc, op, x, y) -> Pow(loc, x, y), spaces(), char("^")),
]

// Build expression parser
let expr = precedence(ops, 0)
```

## Implementation Phases

### Phase 1: Core Types and Basic Parsers
- [ ] Define `Parser(a)`, `State`, `Position`, `Location`, `Range` types
- [ ] Implement `ok`, `fail`, `state`, `position`
- [ ] Implement character parsers (`any_char`, `char`, `char_if`, etc.)
- [ ] Implement text parsers (`text`, `text_of`, `word`)
- [ ] Implement whitespace parsers

### Phase 2: Sequence and Choice Combinators
- [ ] Implement `chain`, `zero_or_one`, `zero_or_more`, `one_or_more`
- [ ] Implement `exactly`, `at_least`, `at_most`, `between`
- [ ] Implement `one_of`, `commit_one_of`, `choose`

### Phase 3: Padding and Delimiters
- [ ] Implement `padded_l`, `padded_r`, `padded`
- [ ] Implement `inbetween`, `delimited_by`, `separated_by`

### Phase 4: Lookahead and Error Handling
- [ ] Implement `lookahead`, `lookahead_not`, `assert`, `not`
- [ ] Implement `expect`, `commit`, `uncommit`, `recover`
- [ ] Implement `skip`, `skip_then`, `then_skip`

### Phase 5: Expression Parsers (Pratt Parsing)
- [ ] Define `ExprParser(a)` type
- [ ] Implement `atom`, `group`, `prefix`, `suffix`
- [ ] Implement `infix_l`, `infix_r`
- [ ] Implement `precedence`

### Phase 6: Integration with Core Language
- [ ] Update core language grammar to use the generic library
- [ ] Define core language operators using the generic combinators
- [ ] Test with core language examples

### Phase 7: High-Level Language Integration
- [ ] Define high-level language grammar using the generic library
- [ ] Test with high-level language examples

## Design Decisions

### Parser Type Design

The parser type uses a state-passing style similar to the Haskell reference:

```gleam
pub type Parser(a) {
  Parser(fn(State) -> Result(#(a, State), State))
}
```

This allows:
- State threading (remaining input, position, etc.)
- Error recovery (failed state is returned for recovery)
- Type safety (result type is tracked)

### Error Recovery

The library supports error recovery through:
- `expect`: Set expected message on failure
- `commit`: Commit to a parse (don't backtrack)
- `uncommit`: Uncommit from a parse (allow backtracking)
- `recover`: Recover from errors with a recovery parser

### Expression Parsing

The library uses Pratt parsing (operator precedence parsing) for expressions:
- Atoms: Base expressions (identifiers, literals, etc.)
- Prefix operators: Unary operators with precedence
- Infix operators: Binary operators with precedence and associativity
- `precedence`: Build expression parser from operators

This is more flexible than traditional recursive descent and easier to extend with new operators.

## Formatter Library

The formatter library provides **grammar-aware pretty printing** using layout algebra. It converts parse trees or ASTs back into formatted source code.

### Design Goals

1. **Grammar-Aware**: Formatting rules derived from grammar structure
2. **Precedence-Aware**: Parentheses added only when needed for expressions
3. **Configurable Layout**: Line width, indentation, line break preferences
4. **Idempotent**: `format(format(x)) == format(x)`
5. **Preserves Comments**: Comments attached to AST nodes survive formatting

### Core Types

```gleam
/// Layout document - can be rendered at different widths
pub type Doc {
  /// Empty document
  Empty
  /// Text segment (cannot be broken)
  Text(String)
  /// Line break (becomes space or newline depending on layout)
  Line
  /// Forced line break (always newline)
  HardLine
  /// Nested/indented document
  Nest(Int, Doc)
  /// Choice between compact and expanded layout
  FlatAlt(Doc, Doc)
  /// Group: try flat first, expand if doesn't fit
  Group(Doc)
  /// Concatenate documents
  Concat(Doc, Doc)
}

/// Formatting context
pub type FormatContext {
  FormatContext(
    /// Current line width limit
    width: Int,
    /// Current indentation string
    indent: String,
    /// Current column position
    col: Int,
    /// Whether we're in "flat" mode (trying to fit on one line)
    is_flat: Bool,
  )
}

/// Formatter function type
pub type Formatter(a) {
  Formatter(fn(a, FormatContext) -> Doc)
}
```

### Layout Algebra (Wadler's "A Prettier Printer")

Based on [A Prettier Printer](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf):

```gleam
/// Empty document
pub fn empty() -> Doc

/// Text (cannot be broken)
pub fn text(str: String) -> Doc

/// Line break (space or newline)
pub fn line() -> Doc

/// Hard line break (always newline)
pub fn hardline() -> Doc

/// Concatenate documents
pub fn concat(doc1: Doc, doc2: Doc) -> Doc

/// Concatenate list of documents
pub fn concat_all(docs: List(Doc)) -> Doc

/// Join documents with separator
pub fn join(sep: Doc, docs: List(Doc)) -> Doc

/// Nest document by indentation
pub fn nest(indent: Int, doc: Doc) -> Doc

/// Group: try flat, expand if needed
pub fn group(doc: Doc) -> Doc

/// Flat alternative: use first if fits, otherwise second
pub fn flat_alt(flat: Doc, expanded: Doc) -> Doc

/// Render document to string
pub fn render(doc: Doc, width: Int, indent: String) -> String
```

### Key Formatting Combinators

```gleam
/// Format with parentheses if needed
pub fn parens_if(cond: Bool, doc: Doc) -> Doc

/// Format optional semicolon
pub fn opt_semi(cond: Bool) -> Doc

/// Format block with braces
pub fn braces(doc: Doc) -> Doc

/// Format block with parens
pub fn parens(doc: Doc) -> Doc

/// Format block with brackets
pub fn brackets(doc: Doc) -> Doc

/// Format comma-separated list
pub fn comma_sep(docs: List(Doc)) -> Doc

/// Format space-separated list
pub fn space_sep(docs: List(Doc)) -> Doc

/// Format list with soft line breaks
pub fn soft_sep(docs: List(Doc)) -> Doc

/// Format indented block
pub fn indented(doc: Doc) -> Doc

/// Format hanging indent (first line flush, rest indented)
pub fn hanging_indent(indent: Int, doc: Doc) -> Doc
```

### Precedence-Aware Expression Formatting

```gleam
/// Format expression with precedence-aware parentheses
pub fn format_expr(
  expr: Expr,
  parent_prec: Int,
  assoc: Assoc,
  ctx: FormatContext,
) -> Doc

/// Get precedence of an operator
pub fn get_prec(op: Operator) -> Int

/// Get associativity of an operator
pub fn get_assoc(op: Operator) -> Assoc

/// Associativity
pub type Assoc {
  Left
  Right
  NonAssoc
}
```

### Grammar-Aware Formatting

The formatter derives formatting rules from grammar structure:

```gleam
/// Convert grammar to formatter
pub fn grammar_to_formatter(grammar: Grammar) -> Formatter(ParseTree)

/// Format a parse tree node
pub fn format_node(
  node: ParseTree,
  grammar: Grammar,
  ctx: FormatContext,
) -> Doc

/// Get formatting rules for a grammar rule
pub fn get_format_rules(
  rule_name: String,
  grammar: Grammar,
) -> FormatRules
```

### Example Usage

```gleam
import formatter.{type Doc, text, line, group, nest, concat}

// Simple expression formatting
let format_expr = fn(expr, ctx) {
  case expr {
    BinOp(op, left, right) -> {
      let op_doc = text(op)
      let left_doc = format_expr(left, ctx)
      let right_doc = format_expr(right, ctx)
      
      group(
        concat(
          left_doc,
          concat(
            concat(text(" "), op_doc),
            concat(line(), right_doc)
          )
        )
      )
    }
    Lit(n) -> text(int.to_string(n))
  }
}

// Render with 80 character width
let doc = format_expr(my_expr, default_context())
let output = formatter.render(doc, 80, "  ")
```

### Rendering Algorithm

```gleam
/// Best-fit rendering
fn best_fit(width: Int, doc: Doc) -> String {
  // Try to render in flat mode first
  // If it exceeds width, expand groups
  // Use greedy algorithm for line breaks
}
```

---

## Grammar DSL

The grammar DSL is the **single source of truth** for language syntax. Define a grammar once, and the system generates both a parser and a formatter.

### Design Goals

1. **Declarative**: Describe what the language looks like, not how to parse it
2. **Composable**: Build complex grammars from simple rules
3. **Type-Safe**: Grammar errors caught at compile time where possible
4. **Automatic Generation**: Parser and formatter derived automatically
5. **Extensible**: Allow custom actions for semantic analysis
6. **Error Recovery**: Grammar includes recovery information

### Core Types

```gleam
/// A complete grammar
pub type Grammar {
  Grammar(
    /// Name of the grammar
    name: String,
    /// Start rule
    start: String,
    /// All grammar rules
    rules: List(Rule),
    /// Token definitions
    tokens: List(TokenDef),
    /// Precedence levels for expressions
    precedence: List(PrecedenceLevel),
  )
}

/// A grammar rule
pub type Rule {
  Rule(
    /// Rule name (non-terminal)
    name: String,
    /// Rule definition
    definition: Symbol,
    /// Documentation
    doc: String,
  )
}

/// A symbol in a grammar (terminal or non-terminal)
pub type Symbol {
  /// Terminal: match literal string
  Token(value: String)
  /// Terminal: match token class
  TokenClass(String)
  /// Non-terminal: reference another rule
  Ref(name: String)
  /// Sequence of symbols
  Seq(List(Symbol))
  /// Choice between alternatives
  Choice(List(Symbol))
  /// Optional symbol (0 or 1)
  Opt(Symbol)
  /// Zero or more repetitions
  Rep(Symbol)
  /// One or more repetitions
  Rep1(Symbol)
  /// Separated list
  Sep(Symbol, Symbol)  // item, separator
  /// Grouped symbol (for precedence)
  Group(Symbol)
  /// Labeled symbol (for semantic actions)
  Label(String, Symbol)
  /// Precedence-climbing expression
  Expr(ExprGrammar)
}

/// Token definition
pub type TokenDef {
  TokenDef(
    name: String,
    pattern: String,  // Regex pattern
    priority: Int,    // For disambiguation
  )
}

/// Expression grammar for Pratt parsing
pub type ExprGrammar {
  ExprGrammar(
    atoms: List(AtomDef),
    prefix_ops: List(PrefixOp),
    postfix_ops: List(PostfixOp),
    infix_ops: List(InfixOp),
  )
}

pub type AtomDef {
  AtomDef(name: String, parser: String)
}

pub type PrefixOp {
  PrefixOp(
    op: String,
    precedence: Int,
    assoc: Assoc,
  )
}

pub type PostfixOp {
  PostfixOp(
    op: String,
    precedence: Int,
  )
}

pub type InfixOp {
  InfixOp(
    op: String,
    precedence: Int,
    assoc: Assoc,
  )
}

pub type Assoc {
  Left
  Right
  NonAssoc
}

/// Precedence level
pub type PrecedenceLevel {
  PrecedenceLevel(
    name: String,
    level: Int,
    ops: List(String),
  )
}
```

### Grammar DSL API

```gleam
// ============================================================================
// GRAMMAR CONSTRUCTION
// ============================================================================

/// Create a new grammar
pub fn grammar(name: String, start: String, rules: List(Rule)) -> Grammar

/// Add token definitions to grammar
pub fn with_tokens(grammar: Grammar, tokens: List(TokenDef)) -> Grammar

/// Add precedence levels to grammar
pub fn with_precedence(grammar: Grammar, levels: List(PrecedenceLevel)) -> Grammar

// ============================================================================
// RULE DEFINITION
// ============================================================================

/// Define a grammar rule
pub fn rule(name: String, definition: Symbol) -> Rule

/// Define a rule with documentation
pub fn rule_doc(name: String, doc: String, definition: Symbol) -> Rule

// ============================================================================
// SYMBOL COMBINATORS
// ============================================================================

/// Match a literal token
pub fn token(value: String) -> Symbol

/// Match a token class (e.g., "Ident", "Number")
pub fn token_class(name: String) -> Symbol

/// Reference another rule
pub fn ref(name: String) -> Symbol

/// Sequence of symbols
pub fn seq(symbols: List(Symbol)) -> Symbol

/// Convenience: sequence of 2 symbols
pub fn seq2(s1: Symbol, s2: Symbol) -> Symbol

/// Convenience: sequence of 3 symbols
pub fn seq3(s1: Symbol, s2: Symbol, s3: Symbol) -> Symbol

/// Choice between alternatives
pub fn choice(alternatives: List(Symbol)) -> Symbol

/// Optional symbol
pub fn opt(symbol: Symbol) -> Symbol

/// Zero or more repetitions
pub fn rep(symbol: Symbol) -> Symbol

/// One or more repetitions
pub fn rep1(symbol: Symbol) -> Symbol

/// Separated list (item, separator)
pub fn sep(item: Symbol, separator: Symbol) -> Symbol

/// Convenience: comma-separated list
pub fn comma_sep(item: Symbol) -> Symbol

/// Convenience: semicolon-separated list
pub fn semicolon_sep(item: Symbol) -> Symbol

/// Grouped symbol
pub fn group(symbol: Symbol) -> Symbol

/// Labeled symbol
pub fn label(name: String, symbol: Symbol) -> Symbol

// ============================================================================
// EXPRESSION GRAMMAR
// ============================================================================

/// Define expression grammar
pub fn expr_grammar(
  atoms: List(AtomDef),
  prefix_ops: List(PrefixOp),
  postfix_ops: List(PostfixOp),
  infix_ops: List(InfixOp),
) -> ExprGrammar

/// Define an atom
pub fn atom(name: String) -> AtomDef

/// Define a prefix operator
pub fn prefix_op(op: String, prec: Int) -> PrefixOp

/// Define a postfix operator
pub fn postfix_op(op: String, prec: Int) -> PostfixOp

/// Define a left-associative infix operator
pub fn infix_l(op: String, prec: Int) -> InfixOp

/// Define a right-associative infix operator
pub fn infix_r(op: String, prec: Int) -> InfixOp

// ============================================================================
// TOKEN DEFINITIONS
// ============================================================================

/// Define a token
pub fn token_def(name: String, pattern: String) -> TokenDef

/// Define a token with priority
pub fn token_def_priority(name: String, pattern: String, priority: Int) -> TokenDef

/// Common token: identifier
pub fn tok_ident() -> TokenDef

/// Common token: integer
pub fn tok_integer() -> TokenDef

/// Common token: float
pub fn tok_float() -> TokenDef

/// Common token: string
pub fn tok_string() -> TokenDef

/// Common token: comment (single line)
pub fn tok_comment_single() -> TokenDef

/// Common token: comment (multi-line)
pub fn tok_comment_multi() -> TokenDef

/// Common token: whitespace
pub fn tok_whitespace() -> TokenDef
```

### Example Grammar

```gleam
import grammar

pub fn expression_grammar() -> Grammar {
  grammar.grammar("Expression", "Expr", [
    // Let binding
    grammar.rule("Expr", grammar.choice([
      grammar.seq([
        grammar.token("let"),
        grammar.token_class("Ident"),
        grammar.token("="),
        grammar.ref("Expr"),
      ]),
      grammar.expr(grammar.expr_grammar(
        atoms: [grammar.atom("Term")],
        prefix_ops: [
          grammar.prefix_op("-", 100),
          grammar.prefix_op("not", 90),
        ],
        postfix_ops: [],
        infix_ops: [
          // Low precedence
          grammar.infix_l("=", 10),
          grammar.infix_l("and", 20),
          grammar.infix_l("or", 20),
          // Medium precedence
          grammar.infix_l("<", 30),
          grammar.infix_l(">", 30),
          grammar.infix_l("<=", 30),
          grammar.infix_l(">=", 30),
          grammar.infix_l("==", 30),
          grammar.infix_l("!=", 30),
          // High precedence
          grammar.infix_l("+", 40),
          grammar.infix_l("-", 40),
          grammar.infix_l("*", 50),
          grammar.infix_l("/", 50),
          grammar.infix_l("%", 50),
          // Highest precedence
          grammar.infix_r("^", 60),
        ],
      )),
    ])),

    grammar.rule("Term", grammar.choice([
      grammar.token_class("Ident"),
      grammar.token_class("Integer"),
      grammar.token_class("Float"),
      grammar.seq([
        grammar.token("("),
        grammar.ref("Expr"),
        grammar.token(")"),
      ]),
    ])),
  ])
  |> grammar.with_tokens([
    grammar.tok_ident(),
    grammar.tok_integer(),
    grammar.tok_float(),
    grammar.tok_whitespace(),
    grammar.tok_comment_single(),
  ])
}
```

### Grammar to Parser Generation

```gleam
/// Convert grammar to parser function
pub fn to_parser(grammar: Grammar) -> fn(String) -> ParseResult(ParseTree)

/// Convert grammar to parser with custom error recovery
pub fn to_parser_with_recovery(
  grammar: Grammar,
  recovery: RecoveryStrategy,
) -> fn(String) -> ParseResult(ParseTree)

/// Internal: compile grammar rule to parser
fn compile_rule(rule: Rule, grammar: Grammar) -> Parser(ParseTree)

/// Internal: compile symbol to parser
fn compile_symbol(symbol: Symbol, grammar: Grammar) -> Parser(ParseTree)

/// Internal: compile expression grammar to Pratt parser
fn compile_expr_grammar(expr: ExprGrammar) -> Parser(ParseTree)
```

#### Compilation Strategy

1. **Tokenize**: Generate lexer from `TokenDef` list
2. **Compile Rules**: Each `Rule` becomes a `Parser(ParseTree)`
   - `Token(value)` → `parser.token(value)`
   - `TokenClass(name)` → `parser.named(name)`
   - `Ref(name)` → lookup and call rule parser
   - `Seq(symbols)` → `parser.chain([compiled_symbols])`
   - `Choice(alts)` → `parser.one_of([compiled_alts])`
   - `Opt(sym)` → `parser.zero_or_one(compiled_sym)`
   - `Rep(sym)` → `parser.zero_or_more(compiled_sym)`
   - `Rep1(sym)` → `parser.one_or_more(compiled_sym)`
   - `Sep(item, sep)` → custom separated parser
   - `Expr(expr_grammar)` → Pratt parser from operators
3. **Wire Up**: Connect start rule to complete parser

### Grammar to Formatter Generation

```gleam
/// Convert grammar to formatter function
pub fn to_formatter(grammar: Grammar) -> fn(ParseTree) -> String

/// Convert grammar to formatter with custom options
pub fn to_formatter_with_options(
  grammar: Grammar,
  options: FormatOptions,
) -> fn(ParseTree) -> String

/// Internal: get formatter for a rule
fn get_rule_formatter(rule: Rule, grammar: Grammar) -> Formatter(ParseTree)

/// Internal: get formatter for a symbol
fn get_symbol_formatter(symbol: Symbol) -> Formatter(ParseTree)
```

#### Formatting Rules Derivation

The formatter derives layout from grammar structure:

| Grammar Pattern | Formatting Rule |
|-----------------|-----------------|
| `Seq([Token(_), ...])` | Inline with spaces |
| `Seq([Token("{"), Rep(rule), Token("}")])` | Block with indentation |
| `Sep(item, Token(","))` | Comma-separated, soft breaks |
| `Choice([...])` | Format based on which alternative matched |
| `Expr(...)` | Precedence-aware with minimal parens |
| `Opt(sym)` | Format if present, empty if not |
| `Rep(sym)` | One item per line if many, else inline |

### Parse Tree Type

```gleam
/// Result of parsing
pub type ParseTree {
  /// Token leaf with value
  TreeToken(value: String, location: Location)
  /// Named node with children
  TreeNode(name: String, children: List(ParseTree), location: Location)
  /// Error node (for error recovery)
  TreeError(errors: List(ParseError), children: List(ParseTree))
}
```

### Complete Usage Example

```gleam
import grammar
import io

pub fn main() {
  // Define grammar
  let g = expression_grammar()

  // Generate parser and formatter
  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  // Parse source code
  let source = "let x = 42 + y * 2"
  let result = parse(source)

  // Handle errors
  case result {
    ParseResult(ast, []) -> {
      // No errors - format the AST
      let formatted = format(ast)
      io.println(formatted)
    }
    ParseResult(ast, errors) -> {
      // Errors but got partial AST
      io.println("Parse errors:")
      list.each(errors, fn(e) {
        io.println(grammar.format_error(e, source))
      })
      
      // Still try to format what we got
      io.println("Formatted (partial):")
      io.println(format(ast))
    }
  }
}
```

---

## Updated Implementation Phases

### Phase 1-5: Parser Library ✅ COMPLETE

### Phase 6: Formatter Library
- [ ] Define `Doc`, `FormatContext`, `Formatter(a)` types
- [ ] Implement layout algebra: `empty`, `text`, `line`, `concat`, `nest`, `group`
- [ ] Implement rendering: `render`, `best_fit`
- [ ] Implement formatting combinators: `parens_if`, `braces`, `comma_sep`
- [ ] Implement precedence-aware expression formatting
- [ ] Add grammar-aware formatting hooks

### Phase 7: Grammar DSL
- [ ] Define `Grammar`, `Rule`, `Symbol` types
- [ ] Define `ExprGrammar`, `TokenDef`, `PrecedenceLevel` types
- [ ] Implement grammar DSL API: `grammar`, `rule`, `token`, `ref`, `seq`, `choice`
- [ ] Implement expression grammar: `expr_grammar`, `infix_l`, `prefix_op`
- [ ] Implement token definitions: `token_def`, `tok_ident`, `tok_integer`

### Phase 8: Grammar to Parser Generation
- [ ] Implement `to_parser`: grammar → parser function
- [ ] Implement rule compilation: `compile_rule`
- [ ] Implement symbol compilation: `compile_symbol`
- [ ] Implement expression grammar compilation: `compile_expr_grammar`
- [ ] Add error recovery integration

### Phase 9: Grammar to Formatter Generation
- [ ] Implement `to_formatter`: grammar → formatter function
- [ ] Implement rule formatter derivation: `get_rule_formatter`
- [ ] Implement symbol formatter derivation: `get_symbol_formatter`
- [ ] Add formatting rule derivation from grammar patterns
- [ ] Integrate with layout algebra

### Phase 10: Integration and Testing
- [ ] Create example grammar (simple expression language)
- [ ] Test parser generation
- [ ] Test formatter generation
- [ ] Verify idempotence: `format(parse(format(parse(x)))) == format(parse(x))`
- [ ] Add comprehensive tests for all modules
- [ ] Integrate with core language

---

## Design Decisions

### Why Grammar DSL Instead of Direct Parser Combinators?

**Direct Combinators** (like the current `parser.gleam`):
- ✅ Maximum flexibility
- ✅ Full control over parsing strategy
- ❌ Verbose for simple grammars
- ❌ Parser and formatter can drift apart
- ❌ Hard to visualize grammar

**Grammar DSL**:
- ✅ Single source of truth
- ✅ Declarative and readable
- ✅ Automatic parser + formatter generation
- ✅ Easy to visualize and document
- ❌ Less control over low-level details
- ❌ May need escape hatches for complex cases

**Solution**: Provide both! Use Grammar DSL for standard cases, drop to direct combinators when needed.

### Why Layout Algebra for Formatting?

Based on Wadler's "A Prettier Printer":
- ✅ Composable like parser combinators
- ✅ Automatic line breaking based on width
- ✅ Consistent formatting decisions
- ✅ Separation of *what* from *how*

### Why ParseTree Instead of Direct AST?

- ✅ Grammar is generic - doesn't know target AST types
- ✅ ParseTree preserves all syntactic information
- ✅ Can transform ParseTree → AST in separate phase
- ✅ Easier error recovery (TreeError nodes)
- ❌ Extra transformation step needed

**Alternative**: Allow semantic actions in grammar to build custom AST directly.

### Error Recovery in Grammar DSL

The grammar DSL includes recovery information:
- Sync points derived from rule structure
- Expected tokens from grammar
- Recovery strategies per rule type

```gleam
/// Recovery strategy
pub type RecoveryStrategy {
  /// Panic mode: skip to sync point
  PanicMode(sync_points: List(String))
  /// Phrase level: insert/delete tokens
  PhraseLevel(insert: List(String), delete: Int)
  /// Custom recovery function
  Custom(fn(ParseError) -> ParseResult(ParseTree))
}
```

---

## Next Steps

1. ✅ Parser library complete - move to formatter
2. Implement Phase 6: Formatter Library (layout algebra)
3. Implement Phase 7: Grammar DSL (types and combinators)
4. Implement Phase 8: Grammar → Parser generation
5. Implement Phase 9: Grammar → Formatter generation
6. Test with example grammars
7. Integrate with core language
8. Document usage patterns and best practices
