# Tao Syntax Test Plan

> **Goal**: Comprehensive syntax tests covering success cases, error reporting, and error recovery
> **Status**: 📋 Planning
> **Date**: March 15, 2026

---

## Test Categories

### 1. Success Cases (Parse Correctly)

#### 1.1 Basic Expressions
- [x] Number literals (integers)
- [x] Variable references
- [x] Binary operators (+, -, *, /)
- [x] Unary operators (-, !)
- [x] Parenthesized expressions
- [ ] Boolean literals (true, false)
- [ ] String literals (TODO: not yet implemented)

#### 1.2 Operator Precedence
- [x] Multiplication binds tighter than addition
- [x] Parentheses override precedence
- [ ] Comparison operators (<, >, <=, >=, ==, !=)
- [ ] Logical operators (&&, ||)
- [ ] Mixed precedence chains

#### 1.3 Let Bindings
- [x] Simple let: `let x = 10`
- [ ] Let with mut: `let mut x = 10`
- [ ] Let with type: `let x: Int = 10`
- [ ] Let with mut and type: `let mut x: Int = 10`
- [ ] Multiple lets: `let x = 10; let y = 20; x + y`

#### 1.4 Function Definitions
- [ ] Simple function: `fn add(x, y) { x + y }`
- [ ] Function with type params: `fn id<a>(x: a) -> a { x }`
- [ ] Overloaded operator: `fn (+)(x: I32) -> I32 { ... }`

#### 1.5 Control Flow
- [ ] If expression: `if x > 0 { x } else { -x }`
- [ ] Match expression: `match x { | 0 -> 1 | _ -> x }`
- [ ] While loop: `while x > 0 { x = x - 1 }`
- [ ] For loop: `for i in list { i }`
- [ ] Loop with break: `loop { if cond { break } }`

#### 1.6 Import Statements
- [ ] Simple import: `import math`
- [ ] Import with alias: `import math as m`
- [ ] Selective import: `import math { sin, cos }`
- [ ] Wildcard import: `import math as *`

---

### 2. Syntax Error Reporting (Correct Spans)

#### 2.1 Missing Tokens
- [ ] Missing closing paren: `(1 + 2` → Error at EOF, expected `)`
- [ ] Missing closing brace: `{ x + 1` → Error at EOF, expected `}`
- [ ] Missing operator: `1 2` → Error at `2`, expected operator
- [ ] Missing equals in let: `let x 10` → Error at `10`, expected `=`
- [ ] Missing colon in type: `let x Int = 10` → Error at `Int`, expected `:`

#### 2.2 Invalid Tokens
- [ ] Invalid number: `123abc` → Error at `abc`, expected number end
- [ ] Invalid identifier: `123var` → Error at start, expected identifier
- [ ] Unknown operator: `1 @ 2` → Error at `@`, expected known operator
- [ ] Unclosed string: `"hello` → Error at EOF, expected `"`

#### 2.3 Span Accuracy
- [ ] Error span starts at error location
- [ ] Error span ends at error location (or token end)
- [ ] Error context includes surrounding tokens
- [ ] Multi-line errors have correct line/column

---

### 3. Error Recovery (Continue Parsing After Errors)

#### 3.1 Statement-Level Recovery
- [ ] Skip to next `;` after error in statement
- [ ] Skip to next `}` after error in block
- [ ] Skip to next statement after malformed let
- [ ] Skip to next statement after malformed fn

#### 3.2 Expression-Level Recovery
- [ ] Skip to next `)` in parenthesized expression
- [ ] Skip to next `,` in argument list
- [ ] Skip to next operator in expression chain
- [ ] Use error placeholder for missing subexpression

#### 3.3 Pattern Matching Recovery
- [ ] Skip to next `|` after malformed pattern
- [ ] Skip to next `->` after malformed guard
- [ ] Skip to next `}` after malformed match arm
- [ ] Continue with remaining arms after error

#### 3.4 Import Recovery
- [ ] Skip malformed import path
- [ ] Continue after missing `as` keyword
- [ ] Skip invalid import name in list
- [ ] Continue after missing `}` in selective import

---

### 4. Edge Cases

#### 4.1 Empty/Input Boundaries
- [ ] Empty source: `` → Error or empty AST
- [ ] Whitespace only: `   \n  ` → Error or empty AST
- [ ] Single token: `42` → Success
- [ ] Single keyword: `let` → Error with helpful message

#### 4.2 Deep Nesting
- [ ] Deeply nested parens: `(((1)))` → Success
- [ ] Deeply nested lets: `let x = let y = let z = 1 in ...` → Success
- [ ] Deeply nested calls: `f(g(h(i(x))))` → Success

#### 4.3 Unicode/Special Characters
- [ ] Unicode in identifiers: `let 变量 = 10` → Success (if supported)
- [ ] Unicode in strings: `"你好"` → Success (if supported)
- [ ] Emoji in comments: `// 😀` → Success (if comments supported)

---

### 5. CLI Integration Tests

#### 5.1 Error Output Format
- [ ] Parse errors shown with source snippet
- [ ] Error message is clear and actionable
- [ ] Caret points to correct location
- [ ] Multiple errors shown (not just first)

#### 5.2 Exit Codes
- [ ] Success → exit code 0
- [ ] Parse errors → exit code non-zero
- [ ] Type errors → exit code non-zero
- [ ] Mixed errors → exit code non-zero

---

## Implementation Priority

### Phase 1: Core Success Cases (Immediate)
1. Basic expressions (numbers, vars, operators)
2. Operator precedence
3. Let bindings (simple)
4. Round-trip tests

### Phase 2: Error Reporting (Short-term)
1. Missing token errors
2. Invalid token errors
3. Span accuracy tests
4. CLI error format verification

### Phase 3: Error Recovery (Medium-term)
1. Statement-level recovery
2. Expression-level recovery
3. Pattern matching recovery
4. Import recovery

### Phase 4: Edge Cases & Integration (Long-term)
1. Empty/input boundary cases
2. Deep nesting
3. Unicode handling
4. CLI exit codes

---

## Test Structure

```gleam
// Success cases
pub fn parse_let_simple_test() {
  let ParseResult(ast, errors) = parse("let x = 10")
  errors |> should.equal([])
  case ast {
    Let("x", False, None, Int(10, _), _) -> Nil
    _ -> panic as "Expected Let"
  }
}

// Error cases
pub fn parse_let_missing_equals_test() {
  let ParseResult(_ast, errors) = parse("let x 10")
  errors |> should.not.equal([])
  // Verify error mentions "expected '='"
  case list.first(errors) {
    Some(ParseError(expected: exp, ..)) -> 
      string.contains(exp, "=") |> should.be_true
    None -> panic as "Expected error"
  }
}

// Recovery cases
pub fn parse_let_recovery_test() {
  let ParseResult(ast, errors) = parse("let x = ; let y = 20; y")
  // Should recover and parse second let
  errors |> should.not.equal([])  // Has error for missing value
  // ast should contain second let binding
  // TODO: Verify structure
}
```

---

## Notes

1. **Error Recovery Strategy**: The grammar library uses `alt()` for recovery - if one alternative fails, try the next. We can add error recovery by:
   - Adding "sync" patterns that skip to known tokens
   - Using `opt()` for optional parts
   - Providing sensible defaults in constructors

2. **Span Accuracy**: The grammar library automatically tracks spans through `span_from_values()` and `span_from_token()`. Tests should verify these are correct.

3. **CLI Integration**: The CLI uses `error_reporter.format_diagnostic()` which shows source snippets. Tests should verify the format is user-friendly.

4. **Incremental Approach**: Start with simple, obvious cases. As we encounter real-world parsing issues, add specific tests and refine the grammar.
