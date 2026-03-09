# Core Language Implementation - Issues & Considerations

## Current State

The generic grammar system is implemented and working for the calculator example:
- ✅ 229 tests passing
- ✅ Left-associative operators work correctly
- ✅ Operator precedence works correctly
- ✅ Parser generated from grammar
- ⚠️ Formatter is AST-specific (uses grammar precedence but pattern-matches on AST)

## Issues for Core Language Implementation

### 1. Formatter Cannot Be Fully Generic

**Problem**: The formatter needs to pattern-match on concrete AST types to extract children for formatting.

**Current Approach**: 
```gleam
// In calc/syntax.gleam
pub fn format(ast: Expr) -> String {
  format_expr(ast, 0)  // AST-specific
}

fn format_expr(expr: Expr, parent_prec: Int) -> String {
  case expr {
    Int(n) -> int.to_string(n)
    Add(l, r) => { ... }  // Pattern match on concrete type
    Mul(l, r) => { ... }
  }
}
```

**Why This Is Necessary**:
- Grammar knows structure (`seq([ref("Term"), keyword("+"), ref("Expr")])`)
- But formatter needs to extract `l` and `r` from `Add(l, r)`
- Can't generically extract children from unknown AST type `a`

**Potential Solutions**:

#### A. Store Child Extractors in Grammar (Complex)
```gleam
pub type Rule(a) {
  Rule(
    // ... other fields
    child_extractors: List(fn(a) -> Option(a)),  // Extract each child
  )
}
```
**Pros**: Truly generic formatter
**Cons**: Massive boilerplate, type erasure issues

#### B. Format Templates with Placeholders (Moderate)
```gleam
pub type FormatTemplate {
  TemplateWithExtractors(
    template: String,  // "{0} + {1}"
    extractors: List(fn(a) -> a),  // How to get each child
  )
}
```
**Pros**: Less boilerplate than A
**Cons**: Still need extractors, limited flexibility

#### C. Keep AST-Specific Formatters (Current) ✅ RECOMMENDED
```gleam
// Grammar provides precedence
pub fn calc_grammar() -> Grammar(Expr) { ... }

// AST provides formatting
pub fn format(ast: Expr) -> String { format_expr(ast, 0) }
```
**Pros**: Simple, type-safe, flexible
**Cons**: Duplication of precedence values

**Recommendation**: Use approach C. The duplication is minimal (just precedence integers) and the type safety is worth it.

---

### 2. Complex Core AST Types

**Problem**: Core language has many more constructs than calculator:
- Lambda: `Lam(name, body)`
- Pi types: `Pi(name, in, out)`
- Match: `Match(arg, motive, cases)`
- Records: `Rcd(fields)`
- Constructors: `Ctr(tag, arg)`
- etc.

**Considerations**:

#### Lambda Formatting
```gleam
fn(x) { x + 1 }  // Simple
fn(x: Int) -> Int { x + 1 }  // With type annotations
```
Need to handle optional type annotations.

#### Match Formatting
```gleam
match x {
  0 -> "zero"
  n if n > 0 -> "positive"
  _ -> "negative"
}
```
Need to handle:
- Multiple cases
- Guards (`if` conditions)
- Pattern formatting

#### Record Formatting
```gleam
{x: 1, y: 2}  // Inline
{
  x: 1,
  y: 2,
}  // Multiline
```
Need to decide when to use multiline vs inline.

**Recommendation**: Start with minimal formatting (no pretty-printing), add complexity later.

---

### 3. Grammar Size and Complexity

**Problem**: Core language grammar will be much larger than calculator.

**Calculator**: ~70 lines
**Core Language**: Estimated ~500+ lines

**Considerations**:
- Split grammar into multiple functions?
- Use helper functions for common patterns?
- Document each rule clearly?

**Recommendation**: 
```gleam
pub fn core_grammar() -> Grammar(Term) {
  grammar.new()
  |> grammar.start("Expr")
  |> with_type_rules(_)
  |> with_term_rules(_)
  |> with_pattern_rules(_)
  |> with_case_rules(_)
}

fn with_type_rules(g: Grammar(Term)) -> Grammar(Term) { ... }
fn with_term_rules(g: Grammar(Term)) -> Grammar(Term) { ... }
```

---

### 4. Error Messages and Recovery

**Problem**: Current parser panics on errors.

**Current**:
```gleam
Error(_) -> parser.ParseResult(ast: panic as "Parse failed", errors: [])
```

**Needed for Core Language**:
- Meaningful error messages
- Error recovery (continue parsing after error)
- Source locations

**Recommendation**: Implement error recovery in a follow-up iteration. Start with panics for development.

---

### 5. Performance Considerations

**Problem**: Recursive descent with many `parse_symbol` calls.

**Current Performance**:
- Calculator: Fast enough for testing
- Core Language: Unknown

**Potential Issues**:
- Deep recursion for nested expressions
- Many string comparisons for keywords
- List operations in `parse_many`, `parse_sep`

**Recommendations**:
1. Profile before optimizing
2. Consider iterative approaches for common patterns
3. Use more efficient data structures if needed

---

### 6. Token Kind Proliferation

**Problem**: Calculator uses 4 token kinds. Core language needs many more.

**Calculator Tokens**:
- `Number`, `Operator`, `LParen`, `RParen`

**Core Language Tokens** (estimated):
- `Ident`, `Int`, `Float`, `String`
- `LParen`, `RParen`, `LBrace`, `RBrace`, `LBracket`, `RBracket`
- `Comma`, `Colon`, `Arrow`, `Pipe`, `Dot`
- `Eq`, `EqEq`, `NotEq`, `Lt`, `LtEq`, `Gt`, `GtEq`
- `Plus`, `Minus`, `Star`, `Slash`, `Percent`
- Keywords: `fn`, `let`, `rec`, `match`, `if`, `else`, `return`, etc.

**Considerations**:
- Lexer needs to support all these
- Grammar rules reference token kinds by string
- Typos in token kind strings cause runtime errors

**Recommendation**: 
- Define token kind constants
- Consider type-safe token kinds (enum instead of String)

---

### 7. Testing Strategy

**Current**: Calculator has 229 tests covering:
- Parsing
- Precedence
- Associativity
- Evaluation
- Formatting
- Round-trips

**Core Language Needs**:
- Similar coverage for each construct
- Integration tests (parse → typecheck → eval)
- Error case tests
- Performance benchmarks

**Recommendation**: 
- Start with parsing tests for each construct
- Add evaluation tests incrementally
- Use property-based testing for round-trips

---

## Implementation Priority

1. **Define Core AST Types** - `Term`, `Pattern`, `Case`, etc.
2. **Define Core Grammar** - Start with simple constructs, add complexity
3. **Implement Parser** - Use existing generic grammar system
4. **Implement Formatter** - AST-specific, use grammar precedence
5. **Add Tests** - Incremental, start with parsing
6. **Error Handling** - Follow-up iteration
7. **Performance** - Profile and optimize if needed

---

## Open Questions

1. **Should grammar generate formatter skeletons?**
   - Could generate case expressions with precedence
   - Still need AST-specific child extraction

2. **How to handle optional components?**
   - Type annotations in lambdas
   - Guards in match cases
   - Default values in records

3. **Pretty-printing vs minimal formatting?**
   - Start minimal, add pretty-printing later

4. **How to handle source locations?**
   - Current grammar doesn't track spans
   - Need for error messages
   - Need for IDE support

---

## Conclusion

The generic grammar system works well for the calculator example. For the core language:

- **Parser**: Can be fully generated from grammar ✅
- **Formatter**: Will be AST-specific, using grammar precedence ⚠️
- **Complexity**: Manage with modular grammar definition
- **Testing**: Incremental approach, start with parsing

The key insight: **Formatting is inherently AST-specific** because it needs to pattern-match on concrete types to extract children. The grammar can provide structure and precedence, but the actual formatting logic must know the AST type.

This is acceptable because:
1. Parser is the complex part (precedence, associativity, error handling)
2. Formatter is straightforward (pattern match, add parens based on precedence)
3. Precedence values are simple integers (minimal duplication)
4. Type safety is maintained (no dynamic type erasure)
