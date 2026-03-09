# Implementation Plan

> **Status**: ✅ Phases 1-6 complete, ⏳ Phase 7+ in progress
> **Date**: March 2025

---

## Current Status

### ✅ Working

- Lexer tokenizes numbers, identifiers, operators, parentheses, strings, comments
- Grammar DSL with declarative builder pattern
- Parser handles all patterns (Token, Keyword, Op, Ref, Seq, Choice, Opt, Many, Sep1, Parens)
- **Left-associative operator parsing** - Correctly handles multiple operators at same precedence
- **Operator precedence** - Higher precedence operators bind tighter
- **Parenthesized expressions** - Correctly overrides precedence
- **Formatter with precedence-based parenthesization** - Correctly adds/removes parentheses
- **Round-trip parsing** - parse → format → parse produces consistent output
- **238 tests passing**

### ⏳ Needs Work

1. **Automatic formatter from grammar** - Currently manual per-language
2. **Error handling** - Panics on parse failure instead of returning errors
3. **Core language migration** - Use new grammar system for core language

---

## Implementation Phases

### Phase 1: Fix Left-Associative Operator Parsing ✅

**Problem**: The `Many` combinator returns a flat `List(Value(a))`, but for left-associative operators we need to fold them correctly.

**Solution**:
1. Changed `Many` to wrap each matched sequence in `ListValue`
2. Updated `fold_operators_multi` to handle the nested structure
3. Changed `left_assoc` to create a single alternative with `Choice` for multiple operators at same precedence

**Files modified**:
- `src/syntax/grammar.gleam` - `parse_many`, `create_operator_pattern`, `fold_operators_multi`

**Tests passing**:
- ✅ `parse_left_assoc_test()` - `1 + 2 + 3` = `Add(Add(1, 2), 3)`
- ✅ `parse_mul_div_mix_test()` - `12 / 3 * 2` = `Mul(Div(12, 3), 2)`

### Phase 2: Fix Parenthesized Expressions ✅

**Problem**: Parenthesized expressions weren't parsing correctly.

**Solution**:
1. Changed `grammar.parenthesized()` to return `Parens` pattern instead of `Seq`
2. `parse_parens` wraps result in `ParensValue` for special handling

**Files modified**:
- `src/syntax/grammar.gleam` - `parenthesized()` function

**Tests passing**:
- ✅ `parse_parens_number_test()` - `(42)` = `Int(42)`
- ✅ `parse_parens_add_test()` - `(1 + 2)` = `Add(1, 2)`
- ✅ `parse_parens_override_precedence_test()` - `(1 + 2) * 3` = `Mul(Add(1, 2), 3)`
- ✅ `parse_parens_nested_test()` - `((1 + 2) * 3)` = `Mul(Add(1, 2), 3)`

### Phase 3: Fix Operator Precedence ✅

**Problem**: Multiple operators at same precedence level (e.g., `*` and `/`) weren't handled correctly.

**Solution**:
1. Changed `left_assoc` to create a single alternative with `Choice` of operators
2. Added `fold_operators_multi` that looks up the correct operator by token value

**Files modified**:
- `src/syntax/grammar.gleam` - `left_assoc`, `create_operator_pattern`, `fold_operators_multi`

**Tests passing**:
- ✅ `parse_precedence_test()` - `1 + 2 * 3` = `Add(1, Mul(2, 3))`
- ✅ `parse_complex_precedence_test()` - `2 * 3 + 4 * 5` = `Add(Mul(2, 3), Mul(4, 5))`
- ✅ `parse_all_operators_test()` - `1 + 2 * 3 - 4 / 2` = `Sub(Add(1, Mul(2, 3)), Div(4, 2))`

### Phase 4: Add Comprehensive Tests ✅

**Tests added**:
- Number parsing (single digit, multi-digit, zero)
- Addition (simple, multiple, four operands)
- Subtraction (simple, multiple)
- Multiplication (simple, multiple)
- Division (simple)
- Precedence (mul before add, mul before sub, complex)
- Parentheses (number, add, override precedence, nested, complex, deeply nested)
- Mixed operators (add/sub mix, mul/div mix, all operators)

**Test results**: All passing

### Phase 5: Implement Formatter ✅

**Problem**: Formatter returned `<ast>` placeholder for all ASTs.

**Solution**:
1. Added manual `format_expr` function in `calc.gleam` with precedence-based parenthesization
2. For left-associative operators:
   - Left operand: same precedence (no parens for same level)
   - Right operand: precedence + 1 (parens for same level)
3. Added `format_binop` helper that wraps in parens when child precedence < parent precedence

**Files modified**:
- `src/examples/calc.gleam` - Added `format_expr`, `format_binop`

**Tests passing**:
- ✅ `format_int_test()` - `Int(42)` = `"42"`
- ✅ `format_add_test()` - `Add(1, 2)` = `"1 + 2"`
- ✅ `format_sub_test()` - `Sub(5, 3)` = `"5 - 3"`
- ✅ `format_mul_test()` - `Mul(2, 3)` = `"2 * 3"`
- ✅ `format_div_test()` - `Div(10, 2)` = `"10 / 2"`
- ✅ `format_nested_test()` - `Add(1, Mul(2, 3))` = `"1 + 2 * 3"`
- ✅ `format_parens_needed_test()` - `Mul(Add(1, 2), 3)` = `"(1 + 2) * 3"`
- ✅ `format_complex_test()` - `Sub(Add(1, Mul(2, 3)), Div(4, 2))` = `"1 + 2 * 3 - 4 / 2"`

### Phase 6: Round-Trip Tests ✅

**Goal**: Verify parse → format → parse produces same AST.

**Tests added**:
- ✅ `roundtrip_int_test()` - `"42"` → parse → format → `"42"`
- ✅ `roundtrip_add_test()` - `"1 + 2"` → parse → format → `"1 + 2"`
- ✅ `roundtrip_sub_test()` - `"5 - 3"` → parse → format → `"5 - 3"`
- ✅ `roundtrip_mul_test()` - `"2 * 3"` → parse → format → `"2 * 3"`
- ✅ `roundtrip_div_test()` - `"10 / 2"` → parse → format → `"10 / 2"`
- ✅ `roundtrip_precedence_test()` - `"1 + 2 * 3"` → parse → format → `"1 + 2 * 3"`
- ✅ `roundtrip_parens_test()` - `"(1 + 2) * 3"` → parse → format → `"(1 + 2) * 3"`
- ✅ `roundtrip_nested_parens_test()` - `"((1 + 2) * 3)"` → parse → format → `"(1 + 2) * 3"`
- ✅ `roundtrip_complex_test()` - `"1 + 2 * 3 - 4 / 2"` → parse → format → `"1 + 2 * 3 - 4 / 2"`
- ✅ `roundtrip_all_ops_test()` - `"1 + 2 - 3 * 4 / 2"` → parse → format → `"1 + 2 - 3 * 4 / 2"`
- ✅ `roundtrip_multi_digit_test()` - `"123 + 456 * 789"` → parse → format → `"123 + 456 * 789"`

**Test results**: All passing

### Phase 7: Error Handling ⏳ DEFERRED

**Problem**: Parser panics with "Parse failed" on invalid input.

**Current behavior**:
```gleam
parse("abc")  // Panics
```

**Expected behavior**:
```gleam
parse("abc")  // Returns ParseResult with errors list
```

**Status**: Tests commented out, to be implemented in future iteration.

**Files to modify**:
- `src/syntax/grammar.gleam` - `parse`, `parse_rule`, `try_alternatives`

---

## Next Steps

### Phase 8: Automatic Formatter Generation ⏳

**Goal**: Generate formatter automatically from grammar definition.

**Approach**: Store deconstructors in grammar for automatic lookup.

**Tasks**:
- [ ] Add `deconstructor` field to `Operator` and `Alternative`
- [ ] Implement `format_ast` that uses deconstructors
- [ ] Add typed token helpers (`int_token`, `string_token`)
- [ ] Update calc grammar to provide deconstructors
- [ ] Add tests for automatic formatting

### Phase 9: Core Language Migration ⏳

**Goal**: Migrate core language parser to use new grammar system.

**Tasks**:
- [ ] Define core language grammar using new DSL
- [ ] Verify parsing matches existing behavior
- [ ] Remove old parser implementation
- [ ] Add integration tests

### Phase 10: Polish ⏳

**Tasks**:
- [ ] Better error messages
- [ ] Grammar validation (check for undefined rules, etc.)
- [ ] Performance optimizations
- [ ] Documentation improvements

---

## Key Design Decisions

### 1. Left-Associativity

**Problem**: Standard sequence parsing produces right-associative trees.

**Solution**: Special `LeftAssoc` symbol type with dedicated parsing logic that folds left-to-right.

### 2. Precedence Tracking

**Problem**: Both parser and formatter need precedence information.

**Solution**: Single `precedence` field in `Operator` and `Rule` used by both.

### 3. Token Value Extraction

**Problem**: `Number` token → `Int` conversion is repetitive.

**Solution**: Built-in converters (`int_token`, `float_token`, `string_token`).

### 4. Deconstructors for Formatting

**Problem**: Formatter needs to extract operands from AST.

**Solution**: Store `deconstructor` functions in `Operator` and `Alternative`.

### 5. Layout in Grammar

**Problem**: Formatting rules duplicated in grammar and formatter.

**Solution**: Store layout metadata in grammar (`LayoutStyle`, `OperatorLayout`).

---

## Code Comparison

### Before (Legacy)

```gleam
// 85+ lines of boilerplate
pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  // ... lots of boilerplate
}

// Separate manual formatter (80+ lines)
fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  case expr {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> grammar.format_op(g, "+", l, r, parent_prec, format_child)
    // ...
  }
}
```

**Total**: 165+ lines

### After (Current - Manual Formatter)

```gleam
// 40 lines - grammar definition
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define
  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10),
    grammar.op("-", Sub, 10),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}

// 40 lines - manual formatter
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) -> format_binop(format_expr(l, 10), format_expr(r, 11), " + ", 10, parent_prec)
    // ...
  }
}
```

**Total**: 80 lines (**52% reduction**)

### Future (Automatic Formatter)

```gleam
// 40 lines - grammar definition with deconstructors
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define
  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op_full("+", Add, fn(ast) { case ast { Add(l, r) -> #(l, r) } }, 10),
    grammar.op_full("-", Sub, fn(ast) { case ast { Sub(l, r) -> #(l, r) } }, 10),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}

// 0 lines - automatically generated!
```

**Total**: 40 lines (**76% reduction**)

---

## Testing Checklist

### Parsing Tests

- [x] Number parsing (single digit, multi-digit, zero)
- [x] Addition (simple, multiple, four operands)
- [x] Subtraction (simple, multiple)
- [x] Multiplication (simple, multiple)
- [x] Division (simple)
- [x] Precedence (mul before add, mul before sub, complex)
- [x] Parentheses (number, add, override precedence, nested, complex)
- [x] Mixed operators (add/sub mix, mul/div mix, all operators)
- [x] Left associativity (1 + 2 + 3, 12 / 3 * 2)
- [ ] Error cases (invalid input, unexpected tokens)

### Formatting Tests

- [x] Integer formatting
- [x] Binary operators (add, sub, mul, div)
- [x] Nested expressions
- [x] Precedence-based parens
- [x] Complex expressions
- [ ] Layout breaking (long expressions)
- [ ] Custom layouts (ternary, functions)

### Round-Trip Tests

- [x] Basic expressions (int, add, sub, mul, div)
- [x] Precedence tests
- [x] Parentheses tests
- [x] Complex expressions
- [x] All operators
- [ ] Error recovery round-trips

---

## Performance Considerations

1. **No Backtracking**: Once committed, don't backtrack (use `commit`)
2. **Left-Factoring**: Grammar should be left-factored for efficiency
3. **Token Caching**: Cache token lookups by position
4. **Dict Lookups**: Operator lookup by keyword (minor cost)

---

## Limitations

1. **Recursive Grammars**: Limited support for left-recursive rules
2. **Error Quality**: Generic errors, not rule-specific messages
3. **Recovery**: Basic sync-point recovery, not phrase-level
4. **Runtime Type Inspection**: Gleam doesn't support it, need explicit deconstructors

---

## Future Enhancements

### If Gleam Adds Macros

```gleam
@derive_formatter
pub type Expr {
  Int(Int)
  Add(Expr, Expr)  // @op("+", precedence: 10, layout: BreakAfter(2))
  Mul(Expr, Expr)  // @op("*", precedence: 20, layout: BreakAfter(2))
  Rcd(List(#(String, Expr)))
}
```

### Advanced Layout Features

- Per-rule `break_width` (override global width)
- `always_break` flag for forcing multi-line
- Nested indentation tracking
- Layout hints for choice/alternative patterns

### Better Error Reporting

- Rule-specific error messages
- Suggestion hints
- Source snippets with context
- Multiple error accumulation

---

## See Also

- [Grammar DSL](./02-grammar-dsl.md)
- [Parser Library](./03-parser-library.md)
- [Formatter Library](./04-formatter-library.md)
- [Current Implementation](../../src/syntax/grammar.gleam)
- [Calc Example](../../src/examples/calc.gleam)
