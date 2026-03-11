# Let-Binding Implementation Plan

> **Goal**: Add let-bindings as syntax sugar (desugared to beta reduction)
> **Status**: ✅ Complete
> **Date**: March 2025

---

## Overview

Let-bindings provide convenient syntax for naming values and functions. Instead of adding a new Term constructor, let-bindings are **desugared** to beta reduction during parsing:

```
let x = value in body   ≡   (x -> body)(value)
```

This approach:
- ✅ Keeps the core calculus minimal (no new Term constructor needed)
- ✅ Reuses existing type checking and evaluation rules
- ✅ Provides syntactic convenience for users
- ✅ Maintains semantic equivalence

---

## Implementation Status

### Phase 1: Grammar and Parser ✅

**Syntax**:
```
let name = value in body
```

**Desugaring**:
```
let x = 42 in x   →   (x -> x)(42)
```

**Implementation**:
- [x] Add `Let` and `In` tokens to lexer
- [x] Add grammar rule for `let` expressions
- [x] Desugar to `(name -> body)(value)` in parser

### Phase 2: Examples and Tests ✅

**Examples**:
- [x] `examples/core/terms/11_let_binding.core.tao` - Basic let binding
- [x] `examples/core/terms/12_let_function.core.tao` - Let with simple value

**Error Cases**:
- [x] `examples/core/errors/type_errors/04_let_function_inference.core.tao` - Type inference limitation (documented)

**Tests**:
- [x] `test/syntax/lexer_test.gleam` - Tokenizer test for "let" keyword
- [x] `test/syntax/examples/calc_test.gleam` - Error tests updated

---

## Syntax Details

### Basic Let Binding
```
let x = 42 in x
```
Desugars to:
```
(x -> x)(42)
```

### Let with Function
```
let id = x -> x in id(42)
```
Desugars to:
```
(id -> id(42))(x -> x)
```

**Note**: This currently fails type checking due to type inference limitations. The type checker cannot infer that `id` must be a function from its application context.

### Nested Let Bindings
```
let x = 1 in let y = 2 in x + y
```
Desugars to:
```
(x -> (y -> x + y)(2))(1)
```

### Let Shadowing
```
let x = 1 in let x = 2 in x
```
Desugars to:
```
(x -> (x -> x)(2))(1)  // Returns 2 (inner binding shadows outer)
```

---

## Known Limitations

### Type Inference with Functions

Let-bindings with functions currently fail type checking:

```
let id = x -> x in id(42)  // Type error: "Not a function"
```

**Reason**: The type checker creates a hole for the type of `id`, but cannot solve it from the application context. This is a limitation of the current bidirectional type checking algorithm.

**Workaround**: Use explicit type annotations (future feature) or avoid let-bindings with functions until type inference is improved.

---

## Error Cases

### Missing `in` Keyword
```
let x = 42 x
```
**Error**: Expected `in` after value

### Missing Value
```
let x in x
```
**Error**: Expected expression after `=`

### Unclosed Let
```
let x = 42 in
```
**Error**: Expected expression after `in`

---

## Testing Strategy

### Parse Tests
```gleam
pub fn parse_let_binding_test() {
  parse_ok("let x = 42 in x")
  |> should.evaluate_to(42)
}
```

### Type Checking Tests
```gleam
pub fn type_check_let_binding_test() {
  let source = "let x = 42 in x"
  let result = type_check(source)
  result |> should.be_ok()
}
```

### Evaluation Tests
```gleam
pub fn evaluate_let_binding_test() {
  let source = "let x = 42 in x"
  let result = evaluate(source)
  result |> should.equal(Int(42))
}
```

---

## Success Criteria

- ✅ Let-bindings parse correctly
- ✅ Let-bindings desugar to beta reduction
- ✅ Type checking works for simple let-bindings
- ✅ Evaluation works for let-bindings
- ✅ Error messages are clear for invalid let syntax
- ✅ All existing tests continue to pass (344 tests)

---

## Related Documents

- [Core Language Overview](../../docs/plans/core/01-overview.md)
- [Language Enhancements Plan](../../docs/plans/core/11-language-enhancements.md)
- [Error Reporting Plan](../../docs/plans/error-reporting/01-overview.md)
