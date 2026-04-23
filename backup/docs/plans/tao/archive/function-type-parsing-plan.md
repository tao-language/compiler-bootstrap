# Function Type Parsing Implementation Plan

**Date**: 2026-03-17  
**Status**: 📋 **Planned**  
**Priority**: High - Enables higher-order functions

---

## Problem

Tao cannot parse function types in parameter annotations:

```tao
// This fails to parse:
fn apply(f: fn(I32) -> I32, x: I32) -> I32 {
  f(x)
}
```

**Error**: Parser expects simple `Ident` for type annotations, not complex `fn(...) -> ...` types.

---

## Root Cause

The parser currently uses `token_pattern("Ident")` for type annotations:

```gleam
// Current implementation (src/tao/syntax.gleam:607)
opt(seq([
  token_pattern("Colon"),
  token_pattern("Ident"),  // ❌ Only simple types like "I32"
])),
```

This doesn't support:
- Function types: `fn(I32) -> I32`
- Generic types with args: `List(Int)`, `Option(a)`
- Nested function types: `fn(fn(I32) -> I32) -> I32`

---

## Solution

### Step 1: Add Type Rule

Add a new grammar rule for types that supports:
1. Simple types: `Ident`
2. Generic types: `Ident(Type, Type, ...)`
3. Function types: `fn(Type, Type, ...) -> Type`

```gleam
// Type = Ident | Ident(Type, ...) | "fn" "(" [Type ("," Type)*] ")" "->" Type
rule("Type", [
  // Function type: fn(I32, I32) -> I32
  alt(
    seq([
      keyword_pattern("fn"),
      token_pattern("LParen"),
      opt(seq([
        ref("Type"),
        many(seq([
          token_pattern("Comma"),
          ref("Type"),
        ])),
      ])),
      token_pattern("RParen"),
      token_pattern("Arrow"),
      ref("Type"),
    ]),
    make_fn_type,
  ),
  // Generic type: List(Int)
  alt(
    seq([
      token_pattern("Ident"),
      opt(seq([
        token_pattern("LParen"),
        sep1(ref("Type"), token_pattern("Comma")),
        token_pattern("RParen"),
      ])),
    ]),
    make_generic_type,
  ),
  // Simple type: I32, String, etc.
  alt(
    token_pattern("Ident"),
    make_simple_type,
  ),
]),
```

### Step 2: Update Type AST

The `tao/ast.Type` already has the right structure:

```gleam
pub type Type {
  TVar(String)           // Simple type: I32
  TApp(String, List(Type))  // Generic: List(Int)
  TFn(List(Type), Type)     // Function: fn(I32) -> I32
  TRecord(List(#(String, Type)))
  TTuple(List(Type))
  THole
}
```

We need to add syntax.gleam equivalents:

```gleam
// In src/tao/syntax.gleam
pub type Type {
  TVar(name: String)
  TApp(name: String, args: List(Type))
  TFn(params: List(Type), ret: Type)
}
```

### Step 3: Update Parameter Parsing

Change parameter type annotations from `token_pattern("Ident")` to `ref("Type")`:

```gleam
// Before
opt(seq([
  token_pattern("Colon"),
  token_pattern("Ident"),
])),

// After
opt(seq([
  token_pattern("Colon"),
  ref("Type"),
])),
```

### Step 4: Update Helper Functions

Update `extract_params_from_many_with_types` to handle `AstValue(Type)` instead of `TokenValue`:

```gleam
// Before: handles TokenValue(type_name)
[TokenValue(name_tok), TokenValue(_colon), TokenValue(type_tok), ..] ->
  extract_params_from_many_with_types(rest, [#(name_tok.value, Some(type_tok.value)), ..acc])

// After: handles AstValue(type_ast)
[TokenValue(name_tok), TokenValue(_colon), AstValue(type_ast), ..] ->
  extract_params_from_many_with_types(rest, [#(name_tok.value, Some(type_ast_to_string(type_ast))), ..acc])
```

### Step 5: Add Conversion Function

```gleam
fn type_ast_to_string(type_ast: Type) -> String {
  case type_ast {
    TVar(name) -> name
    TApp(name, args) -> name <> "(" <> string_join(list.map(args, type_ast_to_string), ", ") <> ")"
    TFn(params, ret) -> "fn(" <> string_join(list.map(params, type_ast_to_string), ", ") <> ") -> " <> type_ast_to_string(ret)
  }
}
```

---

## Implementation Checklist

- [ ] Add `Type` type to syntax.gleam
- [ ] Add `Type` grammar rule
- [ ] Update function parameter parsing to use `ref("Type")`
- [ ] Update return type parsing to use `ref("Type")`
- [ ] Update `extract_params_from_many_with_types` to handle Type AST
- [ ] Add `type_ast_to_string` helper function
- [ ] Update `make_simple_fn` to handle Type AST for return type
- [ ] Update `make_overloaded_fn` to handle Type AST
- [ ] Add tests for function type parsing
- [ ] Test with `higher_order.tao` example

---

## Test Cases

### Simple Function Type

```tao
fn apply(f: fn(I32) -> I32, x: I32) -> I32 {
  f(x)
}
```

**Expected AST**:
```gleam
SimpleFn(
  "apply",
  [
    #("f", Some(TFn([TVar("I32")], TVar("I32")))),
    #("x", Some(TVar("I32")))
  ],
  Some(TVar("I32")),
  body,
  span
)
```

### Nested Function Type

```tao
fn compose(f: fn(I32) -> I32, g: fn(I32) -> I32) -> fn(I32) -> I32 {
  fn(x) { f(g(x)) }
}
```

### Generic Type

```tao
fn map(opt: Option(Int), f: fn(Int) -> Int) -> Option(Int) {
  match opt {
    | Some(x) -> Some(f(x))
    | None -> None
  }
}
```

---

## Impact

### Files Modified
- `src/tao/syntax.gleam` - Type rule and parsing
- `src/tao/ast.gleam` - No changes needed (already has TFn)

### Examples Unblocked
- `examples/tao/pending/higher_order.tao` ✅
- `examples/tao/pending/recursive_fn.tao` ✅ (partial)
- Future: Callback patterns, strategy pattern, etc.

### Backward Compatibility
- ✅ All existing examples continue to work
- ✅ Simple type annotations (`x: I32`) still supported
- ✅ Type inference still works for unannotated params

---

## Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Grammar ambiguity (fn keyword) | LOW | MEDIUM | Careful rule ordering, test thoroughly |
| Type AST complexity | LOW | LOW | Reuse existing tao/ast.Type structure |
| Param extraction bugs | MEDIUM | LOW | Add comprehensive tests |
| Performance (recursive types) | VERY LOW | LOW | Limit nesting depth if needed |

---

## Estimated Effort

- **Implementation**: 2-3 hours
- **Testing**: 1 hour
- **Documentation**: 30 minutes
- **Total**: ~4 hours

---

## References

- [Tao AST Type Definition](../../src/tao/ast.gleam#L379)
- [Syntax Library Grammar Rules](../../src/syntax/grammar.gleam)
- [Function Type Design Discussion](../../docs/plans/tao/10-overloading-design.md)

---

**Next Steps**: Implement when ready to unblock higher-order functions.
