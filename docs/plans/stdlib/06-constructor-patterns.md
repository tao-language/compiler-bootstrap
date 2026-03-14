# Constructor Representation

> **Goal**: Simplify constructor representation using Unit for nullary constructors
> **Status**: ✅ **Complete** - Unified Ctr(tag, arg) with Unit for nullary
> **Date**: March 2026

---

## Status

### What's Working

- ✅ Unified constructor representation: `Ctr(tag: String, arg: Term)`
- ✅ Unit term for nullary constructors: `#True(Unit)`, `#False(Unit)`, `#None(Unit)`
- ✅ Formatter special-cases Unit to display as `#True`, `#False`, `#None`
- ✅ Constructor patterns with Unit: `#True(Unit)`, `#Some(x)`
- ✅ Type checking and evaluation for Unit-based constructors
- ✅ **424 tests passing**

### Design Decision

Instead of having separate `Ctr` and `CtrNullary` constructors, we use a single `Ctr(tag, arg)` with `Unit` for nullary:

```core
// Nullary constructors (displayed as #True, #False, etc.)
#True   ≡  Ctr("True", Unit)
#False  ≡  Ctr("False", Unit)
#None   ≡  Ctr("None", Unit)

// Constructors with arguments
#Some(x)  ≡  Ctr("Some", x)
#Ok(v)    ≡  Ctr("Ok", v)
```

This simplifies:
- Type definitions (one constructor instead of two)
- Pattern matching (uniform handling)
- Exhaustiveness checking (simpler head comparison)
- Normalization by evaluation (fewer cases)

### Related

- See **[05-polymorphic-constructors.md](./05-polymorphic-constructors.md)** for polymorphic constructors
- See **[../core/02-syntax.md](../core/02-syntax.md)** for Core syntax

---

## Problem

### Previous Approach

Previously, we had separate constructors:
- `Ctr(tag, arg)` for constructors with arguments
- `CtrNullary(tag)` for nullary constructors

This led to:
- Duplicated code in evaluation, quoting, unification
- Complex exhaustiveness checking (two head types)
- Inconsistent pattern matching

### Solution

Use a single `Ctr(tag, arg)` with `Unit` for nullary constructors.

---

## Implementation

### Term Type

```gleam
pub type Term {
  // ... other constructors
  Ctr(tag: String, arg: Term)  // Unified constructor
  Unit                          // Unit value for nullary constructors
}
```

### Pattern Type

```gleam
pub type Pattern {
  // ... other patterns
  PCtr(tag: String, arg: Pattern)  // Constructor pattern
  PUnit                             // Unit pattern
}
```

### Value Type

```gleam
pub type Value {
  // ... other values
  VCtrValue(VCtr(tag: String, arg: Value))  // Constructor value
  VUnit                                      // Unit value
}
```

### Formatter Special-Case

The formatter displays `Ctr(tag, Unit)` as `#tag` for better readability:

```gleam
fn format_term(term, parent_prec, bindings) {
  case term {
    Ctr(tag, arg) ->
      case arg.data {
        Unit -> text("#") <> text(tag)  // Display as #True, #False, etc.
        _ -> text("#") <> text(tag) <> parens(format_term(arg))
      }
    Unit -> text("Unit")
    // ...
  }
}
```

### Example: Bool Type

```core
// Type definition
type Bool = %Type.1

// Constructors
#True : Bool   ≡   Ctr("True", Unit)
#False : Bool  ≡   Ctr("False", Unit)

// Pattern matching
match b {
  | #True -> 1
  | #False -> 0
}
```

### Parser Grammar

```gleam
rule("Pattern", [
  // Constructor with args: #Some(x)
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
      token_pattern("LParen"),
      ref("Pattern"),
      token_pattern("RParen"),
    ]),
    make_pattern_ctr_app,
  ),
  // Nullary constructor: #True (parsed as #True(Unit))
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
    ]),
    make_pattern_ctr,  // Creates NPCtr(tag, NPUnit(span), span)
  ),
])

fn make_pattern_ctr(values) -> ParseValue {
  case values {
    [_, TokenValue(tag_token)] ->
      AsPattern(NPCtr(
        tag_token.value,
        NPUnit(grammar.span_from_token(tag_token, "input")),
        grammar.span_from_token(tag_token, "input"),
      ))
    _ -> panic as "Expected constructor pattern"
  }
}
```

---

## Testing

All tests passing (424 total):

```gleam
// Test: Nullary constructor roundtrip
pub fn roundtrip_constructor_nullary_test() {
  let source = "#True"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)  // #True displays without Unit
}

// Test: Match with nullary constructors
pub fn match_with_nullary_constructors_test() {
  let source = "%match x { | #True -> 1 | #False -> 0 }"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  // Evaluates correctly
}
```

---

## Alternatives Considered

### Alternative 1: Separate Ctr and CtrNullary

Have two constructors: `Ctr(tag, arg)` and `CtrNullary(tag)`.

**Rejected**: Duplicates code, complicates pattern matching and exhaustiveness checking.

### Alternative 2: Keep Dummy Arguments

Use `Typ(0)` as dummy argument for nullary constructors.

**Rejected**: Unnatural, leaks implementation detail to users.

### Alternative 3: Special Syntax for Nullary

Use `##True` for nullary constructors.

**Rejected**: Inconsistent, adds complexity to grammar.

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Unified Ctr representation with Unit implemented |
| March 2026 | Initial nullary constructor plan created |
