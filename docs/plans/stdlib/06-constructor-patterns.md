# Constructor Pattern Parsing Fix

> **Goal**: Support nullary constructors in pattern matching (e.g., `#True` without arguments)
> **Status**: ✅ **Complete** - Nullary constructors implemented and working
> **Date**: March 2026

---

## Status

### What's Working

- ✅ Nullary constructor syntax: `#True`, `#False`, `#None`, `#LT`, `#EQ`, `#GT`
- ✅ Constructor patterns with args: `#Some(x)`, `#Ok(n)`, `#Err(e)`
- ✅ Type parameters for polymorphic constructors
- ✅ Pattern matching with nullary constructors (basic cases)
- ✅ **424 tests passing**

### What's Pending

- 📋 Full exhaustiveness checking for nullary constructors
- 📋 Proper type representation for prelude types (Bool, Option, etc.)
- 📋 Match examples with nullary constructors

### Related

- See **[05-polymorphic-constructors.md](./05-polymorphic-constructors.md)** for polymorphic constructors
- See **[../core/02-syntax.md](../core/02-syntax.md)** for Core syntax

---

## Problem

### Current Limitation

Core language requires all constructor patterns to have arguments:

```core
// Current (works)
match x { | #Some(n) -> n | #None(n) -> 0 }

// Desired (doesn't parse)
match x { | #True -> 1 | #False -> 0 }
match x { | #Some(n) -> n | #None -> 0 }
```

### Root Cause

Pattern grammar only accepts constructors with arguments:

```gleam
// Current pattern grammar (src/core/syntax.gleam)
rule("Pattern", [
  // Constructor pattern: #Name(pat) - REQUIRES argument
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
      token_pattern("LParen"),
      ref("Pattern"),
      token_pattern("RParen"),
    ]),
    make_pattern_ctr,
  ),
  // ... other patterns
])
```

---

## Solution

### Option 1: Make Constructor Argument Optional (Recommended)

```gleam
rule("Pattern", [
  // Constructor with args: #Name(pat)
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
      token_pattern("LParen"),
      ref("Pattern"),
      token_pattern("RParen"),
    ]),
    make_pattern_ctr_with_arg,
  ),
  // Constructor without args: #Name
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
    ]),
    make_pattern_ctr_nullary,
  ),
  // ... other patterns
])
```

**Pros**:
- Minimal change to grammar
- Backward compatible (constructors with args still work)
- Natural syntax for nullary constructors

**Cons**:
- Need to handle both cases in type checking

### Option 2: Use Unit Type for Nullary

Keep current grammar but document that nullary constructors take `Typ(0)`:

```core
match #True(Typ(0)) { | #True(_) -> 1 | #False(_) -> 0 }
```

**Pros**:
- No grammar changes needed
- Consistent with current design

**Cons**:
- Verbose and unnatural
- Users must remember to add dummy argument

### Option 3: Separate Nullary Constructor Syntax

Use different syntax for nullary constructors (e.g., `#True` vs `#Some(x)`).

**Pros**:
- Clear distinction

**Cons**:
- More complex grammar
- Inconsistent syntax

---

## Implementation Plan

### Phase 1: Grammar Changes

#### Step 1.1: Add Nullary Constructor Pattern Rule

```gleam
// In src/core/syntax.gleam
rule("Pattern", [
  // Constructor with args (existing)
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
      token_pattern("LParen"),
      ref("Pattern"),
      token_pattern("RParen"),
    ]),
    make_pattern_ctr_with_arg,
  ),
  // Constructor without args (NEW)
  alt(
    seq([
      token_pattern("Hash"),
      token_pattern("Ident"),
    ]),
    make_pattern_ctr_nullary,
  ),
  // ... rest of patterns
])
```

#### Step 1.2: Add Parser Function

```gleam
fn make_pattern_ctr_nullary(values) -> ParseValue {
  case values {
    [_, TokenValue(tag_token)] ->
      AsPattern(NPCtrNullary(
        tag_token.value,
        grammar.span_from_token(tag_token, "input"),
      ))
    _ -> panic as "Expected nullary constructor pattern"
  }
}
```

### Phase 2: AST Changes

#### Step 2.1: Extend NamedPattern Type

```gleam
pub type NamedPattern {
  // ... existing
  NPCtr(tag: String, arg: NamedPattern, span: Span)
  NPCtrNullary(tag: String, span: Span)  // NEW
}
```

### Phase 3: Type Checking Changes

#### Step 3.1: Update bind_pattern

```gleam
pub fn bind_pattern(...) {
  case pattern {
    // ... existing cases
    
    NPCtrNullary(tag, pat_span) -> {
      case list.key_find(s.ctrs, tag) {
        Error(Nil) -> #(VErr, with_err(s, CtrUndefined(tag, pat_span)))
        Ok(ctr) -> {
          // Check constructor has no type parameters or they're all instantiated
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          // Nullary constructor - no argument to bind
          #(VCtrNullary(tag), s)
        }
      }
    }
  }
}
```

### Phase 4: Evaluation Changes

#### Step 4.1: Extend Value Type

```gleam
pub type Value {
  // ... existing
  VCtr(tag: String, arg: Value)
  VCtrNullary(tag: String)  // NEW
}
```

#### Step 4.2: Update eval

```gleam
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  case term.data {
    // ... existing cases
    Ctr(tag, arg) -> {
      // Check if arg is Typ(0) (dummy unit)
      case arg.data {
        Typ(0) -> VCtrNullary(tag)  // Nullary constructor
        _ -> VCtr(tag, eval(ffi, env, arg))
      }
    }
  }
}
```

---

## Testing

### Test Cases

```gleam
// Test 1: Nullary constructor pattern
pub fn nullary_constructor_pattern_test() {
  let term = /* #True pattern */
  let result = bind_pattern(s, term, ...)
  result |> should.equal(VCtrNullary("True"))
}

// Test 2: Match with nullary constructors
%match #True ~ (_ -> I32T) {
  | #True -> I32(1)
  | #False -> I32(0)
}
// Should evaluate to I32(1)
```

---

## Alternatives Considered

### Alternative 1: Keep Dummy Arguments

Document that nullary constructors use `Typ(0)` as dummy argument.

**Rejected**: Unnatural syntax, burdens users.

### Alternative 2: Special Syntax for Nullary

Use `##True` for nullary constructors.

**Rejected**: Inconsistent, adds complexity.

---

## Open Questions

1. **Should we distinguish in the AST?** - Yes, cleaner type checking
2. **Should evaluation distinguish?** - Yes, simpler runtime
3. **Backward compatibility?** - Yes, constructors with args unchanged

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Plan created |
