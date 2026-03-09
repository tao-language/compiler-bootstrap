# Plan: Fix Variable Shadowing in Parser/Formatter

## Problem

Currently, the parser converts all variable references to De Bruijn indices immediately during parsing, without tracking which variables are bound in scope. This causes issues:

- `x -> y -> x` parses as `Lam("x", Lam("y", Var(0)))` where `Var(0)` refers to `y` (innermost), not `x`
- The formatter correctly outputs `x -> y -> y` based on the De Bruijn index
- But the user's intent (`x -> y -> x` where inner `x` refers to outer `x`) is lost

## Root Cause

The grammar DSL parses each rule independently without maintaining a binding environment. Variable resolution happens at parse time with no context about enclosing binders.

## Solution Options

### Option 1: Two-Pass Parsing (Recommended)

**Pass 1**: Parse to an intermediate AST with named variables
**Pass 2**: Convert named variables to De Bruijn indices with proper scope tracking

#### Intermediate AST Type

```gleam
pub type NamedTerm {
  NVar(name: String, span: Span)
  NLit(value: Literal, span: Span)
  NLam(name: String, body: NamedTerm, span: Span)
  NPi(name: String, in_type: NamedTerm, out_type: NamedTerm, span: Span)
  NApp(fun: NamedTerm, arg: NamedTerm, span: Span)
  // ... etc
}
```

#### Conversion Function

```gleam
pub fn to_de_bruijn(term: NamedTerm) -> Term {
  to_de_bruijn_loop(term, [])
}

fn to_de_bruijn_loop(term: NamedTerm, env: List(String)) -> Term {
  case term {
    NVar(name, span) -> {
      case list.index(env, fn(n) { n == name }) {
        Ok(index) -> Term(Var(index), span)
        Error(_) -> Term(Var(0), span) // Free variable
      }
    }
    NLam(name, body, span) -> {
      let body_db = to_de_bruijn_loop(body, [name, ..env])
      Term(Lam(name, body_db), span)
    }
    // ... handle other cases
  }
}
```

#### Implementation Steps

1. **Create `NamedTerm` type** in `src/core/syntax.gleam`
   - Mirror all `Term` variants but use `String` names instead of `Int` indices
   - ~15 variants

2. **Update grammar constructors** to build `NamedTerm` instead of `Term`
   - Change all `make_*` functions to return `NamedTerm`
   - Update grammar type signature: `grammar.Grammar(NamedTerm)`

3. **Add conversion function** `named_to_de_bruijn/1`
   - Recursive function with environment tracking
   - Handle variable lookup with proper shadowing

4. **Update public API**:
   ```gleam
   pub fn parse(source: String) -> ParseResult(Term) {
     case parse_named(source) {
       Ok(named_term) -> {
         let term = named_to_de_bruijn(named_term)
         Ok(term)
       }
       Error(e) -> Error(e)
     }
   }
   ```

5. **Update tests** to verify correct variable resolution
   - Add test: `x -> y -> x` should format as `x -> y -> x`
   - Add test: `x -> x -> x` should format as `x -> var0 -> var1` (shadowing)

#### Pros
- Clean separation of concerns (parsing vs. name resolution)
- Matches how real compilers work
- Can provide better error messages for unbound variables
- Easy to extend with more sophisticated scoping rules

#### Cons
- Requires duplicating all term variants
- Two passes over the AST
- ~200-300 lines of additional code

---

### Option 2: Parser Combinator with Environment

Modify the grammar DSL to support environment passing. This is more invasive but could be useful for other features.

#### Changes Required

1. Add `Env` type parameter to `Grammar`, `Pattern`, `Alternative`
2. Modify `parse_pattern` to thread environment through parsing
3. Add special `Bind` pattern that extends environment
4. Variable tokens look up in environment during parsing

#### Pros
- Single pass
- More general solution for other context-sensitive parsing

#### Cons
- Major refactoring of grammar DSL (~500+ lines changed)
- More complex type signatures
- Harder to understand and maintain

---

### Option 3: Post-Processing Fix-Up

Parse normally, then walk the AST and fix up variable indices based on names stored in `Lam`/`Pi` nodes.

#### Implementation

```gleam
pub fn fix_variables(term: Term) -> Term {
  fix_loop(term, [])
}

fn fix_loop(term: Term, bindings: List(String)) -> Term {
  case term {
    Term(Lam(name, body), span) -> {
      let fixed_body = fix_loop(body, [name, ..bindings])
      Term(Lam(name, fixed_body), span)
    }
    Term(Var(index), span) -> {
      // Can't fix - we've lost the name information!
      term
    }
    // ...
  }
}
```

#### Problem
This doesn't work because the parser already converted names to indices. We'd need to store both the name AND the index in `Var`, which is wasteful.

**Verdict: Not viable without changing `Term` type.**

---

## Recommended Approach: Option 1 (Two-Pass)

### Implementation Checklist

- [ ] Create `NamedTerm` type with all variants
- [ ] Update all `make_*` constructor functions to return `NamedTerm`
- [ ] Update grammar type signature to `Grammar(NamedTerm)`
- [ ] Implement `named_to_de_bruijn/1` with environment tracking
- [ ] Update `parse/1` to compose parsing + conversion
- [ ] Add comprehensive tests for variable shadowing scenarios
- [ ] Update formatter tests to verify correct output

### Test Cases to Add

```gleam
// Basic shadowing
"x -> y -> x" |> parse_and_format |> should.equal("x -> y -> x")

// Self-shadowing
"x -> x -> x" |> parse_and_format |> should.equal("x -> var0 -> var1")

// Pi type shadowing
"(x : $Type) -> (x : $Type) -> x" |> parse_and_format 
  |> should.equal("(x : $Type) -> (x : $Type) -> var0")

// Mixed shadowing
"x -> (y : $Type) -> x" |> parse_and_format 
  |> should.equal("x -> (y : $Type) -> x")
```

### Estimated Effort

- Core implementation: 2-3 hours
- Testing: 1 hour
- Total: ~3-4 hours

---

## Future Considerations

Once this is implemented, we can add:

1. **Unbound variable errors**: Detect when a variable is used but not in scope
2. **Better error messages**: Show which binding a variable refers to
3. **Alpha-equivalence checking**: Two terms are equal up to renaming
4. **Capture-avoiding substitution**: Critical for evaluation
