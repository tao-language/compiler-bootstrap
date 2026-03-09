# Plan: Extend Grammar DSL for Records with Fields

## Problem

The current grammar DSL requires all rules to return the same type (`Term`). This prevents us from parsing record fields as a list `List(#(String, Term))` because:

1. The `FieldList` rule would need to return `List(#(String, Term))`, not `Term`
2. The grammar DSL's type system doesn't support heterogeneous return types across rules

Current workaround: Only support empty records `{}`.

## Goal

Support full record syntax:
- Empty: `{}`
- Single field: `{x: 1}`
- Multiple fields: `{x: 1, y: 2, z: 3}`

## Solution Options

### Option 1: Multi-Type Grammar DSL (Recommended)

Extend the grammar DSL to support multiple result types via a sum type.

#### Implementation

Create a wrapper type that can hold either a `Term` or field list:

```gleam
type ParseResult {
  AsTerm(Term)
  AsFields(List(#(String, Term)))
}
```

Update grammar to use this type:

```gleam
pub fn core_grammar() -> grammar.Grammar(ParseResult) {
  use g <- grammar.define

  g
  |> grammar.name("Core")
  |> grammar.start("Expr")
  // ...
  |> grammar.rule("Atom", [
    // Record with fields
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.ref("FieldList"),
        grammar.token_pattern("RBrace"),
      ]),
      fn(values) {
        case values {
          [_, AsFields(fields), _] -> AsTerm(Term(Rcd(fields), span))
          _ -> panic as "Expected fields"
        }
      },
      // formatter...
    ),
    // Empty record
    grammar.alt(...),
  ])
  // Field list returns AsFields
  |> grammar.rule("FieldList", [
    // Single field: x: expr
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
      ]),
      fn(values) {
        case values {
          [TokenValue(name), _, AsTerm(value)] ->
            AsFields([#(name.value, value)])
          _ -> panic as "Expected field"
        }
      },
      fn(_, _) { parser } // No formatter needed for internal rule
    ),
    // Multiple fields: x: expr, fields...
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
        grammar.token_pattern("Comma"),
        grammar.ref("FieldList"),
      ]),
      fn(values) {
        case values {
          [TokenValue(name), _, AsTerm(value), _, AsFields(rest)] ->
            AsFields([#(name.value, value), ..rest])
          _ -> panic as "Expected field list"
        }
      },
      fn(_, _) { parser },
    ),
  ])
}
```

Then unwrap at the end:

```gleam
pub fn parse(source: String) -> ParseResult(Term) {
  case grammar.parse(core_grammar(), source) {
    Ok(ast) -> {
      case ast {
        AsTerm(term) -> Ok(term)
        AsFields(_) -> Error("Expected expression, got field list")
      }
    }
    Error(e) -> Error(e)
  }
}
```

#### Pros
- Minimal changes to grammar DSL
- Type-safe (compiler checks all cases)
- Clear separation of concerns

#### Cons
- Wrapper type adds slight overhead
- Need to unwrap at each usage site
- ~50-80 lines of changes

---

### Option 2: Inline Field Parsing

Don't use a sub-rule for fields. Instead, parse all field patterns directly in the `Atom` rule.

#### Implementation

```gleam
pub fn core_grammar() -> grammar.Grammar(Term) {
  // ...
  |> grammar.rule("Atom", [
    // Empty record
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.token_pattern("RBrace"),
      ]),
      fn(_) { Term(Rcd([]), span) },
      fn(t, p) { format_term(t, p, []) },
    ),
    // Single field record: {x: expr}
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
        grammar.token_pattern("RBrace"),
      ]),
      fn(values) {
        case values {
          [_, TokenValue(name), _, AstValue(value), _] ->
            Term(Rcd([#(name.value, value)]), span)
          _ -> panic as "Expected field"
        }
      },
      fn(t, p) { format_term(t, p, []) },
    ),
    // Two field record: {x: expr, y: expr}
    grammar.alt(
      grammar.seq([
        grammar.token_pattern("LBrace"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
        grammar.token_pattern("Comma"),
        grammar.token_pattern("Ident"),
        grammar.token_pattern("Colon"),
        grammar.ref("Expr"),
        grammar.token_pattern("RBrace"),
      ]),
      fn(values) { /* build 2-field record */ },
      fn(t, p) { format_term(t, p, []) },
    ),
    // ... would need separate rule for each arity!
  ])
}
```

#### Pros
- No changes to grammar DSL
- Everything stays as `Term`

#### Cons
- **Not scalable**: Need separate rule for each field count
- Exponential grammar size
- **Not recommended**

---

### Option 3: Extend Grammar DSL with Generic Types

Add proper support for rules returning different types via type parameters.

#### Changes to Grammar DSL

1. Make `Grammar` polymorphic:
   ```gleam
   pub type Grammar(result) {
     Grammar(
       name: String,
       start_rule: String,
       rules: dict.Dict(String, Rule(result)),
       // ...
     )
   }
   ```

2. Allow rules to specify their return type via phantom types or existentials

3. Add `SubRule` pattern that can return a different type

#### Implementation Complexity

This requires significant refactoring:
- Change all `Pattern(a)` to support multiple result types
- Add existential types or GADTs (not directly supported in Gleam)
- Update all parsing functions to handle type erasure

#### Pros
- Most elegant long-term solution
- Enables other advanced features

#### Cons
- **Major refactoring** (~300-500 lines changed)
- Gleam's type system limitations make this challenging
- May require runtime type tags

---

### Option 4: String-Based Field List (Hack)

Parse field list as a string, then recursively parse each field.

#### Implementation

```gleam
// In grammar, capture field list as raw text
grammar.alt(
  grammar.seq([
    grammar.token_pattern("LBrace"),
    grammar.capture_until("RBrace"), // Captures "x: 1, y: 2"
    grammar.token_pattern("RBrace"),
  ]),
  fn(values) {
    case values {
      [_, TokenValue(captured), _] -> {
        let fields = parse_fields_manually(captured.value)
        Term(Rcd(fields), span)
      }
      _ -> panic
    }
  },
  // ...
)
```

#### Pros
- Works with current grammar DSL

#### Cons
- Loses source location information
- Duplicates parsing logic
- Error messages point to wrong locations
- **Not recommended**

---

## Recommended Approach: Option 1 (Multi-Type via Sum Type)

### Implementation Steps

1. **Create wrapper type** in `src/core/syntax.gleam`:
   ```gleam
   type ParseValue {
     AsTerm(Term)
     AsFields(List(#(String, Term)))
   }
   ```

2. **Update grammar signature**:
   ```gleam
   pub fn core_grammar() -> grammar.Grammar(ParseValue)
   ```

3. **Update all constructor functions** to wrap results:
   ```gleam
   fn make_var(values) -> ParseValue {
     case values {
       [TokenValue(token)] -> AsTerm(Term(Var(0), span))
       _ -> panic as "Expected identifier"
     }
   }
   ```

4. **Add FieldList rule**:
   ```gleam
   |> grammar.rule("FieldList", [
     // Single field
     grammar.alt(
       grammar.seq([
         grammar.token_pattern("Ident"),
         grammar.token_pattern("Colon"),
         grammar.ref("Expr"),
       ]),
       make_single_field,
       fn(_, _) { formatter.text("") }, // Dummy formatter
     ),
     // Multiple fields
     grammar.alt(...),
   ])
   ```

5. **Update record parsing** to use FieldList:
   ```gleam
   grammar.alt(
     grammar.seq([
       grammar.token_pattern("LBrace"),
       grammar.ref("FieldList"),
       grammar.token_pattern("RBrace"),
     ]),
     fn(values) {
       case values {
         [_, AsFields(fields), _] -> AsTerm(Term(Rcd(fields), span))
         _ -> panic
       }
     },
     fn(t, p) { format_term(t, p, []) },
   )
   ```

6. **Update public parse function**:
   ```gleam
   pub fn parse(source: String) -> grammar.ParseResult(Term) {
     case grammar.parse(core_grammar(), source) {
       Ok(ast) -> {
         case ast {
           AsTerm(term) -> Ok(term)
           AsFields(_) -> Error(...)
         }
       }
       Error(e) -> Error(e)
     }
   }
   ```

7. **Add tests** for all record forms:
   ```gleam
   pub fn roundtrip_record_empty_test() {
     "{}" |> parse_and_format |> should.equal("{}")
   }

   pub fn roundtrip_record_single_test() {
     "{x: 1}" |> parse_and_format |> should.equal("{x: 1}")
   }

   pub fn roundtrip_record_multiple_test() {
     "{x: 1, y: 2, z: 3}" |> parse_and_format 
       |> should.equal("{x: 1, y: 2, z: 3}")
   }
   ```

### Formatter Updates

Update `format_term` to handle records with fields:

```gleam
fn format_term(term: Term, parent_prec: Int, bindings: List(String)) -> formatter.Doc {
  case term.data {
    // ...
    Rcd(fields) -> {
      case fields {
        [] -> formatter.text("{}")
        _ -> {
          let field_docs =
            fields
            |> list.map(fn(field) {
              let #(name, value) = field
              formatter.concat([
                formatter.text(name),
                formatter.text(": "),
                format_term(value, 50, bindings),
              ])
            })
          formatter.concat([
            formatter.text("{"),
            list.intersperse(field_docs, formatter.text(", ")) 
              |> formatter.concat,
            formatter.text("}"),
          ])
        }
      }
    }
    // ...
  }
}
```

### Estimated Effort

- Core implementation: 1-2 hours
- Testing: 30 minutes
- Total: ~2 hours

---

## Future Extensions

Once this is working, we can add:

1. **Trailing commas**: `{x: 1, y: 2,}`
2. **Record update syntax**: `{..old, x: 1}`
3. **Label shorthand**: `{x}` instead of `{x: x}`
4. **Multi-line formatting**: Break fields across lines when too long
