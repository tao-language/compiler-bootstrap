# Additional Modules Reference

## Visitor Pattern (core/visitor.gleam)

The visitor pattern provides generic AST traversal for Core terms, eliminating code duplication across `subst`, `generalize`, `quote`, and other modules.

### Why a Visitor?

Without a visitor, every module that needs to traverse the AST writes its own recursive `case` match:

```gleam
// Without visitor (duplication in every module):
fn replace_holes(term, replacement) {
  case term {
    Var(i, s) -> Var(i, s)
    Hole(id, s) -> replacement(id, s)
    Lam(p, b, s) -> Lam(p, replace_holes(b, replacement), s)
    Pi(d, c, s) -> Pi(d, c, s)
    App(f, a, s) -> App(replace_holes(f, replacement), replace_holes(a, replacement), s)
    // ... 20 constructors to handle
  }
}
```

With a visitor, the traversal is handled once:

```gleam
// With visitor (no duplication):
visit_term(
  term,
  fn(i, s) -> Var(i, s),                              // var
  fn(id, s) -> replacement(id, s),                     // hole
  fn(imp, p, b, s) -> Lam(imp, p, b, s),               // lam
  fn(imp, n, d, c, s) -> Pi(imp, n, d, c, s),          // pi
  fn(f, imp, a, s) -> App(replace_holes(f), imp, replace_holes(a), s), // app
  // ... all other constructors
)
```

### Visitor API

```gleam
/// Generic term visitor
pub fn visit_term(
  term: Term,
  var: fn(Int, Span) -> Term,
  hole: fn(Int, Span) -> Term,
  lam: fn(List(String), #(String, Term), Term, Span) -> Term,
  pi: fn(List(String), String, Term, Term, Span) -> Term,
  app: fn(Term, List(Term), Term, Span) -> Term,
  match: fn(Term, Term, List(Case), Span) -> Term,
  ctr: fn(String, Term, Span) -> Term,
  rcd: fn(List(#(String, Term)), Span) -> Term,
  dot: fn(Term, String, Span) -> Term,
  ann: fn(Term, Term, Span) -> Term,
  call: fn(String, List(#(Term, Term)), Term, Span) -> Term,
  comptime: fn(Term, Span) -> Term,
  fix: fn(String, Term, Span) -> Term,
  let_: fn(String, Term, Term, Span) -> Term,
  typ: fn(Int, Span) -> Term,
  lit: fn(LitValue, Span) -> Term,
  lit_t: fn(LitType, Span) -> Term,
  unit: fn(Span) -> Term,
  err: fn(String, Span) -> Term,
) -> Term

/// Generic value visitor (for evaluation)
pub fn visit_value(
  value: Value,
  vtyp: fn(Int) -> Value,
  vlit: fn(Literal) -> Value,
  vneut: fn(Head, List(Elim)) -> Value,
  vrcd: fn(List(#(String, Value))) -> Value,
  vlam: fn(List(String), String, Env, Term) -> Value,
  vpi: fn(List(String), String, Env, Value, Term) -> Value,
  vctr: fn(String, Value) -> Value,
  vunit: fn() -> Value,
  vcall: fn(String, List(Value), Value) -> Value,
  vfix: fn(String, Env, Term) -> Value,
) -> Value
```

### Visitor Tests

```gleam
should("replace all holes with vars using visitor") {
  let term = Lam(("x", Hole(-1)), App(Hole(1), Var(0)))
  let result = visit_term(
    term,
    fn(i, s) -> Var(i, s),
    fn(id, s) -> Var(id, s),  // Replace holes with vars
    fn(imp, p, b, s) -> Lam(imp, p, visit_children(b), s),
    // ... other constructors
  )
  result == Lam(("x", Var(-1)), App(Var(1), Var(0)))
}

should("count holes in term using visitor") {
  let term = Lam(("x", Hole(-1)), App(Hole(1), Var(0)))
  let count = visit_term(
    term,
    fn(i, s) -> 0,
    fn(id, s) -> 1,  // Count each hole
    fn(imp, p, b, s) -> { count_children(b) },
    // ... other constructors
  )
  count == 2
}
```

## Color Module (core/color.gleam)

ANSI color codes for terminal output:

```gleam
pub type Color {
  Reset
  Bold
  Red
  Green
  Yellow
  Blue
  Magenta
  Cyan
  White
}

pub fn color(c: Color) -> String
pub fn bold(text: String) -> String
pub fn red(text: String) -> String
pub fn green(text: String) -> String
// ... etc.
```

### Color Tests

```gleam
should("produce correct ANSI codes") {
  color(Red) == "\x1b[31m"
  color(Reset) == "\x1b[0m"
}

should("bold text correctly") {
  bold("hello") == "\x1b[1mhello\x1b[0m"
}
```

## List Utils (core/list_utils.gleam)

Shared list helper functions used across Core modules:

```gleam
/// Drop n elements from the front of a list
pub fn drop(list: List(a), n: Int) -> List(a)

/// Take n elements from the front of a list
pub fn take(list: List(a), n: Int) -> List(a)

/// Zip two lists
pub fn zip(list1: List(a), list2: List(b)) -> List(#(a, b))

/// Zip three lists
pub fn zip3(list1: List(a), list2: List(b), list3: List(c)) -> List(#(a, b, c))

/// Interleave two lists
pub fn intersperse(list: List(a), separator: a) -> List(a)

/// Reverse a list
pub fn reverse(list: List(a)) -> List(a)

/// Apply a function to each element, accumulating state
pub fn foldl(fn: fn(a, b) -> a, initial: a, list: List(b)) -> a

/// Apply a function to each element, accumulating state from right
pub fn foldr(fn: fn(a, b) -> a, initial: a, list: List(b)) -> a
```

## AST String (core/ast_string.gleam)

Debug stringification for Core terms and values:

```gleam
/// Convert a Core term to a debug string
pub fn term_to_string(term: Term) -> String

/// Convert a Core value to a debug string
pub fn value_to_string(value: Value) -> String

/// Convert a pattern to a debug string
pub fn pattern_to_string(pattern: Pattern) -> String
```

### AST String Tests

```gleam
should("format lambda term") {
  let term = Lam(("x", Hole(-1)), Var(0))
  term_to_string(term) == "(λ(x: ?). x)"
}

should("format application term") {
  let term = App(Var(0), Var(1))
  term_to_string(term) == "(x y)"
}

should("format pi type term") {
  let term = Pi(Var(0), Var(1))
  term_to_string(term) == "Π(x: ?). y"
}

should("format value with neutral spine") {
  let value = VNeut(HVar(0), [EApp(VLit(ILit(42)))])
  value_to_string(value) == "x 42"
}
```
