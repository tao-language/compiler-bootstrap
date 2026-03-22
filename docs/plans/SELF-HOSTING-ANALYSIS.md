# Self-Hosting Analysis: Writing Tao in Tao

> **Goal**: Analyze what's needed to write the Tao compiler in Tao itself
> **Status**: 📋 Analysis document
> **Date**: March 2026

---

## Executive Summary

**Can you write Tao on itself today?** 

**Short answer**: ❌ **No** - but you're 60-70% of the way there.

**Long answer**: The core language features are mostly complete, but you're missing:
1. **Standard library** (prelude, collections, string operations)
2. **Pattern matching syntax** (desugaring works, but surface syntax is limited)
3. **Let bindings** (partially working, needs full implementation)
4. **Module system** (imports work, but need circular dependency handling)
5. **Error messages** (Tao-specific errors need better surfacing)

**Estimated effort to self-hosting**: 4-6 weeks of focused development

---

## Current State: What Works ✅

### Language Features (90% Complete)

| Feature | Status | Notes |
|---------|--------|-------|
| **Functions** | ✅ | `fn add(x: I32) -> I32 { x + 1 }` |
| **Overloading** | ✅ | Type-based dispatch via implicit args |
| **Operators** | ✅ | `+`, `-`, `*`, `/` with correct precedence |
| **Type annotations** | ✅ | Optional, inferred when omitted |
| **Imports** | ✅ | `import list` works |
| **Test framework** | ✅ | `test "name" { expr }` |
| **Run statements** | ✅ | `run expr` for evaluation |

### Core Language (100% Complete)

| Feature | Status | Notes |
|---------|--------|-------|
| **Dependent types** | ✅ | Full support via Core |
| **Normalization** | ✅ | NbE working correctly |
| **Exhaustiveness** | ✅ | Maranget's algorithm |
| **Error recovery** | ✅ | Continues after errors |
| **Source snippets** | ✅ | Error messages with context |

### Tooling (80% Complete)

| Tool | Status | Notes |
|------|--------|-------|
| **CLI** | ✅ | `gleam run check/run file.tao` |
| **Error reporting** | ✅ | Source snippets, error codes |
| **Formatter** | ✅ | Document algebra based |
| **Test runner** | ✅ | Golden file tests |

---

## What's Missing: Blockers for Self-Hosting ❌

### 1. Standard Library (0% Complete) - **CRITICAL**

**Problem**: No prelude, no collections, no string operations.

**What you need to write a compiler**:
```tao
// Can't do this yet:
import list.{map, filter, fold}
import string.{join, split, length}
import option.{Option, Some, None}
import result.{Result, Ok, Err}

// Need:
List(String)     // For tokens, AST nodes
String           // For source code, error messages
Option(a)        // For partial functions
Result(a, e)     // For error handling
Map(k, v)        // For symbol tables
```

**Estimated effort**: 2-3 weeks

**Phases**:
1. **Prelude** (3-4 days): Bool, Option, Result, Ordering
2. **Numeric** (2-3 days): Int, Float operations, numeric hierarchy
3. **Collections** (1 week): List, Vector, Map, Set
4. **String** (3-4 days): String type, concatenation, interpolation
5. **I/O** (2-3 days): File reading, CLI args

---

### 2. Pattern Matching Syntax (80% Complete) - **MOSTLY COMPLETE**

**Problem**: Core supports it, Tao surface syntax is mostly complete.

**What works**:
```tao
// ✅ Wildcard pattern
match x {
  | _ -> 100
}

// ✅ Variable pattern
match x {
  | n -> n + 1
}

// ✅ Literal pattern
match x {
  | 0 -> 1
  | 1 -> 2
  | _ -> x
}

// ✅ Constructor pattern
match opt {
  | Some(x) -> x
  | None -> 0
}

// ✅ Match guards
match x {
  | n if n > 0 && n < 10 -> 1
  | _ -> 0
}
```

**What's partially working**:
- ❌ Tuple patterns: `(a, b)` - AST support exists, grammar needs work
- ❌ Record patterns: `{x, y}` - AST support exists, grammar needs work  
- ❌ List patterns: `[h, ..t]` - AST support exists, grammar needs work
- ❌ Or patterns: `Some(0) | None` - AST support exists, grammar needs work
- ❌ As patterns: `x @ Some(_)` - AST support exists, grammar needs work

**What's working**:
- ✅ Core match with full pattern support
- ✅ Exhaustiveness checking
- ✅ Guard expressions
- ✅ Basic patterns (wildcard, variable, literal, constructor)

**Estimated effort**: 2-3 days for remaining patterns

**Status**: The AST and desugarer fully support all pattern types. The grammar rules need to be fixed to parse them correctly. This is a matter of updating the grammar, not the core logic.

---

### 3. Let Bindings (60% Complete) - **IMPORTANT**

**Problem**: Basic let works, but needs full feature set.

**What you need**:
```tao
// Partially works:
let x = 42
let mut count = 0

// Need:
let #(head, tail) = list  // Pattern matching in let
let x: List(Int) = []     // Type annotations
let x = { ... }           // Block expressions
```

**What's working**:
- ✅ Simple let bindings
- ✅ Mutable bindings (`let mut`)
- ✅ Desugaring to core

**What's missing**:
- ❌ Pattern matching in let
- ❌ Type annotations (partially working)
- ❌ Let rec for recursive definitions
- ❌ Let in expressions (local bindings)

**Estimated effort**: 3-5 days

---

### 4. Module System (70% Complete) - **IMPORTANT**

**Problem**: Imports work, but circular dependencies and exports need work.

**What you need**:
```tao
// Works:
import list
import option.{Option, Some, None}

// Need:
export fn public_func() { ... }  // Explicit exports
import compiler.{type AST, parse} // Selective imports
// Circular: parser imports lexer, lexer imports parser (via tokens)
```

**What's working**:
- ✅ Basic imports
- ✅ Import resolution
- ✅ Modules as records

**What's missing**:
- ❌ Explicit exports
- ❌ Circular dependency handling
- ❌ Re-exports
- ❌ Module paths (`import compiler.syntax.lexer`)

**Estimated effort**: 1 week

---

### 5. Error Messages (50% Complete) - **NICE TO HAVE**

**Problem**: Core errors work, but Tao-specific errors need better integration.

**What you need**:
```tao
// Should show:
Error: Function 'factorial' not found
  ┌─ factorial.tao:5:3
  │
5 │ factorial(5)
  │ ^^^^^^^^^ Not defined in scope
  │
  💡 Did you mean to define it with 'fn'?
  fn factorial(n: Int) -> Int { ... }
```

**What's working**:
- ✅ Core type errors with snippets
- ✅ Parse errors with locations
- ✅ Error codes (E0001, etc.)

**What's missing**:
- ❌ Tao-specific error messages
- ❌ "Did you mean?" suggestions
- ❌ Multi-span errors (e.g., type mismatch)
- ❌ Color terminal support

**Estimated effort**: 1 week (can be done incrementally)

---

## What's Nice to Have (Not Blockers) ⏳

### 1. Better Type Inference

**Current**: Bidirectional typing works, but sometimes needs annotations.

**Better**: Full Hindley-Milner with local type inference.

**Impact**: Less annotation boilerplate, but not required.

---

### 2. Type Classes / Traits

**Current**: Overloading via implicit type parameters.

**Better**: Haskell-style type classes.

**Impact**: Cleaner numeric hierarchy, but workarounds exist.

---

### 3. Better IDE Support

**Current**: None (CLI only).

**Better**: LSP server with:
- Go to definition
- Type on hover
- Auto-complete
- Find references

**Impact**: Developer experience, but not required for self-hosting.

---

## User Experience: Implementing a Dependent Type Checker

### The Good ✅

1. **Core is solid**: Once you desugar to Core, everything works
2. **Error messages**: Core errors are excellent (snippets, codes, hints)
3. **Normalization**: NbE is efficient and correct
4. **Exhaustiveness**: Maranget's algorithm just works
5. **Test framework**: Golden file tests are great for compilers

### The Challenging ⚠️

1. **De Bruijn indices**: Correct but hard to debug
   ```tao
   // Can't write:
   λx. λy. x  // Need to track indices manually
   
   // Core representation:
   Lam("x", Lam("y", Var(1)))  // Index 1 = "x" (2 binders out)
   ```

2. **Type-level computation**: Powerful but complex
   ```tao
   // This works but is mind-bending:
   fn vec_append(n: Int, m: Int, xs: Vec(n, a), ys: Vec(m, a)) -> Vec(n + m, a)
   
   // Type checker must evaluate n + m at type level
   ```

3. **Unification errors**: Can be cryptic
   ```
   Type error: cannot unify ?A with List(?B)
   
   // What is ?A? Where did it come from?
   // Need better hole tracking
   ```

### The Missing 😕

1. **Debugging tools**: No REPL, no step-through debugger
2. **Performance profiling**: No way to see where time is spent
3. **Visualization**: Can't see the type derivation tree

---

## Roadmap to Self-Hosting

### Phase 1: Prelude (Week 1-2)

**Goal**: Basic types and operations

```tao
// lib/prelude/bool.tao
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

// lib/prelude/option.tao
type Option(a) = Some(a) | None

fn map(opt: Option(a), f: (a) -> b) -> Option(b) {
  match opt {
    | Some(x) -> Some(f(x))
    | None -> None
  }
}

// lib/prelude/result.tao
type Result(a, e) = Ok(a) | Err(e)
```

**Milestone**: Can write basic functions with error handling

---

### Phase 2: Collections (Week 3)

**Goal**: List, Map for AST and symbol tables

```tao
// lib/collections/list.tao
type List(a) = Cons(a, List(a)) | Nil

fn map(xs: List(a), f: (a) -> b) -> List(b) {
  match xs {
    | Cons(x, xs) -> Cons(f(x), map(xs, f))
    | Nil -> Nil
  }
}

fn fold(xs: List(a), acc: b, f: (b, a) -> b) -> b {
  match xs {
    | Cons(x, xs) -> fold(xs, f(acc, x), f)
    | Nil -> acc
  }
}
```

**Milestone**: Can represent ASTs and environments

---

### Phase 3: String (Week 4)

**Goal**: String operations for source code

```tao
// lib/string/string.tao
type String = ...  // Backed by Core FFI

fn concat(s1: String, s2: String) -> String
fn length(s: String) -> Int
fn split(s: String, sep: String) -> List(String)
fn join(xs: List(String), sep: String) -> String
```

**Milestone**: Can manipulate source code, error messages

---

### Phase 4: Pattern Matching Syntax (Week 5)

**Goal**: Surface syntax for match

```tao
// parser.gleam (or parser.tao!)
rule("Match", [
  seq([
    keyword("match"),
    ref("Expr"),
    keyword("{"),
    many(ref("Case")),
    keyword("}"),
  ]),
  fn(values) { make_match(values) },
])
```

**Milestone**: Can write compiler in readable syntax

---

### Phase 5: Bootstrap Compiler (Week 6)

**Goal**: Write Tao compiler in Tao

```tao
// compiler/lexer.tao
pub fn tokenize(source: String) -> Result(List(Token), LexError) {
  // ...
}

// compiler/parser.tao
pub fn parse(tokens: List(Token)) -> Result(AST, ParseError) {
  // ...
}

// compiler/main.tao
pub fn main() {
  let args = get_args()
  let source = read_file(args.file)
  let tokens = tokenize(source)
  let ast = parse(tokens)
  let core = desugar(ast)
  let #(_val, _typ, state) = infer(initial_state, core)
  
  match state.errors {
    | [] -> println("✓ Type checking passed")
    | errors -> print_errors(errors)
  }
}
```

**Milestone**: **Self-hosting achieved!** 🎉

---

## Comparison with Other Languages

| Language | Time to Self-Host | Lines of Code | Notes |
|----------|-------------------|---------------|-------|
| **Rust** | 10 months | ~30k LOC | Strong type system helped |
| **Lean 4** | 3 years | ~50k LOC | Dependent types, large stdlib |
| **Idris 2** | 5 years | ~40k LOC | Bootstrapped from Idris 1 |
| **Tao (estimated)** | 6 weeks | ~5k LOC | Reuses Core, smaller scope |

**Key insight**: You're standing on the shoulders of `src/core/core.gleam` (~3,400 lines). That's the hard part—dependent types, normalization, unification, exhaustiveness. Tao is just the surface syntax.

---

## Recommendations

### For Self-Hosting ASAP

1. **Focus on Prelude** (2 weeks) - Without collections and String, you can't write a compiler
2. **Add pattern matching syntax** (1 week) - Recursive functions are painful without it
3. **Complete let bindings** (3 days) - Needed for local variables
4. **Write incremental pieces** - Start with lexer, then parser, etc.

### For Best Developer Experience

1. **Add REPL** (1 week) - Essential for experimentation
2. **Better error messages** (1 week) - "Did you mean?" suggestions
3. **IDE integration** (2 weeks) - LSP server for editor support
4. **Documentation generator** (1 week) - Like Rust's rustdoc

### For Production Readiness

1. **Performance optimization** (2-3 weeks) - Profile and optimize hot paths
2. **Comprehensive stdlib** (4-6 weeks) - Full collections, I/O, concurrency
3. **Package manager** (2-3 weeks) - Dependency management
4. **Build system** (1-2 weeks) - Incremental compilation

---

## Conclusion

**Can you write Tao on itself today?** No, but you're close.

**What's the critical path?**
1. Standard library (2-3 weeks)
2. Pattern matching syntax (1 week)
3. Let bindings (3 days)

**Total estimated time**: 4-6 weeks

**Is it worth it?** Absolutely. Self-hosting is a milestone that proves the language is usable. Plus, you'll dogfood your own error messages, which will make them better.

**What's the hardest part?** Not the dependent types—Core handles that. The hard part is the **mundane stuff**: strings, collections, I/O. Every language needs these, and they're not glamorous, but you can't write a compiler without them.

**Final advice**: Start with the prelude. Write `List`, `Option`, `Result`, and `String`. Then write the lexer. Then the parser. One step at a time, and you'll have a self-hosting compiler before you know it.

---

## Related Documents

- **[stdlib/01-overview.md](./stdlib/01-overview.md)** - Standard library roadmap
- **[stdlib/02-prelude.md](./stdlib/02-prelude.md)** - Prelude specification
- **[stdlib/03-numeric.md](./stdlib/03-numeric.md)** - Numeric hierarchy
- **[tao/04-desugaring.md](./tao/04-desugaring.md)** - Desugaring rules
- **[tao/10-overloading-design.md](./tao/10-overloading-design.md)** - Overloading design
