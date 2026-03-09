# FFI and Comptime Implementation

> **Status**: ✅ Implemented - Core functionality complete
> **Last Updated**: March 2025

---

## Status

### What's Working

- ✅ `Call` and `Comptime` term constructors
- ✅ `VCall` value constructor for deferred runtime calls
- ✅ `Builtin` type with `Option(Value)` return
- ✅ `Permission` type (AllowRead, AllowWrite)
- ✅ Permission checking with Write-fulfills-Read
- ✅ Default builtins (arithmetic, comparison, logical)
- ✅ `eval()`, `comptime_eval()`, `infer()` handle Call/Comptime
- ✅ `VCall` quotes to `Call`
- ✅ **263 tests passing**

### What's Pending

- [ ] More permission types (AllowEnv, AllowNet, AllowExec)
- [ ] Impure builtins (read_file, write_file, get_env, now)
- [ ] Backend integration (JavaScript, Python, WebAssembly)
- [ ] Caching and incremental compilation
- [ ] `comptime` keyword in surface syntax (grammar support)

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[02-syntax.md](./02-syntax.md)** for syntax specification
- See **[../../src/core/syntax.gleam](../../src/core/syntax.gleam)** for grammar-derived syntax

---

## Design Philosophy

1. **Pure Builtins**: Built-in functions are pure `fn(List(Value)) -> Option(Value)` - no State needed
2. **No Arity Tracking**: Implementation handles arity - no need to store it in Builtin type
3. **Lazy Evaluation**: Unknown FFI functions and non-concrete args return `VCall` (deferred to runtime)
4. **Explicit Comptime**: `comptime` keyword for compile-time evaluation blocks
5. **Impure Allowed**: Comptime can execute IO with proper permissions
6. **Error Handling**: Comptime errors return `VErr` + add `ComptimePermissionDenied` to `State.errors`
7. **Simple Permissions**: AllowRead and AllowWrite (extensible as needed)
8. **Write Fulfills Read**: Having Write permission implicitly grants Read permission (but not vice versa)

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                     Compiler Pipeline                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Source → Parse → Elaborate (infer/check) → Codegen            │
│                │    │                          │                 │
│                │    └─ Returns #(Value, Type, State)            │
│                │       - Value is normalized/evaluated          │
│                │       - Comptime blocks resolved here          │
│                │       - Unknown FFI → VCall (runtime defer)    │
│                │       - Non-concrete args → VCall (defer)      │
│                └─ Raw AST with Call/Comptime nodes               │
│                                                                  │
│  Codegen → Backend Module (user or official)                     │
│            └─ Maps VCall to target runtime calls                 │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Core Data Structures

### Term Extensions

```gleam
pub type TermData {
  // ... existing constructors

  /// Built-in function call (runtime or comptime)
  /// If FFI not found during eval, returns VCall (deferred to runtime)
  Call(name: String, args: List(Term))

  /// Compile-time evaluation block
  Comptime(term: Term)
}
```

### Value Extensions

```gleam
pub type Value {
  // ... existing constructors

  /// Built-in function call deferred to runtime
  /// Created when:
  /// - FFI not found during eval
  /// - Arguments are not concrete (holes, variables, etc.)
  VCall(
    name: String,
    args: List(Value),
  )
}
```

### Builtin Type

```gleam
/// Permission for compile-time operations
/// Extensible - add new permission types as needed
pub type Permission {
  AllowRead(path: String)
  AllowWrite(path: String)
  // Future: AllowEnv, AllowNet, AllowExec, etc.
}

/// Built-in function definition
/// The impl function returns:
/// - Some(result) when arguments are concrete and computation succeeds
/// - None when arguments are not concrete (deferred to runtime)
pub type Builtin {
  Builtin(
    impl: fn(List(Value)) -> Option(Value),
    required_permissions: List(Permission),
  )
}

/// Host FFI registry
pub type FFI =
  List(#(String, Builtin))
```

### Config Type

```gleam
/// Compiler configuration
pub type Config {
  Config(
    /// Target backend module name (e.g., "backend/javascript")
    target: String,
    permissions: List(Permission),
  )
}
```

### State Extensions

```gleam
pub type State {
  State(
    hole: Int,
    var: Int,
    ctrs: CtrEnv,
    ctx: Context,
    sub: Subst,
    errors: List(Error),
    ffi: FFI,
    config: Config,
    // Note: comptime_errors merged into errors as ComptimePermissionDenied
  )
}
```

### Error Extensions

```gleam
pub type Error {
  // ... existing error types

  // Comptime errors
  ComptimePermissionDenied(
    operation: String,
    span: Span,
    required: List(Permission),
  )
}
```

---

## Permission System

### Permission Types

Currently implemented:
- `AllowRead(path: String)` - Read access to a path
- `AllowWrite(path: String)` - Write access to a path

### Permission Matching Rules

1. **Exact match**: `AllowRead("/foo")` matches `AllowRead("/foo")`
2. **Wildcard**: `AllowRead("*")` matches any `AllowRead` request
3. **Write fulfills Read**: `AllowWrite("/foo")` fulfills `AllowRead("/foo")`
4. **Read does NOT fulfill Write**: `AllowRead("/foo")` does NOT fulfill `AllowWrite("/foo")`

### Permission Checking

```gleam
/// Check if a required permission is granted
pub fn check_permission(
  required: Permission,
  granted: Permission,
) -> Bool {
  case required {
    AllowRead(req) ->
      case granted {
        AllowRead(grant) -> req == grant || grant == "*"
        AllowWrite(grant) -> req == grant || grant == "*"  // Write fulfills Read
        _ -> False
      }
    AllowWrite(req) ->
      case granted {
        AllowWrite(grant) -> req == grant || grant == "*"
        _ -> False  // Read does NOT fulfill Write
      }
  }
}

/// Check if all required permissions are granted
pub fn all_permissions_granted(
  required: List(Permission),
  granted: List(Permission),
) -> Bool {
  list.all(required, fn(r) {
    list.any(granted, fn(g) { check_permission(r, g) })
  })
}
```

### Usage Example

```gleam
// Grant read access to specific path
let config = Config("backend/javascript", [AllowRead("/config")])

// Grant write access (also allows read)
let config = Config("backend/javascript", [AllowWrite("*")])

// Grant all access with wildcards
let config = Config("backend/javascript", [
  AllowRead("*"),
  AllowWrite("*"),
])
```

---

## Builtin Implementations

### Default Builtins

All default builtins are pure and require no permissions:

```gleam
pub const ffi_build = [
  // Arithmetic
  #("add", Builtin(add_impl, [])),
  #("sub", Builtin(sub_impl, [])),
  #("mul", Builtin(mul_impl, [])),
  #("div", Builtin(div_impl, [])),
  #("mod", Builtin(mod_impl, [])),

  // Comparison
  #("eq", Builtin(eq_impl, [])),
  #("neq", Builtin(neq_impl, [])),
  #("lt", Builtin(lt_impl, [])),
  #("lte", Builtin(lte_impl, [])),
  #("gt", Builtin(gt_impl, [])),
  #("gte", Builtin(gte_impl, [])),

  // Logical
  #("and", Builtin(and_impl, [])),
  #("or", Builtin(or_impl, [])),
  #("not", Builtin(not_impl, [])),
]
```

### Implementation Pattern

All builtin implementations follow the same pattern:

```gleam
pub fn add_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a + b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a +. b)))
    _ -> None  // Non-concrete args deferred to runtime
  }
}
```

**Key points:**
- Return `Some(result)` for concrete arguments
- Return `None` for non-concrete arguments (holes, variables, etc.)
- The `eval` and `infer` functions handle creating `VCall` for `None` results

---

## Evaluation

### Runtime Evaluation (`eval`)

```gleam
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  case term.data {
    // ... other cases

    Call(name, args) -> {
      let arg_vals = list.map(args, eval(ffi, env, _))
      case list.key_find(ffi, name) {
        Ok(Builtin(impl, _)) -> {
          case impl(arg_vals) {
            Some(result) -> result
            None -> VCall(name, arg_vals)  // Defer to runtime
          }
        }
        Error(Nil) -> VCall(name, arg_vals)  // Unknown builtin
      }
    }

    Comptime(term) -> eval(ffi, env, term)  // Comptime evaluated at elaboration
  }
}
```

### Compile-time Evaluation (`comptime_eval`)

```gleam
pub fn comptime_eval(s: State, term: Term) -> #(Value, State) {
  case term.data {
    Call(name, args) -> {
      case list.key_find(s.ffi, name) {
        Ok(Builtin(impl, required_perms)) -> {
          case all_permissions_granted(required_perms, s.config.permissions) {
            True -> {
              let #(arg_vals, _, s1) = infer_args(s, args)
              case impl(arg_vals) {
                Some(result) -> #(result, s1)  // Concrete result
                None -> #(VCall(name, arg_vals), s1)  // Defer to runtime
              }
            }
            False -> {
              let err = ComptimePermissionDenied(name, term.span, required_perms)
              #(VErr, with_err(s, err))
            }
          }
        }
        Error(Nil) -> {
          let #(arg_vals, _, s1) = infer_args(s, args)
          #(VCall(name, arg_vals), s1)  // Unknown builtin
        }
      }
    }
    _ => {
      let #(val, _, s1) = infer(s, term)
      #(val, s1)
    }
  }
}
```

### Type Inference (`infer`)

```gleam
pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    // ... other cases

    Call(name, args) -> {
      case list.key_find(s.ffi, name) {
        Ok(Builtin(impl, _)) -> {
          let #(arg_vals, arg_tys, s1) = infer_args(s, args)
          case impl(arg_vals) {
            Some(result_val) -> {
              let result_ty = case arg_tys {
                [ty, ..] -> ty
                [] -> VErr
              }
              #(result_val, result_ty, s1)
            }
            None => {
              let result_ty = case arg_tys {
                [ty, ..] -> ty
                [] -> VErr
              }
              #(VCall(name, arg_vals), result_ty, s1)
            }
          }
        }
        Error(Nil) -> {
          let #(arg_vals, arg_tys, s1) = infer_args(s, args)
          let result_ty = case arg_tys {
            [ty, ..] -> ty
            [] -> VErr
          }
          #(VCall(name, arg_vals), result_ty, s1)
        }
      }
    }

    Comptime(term) -> {
      let #(val, s1) = comptime_eval(s, term)
      let quoted = quote(s1.ffi, 0, val, term.span)
      let #(val2, ty, s2) = infer(s1, quoted)
      #(val2, ty, s2)
    }
  }
}
```

---

## Quoting

`VCall` values quote back to `Call` terms:

```gleam
pub fn quote(ffi: FFI, lvl: Int, value: Value, s: Span) -> Term {
  case value {
    // ... other cases

    VCall(name, args) -> {
      Term(Call(name, list.map(args, fn(a) { quote(ffi, lvl, a, s) })), s)
    }
  }
}
```

---

## Usage Examples

### Pure Comptime (Constant Folding)

```gleam
// Source
let x = comptime add(2, 3)
let y = x + 1

// After elaboration
let x = 5  // Comptime evaluated and quoted
let y = 6  // Constant folded

// JavaScript output
const x = 5;
const y = 6;
```

### Non-Concrete Args (Deferred to Runtime)

```gleam
// Source
let x = comptime add(get_input(), 1)

// After elaboration (get_input() returns non-concrete value)
let x = add(get_input(), 1)  // Deferred to runtime

// JavaScript output
const x = add(get_input(), 1);
```

### Unknown Builtin (Deferred to Runtime)

```gleam
// Source
let x = custom_builtin(1, 2)  // Unknown FFI

// After elaboration
let x = VCall("custom_builtin", [1, 2])  // Deferred to runtime

// JavaScript output
const x = custom_builtin(1, 2);
```

### Permission Denied

```gleam
// Source (without --allow-read permission)
let config = comptime read_file("config.json")

// After elaboration
// Error: ComptimePermissionDenied("read_file", span, [AllowRead("config.json")])
```

### Permission Granted

```gleam
// Source (with --allow-read=./config permission)
let config = comptime read_file("./config/data.json")

// After elaboration
let config = "{\"port\": 8080}"  // File content embedded

// JavaScript output
const config = "{\"port\": 8080}";
```

---

## Implementation Status

### ✅ Implemented

1. **Core Data Structures**
   - `Call` and `Comptime` term constructors
   - `VCall` value constructor
   - `Builtin` type with `Option(Value)` return
   - `Permission` type (AllowRead, AllowWrite)
   - `Config` type with String target
   - `ComptimePermissionDenied` error

2. **Evaluation**
   - `eval()` handles Call and Comptime
   - `comptime_eval()` with permission checking
   - `infer()` handles Call and Comptime
   - Non-concrete args return `VCall`

3. **Permission System**
   - `check_permission()` with Write-fulfills-Read
   - `all_permissions_granted()`
   - Wildcard support (`"*"`)

4. **Default Builtins**
   - Arithmetic: add, sub, mul, div, mod
   - Comparison: eq, neq, lt, lte, gt, gte
   - Logical: and, or, not

5. **Quoting**
   - `VCall` quotes to `Call`

6. **Testing**
   - 263 tests passing
   - Builtin implementation tests
   - Permission checking tests
   - Comptime evaluation tests
   - VCall tests

### ⏳ Future Work

1. **More Permission Types**
   - `AllowEnv(var: String)` - Environment variables
   - `AllowNet(host: String)` - Network access
   - `AllowExec(cmd: String)` - Command execution

2. **Impure Builtins**
   - `read_file(path: String)` - Read file content
   - `write_file(path: String, content: String)` - Write file
   - `get_env(var: String)` - Get environment variable
   - `now()` - Current timestamp

3. **Backend Integration**
   - Official backends (JavaScript, Python, WebAssembly)
   - User-defined backend modules
   - VCall to runtime call mapping

4. **Caching**
   - Module hash calculation
   - Incremental compilation
   - Cache invalidation on permission changes

5. **Syntax Sugar**
   - `comptime` keyword in surface syntax (grammar support in progress)
   - Compile-time function execution
   - Macro system integration

---

## API Reference

### Core Functions

```gleam
// Evaluation
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value
pub fn comptime_eval(s: State, term: Term) -> #(Value, State)

// Type Checking
pub fn infer(s: State, term: Term) -> #(Value, Type, State)
pub fn check(s: State, term: Term, expected_ty: Type, ty_span: Span) -> #(Value, State)

// Permission Checking
pub fn check_permission(required: Permission, granted: Permission) -> Bool
pub fn all_permissions_granted(required: List(Permission), granted: List(Permission)) -> Bool

// Quoting
pub fn quote(ffi: FFI, lvl: Int, value: Value, s: Span) -> Term
```

### Default Builtins

```gleam
// Arithmetic
pub fn add_impl(args: List(Value)) -> Option(Value)
pub fn sub_impl(args: List(Value)) -> Option(Value)
pub fn mul_impl(args: List(Value)) -> Option(Value)
pub fn div_impl(args: List(Value)) -> Option(Value)
pub fn mod_impl(args: List(Value)) -> Option(Value)

// Comparison
pub fn eq_impl(args: List(Value)) -> Option(Value)
pub fn neq_impl(args: List(Value)) -> Option(Value)
pub fn lt_impl(args: List(Value)) -> Option(Value)
pub fn lte_impl(args: List(Value)) -> Option(Value)
pub fn gt_impl(args: List(Value)) -> Option(Value)
pub fn gte_impl(args: List(Value)) -> Option(Value)

// Logical
pub fn and_impl(args: List(Value)) -> Option(Value)
pub fn or_impl(args: List(Value)) -> Option(Value)
pub fn not_impl(args: List(Value)) -> Option(Value)
```

### Constants

```gleam
pub const ffi_build: FFI
pub const default_config: Config
pub const initial_state: State
```

---

## References

- [Normalization by Evaluation](https://en.wikipedia.org/wiki/Normalization_by_evaluation)
- [Zig Comptime](https://ziglang.org/documentation/master/#comptime)
- [Idris 2 Evaluation](https://idris2.readthedocs.io/en/latest/)
- [Rust Procedural Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
