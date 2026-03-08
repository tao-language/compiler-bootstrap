# FFI and Comptime Implementation Plan

> **Status**: Implemented - Core functionality complete
> **Goal**: Support pure/impure built-ins, compile-time evaluation, and pluggable backends
> **Last Updated**: After implementing generic grammar system with runtime formatter

---

## Design Philosophy

1. **Pure Builtins**: Built-in functions are pure `fn(List(Value)) -> Value` - no State needed
2. **No Arity Tracking**: Implementation handles arity - no need to store it in Builtin type
3. **Lazy Evaluation**: Unknown FFI functions return `VCall` (deferred to runtime)
4. **Explicit Comptime**: `comptime` keyword for compile-time evaluation blocks
5. **Impure Allowed**: Comptime can execute IO with proper permissions
6. **Error Handling**: Comptime errors return `VErr` + add to `State.errors`
7. **Backends as Modules**: User-creatable, importable backend modules

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                     Compiler Pipeline                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Source → Parse → Elaborate (infer/check) → Hash → Codegen     │
│                │    │                          │                 │
│                │    └─ Returns #(Value, Type, State)            │
│                │       - Value is normalized/evaluated          │
│                │       - Comptime blocks resolved here          │
│                │       - Unknown FFI → VCall (runtime defer)    │
│                └─ Raw AST with Comptime blocks                   │
│                                                                  │
│  Codegen → Backend Module (user or official)                     │
│            └─ Maps VCall to target runtime calls                 │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 1. Core Data Structures (Updated)

### 1.1 Term Extensions

```gleam
// In src/core/core.gleam

pub type TermData {
  // ... existing constructors

  /// Built-in function call (runtime or comptime)
  /// If FFI not found during eval, returns VCall (deferred to runtime)
  Call(name: String, args: List(Term))

  /// Compile-time evaluation block
  Comptime(term: Term)
}
```

### 1.2 Value Extensions

```gleam
// In src/core/core.gleam

pub type Value {
  // ... existing constructors

  /// Built-in function call deferred to runtime
  /// Created when FFI not found during eval
  VCall(
    name: String,
    arity: Int,  // Inferred from args at runtime
    collected_args: List(Value),
    impl: fn(List(Value)) -> Value,  // Pure function
  )
}
```

**Note**: The `arity` field in `VCall` is for runtime type checking only - it's inferred from the actual arguments passed, not stored in the Builtin definition.

### 1.3 Builtin Type (Simplified)

```gleam
// In src/core/core.gleam

/// Built-in function definition
pub type Builtin {
  Builtin(
    name: String,
    impl: fn(List(Value)) -> Value,  // Pure function - no State!
    required_permissions: List(Permission),
  )
}

/// Host FFI registry
pub type FFI =
  List(#(String, Builtin))
```

**Key Changes**:
- ❌ **Removed**: `arity: Int` - implementation handles arity checking
- ✅ **Changed**: `impl` is now pure `fn(List(Value)) -> Value`
- ✅ **Kept**: `required_permissions` for comptime permission checking

### 1.4 Compiler Configuration

```gleam
// New module: src/compiler/config.gleam

/// Compilation target
pub type Target {
  JavaScript
  Python
  WebAssembly
  Native(os: String, arch: String)
}

/// Permission for compile-time operations
pub type Permission {
  AllowRead(path: String)
  AllowWrite(path: String)
  AllowEnv(var: String)
  AllowNet(host: String)
  AllowExec(cmd: String)
}

/// Compiler configuration
pub type Config {
  Config(
    target: Target,
    permissions: List(Permission),
    /// Path to backend module (None = use default for target)
    backend_module: Option(String),
  )
}
```

### 1.5 State Extensions

```gleam
// In src/core/core.gleam (extend existing State)

pub type State {
  State(
    // ... existing fields
    hole: Int,
    var: Int,
    ctrs: CtrEnv,
    ctx: Context,
    sub: Subst,
    errors: List(Error),
    
    /// Host FFI registry (for built-in evaluation)
    ffi: FFI,

    /// Compiler configuration (for permissions, etc.)
    config: Config,

    /// Backend registry (for codegen)
    backend: BackendRegistry,

    /// Comptime execution errors
    comptime_errors: List(ComptimeError),
  )
}

pub type ComptimeError {
  ComptimeError(
    message: String,
    span: Span,
    /// Permission that was denied (if applicable)
    permission: Option(Permission),
  )
}
```

### 1.6 Backend Registry

```gleam
// New module: src/backend/registry.gleam

/// Built-in definition for codegen
pub type BuiltinDef {
  BuiltinDef(
    name: String,
    /// Code generation function
    codegen: fn(List(Term), Target) -> Result(String, String),
    /// Platform availability (None = all platforms)
    platforms: Option(List(Target)),
  )
}

/// Backend registry (from backend module)
pub type BackendRegistry {
  BackendRegistry(
    target: Target,
    builtins: Dict(String, BuiltinDef),
    /// Runtime module path (for user backends)
    runtime_module: Option(String),
  )
}
```

---

## 2. Elaboration (infer/check with Comptime)

### 2.1 Infer Function (Updated)

```gleam
// In src/core/core.gleam

pub fn infer(ffi: FFI, s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    // ... existing cases

    Comptime(inner_term) -> {
      // 1. Type-check the inner expression
      let #(inner_val, inner_ty, s1) = infer(ffi, s, inner_term)

      // 2. Evaluate using HOST FFIs (with permission checks)
      let #(result_val, s2) = host_eval(ffi, s1, inner_term)

      // 3. Quote the result back to a Term
      let quoted_term = quote(ffi, 0, result_val, s2)

      // 4. Return the concrete result (type + value)
      #(result_val, inner_ty, s2)
    }

    Call(name, args) -> {
      // Evaluate all arguments first
      let arg_vals = list.map(args, eval(ffi, env, _))
      
      // Look up the builtin and call it
      case list.key_find(ffi, name) {
        Ok(Builtin(_, impl, _)) -> impl(arg_vals)
        Error(Nil) -> {
          // FFI not found - return VCall (deferred to runtime)
          VCall(name, list.length(arg_vals), arg_vals, todo as "unknown builtin")
        }
      }
    }

    // ... other cases
  }
}
```

### 2.2 Check Function (Simplified)

```gleam
// In src/core/core.gleam

/// Check that a term has the expected type (verification direction).
///
/// Note: This function now delegates entirely to infer + unify.
/// The bidirectional structure is kept for API clarity and future extensions,
/// but currently all terms follow the same infer-then-unify pattern.
pub fn check(
  ffi: FFI,
  s: State,
  term: Term,
  expected_ty: Type,
  ty_span: Span,
) -> #(Value, State) {
  let #(value, inferred_ty, s) = infer(ffi, s, term)
  case unify(s, inferred_ty, expected_ty, term.span, ty_span) {
    Ok(s) -> #(force(s.ffi, s.sub, value), s)
    Error(e) -> #(VErr, with_err(s, e))
  }
}
```

**Note**: `check` is now just `infer` + `unify`. Most check-specific tests can be removed since they're redundant with infer tests. Keep only a handful to verify:
- Type mismatches are caught
- Spans are reported correctly for both term and type

### 2.3 Built-in Elaboration (Lazy Execution)

```gleam
// In src/core/core.gleam

fn elaborate_builtin(
  ffi: FFI,
  s: State,
  name: String,
  args: List(Term),
) -> #(Value, Type, State) {
  // Evaluate arguments
  let #(arg_vals, arg_tys, s1) = elaborate_args(ffi, s, args)

  // Try to execute (if impl available)
  case list.key_find(ffi, name) {
    Ok(Builtin(_, impl, _)) -> {
      let result = impl(arg_vals)
      #(result, compute_builtin_type(name, arg_tys), s1)
    }
    Error(Nil) => {
      // No implementation - return stuck built-in (VCall)
      #(
        VCall(name, list.length(arg_vals), arg_vals, todo as "unknown builtin"),
        compute_builtin_type(name, arg_tys),
        s1,
      )
    }
  }
}

fn elaborate_args(ffi: FFI, s: State, args: List(Term)) -> #(List(Value), List(Type), State) {
  elaborate_args_loop(ffi, args, [], [], s)
}

fn elaborate_args_loop(
  ffi: FFI,
  args: List(Term),
  vals: List(Value),
  tys: List(Type),
  s: State,
) -> #(List(Value), List(Type), State) {
  case args {
    [] -> #(list.reverse(vals), list.reverse(tys), s)
    [arg, ..rest] -> {
      let #(val, ty, s1) = infer(ffi, s, arg)
      elaborate_args_loop(ffi, rest, [val, ..vals], [ty, ..tys], s1)
    }
  }
}
```

---

## 3. Host Evaluation (Comptime Execution)

### 3.1 Host FFI Registry

```gleam
// In src/core/core.gleam

/// Default host FFIs
pub const default_builtins = [
  // Arithmetic (pure, always allowed)
  #("add", Builtin("add", add_impl, [])),
  #("sub", Builtin("sub", sub_impl, [])),
  #("mul", Builtin("mul", mul_impl, [])),
  #("div", Builtin("div", div_impl, [])),
  #("mod", Builtin("mod", mod_impl, [])),

  // Comparison (pure)
  #("eq", Builtin("eq", eq_impl, [])),
  #("neq", Builtin("neq", neq_impl, [])),
  #("lt", Builtin("lt", lt_impl, [])),
  #("lte", Builtin("lte", lte_impl, [])),
  #("gt", Builtin("gt", gt_impl, [])),
  #("gte", Builtin("gte", gte_impl, [])),

  // Logical (pure)
  #("and", Builtin("and", and_impl, [])),
  #("or", Builtin("or", or_impl, [])),
  #("not", Builtin("not", not_impl, [])),
]
```

### 3.2 Permission Checking

```gleam
// In src/host/ffi.gleam

fn check_permission(required: Permission, granted: List(Permission)) -> Bool {
  case required {
    AllowRead(req_path) -> {
      list.any(granted, fn(p) {
        case p {
          AllowRead("*") -> True
          AllowRead(path) -> string.starts_with(req_path, path)
          _ -> False
        }
      })
    }
    AllowEnv(req_var) -> {
      list.any(granted, fn(p) {
        case p {
          AllowEnv("*") -> True
          AllowEnv(var) -> var == req_var
          _ -> False
        }
      })
    }
    // ... other cases
  }
}

fn all_permissions_granted(required: List(Permission), granted: List(Permission)) -> Bool {
  list.all(required, fn(p) { check_permission(p, granted) })
}
```

### 3.3 Host Evaluation

```gleam
// In src/core/core.gleam

fn host_eval(ffi: FFI, s: State, term: Term) -> #(Value, State) {
  case term.data {
    Call(name, args) -> {
      case list.key_find(ffi, name) {
        Ok(Builtin(_, impl, required_perms)) -> {
          // Check permissions
          if !all_permissions_granted(required_perms, s.config.permissions) {
            let err = ComptimeError(
              "Permission denied for comptime operation: " <> name,
              term.span,
              required_perms |> list.first,
            )
            #(VErr, add_comptime_error(s, err))
          } else {
            // Evaluate arguments
            let #(arg_vals, _, s1) = elaborate_args(ffi, s, args)

            // Execute (pure function)
            let result = impl(arg_vals)
            #(result, s1)
          }
        }
        Error(_) => {
          // Unknown FFI - return VCall (deferred to runtime)
          let #(arg_vals, _, s1) = elaborate_args(ffi, s, args)
          #(VCall(name, list.length(arg_vals), arg_vals, todo as "unknown"), s1)
        }
      }
    }

    // Recursively evaluate other terms
    _ => infer(ffi, s, term)
  }
}
```

### 3.4 Example Host Implementations

```gleam
// In src/core/core.gleam

fn add_impl(args: List(Value)) -> Value {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> VLit(I32(a + b))
    [VLit(F64(a)), VLit(F64(b))] -> VLit(F64(a +. b))
    [a, b] -> {
      // Arguments not concrete - return stuck built-in
      VCall("add", 2, [a, b], add_impl)
    }
    _ -> VErr
  }
}

fn read_file_impl(args: List(Value)) -> Value {
  case args {
    [VLit(String(path))] -> {
      // Read file content
      case file.read(path) {
        Ok(content) -> VLit(String(content))
        Error(e) -> VErr  // Error handled by caller
      }
    }
    _ -> VErr
  }
}

fn now_impl(args: List(Value)) -> Value {
  // Get current timestamp (impure, but allowed)
  let timestamp = time.now() |> time.to_unix
  VLit(Int(timestamp))
}
```

---

## 4. Quoting (Value → Term)

```gleam
// In src/core/core.gleam

pub fn quote(ffi: FFI, lvl: Int, val: Value, s: Span) -> Term {
  case val {
    VTyp(k) -> Term(Typ(k), s)
    VLit(k) -> Term(Lit(k), s)
    VLitT(k) -> Term(LitT(k), s)
    
    VNeut(head, spine) -> {
      let head_term = quote_head(lvl, head, s)
      quote_neut(ffi, lvl, head_term, spine, s)
    }
    
    VRcd(fields) ->
      Term(Rcd(list.map(fields, fn(kv) { #(kv.0, quote(ffi, lvl, kv.1, s)) })), s)
    
    VCtr(tag, arg) -> Term(Ctr(tag, quote(ffi, lvl, arg, s)), s)
    
    VLam(name, env, body) -> {
      // Create a fresh neutral variable at the current level
      let fresh = VNeut(HVar(lvl), [])
      // Apply it to the body and evaluate
      let body_val = eval(ffi, [fresh, ..env], body)
      // Quote the result at level + 1
      let body_quote = quote(ffi, lvl + 1, body_val, body.span)
      Term(Lam(name, body_quote), s)
    }
    
    VPi(name, env, in_val, out_term) -> {
      // Quote the domain (already evaluated)
      let in_quote = quote(ffi, lvl, in_val, s)
      // Create a fresh neutral variable for the codomain
      let fresh = VNeut(HVar(lvl), [])
      let out_val = eval(ffi, [fresh, ..env], out_term)
      let out_quote = quote(ffi, lvl + 1, out_val, out_term.span)
      Term(Pi(name, in_quote, out_quote), s)
    }
    
    VCall(name, _, args, _) -> {
      // Quote stuck built-in with collected args
      Term(Call(name, list.map(args, fn(a) { quote(ffi, lvl, a, s) })), s)
    }
    
    VErr -> Term(Hole(-1), s)
  }
}
```

---

## 5. Backends as Modules

### 5.1 Backend Module Interface

```gleam
// User-created backend module: my_backend.gleam

import backend/registry

pub fn get_registry(target: Target) -> BackendRegistry {
  BackendRegistry(
    target: target,
    builtins: dict.from_list([
      #("print", BuiltinDef(
        name: "print",
        codegen: fn(args, _target) {
          Ok("console.log(" <> emit(args[0]) <> ")")
        },
        platforms: None,
      )),
      #("add", BuiltinDef(
        name: "add",
        codegen: fn(args, _target) {
          Ok(emit(args[0]) <> " + " <> emit(args[1]))
        },
        platforms: None,
      )),
    ]),
    runtime_module: Some("./runtime/my_backend_runtime.js"),
  )
}

fn emit(term: Term) -> String {
  // Emit term as JavaScript
  // ...
}
```

### 5.2 Official Backend: JavaScript

```gleam
// src/backend/javascript.gleam

import backend/registry

pub fn get_registry() -> BackendRegistry {
  BackendRegistry(
    target: JavaScript,
    builtins: dict.from_list([
      #("print", BuiltinDef(
        name: "print",
        codegen: fn(args, _target) {
          Ok("console.log(" <> emit_expr(args[0]) <> ")")
        },
        platforms: None,
      )),
      #("add", BuiltinDef(
        name: "add",
        codegen: fn(args, _target) {
          Ok(emit_expr(args[0]) <> " + " <> emit_expr(args[1]))
        },
        platforms: None,
      )),
      #("read_file", BuiltinDef(
        name: "read_file",
        codegen: fn(_args, _target) {
          Error("read_file must be used in comptime block for JavaScript target")
        },
        platforms: None,
      )),
    ]),
    runtime_module: None, // No runtime needed for JS
  )
}

fn emit_expr(term: Term) -> String {
  case term.data {
    Lit(Int(n)) -> int.to_string(n)
    Lit(String(s)) -> "\"" <> string.replace(s, "\"", "\\\"") <> "\""
    Call(name, args) -> {
      // Look up in registry
      // ...
    }
    // ... other cases
  }
}
```

### 5.3 Handling VCall at Codegen Time

```gleam
// In src/codegen/generator.gleam

fn emit_term(term: Term, gen: Generator) -> Result(String, String) {
  case term.data {
    Call(name, args) -> {
      case dict.get(gen.backend.builtins, name) {
        Ok(builtin) -> {
          // Check platform availability
          case builtin.platforms {
            Some(platforms) -> {
              if !list.contains(platforms, gen.target) {
                // Platform not supported - emit runtime error
                Ok(emit_runtime_error(gen.target, "Unsupported: " <> name))
              } else {
                builtin.codegen(args, gen.target)
              }
            }
            None -> builtin.codegen(args, gen.target)
          }
        }
        Error(_) -> {
          // Unknown built-in at codegen time
          // This means it was deferred to runtime (VCall)
          // Emit runtime call
          Ok(emit_runtime_call(name, args))
        }
      }
    }

    // ... other cases
  }
}

fn emit_runtime_call(name: String, args: List(Term)) -> String {
  // Emit as runtime function call
  name <> "(" <> string.join(list.map(args, emit_expr), ", ") <> ")"
}
```

---

## 6. Code Generation Pipeline

```gleam
// New module: src/codegen/generator.gleam

pub type Generator {
  Generator(
    backend: BackendRegistry,
    target: Target,
  )
}

pub fn generate(gen: Generator, term: Term) -> Result(String, String) {
  emit_term(term, gen)
}

fn emit_term(term: Term, gen: Generator) -> Result(String, String) {
  case term.data {
    Call(name, args) -> {
      case dict.get(gen.backend.builtins, name) {
        Ok(builtin) -> {
          // Check platform availability
          case builtin.platforms {
            Some(platforms) -> {
              if !list.contains(platforms, gen.target) {
                // Platform not supported - emit runtime error
                Ok(emit_runtime_error(gen.target, "Unsupported: " <> name))
              } else {
                builtin.codegen(args, gen.target)
              }
            }
            None -> builtin.codegen(args, gen.target)
          }
        }
        Error(_) -> {
          // Unknown built-in at codegen time
          // This means it was deferred to runtime (VCall)
          // Emit runtime call
          Ok(emit_runtime_call(name, args))
        }
      }
    }

    // ... other cases
  }
}
```

---

## 7. Caching and Determinism

### 7.1 Module Hash

```gleam
// New module: src/compiler/cache.gleam

pub type ModuleHash {
  ModuleHash(
    source_hash: String,
    imports_hash: String,
    comptime_hash: String, // Hash of elaborated AST
  )
}

pub fn calculate_hash(
  source: String,
  imports: List(ModuleHash),
  elaborated_ast: Term,
) -> ModuleHash {
  ModuleHash(
    source_hash: hash(source),
    imports_hash: hash(list.map(imports, fn(i) { i.source_hash })),
    comptime_hash: hash(elaborated_ast), // Includes quoted comptime results
  )
}
```

### 7.2 Handling Non-Determinism

```gleam
// Example: Timestamp (changes every compilation)
pub fn comptime_timestamp_example() {
  // Source
  let timestamp = comptime now()

  // After elaboration
  let timestamp = 1234567890 // Literal embedded

  // Module hash includes this literal
  // If timestamp changes, hash changes, module rebuilds
}

// Example: File content (deterministic if file doesn't change)
pub fn comptime_file_example() {
  // Source
  let config = comptime read_file("config.json")

  // After elaboration
  let config = "{\"port\": 8080}" // Content embedded

  // Module hash includes this content
  // If file changes, hash changes, module rebuilds
}
```

---

## 8. Implementation Phases

### Phase 1: Built-in Infrastructure (Week 1-2) ✅ COMPLETE

- [x] Add `Call(name, args)` to `TermData`
- [x] Add `VCall` to `Value`
- [x] Implement `add_impl`, `sub_impl`, etc. (pure arithmetic)
- [x] Update `infer` to handle `Call`
- [x] Add `ffi` to `State`
- [x] Make `Builtin` pure (no State in impl)
- [x] Remove `arity` from `Builtin`

### Phase 2: Comptime Blocks (Week 3-4)

- [ ] Add `Comptime(term)` to `TermData`
- [ ] Implement `host_eval` function
- [ ] Implement `quote` function (Value → Term)
- [ ] Update `infer` to handle `Comptime`
- [ ] Add permission checking to `State`

### Phase 3: Host FFIs (Week 5-6)

- [ ] Implement `read_file_impl`
- [ ] Implement `get_env_impl`
- [ ] Implement `now_impl` (timestamp)
- [ ] Add `ComptimeError` to `State.errors`
- [ ] Wire up comptime to use host FFIs

### Phase 4: Backend Modules (Week 7-8)

- [ ] Create `BackendRegistry` type
- [ ] Implement JavaScript backend
- [ ] Implement WebAssembly backend
- [ ] Add backend module loading
- [ ] Support user-created backends

### Phase 5: Caching (Week 9-10)

- [ ] Implement `ModuleHash` calculation
- [ ] Add cache lookup before codegen
- [ ] Implement incremental compilation
- [ ] Add cache invalidation on permission changes

---

## 9. Example Usage

### 9.1 Pure Comptime (Constant Folding)

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

### 9.2 File Reading at Compile-Time

```gleam
// Source (with --allow-read=./config permission)
let config = comptime read_file("config.json")
let port = parse_port(config)

// After elaboration
let config = "{\"port\": 8080}"  // File content embedded
let port = 8080  // Parsed at compile-time

// JavaScript output
const config = "{\"port\": 8080}";
const port = 8080;
```

### 9.3 Unknown FFI Deferred to Runtime

```gleam
// Source
let x = custom_builtin(1, 2)  // Unknown FFI

// After elaboration
let x = VCall("custom_builtin", 2, [1, 2], todo)  // Deferred to runtime

// JavaScript output
const x = custom_builtin(1, 2);  // Runtime call
```

### 9.4 Timestamp for Release

```gleam
// Source (impure comptime)
let release_time = comptime now()

// After elaboration
let release_time = 1234567890  // Timestamp embedded

// JavaScript output
const release_time = 1234567890;
```

### 9.5 Platform-Specific Built-in

```gleam
// Source
let data = fs_read("data.txt")  // Only works on Native target

// WebAssembly codegen
// (unreachable) ;; fs_read not supported on WASM
// Compiler warning: "fs_read is not available on WebAssembly target"

// Native codegen
const data = fs_read("data.txt");
```

### 9.6 User-Created Backend

```gleam
// my_java_backend.gleam
import backend/registry

pub fn get_registry() -> BackendRegistry {
  BackendRegistry(
    target: Custom("Java"),
    builtins: dict.from_list([
      #("print", BuiltinDef(
        name: "print",
        codegen: fn(args, _target) {
          Ok("System.out.println(" <> emit(args[0]) <> ")")
        },
        platforms: None,
      )),
    ]),
    runtime_module: Some("./runtime/java_runtime.jar"),
  )
}

// Compile with custom backend
mylang build --backend=./my_java_backend.gleam
```

---

## 10. Security Considerations

### 10.1 Permission Model

```bash
# Compile with permissions
mylang build --allow-read=./config --allow-env=API_KEY

# Without permissions, comptime file reads fail
mylang build
# Error: Permission denied for comptime operation: read_file
# Required: AllowRead("./config")
# Granted: []
```

### 10.2 Sandboxing

- Comptime execution runs in the compiler process
- No network access by default
- File access restricted to explicit paths
- Environment variables must be explicitly allowed

---

## 11. Integration with Existing Code

### 11.1 Updated Function Signatures

All evaluation functions now take `ffi: FFI` as first argument:

```gleam
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value
pub fn quote(ffi: FFI, lvl: Int, value: Value, s: Span) -> Term
pub fn normalize(ffi: FFI, env: Env, term: Term, s: Span) -> Term
pub fn do_app(ffi: FFI, fun: Value, arg: Value) -> Value
pub fn force(ffi: FFI, sub: Subst, value: Value) -> Value
pub fn apply_spine(ffi: FFI, value: Value, spine: List(Elim)) -> Value
```

### 11.2 Test Updates Required

All tests need to be updated to pass `default_builtins` as first argument:

```gleam
// Before
c.eval([], term)
c.quote(0, value, s1)
c.normalize([], term, s1)

// After
c.eval(c.default_builtins, [], term)
c.quote(c.default_builtins, 0, value, s1)
c.normalize(c.default_builtins, [], term, s1)
```

### 11.3 Check Tests Simplification

Since `check` is now just `infer` + `unify`, most check-specific tests are redundant. Keep only:

1. **Type mismatch detection** - Verify errors are caught
2. **Span reporting** - Verify both term and type spans are correct
3. **Error accumulation** - Verify multiple errors are collected

Remove tests that just duplicate infer tests.

---

## 12. Testing Strategy

### 12.1 Call Tests (New)

Add comprehensive tests for `Call` term:

```gleam
// eval_call_known_test()
// - Known FFI executes correctly
// - Arguments evaluated before call

// eval_call_unknown_test()
// - Unknown FFI returns VCall
// - Arguments still evaluated

// quote_call_test()
// - VCall quotes back to Call term
// - Args quoted recursively

// unify_call_test()
// - VCall unifies with same VCall
// - VCall doesn't unify with different VCall

// infer_call_test()
// - Known FFI infers correct type
// - Unknown FFI infers VCall type
```

### 12.2 Check Tests (Reduced)

Keep only essential check tests:

```gleam
// check_type_mismatch_test()
// - Verify type mismatch caught
// - Verify span reported correctly

// check_error_accumulation_test()
// - Verify multiple errors collected

// check_span_reporting_test()
// - Verify both term and type spans correct
```

---

## 13. Open Questions (Answered)

| Question | Decision |
|----------|----------|
| Store arity in Builtin? | **No** - implementation handles it |
| Unknown FFI during eval? | **Return VCall** (deferred to runtime) |
| Builtin impl signature? | **Pure** `fn(List(Value)) -> Value` |
| Comptime explicit or inferred? | **Explicit** (`comptime` keyword) |
| Impure built-ins in comptime? | **Yes** (with permissions) |
| Comptime errors? | **VErr + State.errors** |
| Backends pluggable? | **Yes** (as modules) |

---

## 14. References

- [Normalization by Evaluation](https://en.wikipedia.org/wiki/Normalization_by_evaluation)
- [Zig Comptime](https://ziglang.org/documentation/master/#comptime)
- [Idris 2 Evaluation](https://idris2.readthedocs.io/en/latest/)
- [Rust Procedural Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
