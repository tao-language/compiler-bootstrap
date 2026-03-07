# FFI and Comptime Implementation Plan

> **Status**: Design Document (Updated for existing architecture)
> **Goal**: Support pure/impure built-ins, compile-time evaluation, and pluggable backends

---

## Design Philosophy

1. **Elaboration**: `infer` and `check` already return normalized `Value` - comptime integrates naturally
2. **Explicit Comptime**: `comptime` keyword for compile-time evaluation blocks
3. **Impure Allowed**: Comptime can execute IO with proper permissions
4. **Error Handling**: Comptime errors return `VErr` + add to `State.errors`
5. **Backends as Modules**: User-creatable, importable backend modules

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
│                └─ Raw AST with Comptime blocks                   │
│                                                                  │
│  Codegen → Backend Module (user or official)                     │
│            └─ Maps VBuiltIn to target code                       │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 1. Core Data Structures (Aligned with core.gleam)

### 1.1 Term Extensions

```gleam
// In src/core/core.gleam

pub type TermData {
  // ... existing constructors
  
  /// Built-in function call (runtime)
  BuiltIn(name: String, args: List(Term))
  
  /// Compile-time evaluation block
  Comptime(term: Term)
}
```

### 1.2 Value Extensions

```gleam
// In src/core/core.gleam

pub type Value {
  // ... existing constructors
  
  /// Built-in function (first-class, knows its arity)
  VBuiltIn(
    name: String,
    arity: Int,
    collected_args: List(Value),
    impl: fn(List(Value), State) -> #(Value, State),
  )
}
```

### 1.3 Compiler Configuration

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

### 1.4 State Extensions

```gleam
// In src/core/core.gleam (extend existing State)

pub type State {
  State(
    // ... existing fields
    
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

### 1.5 Backend Registry

```gleam
// New module: src/backend/registry.gleam

/// Built-in definition for codegen
pub type BuiltinDef {
  BuiltinDef(
    name: String,
    arity: Int,
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

pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    // ... existing cases
    
    Comptime(inner_term) -> {
      // 1. Type-check the inner expression
      let #(inner_val, inner_ty, s1) = infer(s, inner_term)
      
      // 2. Evaluate using HOST FFIs (with permission checks)
      let #(result_val, s2) = host_eval(s1, inner_term)
      
      // 3. Quote the result back to a Term
      let quoted_term = quote(0, result_val, s2)
      
      // 4. Return the concrete result (type + value)
      #(result_val, inner_ty, s2)
    }
    
    BuiltIn(name, args) -> {
      case dict.get(s.backend.builtins, name) {
        Ok(builtin) -> {
          // Elaborate built-in (lazy execution)
          elaborate_builtin(s, builtin, args)
        }
        Error(_) -> {
          // Unknown built-in - return error
          let err = ComptimeError("Unknown built-in: " <> name, term.span, None)
          #(VErr, VErr, add_comptime_error(s, err))
        }
      }
    }
    
    // ... other cases
  }
}
```

### 2.2 Check Function (Updated)

```gleam
// In src/core/core.gleam

pub fn check(
  s: State,
  term: Term,
  expected_ty: Value,
  ty_span: Span,
) -> #(Value, State) {
  case term.data {
    Comptime(inner_term) -> {
      // Comptime blocks evaluate regardless of check vs infer
      let #(val, ty, s1) = infer(s, inner_term)
      
      // Unify with expected type
      case unify(ty, expected_ty, s1) {
        Ok(s2) -> #(val, s2)
        Error(_) -> {
          // Type mismatch - return VErr
          #(VErr, s1)
        }
      }
    }
    
    // ... other cases
  }
}
```

### 2.3 Built-in Elaboration (Lazy Execution)

```gleam
// In src/core/core.gleam

fn elaborate_builtin(
  s: State,
  builtin: BuiltinDef,
  args: List(Term),
) -> #(Value, Type, State) {
  // Evaluate arguments
  let #(arg_vals, arg_tys, s1) = elaborate_args(s, args)
  
  // Check arity
  if list.length(arg_vals) != builtin.arity {
    let err = ComptimeError(
      "Built-in `" <> builtin.name <> "` expects " <> int.to_string(builtin.arity) <> " arguments",
      args |> list.last |> result.map(fn(t) { t.span }) |> result.unwrap(Span(0, 0)),
      None,
    )
    #(VErr, VErr, add_comptime_error(s1, err))
  } else {
    // Try to execute (if host_impl available)
    case builtin.host_impl {
      Some(impl) -> {
        let #(result, s2) = impl(arg_vals, s1)
        case result {
          Ok(val) -> #(val, compute_builtin_type(builtin, arg_tys), s2)
          Error(_) -> #(VErr, VErr, s2)
        }
      }
      None -> {
        // No host implementation - return stuck built-in
        #(
          VBuiltIn(builtin.name, builtin.arity, [], builtin.host_impl),
          compute_builtin_type(builtin, arg_tys),
          s1,
        )
      }
    }
  }
}

fn elaborate_args(s: State, args: List(Term)) -> #(List(Value), List(Type), State) {
  elaborate_args_loop(args, [], [], s)
}

fn elaborate_args_loop(
  args: List(Term),
  vals: List(Value),
  tys: List(Type),
  s: State,
) -> #(List(Value), List(Type), State) {
  case args {
    [] -> #(list.reverse(vals), list.reverse(tys), s)
    [arg, ..rest] -> {
      let #(val, ty, s1) = infer(s, arg)
      elaborate_args_loop(rest, [val, ..vals], [ty, ..tys], s1)
    }
  }
}
```

---

## 3. Host Evaluation (Comptime Execution)

### 3.1 Host FFI Registry

```gleam
// New module: src/host/ffi.gleam

/// Host FFI function
pub type HostFFI {
  HostFFI(
    name: String,
    arity: Int,
    impl: fn(List(Value), State) -> #(Value, State),
    required_permissions: List(Permission),
  )
}

/// Host FFI registry
pub type HostRegistry {
  HostRegistry(
    ffis: Dict(String, HostFFI),
  )
}

/// Default host FFIs
pub fn default_host_registry() -> HostRegistry {
  HostRegistry(
    ffis: dict.from_list([
      // Arithmetic (pure, always allowed)
      #("add", HostFFI("add", 2, add_impl, [])),
      #("sub", HostFFI("sub", 2, sub_impl, [])),
      #("mul", HostFFI("mul", 2, mul_impl, [])),
      
      // String operations (pure)
      #("concat", HostFFI("concat", 2, concat_impl, [])),
      
      // File I/O (requires permission)
      #("read_file", HostFFI("read_file", 1, read_file_impl, [AllowRead("*")])),
      #("write_file", HostFFI("write_file", 2, write_file_impl, [AllowWrite("*")])),
      
      // Environment (requires permission)
      #("get_env", HostFFI("get_env", 1, get_env_impl, [AllowEnv("*")])),
      
      // Time (impure, but useful for timestamps)
      #("now", HostFFI("now", 0, now_impl, [])),
    ]),
  )
}
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

fn host_eval(s: State, term: Term) -> #(Value, State) {
  case term.data {
    BuiltIn(name, args) -> {
      case dict.get(s.host_registry.ffis, name) {
        Ok(ffi) -> {
          // Check permissions
          if !all_permissions_granted(ffi.required_permissions, s.config.permissions) {
            let err = ComptimeError(
              "Permission denied for comptime operation: " <> name,
              term.span,
              ffi.required_permissions |> list.first,
            )
            #(VErr, add_comptime_error(s, err))
          } else {
            // Evaluate arguments
            let #(arg_vals, _, s1) = elaborate_args(s, args)
            
            // Execute
            ffi.impl(arg_vals, s1)
          }
        }
        Error(_) -> {
          let err = ComptimeError("Unknown host FFI: " <> name, term.span, None)
          #(VErr, add_comptime_error(s, err))
        }
      }
    }
    
    // Recursively evaluate other terms
    _ -> infer(s, term)
  }
}
```

### 3.4 Example Host Implementations

```gleam
// In src/host/ffi.gleam

fn add_impl(args: List(Value), s: State) -> #(Value, State) {
  case args {
    [VLit(Int(a)), VLit(Int(b))] -> #(VLit(Int(a + b)), s)
    [a, b] -> {
      // Arguments not concrete - return neutral
      #(VNeut(HBuiltIn("add", [a, b]), []), s)
    }
    _ -> #(VErr, s)
  }
}

fn read_file_impl(args: List(Value), s: State) -> #(Value, State) {
  case args {
    [VLit(String(path))] -> {
      // Read file content
      case file.read(path) {
        Ok(content) -> #(VLit(String(content)), s)
        Error(e) -> {
          let err = ComptimeError("Failed to read file: " <> path <> " - " <> e, Span(0, 0), None)
          #(VErr, add_comptime_error(s, err))
        }
      }
    }
    _ -> #(VErr, s)
  }
}

fn now_impl(args: List(Value), s: State) -> #(Value, State) {
  // Get current timestamp (impure, but allowed)
  let timestamp = time.now() |> time.to_unix
  #(VLit(Int(timestamp)), s)
}
```

---

## 4. Quoting (Value → Term)

```gleam
// In src/core/core.gleam

fn quote(lvl: Int, val: Value, s: State) -> Term {
  case val {
    VLit(literal) -> Term(Lit(literal), Span(0, 0))
    
    VRcd(fields) -> {
      Term(Rcd(list.map(fields, fn(#(k, v)) { #(k, quote(lvl, v, s)) })), Span(0, 0))
    }
    
    VCtr(tag, arg) -> {
      Term(Ctr(tag, quote(lvl, arg, s)), Span(0, 0))
    }
    
    VNeut(HBuiltIn("read_file", [VLit(String(_))]), []) -> {
      // File reads become string literals (content already read)
      // The value already contains the content
      quote(lvl, val, s)
    }
    
    VBuiltIn(name, _, _, _) -> {
      // Built-ins that weren't fully applied
      Term(BuiltIn(name, []), Span(0, 0))
    }
    
    VErr -> {
      // Error value - return error term
      Term(Lit(Int(0)), Span(0, 0)) // Placeholder
    }
    
    _ -> {
      // Cannot quote closures, functions, etc.
      // This is a comptime error
      let err = ComptimeError("Cannot quote value at compile-time", Span(0, 0), None)
      Term(Lit(Int(0)), Span(0, 0)) // Placeholder
    }
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
        arity: 1,
        codegen: fn(args, _target) {
          Ok("console.log(" <> emit(args[0]) <> ")")
        },
        platforms: None,
      )),
      #("add", BuiltinDef(
        name: "add",
        arity: 2,
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
        arity: 1,
        codegen: fn(args, _target) {
          Ok("console.log(" <> emit_expr(args[0]) <> ")")
        },
        platforms: None,
      )),
      #("add", BuiltinDef(
        name: "add",
        arity: 2,
        codegen: fn(args, _target) {
          Ok(emit_expr(args[0]) <> " + " <> emit_expr(args[1]))
        },
        platforms: None,
      )),
      #("read_file", BuiltinDef(
        name: "read_file",
        arity: 1,
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
    BuiltIn(name, args) -> {
      // Look up in registry
      // ...
    }
    // ... other cases
  }
}
```

### 5.3 Official Backend: WebAssembly

```gleam
// src/backend/webassembly.gleam

import backend/registry

pub fn get_registry() -> BackendRegistry {
  BackendRegistry(
    target: WebAssembly,
    builtins: dict.from_list([
      #("print", BuiltinDef(
        name: "print",
        arity: 1,
        codegen: fn(_args, _target) {
          // WASM has no console - emit trap
          Ok("(unreachable) ;; print not supported in WASM")
        },
        platforms: None,
      )),
      #("add", BuiltinDef(
        name: "add",
        arity: 2,
        codegen: fn(args, _target) {
          Ok("i32.add(" <> emit_expr(args[0]) <> ", " <> emit_expr(args[1]) <> ")")
        },
        platforms: None,
      )),
    ]),
    runtime_module: Some("./runtime/wasm_runtime.js"),
  )
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
    BuiltIn(name, args) -> {
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
        Error(_) -> Error("Unknown built-in: " <> name)
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

### Phase 1: Built-in Infrastructure (Week 1-2)

- [ ] Add `BuiltIn(name, args)` to `TermData`
- [ ] Add `VBuiltIn` to `Value`
- [ ] Implement `add_impl`, `sub_impl`, etc. (pure arithmetic)
- [ ] Update `infer` to handle `BuiltIn`
- [ ] Add `host_registry` to `State`

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

### 9.3 Timestamp for Release

```gleam
// Source (impure comptime)
let release_time = comptime now()

// After elaboration
let release_time = 1234567890  // Timestamp embedded

// JavaScript output
const release_time = 1234567890;
```

### 9.4 Platform-Specific Built-in

```gleam
// Source
let data = fs_read("data.txt")  // Only works on Native target

// WebAssembly codegen
// (unreachable) ;; fs_read not supported on WASM
// Compiler warning: "fs_read is not available on WebAssembly target"

// Native codegen
const data = fs_read("data.txt");
```

### 9.5 User-Created Backend

```gleam
// my_java_backend.gleam
import backend/registry

pub fn get_registry() -> BackendRegistry {
  BackendRegistry(
    target: Custom("Java"),
    builtins: dict.from_list([
      #("print", BuiltinDef(
        name: "print",
        arity: 1,
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

### 11.1 Existing infer/check Signatures

The existing signatures already support this design:

```gleam
pub fn infer(s: State, term: Term) -> #(Value, Type, State)
pub fn check(s: State, term: Term, expected_ty: Value, ty_span: Span) -> #(Value, State)
```

Both return normalized `Value`, which is exactly what we need for comptime evaluation.

### 11.2 Existing Error Handling

The existing `State.errors` list can hold `ComptimeError`:

```gleam
pub type State {
  State(
    // ... existing fields
    errors: List(Error),
  )
}

// ComptimeError can be added to errors
fn add_comptime_error(s: State, err: ComptimeError) -> State {
  State(..s, errors: [ComptimeErr(err), ..s.errors])
}
```

### 11.3 Existing VErr

The existing `VErr` value is perfect for comptime failures:

```gleam
pub type Value {
  // ... existing constructors
  VErr  // Already exists!
}
```

---

## 12. Open Questions (Answered)

| Question | Decision |
|----------|----------|
| Comptime explicit or inferred? | **Explicit** (`comptime` keyword) |
| Impure built-ins in comptime? | **Yes** (with permissions) |
| Comptime errors? | **VErr + State.errors** |
| Backends pluggable? | **Yes** (as modules) |

---

## 13. References

- [Normalization by Evaluation](https://en.wikipedia.org/wiki/Normalization_by_evaluation)
- [Zig Comptime](https://ziglang.org/documentation/master/#comptime)
- [Idris 2 Evaluation](https://idris2.readthedocs.io/en/latest/)
- [Rust Procedural Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
