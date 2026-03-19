// ============================================================================
// TAO GLOBAL CONTEXT
// ============================================================================
/// Global context for tracking all modules during compilation.
///
/// Each .tao file compiles to a Record containing all public names.
/// Modules are stored as @path records (e.g., @math/trig, @math).
///
/// For detailed documentation see:
/// - [Import System](../../docs/plans/tao/12-import-system.md)
/// - [Stmt System](../../docs/plans/tao/13-stmt-system.md)

import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{type Option, Some, None}
import gleam/string
import tao/ast.{type Module, get_public_names}
import tao/import_ast.{
  ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias,
  ImportWildcard, type Import,
}

// ============================================================================
// GLOBAL CONTEXT
// ============================================================================

/// Global context tracking all modules.
pub type GlobalContext {
  GlobalContext(
    /// Map from module path to module reference
    modules: Dict(String, ModuleRef),
    /// Current module being compiled (for error messages)
    current_module: Option(String),
  )
}

/// Module reference - tracks a module's public names and compiled value.
pub type ModuleRef {
  ModuleRef(
    /// Module path (e.g., "math/trig", "math")
    path: String,
    /// Public names exported by this module
    public_names: List(String),
    /// Compiled Core term (None = not yet compiled)
    /// Using dynamic to avoid circular dependency with core
    value: Option(Dynamic),
    /// Source module AST
    source: Option(Module),
  )
}

/// Dynamic placeholder for Core term (avoids circular dependency).
pub type Dynamic {
  Dynamic(value: String)
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Create a new empty global context.
pub fn new_context() -> GlobalContext {
  GlobalContext(
    modules: dict.new(),
    current_module: None,
  )
}

/// Set the current module being compiled.
pub fn set_current_module(ctx: GlobalContext, path: String) -> GlobalContext {
  GlobalContext(..ctx, current_module: Some(path))
}

/// Get the current module path.
pub fn get_current_module(ctx: GlobalContext) -> Option(String) {
  ctx.current_module
}

/// Register a module placeholder in the global context.
/// This creates a ModuleRef with None value, allowing circular references.
pub fn register_module(
  ctx: GlobalContext,
  path: String,
  module: Module,
) -> GlobalContext {
  let public_names = get_public_names(module.body)
  let module_ref = ModuleRef(
    path: path,
    public_names: public_names,
    value: None,
    source: Some(module),
  )
  
  GlobalContext(
    ..ctx,
    modules: dict.insert(ctx.modules, path, module_ref),
  )
}

/// Get a module reference by path.
pub fn get_module(ctx: GlobalContext, path: String) -> Option(ModuleRef) {
  case dict.get(ctx.modules, path) {
    Ok(module_ref) -> Some(module_ref)
    Error(_) -> None
  }
}

/// Check if a module exists.
pub fn has_module(ctx: GlobalContext, path: String) -> Bool {
  case dict.get(ctx.modules, path) {
    Ok(_) -> True
    Error(_) -> False
  }
}

/// Update a module's compiled value.
pub fn set_module_value(
  ctx: GlobalContext,
  path: String,
  value: Dynamic,
) -> Result(GlobalContext, String) {
  case dict.get(ctx.modules, path) {
    Ok(module_ref) -> {
      let updated_ref = ModuleRef(..module_ref, value: Some(value))
      Ok(GlobalContext(
        ..ctx,
        modules: dict.insert(ctx.modules, path, updated_ref),
      ))
    }
    Error(_) -> Error("Module not found: " <> path)
  }
}

/// Get a module's compiled value.
pub fn get_module_value(
  ctx: GlobalContext,
  path: String,
) -> Option(Dynamic) {
  case dict.get(ctx.modules, path) {
    Ok(module_ref) -> module_ref.value
    Error(_) -> None
  }
}

/// Get a module's public names.
pub fn get_module_public_names(
  ctx: GlobalContext,
  path: String,
) -> Option(List(String)) {
  case dict.get(ctx.modules, path) {
    Ok(module_ref) -> Some(module_ref.public_names)
    Error(_) -> None
  }
}

/// Check if a name is exported by a module.
pub fn is_exported(
  ctx: GlobalContext,
  module_path: String,
  name: String,
) -> Bool {
  case get_module_public_names(ctx, module_path) {
    Some(names) -> list.contains(names, name)
    None -> False
  }
}

// ============================================================================
// MODULE PATH UTILITIES
// ============================================================================

/// Convert a file path to a module path.
/// E.g., "src/math/trig.tao" → "math/trig"
pub fn path_to_module_path(file_path: String) -> String {
  file_path
  |> string.replace("src/", "")
  |> string.replace(".tao", "")
  |> string.replace("/", "/")
}

/// Get the directory path from a module path.
/// E.g., "math/trig" → "math"
pub fn module_directory(module_path: String) -> String {
  case string.split(module_path, "/") {
    [dir, ..] -> dir
    [] -> module_path
  }
}

/// Get the base name from a module path.
/// E.g., "math/trig" → "trig"
pub fn module_base_name(module_path: String) -> String {
  case string.split(module_path, "/") {
    parts -> {
      case list.last(parts) {
        Ok(name) -> name
        Error(_) -> module_path
      }
    }
  }
}

/// Check if a module is a prelude module.
pub fn is_prelude_module(module_path: String) -> Bool {
  string.starts_with(module_path, "prelude")
}

// ============================================================================
// IMPORT RESOLUTION
// ============================================================================

/// Resolve an import to a module path.
pub fn resolve_import(
  ctx: GlobalContext,
  import_item: Import,
  _current_module: String,
) -> Result(String, String) {
  let module_path = case import_item {
    ImportModule(path: path, ..) -> path
    ImportAlias(path: path, ..) -> path
    ImportSelective(path: path, ..) -> path
    ImportSelectiveAlias(path: path, ..) -> path
    ImportWildcard(path: path, ..) -> path
  }
  
  // Check if module exists
  case has_module(ctx, module_path) {
    True -> Ok(module_path)
    False -> Error("Module not found: " <> module_path)
  }
}

/// Get all modules in a directory (for directory imports).
pub fn get_directory_modules(
  ctx: GlobalContext,
  dir_path: String,
) -> List(String) {
  get_directory_modules_loop(ctx.modules, dir_path, [])
}

fn get_directory_modules_loop(
  modules: Dict(String, ModuleRef),
  dir_path: String,
  acc: List(String),
) -> List(String) {
  case dict.to_list(modules) {
    [] -> list.reverse(acc)
    [pair, ..rest] -> {
      let #(path, _) = pair
      case string.starts_with(path, dir_path) {
        True -> get_directory_modules_loop(
          dict.from_list(rest),
          dir_path,
          [path, ..acc],
        )
        False -> get_directory_modules_loop(
          dict.from_list(rest),
          dir_path,
          acc,
        )
      }
    }
  }
}

// ============================================================================
// ERROR HANDLING
// ============================================================================

/// Create an error placeholder module reference.
pub fn error_module_ref(path: String, _error: String) -> ModuleRef {
  ModuleRef(
    path: path,
    public_names: [],
    value: None,
    source: None,
  )
}

/// Register an error placeholder in the global context.
pub fn register_error_module(
  ctx: GlobalContext,
  path: String,
  error: String,
) -> GlobalContext {
  let error_ref = error_module_ref(path, error)
  GlobalContext(
    ..ctx,
    modules: dict.insert(ctx.modules, path, error_ref),
  )
}

// ============================================================================
// INITIALIZATION
// ============================================================================

/// Initialize global context with prelude modules.
pub fn with_prelude(ctx: GlobalContext) -> GlobalContext {
  // Register prelude modules as placeholders with their full paths
  // Each module has its own path (e.g., "prelude/bool", "prelude/option")
  let bool_ref = ModuleRef(
    path: "prelude/bool",
    public_names: ["Bool", "True", "False", "not", "and", "or", "xor", "to_int", "from_int", "to_string"],
    value: None,
    source: None,
  )

  let option_ref = ModuleRef(
    path: "prelude/option",
    public_names: ["Option", "Some", "None", "is_some", "is_none", "unwrap", "map", "and_then", "unwrap_or"],
    value: None,
    source: None,
  )

  let result_ref = ModuleRef(
    path: "prelude/result",
    public_names: ["Result", "Ok", "Err", "is_ok", "is_err", "unwrap", "map", "and_then", "unwrap_or"],
    value: None,
    source: None,
  )

  let ordering_ref = ModuleRef(
    path: "prelude/ordering",
    public_names: ["Ordering", "LT", "EQ", "GT", "compare", "reverse"],
    value: None,
    source: None,
  )

  // Insert all prelude modules
  let ctx1 = GlobalContext(
    ..ctx,
    modules: dict.insert(ctx.modules, "prelude/bool", bool_ref),
  )
  let ctx2 = GlobalContext(
    ..ctx1,
    modules: dict.insert(ctx1.modules, "prelude/option", option_ref),
  )
  let ctx3 = GlobalContext(
    ..ctx2,
    modules: dict.insert(ctx2.modules, "prelude/result", result_ref),
  )
  GlobalContext(
    ..ctx3,
    modules: dict.insert(ctx3.modules, "prelude/ordering", ordering_ref),
  )
}
