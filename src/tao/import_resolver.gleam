// ============================================================================
// TAO IMPORT RESOLVER
// ============================================================================
/// Import resolution for Tao.
///
/// Resolves import paths to files, handles directory imports, and manages
/// name resolution with proper scoping.
///
/// For detailed documentation see:
/// - **[../plans/tao/12-import-system.md](../plans/tao/12-import-system.md)** - Import system specification
import tao/import_ast.{
  type Import, ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias, ImportWildcard,
  type ImportItem, ImportName, ImportType, ImportOperator,
  type ResolvedImport, ResolvedImport,
  type ImportContext, ImportContext, empty_context, add_import,
  get_import_path, get_import_alias, is_wildcard_import, is_selective_import, get_imported_names,
  get_item_name, get_item_alias, get_local_name,
}
import syntax/grammar.{type Span, Span}
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import gleam/option.{type Option, Some, None}
import gleam/dict.{type Dict, insert, new}
import simplifile

// ============================================================================
// RESOLUTION RESULT
// ============================================================================

/// Result of resolving an import.
pub type ResolutionResult {
  /// Successfully resolved
  ResolutionSuccess(
    resolved: ResolvedImport,
    warnings: List(ResolutionWarning),
  )
  
  /// Failed to resolve
  ResolutionError(
    import_item: Import,
    errors: List(ResolutionErrorType),
  )
}

/// Warning during resolution.
pub type ResolutionWarning {
  /// Duplicate import from same module
  DuplicateImport(name: String, module: String, span: Span)
  
  /// Name already in scope from different module
  ShadowedName(name: String, from_module: String, shadowed_by: String, span: Span)
}

/// Error during resolution.
pub type ResolutionErrorType {
  /// Module not found
  ModuleNotFound(path: String, span: Span)
  
  /// File not found (for explicit file imports)
  FileNotFound(path: String, span: Span)
  
  /// Directory not found (for directory imports)
  DirectoryNotFound(path: String, span: Span)
  
  /// Cannot import private name
  PrivateName(path: String, module: String, span: Span)
  
  /// Circular import detected
  CircularImport(path: String, cycle: List(String), span: Span)
  
  /// Name not exported from module
  NameNotExported(name: String, module: String, span: Span)
}

// ============================================================================
// MODULE INFO
// ============================================================================

/// Information about a resolved module.
pub type ModuleInfo {
  ModuleInfo(
    path: String,
    exported_names: List(String),
    exported_types: List(String),
    exported_constructors: List(String),
    is_private: Bool,  // true if file starts with _
  )
}

// ============================================================================
// RESOLVER STATE
// ============================================================================

/// State maintained during resolution.
pub type ResolverState {
  ResolverState(
    /// Cache of resolved modules
    resolved_modules: Dict(String, ModuleInfo),
    /// Current import stack (for cycle detection)
    import_stack: List(String),
    /// Project root directory
    project_root: String,
    /// Accumulated warnings
    warnings: List(ResolutionWarning),
    /// Accumulated errors
    errors: List(ResolutionErrorType),
  )
}

/// Create initial resolver state.
pub fn initial_state(project_root: String) -> ResolverState {
  ResolverState(
    new(),  // resolved_modules
    [],  // import_stack
    project_root,
    [],  // warnings
    [],  // errors
  )
}

// ============================================================================
// MAIN RESOLUTION API
// ============================================================================

/// Resolve all imports in a file.
pub fn resolve_imports(
  imports: List(Import),
  current_file: String,
  project_root: String,
) -> #(ImportContext, List(ResolutionResult)) {
  let state = initial_state(project_root)
  let context = empty_context(current_file, project_root)
  
  resolve_imports_loop(imports, context, state, [])
}

/// Check if a file is a prelude file (in lib/prelude/ directory).
pub fn is_prelude_file(file_path: String) -> Bool {
  // Check if the file path contains "lib/prelude" or starts with "prelude"
  string.contains(file_path, "lib/prelude") || string.starts_with(file_path, "prelude")
}

fn resolve_imports_loop(
  imports: List(Import),
  context: ImportContext,
  state: ResolverState,
  results: List(ResolutionResult),
) -> #(ImportContext, List(ResolutionResult)) {
  case imports {
    [] -> #(context, list.reverse(results))
    [import_item, ..rest] -> {
      let #(new_context, result, new_state) = resolve_single_import(import_item, context, state)
      resolve_imports_loop(rest, new_context, new_state, [result, ..results])
    }
  }
}

fn resolve_single_import(
  import_item: Import,
  context: ImportContext,
  state: ResolverState,
) -> #(ImportContext, ResolutionResult, ResolverState) {
  let path = get_import_path(import_item)
  
  // Check for circular imports
  case list.contains(state.import_stack, path) {
    True -> {
      let error = CircularImport(path, state.import_stack, get_import_span(import_item))
      let new_state = add_error(state, error)
      let result = ResolutionError(import_item, [error])
      #(context, result, new_state)
    }
    False -> {
      // Resolve the path
      let resolved_path = resolve_path(path, context.current_dir, state.project_root)
      
      // Check for prelude self-import (prelude file importing prelude)
      let is_prelude_self_import = is_prelude_file(context.current_file) && is_prelude_file(path)
      
      // Try to read the file/directory
      case resolve_module_path(resolved_path, state) {
        Ok(module_info) -> {
          // Check if importing private file from outside
          case module_info.is_private && !is_explicit_private_import(path) && !is_prelude_self_import {
            True -> {
              let error = PrivateName(path, path, get_import_span(import_item))
              let new_state = add_error(state, error)
              let result = ResolutionError(import_item, [error])
              #(context, result, new_state)
            }
            False -> {
              // Create resolved import
              let resolved_import = create_resolved_import(import_item, resolved_path, module_info)
              let new_context = add_import(context, resolved_import)
              let new_state = add_module_to_cache(state, module_info)
              let result = ResolutionSuccess(resolved_import, state.warnings)
              #(new_context, result, new_state)
            }
          }
        }
        Error(error) -> {
          let new_state = add_error(state, error)
          let result = ResolutionError(import_item, [error])
          #(context, result, new_state)
        }
      }
    }
  }
}

// ============================================================================
// PATH RESOLUTION
// ============================================================================

/// Resolve an import path to an absolute file path.
fn resolve_path(path: String, current_dir: String, project_root: String) -> String {
  case string.starts_with(path, "prelude") {
    True -> {
      // Prelude paths are relative to project root
      project_root <> "/lib/" <> path
    }
    False -> {
      case string.starts_with(path, "/") {
        True -> path  // Absolute path
        False -> {
          // Relative to current directory
          current_dir <> "/" <> path
        }
      }
    }
  }
}

/// Resolve a module path to a file or directory.
fn resolve_module_path(
  resolved_path: String,
  state: ResolverState,
) -> Result(ModuleInfo, ResolutionErrorType) {
  // First, try as a file
  case simplifile.read(from: resolved_path <> ".tao") {
    Ok(contents) -> {
      // Successfully read file
      Ok(scan_module_info(resolved_path <> ".tao", contents))
    }
    Error(_) -> {
      // Try as directory - read all .tao files except _*.tao
      resolve_directory_import(resolved_path, state)
    }
  }
}

/// Handle directory import - collect all public files.
fn resolve_directory_import(
  dir_path: String,
  _state: ResolverState,
) -> Result(ModuleInfo, ResolutionErrorType) {
  // Check if directory exists
  case simplifile.is_directory(dir_path) {
    Ok(False) -> Error(DirectoryNotFound(dir_path, Span("unknown", 0, 0, 0, 0)))
    Error(_) -> Error(DirectoryNotFound(dir_path, Span("unknown", 0, 0, 0, 0)))
    Ok(True) -> {
      // Read directory contents
      case simplifile.read_directory(at: dir_path) {
        Error(_) -> Error(DirectoryNotFound(dir_path, Span("unknown", 0, 0, 0, 0)))
        Ok(entries) -> {
          // Filter to .tao files that don't start with _
          let _public_files = list.filter(entries, fn(entry) {
            string.ends_with(entry, ".tao") && !string.starts_with(entry, "_")
          })
          
          // For directory imports, we create a synthetic module that represents
          // the aggregation of all public files
          Ok(ModuleInfo(
            dir_path,
            [],  // exported_names - would be populated by scanning all files
            [],  // exported_types
            [],  // exported_constructors
            False,  // is_private - directories themselves aren't private
          ))
        }
      }
    }
  }
}

/// Scan a module to extract exported names.
fn scan_module_info(path: String, _contents: String) -> ModuleInfo {
  // Simplified: just check if file starts with _
  let file_name = get_file_name(path)
  let is_private = string.starts_with(file_name, "_")
  
  // In a full implementation, we'd parse the module to find exports
  // For now, return empty lists
  ModuleInfo(
    path,
    [],  // exported_names
    [],  // exported_types
    [],  // exported_constructors
    is_private,
  )
}

// ============================================================================
// RESOLVED IMPORT CREATION
// ============================================================================

/// Create a resolved import from an import statement.
fn create_resolved_import(
  import_item: Import,
  resolved_path: String,
  _module_info: ModuleInfo,
) -> ResolvedImport {
  let imported_names = case is_wildcard_import(import_item) {
    True -> []  // Wildcard imports don't introduce unqualified names
    False -> {
      case is_selective_import(import_item) {
        True -> get_imported_names(import_item)
        False -> []  // Module imports don't introduce unqualified names
      }
    }
  }
  
  ResolvedImport(
    import_item,
    resolved_path,
    imported_names,
    False,  // is_directory - would be determined during resolution
  )
}

// ============================================================================
// STATE HELPERS
// ============================================================================

fn add_error(state: ResolverState, error: ResolutionErrorType) -> ResolverState {
  ResolverState(
    state.resolved_modules,
    state.import_stack,
    state.project_root,
    state.warnings,
    [error, ..state.errors],
  )
}

fn add_module_to_cache(state: ResolverState, info: ModuleInfo) -> ResolverState {
  let new_modules = insert(state.resolved_modules, info.path, info)
  ResolverState(
    new_modules,
    state.import_stack,
    state.project_root,
    state.warnings,
    state.errors,
  )
}

// ============================================================================
// UTILITY HELPERS
// ============================================================================

fn get_import_span(_import_item: Import) -> Span {
  // In a full implementation, this would come from the Import type
  Span("unknown", 0, 0, 0, 0)
}

fn get_file_name(path: String) -> String {
  // Find last / and take everything after it
  get_file_name_helper(path, string.length(path) - 1, string.length(path))
}

fn get_file_name_helper(path: String, index: Int, end: Int) -> String {
  case index < 0 {
    True -> string.slice(path, 0, end)
    False -> {
      case string.slice(path, index, 1) {
        "/" -> string.slice(path, index + 1, end - index - 1)
        _ -> get_file_name_helper(path, index - 1, end)
      }
    }
  }
}

fn is_explicit_private_import(path: String) -> Bool {
  // Check if any component of the path starts with _
  let file_name = get_file_name(path)
  string.starts_with(file_name, "_")
}
