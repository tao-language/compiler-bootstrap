// ============================================================================
// TAO IMPORT AST
// ============================================================================
/// Import system AST types.
///
/// For detailed documentation see:
/// - **[../plans/tao/12-import-system.md](../plans/tao/12-import-system.md)** - Import system specification
import syntax/grammar.{type Span}

// ============================================================================
// IMPORT TYPES
// ============================================================================

/// An import statement.
pub type Import {
  /// Import entire module: `import result`
  ImportModule(path: String, span: Span)
  
  /// Import with alias: `import result as res`
  ImportAlias(path: String, alias: String, span: Span)
  
  /// Import specific names: `import result {Ok, Error}`
  ImportSelective(path: String, items: List(ImportItem), span: Span)
  
  /// Import with alias and specific names: `import result as res {Ok, Error}`
  ImportSelectiveAlias(path: String, alias: String, items: List(ImportItem), span: Span)
  
  /// Wildcard import: `import result as *`
  ImportWildcard(path: String, span: Span)
}

/// An imported item (name or type with constructors).
pub type ImportItem {
  /// Simple name: `Ok`
  ImportName(name: String, alias: Option(String))
  
  /// Type with constructors: `Result` (automatically includes Ok, Error)
  ImportType(name: String, alias: Option(String))
  
  /// Operator: `(+)`
  ImportOperator(name: String, alias: Option(String))
}

/// Resolved import with full path.
pub type ResolvedImport {
  ResolvedImport(
    original: Import,
    resolved_path: String,
    imported_names: List(String),
    is_directory: Bool,
  )
}

/// Import context for name resolution.
pub type ImportContext {
  ImportContext(
    imports: List(ResolvedImport),
    current_file: String,
    current_dir: String,
    project_root: String,
  )
}

// ============================================================================
// IMPORT ITEM HELPERS
// ============================================================================

/// Get the name of an import item (without alias).
pub fn get_item_name(item: ImportItem) -> String {
  case item {
    ImportName(name, _) -> name
    ImportType(name, _) -> name
    ImportOperator(name, _) -> name
  }
}

/// Get the alias of an import item (if any).
pub fn get_item_alias(item: ImportItem) -> Option(String) {
  case item {
    ImportName(_, alias) -> alias
    ImportType(_, alias) -> alias
    ImportOperator(_, alias) -> alias
  }
}

/// Get the local name for an import item (alias if present, otherwise name).
pub fn get_local_name(item: ImportItem) -> String {
  case get_item_alias(item) {
    Some(alias) -> alias
    None -> get_item_name(item)
  }
}

// ============================================================================
// IMPORT HELPERS
// ============================================================================

/// Get the path from an import.
pub fn get_import_path(import_item: Import) -> String {
  case import_item {
    ImportModule(path, _) -> path
    ImportAlias(path, _, _) -> path
    ImportSelective(path, _, _) -> path
    ImportSelectiveAlias(path, _, _, _) -> path
    ImportWildcard(path, _) -> path
  }
}

/// Get the alias from an import (if any).
pub fn get_import_alias(import_item: Import) -> Option(String) {
  case import_item {
    ImportModule(_, _) -> None
    ImportAlias(_, alias, _) -> Some(alias)
    ImportSelective(_, _, _) -> None
    ImportSelectiveAlias(_, alias, _, _) -> Some(alias)
    ImportWildcard(_, _) -> None
  }
}

/// Check if an import is a wildcard import.
pub fn is_wildcard_import(import_item: Import) -> Bool {
  case import_item {
    ImportWildcard(_, _) -> True
    _ -> False
  }
}

/// Check if an import is selective (imports specific names).
pub fn is_selective_import(import_item: Import) -> Bool {
  case import_item {
    ImportSelective(_, _, _) -> True
    ImportSelectiveAlias(_, _, _, _) -> True
    _ -> False
  }
}

/// Get all local names introduced by an import.
pub fn get_imported_names(import_item: Import) -> List(String) {
  case import_item {
    ImportModule(_, _) -> []  // No unqualified names
    ImportAlias(_, _, _) -> []  // No unqualified names
    ImportSelective(_, items, _) -> list.map(items, get_local_name)
    ImportSelectiveAlias(_, _, items, _) -> list.map(items, get_local_name)
    ImportWildcard(_, _) -> []  // Module name only, no unqualified names
  }
}

// ============================================================================
// IMPORT CONTEXT HELPERS
// ============================================================================

/// Create an empty import context.
pub fn empty_context(current_file: String, project_root: String) -> ImportContext {
  let current_dir = get_directory(current_file)
  ImportContext([], current_file, current_dir, project_root)
}

/// Add a resolved import to the context.
pub fn add_import(context: ImportContext, resolved: ResolvedImport) -> ImportContext {
  ImportContext(
    [resolved, ..context.imports],
    context.current_file,
    context.current_dir,
    context.project_root,
  )
}

/// Get the directory portion of a file path.
fn get_directory(path: String) -> String {
  // Simple implementation - find last / and take everything before it
  get_directory_helper(path, string.length(path) - 1)
}

fn get_directory_helper(path: String, index: Int) -> String {
  case index < 0 {
    True -> ""  // No directory separator found
    False -> {
      case string.slice(path, index, 1) {
        "/" -> string.slice(path, 0, index)
        _ -> get_directory_helper(path, index - 1)
      }
    }
  }
}

// ============================================================================
// IMPORTS
// ============================================================================

import gleam/string
import gleam/list
import gleam/option.{type Option, Some, None}
