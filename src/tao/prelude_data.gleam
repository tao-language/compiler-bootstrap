// ============================================================================
// TAo PRELUDE DATA
// Module paths and their public names.
// This centralizes prelude knowledge so it can be modified for different
// language implementations without touching compiler logic.
// ============================================================================
import gleam/list

/// Public names for each prelude module, keyed by module path.
/// Used as fallback when source files are not available.
pub fn prelude_public_names(path: String) -> List(String) {
  case path {
    "prelude/bool" -> ["Bool", "True", "False", "not", "and", "or", "xor", "to_int", "from_int", "to_string"]
    "prelude/option" -> ["Option", "Some", "None", "is_some", "is_none", "unwrap", "map", "and_then", "unwrap_or"]
    "prelude/result" -> ["Result", "Ok", "Err", "is_ok", "is_err", "unwrap", "map", "and_then", "unwrap_or"]
    "prelude/ordering" -> ["Ordering", "LT", "EQ", "GT", "compare", "reverse"]
    "prelude/list" -> ["List", "Cons", "Nil", "head", "tail", "is_empty", "length", "map", "fold"]
    _ -> []
  }
}

/// All prelude module paths, in dependency order (dependencies first).
pub fn prelude_paths() -> List(String) {
  [
    "prelude/bool",
    "prelude/option",
    "prelude/result",
    "prelude/ordering",
    "prelude/list",
  ]
}
