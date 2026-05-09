/// Exhaustiveness Checking — Pattern match coverage
///
/// The `exhaustiveness` module checks whether pattern matches cover all
/// possible constructors. It supports both simple constructor-based
/// checking and TypeDef-aware checking.
///
/// For TypeDef-based checking:
/// - Constructors are extracted from the TypeDef
/// - Missing patterns are reported with their tags
/// - Redundant patterns are detected

import core/ast.{type Value, HHole, make_neut}
import core/state.{type State, MatchMissing}
import gleam/list
import syntax/span.{single, type Span}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Check if match cases are exhaustive for a given list of constructors.
///
/// Returns the updated state with any errors accumulated.
///
/// `constructors` is a list of #(tag, ConstructorDef) tuples representing
/// the constructor definitions to check against.
///
/// Supports two formats:
/// - Legacy: `List(#(String, Value, Value, Span))` — #(tag, _, _, _)
/// - VTypeDef: `List(#(String, List(String), Value, Value, Span))` — #(tag, _, _, _, _)
pub fn check_exhaustiveness(
  state: State,
  constructors: List(#(String, Value, Value, Span)),
  covered: List(String),
  span: Span,
) -> State {
  let all_tags = list.map(constructors, fn(c) {
    case c {
      #(tag, _, _, _) -> tag
    }
  })

  check_exhaustiveness_inner(state, all_tags, covered, span)
}

/// Check exhaustiveness for VTypeDef-style constructors.
///
/// VTypeDef constructors have the format: #(tag, type_params, self_type, result_type, span)
pub fn check_exhaustiveness_vdef(
  state: State,
  constructors: List(#(String, List(String), Value, Value, Span)),
  covered: List(String),
  span: Span,
) -> State {
  let all_tags = list.map(constructors, fn(c) {
    case c {
      #(tag, _, _, _, _) -> tag
    }
  })

  check_exhaustiveness_inner(state, all_tags, covered, span)
}

/// Check if a pattern covers all remaining (uncovered) constructor tags.
///
/// Returns True if the pattern is a wildcard (PAny, PVar, or PAlias with wildcard)
/// that would cover all remaining cases. This is used for $Int wildcard
/// exhaustiveness — since integer types are "infinite", a wildcard pattern
/// at the end covers all remaining integer constructors.
pub fn is_wildcard_pattern(pattern: ast.Pattern) -> Bool {
  case pattern {
    ast.PAny(_) -> True
    ast.PVar(_, _) -> True
    ast.PAlias(_, inner, _) -> is_wildcard_pattern(inner)
    _ -> False
  }
}

/// Check if a pattern covers integer literal types.
///
/// Returns True if the pattern would match any integer literal:
/// - PLit with an Int value
/// - PAny (wildcard)
/// - PVar (variable)
pub fn covers_integer_types(pattern: ast.Pattern) -> Bool {
  case pattern {
    ast.PAny(_) -> True
    ast.PVar(_, _) -> True
    ast.PLit(ast.Int(_), _) -> True
    ast.PAlias(_, inner, _) -> covers_integer_types(inner)
    _ -> False
  }
}

/// Check if a pattern covers float literal types.
///
/// Returns True if the pattern would match any float literal:
/// - PLit with a Float value
/// - PAny (wildcard)
/// - PVar (variable)
pub fn covers_float_types(pattern: ast.Pattern) -> Bool {
  case pattern {
    ast.PAny(_) -> True
    ast.PVar(_, _) -> True
    ast.PLit(ast.Float(_), _) -> True
    ast.PAlias(_, inner, _) -> covers_float_types(inner)
    _ -> False
  }
}

/// Internal helper: check exhaustiveness against a list of tags.
fn check_exhaustiveness_inner(
  state: State,
  all_tags: List(String),
  covered: List(String),
  span: Span,
) -> State {
  let missing =
    list.fold(all_tags, [], fn(acc, tag) {
      case list.contains(covered, tag) {
        False -> [tag, ..acc]
        True -> acc
      }
    })

  case missing {
    [] -> state
    _ -> state.with_err(state, MatchMissing(missing, covered, span))
  }
}

/// Check if a pattern is redundant given a list of already-covered tags.
///
/// Returns True if the pattern would match a case already covered by
/// another pattern.
pub fn is_redundant(
  covered: List(String),
  pattern_tag: String,
) -> Bool {
  covered |> list.contains(pattern_tag)
}

// ============================================================================
// TYPEDEF HELPERS
// ============================================================================

/// Extract constructor tags from a list of #(String, Value, Value, Span) tuples.
///
/// Used by the TypeDef-aware exhaustiveness checker.
pub fn extract_tags(
  constructors: List(#(String, Value, Value, Span)),
) -> List(String) {
  list.map(constructors, fn(c) { c.0 })
}

/// Create a TypeDef for testing exhaustiveness.
///
/// This is a helper for tests.
pub fn make_type_def(
  _name: String,
  constructor_tags: List(String),
) -> List(#(String, Value, Value, Span)) {
  list.map(constructor_tags, fn(tag) {
    #(tag, make_neut(HHole(0)), make_neut(HHole(0)), single("", 0, 0))
  })
}
