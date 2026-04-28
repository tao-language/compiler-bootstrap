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

import core/ast.{
  TypeDef,
  ConstructorDef,
  type TypeDef,
  type Value,
  type ConstructorDef,
  type Head,
  HHole,
  make_neut,
}
import core/state.{type State, MatchMissing}
import gleam/list
import syntax/span.{type Span}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Check if match cases are exhaustive for a given list of constructors.
///
/// Returns the updated state with any errors accumulated.
pub fn check_exhaustiveness(
  state: State,
  constructors: List(#(String, ConstructorDef)),
  covered: List(String),
  span: Span,
) -> State {
  let all_tags = list.map(constructors, fn(c) { c.1.tag })
  let missing =
    list.fold(all_tags, [], fn(acc, tag) {
      case covered |> list.contains(tag) {
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

/// Extract constructor tags from a TypeDef.
///
/// Used by the TypeDef-aware exhaustiveness checker.
pub fn extract_tags(td: TypeDef) -> List(String) {
  td.constructors |> list.map(fn(c) { c.tag })
}

/// Create a TypeDef for testing exhaustiveness.
///
/// This is a helper for tests.
pub fn make_type_def(
  name: String,
  constructor_tags: List(String),
) -> TypeDef {
  TypeDef(
    name: name,
    param_count: 0,
    constructors: list.map(constructor_tags, fn(tag) {
      ConstructorDef(
        tag: tag,
        result_template: make_neut(HHole(0)),
      )
    }),
  )
}
