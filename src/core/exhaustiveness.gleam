// ============================================================================
// CORE EXHAUSTIVENESS - Pattern Match Coverage Checking
// ============================================================================
import gleam/list
import syntax/grammar.{type Span, Span as SpanCtr}
import core/ast as ast
import core/state as state

pub type PMatrix =
  List(List(ast.Pattern))

/// Check exhaustiveness of pattern match cases.
/// Returns a list of errors (MatchMissingCase, MatchRedundantCase).
pub fn check_exhaustiveness(
  patterns: List(List(ast.Pattern)),
  types: List(ast.Value),
  span: Span,
) -> List(state.Error) {
  case patterns {
    [] -> [state.MatchMissingCase(span, ast.PAny)]
    _ -> {
      let redundant = find_redundant_cases(patterns)
      let missing = check_missing(patterns, types, span)
      list.append(redundant, missing)
    }
  }
}

fn find_redundant_loop(
  patterns: List(List(ast.Pattern)),
  index: Int,
  acc: List(state.Error),
  earlier_patterns: List(List(ast.Pattern)),
) -> List(state.Error) {
  case patterns {
    [] -> list.reverse(acc)
    [current, ..rest] -> {
      // Check if current pattern is subsumed by any earlier pattern
      let is_redundant = list.any(earlier_patterns, fn(earlier) {
        is_subsumed_by(current, earlier)
      })
      let new_acc = case is_redundant {
        True -> [state.MatchRedundantCase(SpanCtr("", 0, 0, 0, 0)), ..acc]
        False -> acc
      }
      find_redundant_loop(rest, index + 1, new_acc, [current, ..earlier_patterns])
    }
  }
}

/// Find redundant cases (patterns that are subsumed by earlier cases).
fn find_redundant_cases(patterns: List(List(ast.Pattern))) -> List(state.Error) {
  find_redundant_loop(patterns, 0, [], [])
}

/// Check if a pattern is subsumed by an earlier pattern.
/// A pattern is subsumed if the earlier pattern is a wildcard.
fn is_subsumed_by(pattern: List(ast.Pattern), earlier: List(ast.Pattern)) -> Bool {
  case pattern, earlier {
    [ast.PAny, ..], [ast.PAny, ..] -> True  // Wildcard after wildcard is redundant
    _, _ -> False
  }
}

/// Check if there are missing cases (no wildcard and not exhaustive).
/// For now, only check simple cases with literal patterns.
fn check_missing(
  patterns: List(List(ast.Pattern)),
  types: List(ast.Value),
  span: Span,
) -> List(state.Error) {
  case has_wildcard(patterns) {
    True -> []  // Has wildcard, so it's exhaustive
    False -> {
      // Check if all patterns are literals (non-exhaustive without wildcard)
      case all_literals(patterns) {
        True -> [state.MatchMissingCase(span, ast.PAny)]
        False -> []  // Constructor patterns may be exhaustive
      }
    }
  }
}

/// Check if all patterns are literals.
fn all_literals(patterns: List(List(ast.Pattern))) -> Bool {
  list.all(patterns, fn(patterns_row) {
    list.all(patterns_row, fn(p) {
      case p {
        ast.PLit(_) -> True
        _ -> False
      }
    })
  })
}

/// Check if any case has a wildcard pattern.
fn has_wildcard(patterns: List(List(ast.Pattern))) -> Bool {
  list.any(patterns, fn(patterns_row) {
    list.any(patterns_row, fn(p) {
      case p {
        ast.PAny -> True
        _ -> False
      }
    })
  })
}

pub fn get_default_cases(
  patterns: List(List(ast.Pattern)),
  types: List(ast.Value),
) -> List(ast.Pattern) {
  [ast.PAny]
}
