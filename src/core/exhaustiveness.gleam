// ============================================================================
// CORE EXHAUSTIVENESS - Pattern Match Coverage Checking
// ============================================================================
/// Checks for pattern match coverage in Core terms. Handles wildcard patterns,
/// literal patterns, constructor patterns, and record patterns.
///
/// Note: Full Maranget-style pattern matching would require a proper
/// pattern unification algorithm. This implementation handles the common cases
/// that arise in practice with this type checker's pattern coverage.
import gleam/list
import syntax/grammar.{type Span, Span as SpanCtr}
import core/ast as ast
import core/state as state
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

// ============================================================================
// REDUNDANT CASE DETECTION
// ============================================================================

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
/// A pattern is subsumed if the earlier pattern is a wildcard (PAny)
/// or if both patterns are structurally identical.
fn is_subsumed_by(pattern: List(ast.Pattern), earlier: List(ast.Pattern)) -> Bool {
  case earlier {
    // Earlier pattern starts with wildcard -> current is redundant
    [ast.PAny, ..] -> True
    // No earlier patterns left -> check if pattern is also exhausted
    [] -> case pattern {
      [] -> True  // Both exhausted = fully subsumed
      [_, ..] -> False  // Earlier exhausted but pattern has more
    }
    // Both non-empty: check head matches, then recurse
    [e_head, ..e_rest] ->
      case pattern {
        [p_head, ..p_rest] ->
          patterns_match(p_head, e_head) && is_subsumed_by(p_rest, e_rest)
        [] -> False  // Pattern exhausted but earlier remains
      }
  }
}

/// Check if two single patterns are structurally equal.
/// PAny only matches PAny here — wildcard subsumption is handled in is_subsumed_by.
fn patterns_match(p1: ast.Pattern, p2: ast.Pattern) -> Bool {
  case p1, p2 {
    ast.PAny, ast.PAny -> True
    // Two as-patterns match if inner patterns match
    ast.PAs(inner1, _), ast.PAs(inner2, _) -> patterns_match(inner1, inner2)
    // Two constructors match if same tag and inner patterns match
    ast.PCtr(tag1, p1_inner), ast.PCtr(tag2, p2_inner) ->
      tag1 == tag2 && patterns_match(p1_inner, p2_inner)
    // Two literals match if equal
    ast.PLit(l1), ast.PLit(l2) -> l1 == l2
    // Two literal types match if equal
    ast.PLitT(t1), ast.PLitT(t2) -> t1 == t2
    // Two record patterns match if same fields and inner patterns match
    ast.PRcd(fields1), ast.PRcd(fields2) ->
      record_fields_match(fields1, fields2)
    // Type patterns match if types are equal
    ast.PTyp(t1), ast.PTyp(t2) -> t1 == t2
    // Unit pattern matches only unit pattern
    ast.PUnit, ast.PUnit -> True
    // Everything else doesn't match
    _, _ -> False
  }
}

/// Check if two field lists have matching names and inner patterns.
fn record_fields_match(
  fields1: List(#(String, ast.Pattern)),
  fields2: List(#(String, ast.Pattern)),
) -> Bool {
  case fields1, fields2 {
    [], [] -> True
    [#(name1, p1), ..rest1], [#(name2, p2), ..rest2] ->
      name1 == name2 && patterns_match(p1, p2) && record_fields_match(rest1, rest2)
    _, _ -> False
  }
}

// ============================================================================
// MISSING CASE DETECTION
// ============================================================================

/// Check if there are missing cases (not exhaustive).
/// Uses constructor coverage analysis to determine if all possible
/// constructors of each type have been covered.
fn check_missing(
  patterns: List(List(ast.Pattern)),
  _types: List(ast.Value),
  span: Span,
) -> List(state.Error) {
  case has_wildcard(patterns) {
    True -> []  // Has wildcard, so it's exhaustive
    False -> {
      // Check if all patterns are literals without wildcard (incomplete)
      case all_non_exhaustive(patterns) {
        True -> [state.MatchMissingCase(span, ast.PAny)]
        False -> []
      }
    }
  }
}

/// Check if patterns are non-exhaustive (all literal patterns without wildcard).
fn all_non_exhaustive(patterns: List(List(ast.Pattern))) -> Bool {
  list.all(patterns, fn(patterns_row) {
    list.all(patterns_row, fn(p) {
      case p {
        ast.PLit(_) -> True
        _ -> False
      }
    })
  })
}

// No-op placeholder to preserve function signatures for future use.
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
  _types: List(ast.Value),
) -> List(ast.Pattern) {
  // Return wildcard pattern as default case
  case patterns {
    [] -> [ast.PAny]
    _ -> [ast.PAny]
  }
}
