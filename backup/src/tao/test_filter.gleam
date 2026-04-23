// ============================================================================
// TAO TEST FILTER
// ============================================================================
/// Filter tests by name patterns with wildcard support.
///
/// Supports:
/// - Exact match: `"integer addition"`
/// - Prefix: `"parse *"`
/// - Suffix: `"* addition"`
/// - Substring: `"*add*"`
/// - Multiple patterns (OR logic)
///
/// For detailed documentation see:
/// - **[../plans/tao/11-test-system.md](../plans/tao/11-test-system.md)** - Test system specification
import tao/test_parser.{type Test, type Annotation, Skip, Timeout, Group, IO, Retry, Requires}
import gleam/string
import gleam/list
import gleam/option.{Some, None, type Option}
import gleam/result

// ============================================================================
// WILDCARD PATTERN MATCHING
// ============================================================================

/// Check if a test name matches a wildcard pattern.
///
/// Examples:
/// - `"parse *"` matches `"parse integer"`, `"parse expression"`
/// - `"* addition"` matches `"integer addition"`, `"float addition"`
/// - `"*add*"` matches `"add"`, `"addition"`, `"padding"`
/// - `"exact"` matches only `"exact"`
pub fn matches_pattern(pattern: String, test_name: String) -> Bool {
  // Handle wildcard patterns
  case string.contains(pattern, "*") {
    False -> {
      // Exact match
      pattern == test_name
    }
    True -> {
      // Wildcard match
      wildcard_match(pattern, test_name)
    }
  }
}

/// Perform wildcard matching.
fn wildcard_match(pattern: String, text: String) -> Bool {
  // Split pattern by wildcards
  let parts = string.split(pattern, "*")
  
  case parts {
    [] -> True  // Empty pattern matches everything
    [part] -> text == part  // No wildcards (shouldn't happen, but handle it)
    [prefix, ..rest] -> {
      // Check if text starts with prefix (if prefix is not empty)
      let starts_ok = case prefix {
        "" -> True
        _ -> string.starts_with(text, prefix)
      }
      
      case starts_ok {
        False -> False
        True -> {
          // Get remaining text after prefix
          let remaining = case prefix {
            "" -> text
            _ -> string.drop_start(text, string.length(prefix))
          }
          
          // Check all middle parts
          check_middle_parts(rest, remaining)
        }
      }
    }
  }
}

/// Check middle parts of wildcard pattern.
fn check_middle_parts(parts: List(String), text: String) -> Bool {
  case parts {
    [] -> True  // No more parts to match
    [last] -> {
      // Last part - check if text ends with it
      case last {
        "" -> True  // Trailing wildcard
        _ -> string.ends_with(text, last)
      }
    }
    [part, ..rest] -> {
      case part {
        "" -> {
          // Empty part (consecutive wildcards), skip
          check_middle_parts(rest, text)
        }
        _ -> {
          // Find part in text
          case find_substring(text, part) {
            Some(index) -> {
              // Continue with remaining text after this part
              let remaining = string.drop_start(text, index + string.length(part))
              check_middle_parts(rest, remaining)
            }
            None -> False
          }
        }
      }
    }
  }
}

/// Find the index of a substring in a string.
fn find_substring(text: String, substring: String) -> Option(Int) {
  find_substring_helper(text, substring, 0)
}

fn find_substring_helper(text: String, substring: String, offset: Int) -> Option(Int) {
  case string.contains(text, substring) {
    False -> None
    True -> {
      // Find the index by checking prefixes
      find_index(text, substring, offset)
    }
  }
}

fn find_index(text: String, substring: String, offset: Int) -> Option(Int) {
  let sub_len = string.length(substring)
  let text_len = string.length(text)
  
  case text_len < sub_len {
    True -> None
    False -> {
      case string.starts_with(text, substring) {
        True -> Some(offset)
        False -> {
          // Try next position
          find_index(
            string.drop_start(text, 1),
            substring,
            offset + 1,
          )
        }
      }
    }
  }
}

// ============================================================================
// TEST FILTERING
// ============================================================================

/// Filter tests by patterns. A test matches if it matches ANY pattern.
///
/// Also matches against filename (without extension).
pub fn filter_tests(
  tests: List(Test),
  patterns: List(String),
  file: String,
) -> List(Test) {
  let file_base = file_base_name(file)
  
  list.filter(tests, fn(test_item) {
    test_matches_any(test_item, patterns, file_base)
  })
}

/// Check if a test matches any of the patterns.
fn test_matches_any(test_item: Test, patterns: List(String), file_base: String) -> Bool {
  case patterns {
    [] -> True  // No patterns = match all
    [pattern, ..rest] -> {
      matches_pattern(pattern, test_item.name)
      || matches_pattern(pattern, file_base)
      || test_matches_any(test_item, rest, file_base)
    }
  }
}

/// Extract base name from file path (without directory or extension).
///
/// Examples:
/// - `"src/parser.tao"` → `"parser"`
/// - `"tests/math_test.tao"` → `"math_test"`
pub fn file_base_name(file: String) -> String {
  // Get just the filename (no directory)
  let filename = case string.split(file, "/") {
    [] -> file
    parts -> list.last(parts) |> result.unwrap(file)
  }
  
  // Remove extension
  case string.split(filename, ".") {
    [] -> filename
    [_] -> filename
    [name, ..] -> name
  }
}

/// Get all test names (for --list option).
pub fn list_test_names(tests: List(Test)) -> List(String) {
  list.map(tests, fn(test_item) { test_item.name })
}

/// Count tests by annotation type.
pub fn count_by_annotation(tests: List(Test)) -> AnnotationCounts {
  let initial = AnnotationCounts(0, 0, 0, 0, 0)

  list.fold(tests, initial, fn(acc, test_item) {
    count_annotations(acc, test_item.annotations)
  })
}

/// Annotation counts.
pub type AnnotationCounts {
  AnnotationCounts(
    total: Int,
    skip: Int,
    timeout: Int,
    group: Int,
    io: Int,
  )
}

/// Count annotations in a list.
fn count_annotations(counts: AnnotationCounts, annotations: List(Annotation)) -> AnnotationCounts {
  list.fold(annotations, counts, fn(acc, ann) {
    increment_annotation_count(acc, ann)
  })
}

/// Increment the appropriate count based on annotation type.
fn increment_annotation_count(counts: AnnotationCounts, ann: Annotation) -> AnnotationCounts {
  case ann {
    Skip(_) -> increment_skip(counts)
    Timeout(_) -> increment_timeout(counts)
    Group(_) -> increment_group(counts)
    IO -> increment_io(counts)
    Retry(_) -> increment_total(counts)
    Requires(_) -> increment_total(counts)
  }
}

fn increment_total(counts: AnnotationCounts) -> AnnotationCounts {
  let AnnotationCounts(total, skip, timeout, group, io) = counts
  AnnotationCounts(total + 1, skip, timeout, group, io)
}

fn increment_skip(counts: AnnotationCounts) -> AnnotationCounts {
  let AnnotationCounts(total, skip, timeout, group, io) = counts
  AnnotationCounts(total + 1, skip + 1, timeout, group, io)
}

fn increment_timeout(counts: AnnotationCounts) -> AnnotationCounts {
  let AnnotationCounts(total, skip, timeout, group, io) = counts
  AnnotationCounts(total + 1, skip, timeout + 1, group, io)
}

fn increment_group(counts: AnnotationCounts) -> AnnotationCounts {
  let AnnotationCounts(total, skip, timeout, group, io) = counts
  AnnotationCounts(total + 1, skip, timeout, group + 1, io)
}

fn increment_io(counts: AnnotationCounts) -> AnnotationCounts {
  let AnnotationCounts(total, skip, timeout, group, io) = counts
  AnnotationCounts(total + 1, skip, timeout, group, io + 1)
}

// ============================================================================
