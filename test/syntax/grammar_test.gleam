// ============================================================================
// GRAMMAR TESTS
// ============================================================================
/// Tests for the syntax/grammar module (parser + formatter).
import gleeunit
import syntax/grammar.{empty, text, line, space, hardline, concat, append, group, nest, join, space_sep, comma_sep, parens, braces, brackets, format_flat}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

pub fn test_empty_document_test() {
  assert format_flat(empty()) == ""
}

pub fn test_text_document_test() {
  assert format_flat(text("hello")) == "hello"
  assert format_flat(text("")) == ""
}

pub fn test_line_break_test() {
  assert format_flat(line()) == " "
}

pub fn test_hard_line_test() {
  assert format_flat(hardline()) == "\n"
}

pub fn test_concat_documents_test() {
  assert format_flat(concat([text("a"), text("b")])) == "ab"
  assert format_flat(concat([text("a"), text("b"), text("c")])) == "abc"
}

pub fn test_append_documents_test() {
  assert format_flat(append(text("a"), text("b"))) == "ab"
}

pub fn test_group_document_test() {
  assert format_flat(group(text("hello"))) == "hello"
}

pub fn test_nest_document_test() {
  // Nesting is ignored in flat layout
  assert format_flat(nest(4, text("hello"))) == "hello"
}

pub fn test_space_sep_test() {
  assert format_flat(space_sep([text("a"), text("b"), text("c")])) == "a b c"
}

pub fn test_comma_sep_test() {
  assert format_flat(comma_sep([text("a"), text("b"), text("c")])) == "a,b,c"
}

pub fn test_join_test() {
  assert format_flat(join(text(","), [text("a"), text("b")])) == "a,b"
}

pub fn test_parens_test() {
  assert format_flat(parens(text("hello"))) == "(hello)"
}

pub fn test_braces_test() {
  assert format_flat(braces(text("hello"))) == "{hello}"
}

pub fn test_brackets_test() {
  assert format_flat(brackets(text("hello"))) == "[hello]"
}

pub fn test_nested_formatting_test() {
  let doc = concat([
    text("let "),
    text("x"),
    space(),
    text("="),
    space(),
    text("42"),
  ])
  assert format_flat(doc) == "let x = 42"
}
