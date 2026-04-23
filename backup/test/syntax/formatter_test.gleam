// ============================================================================
// FORMATTER TESTS
// ============================================================================
/// Tests for the syntax/formatter module.
/// 
/// The formatter provides document algebra for pretty printing with
/// automatic line breaking and configurable indentation.
import gleam/string
import gleeunit
import gleeunit/should
import syntax/formatter

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// BASIC DOCUMENT TESTS
// ============================================================================

pub fn format_empty_test() {
  formatter.render(formatter.empty(), 80) |> should.equal("")
}

pub fn format_text_test() {
  formatter.render(formatter.text("hello"), 80) |> should.equal("hello")
}

pub fn format_text_multiline_test() {
  formatter.render(formatter.text("hello world"), 80)
  |> should.equal("hello world")
}

// ============================================================================
// LINE BREAKING TESTS
// ============================================================================

pub fn format_line_flat_test() {
  // Line should render as space when flat
  let doc = formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ])
  formatter.render(doc, 80) |> should.equal("hello world")
}

pub fn format_line_break_test() {
  // Line should break when width is exceeded (inside a group)
  let doc = formatter.group(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]))
  // With width 10, "hello world" (11 chars) should break
  let result = formatter.render(doc, 10)
  string.contains(result, "\n") |> should.be_true
}

pub fn format_hardline_test() {
  // HardLine should always break
  let doc = formatter.concat([
    formatter.text("hello"),
    formatter.hardline(),
    formatter.text("world"),
  ])
  formatter.render(doc, 80) |> should.equal("hello\nworld")
}

pub fn format_hardline_always_breaks_test() {
  // HardLine should break even with infinite width
  let doc = formatter.concat([
    formatter.text("hello"),
    formatter.hardline(),
    formatter.text("world"),
  ])
  formatter.render(doc, 1000) |> should.equal("hello\nworld")
}

// ============================================================================
// GROUP TESTS
// ============================================================================

pub fn format_group_flat_test() {
  // Group should render flat when it fits
  let doc = formatter.group(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]))
  formatter.render(doc, 80) |> should.equal("hello world")
}

pub fn format_group_break_test() {
  // Group should break when it doesn't fit
  let doc = formatter.group(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]))
  // With width 10, should break
  let result = formatter.render(doc, 10)
  string.contains(result, "\n") |> should.be_true
}

pub fn format_nested_group_test() {
  // Nested groups should break independently
  let inner = formatter.group(formatter.concat([
    formatter.text("inner"),
    formatter.line(),
    formatter.text("text"),
  ]))
  let doc = formatter.group(formatter.concat([
    formatter.text("outer"),
    formatter.line(),
    inner,
  ]))
  formatter.render(doc, 80) |> should.equal("outer inner text")
}

// ============================================================================
// NESTING TESTS
// ============================================================================

pub fn format_nest_test() {
  // Nest should add indentation (note: render trims leading/trailing whitespace)
  let doc = formatter.nest(2, formatter.concat([
    formatter.text("line1"),
    formatter.hardline(),
    formatter.text("indented"),
  ]))
  let result = formatter.render(doc, 80)
  // Should contain "line1" followed by newline, 2 spaces, and "indented"
  string.contains(result, "line1\n  indented") |> should.be_true
}

pub fn format_nest_custom_indent_test() {
  // Nest with custom indent (4 spaces)
  let doc = formatter.nest(4, formatter.concat([
    formatter.text("line1"),
    formatter.hardline(),
    formatter.text("indented"),
  ]))
  let result = formatter.render(doc, 80)
  // Should contain "line1" followed by newline, 4 spaces, and "indented"
  string.contains(result, "line1\n    indented") |> should.be_true
}

pub fn format_nest_multiple_test() {
  // Multiple nests should accumulate (2 + 2 = 4 spaces)
  let doc = formatter.nest(2, formatter.nest(2, formatter.concat([
    formatter.text("line1"),
    formatter.hardline(),
    formatter.text("double"),
  ])))
  let result = formatter.render(doc, 80)
  // Should contain "line1" followed by newline, 4 spaces, and "double"
  string.contains(result, "line1\n    double") |> should.be_true
}

// ============================================================================
// CONCAT TESTS
// ============================================================================

pub fn format_concat_empty_test() {
  formatter.render(formatter.concat([]), 80) |> should.equal("")
}

pub fn format_concat_single_test() {
  formatter.render(formatter.concat([formatter.text("hello")]), 80)
  |> should.equal("hello")
}

pub fn format_concat_multiple_test() {
  formatter.render(formatter.concat([
    formatter.text("hello"),
    formatter.text(" "),
    formatter.text("world"),
  ]), 80) |> should.equal("hello world")
}

pub fn format_concat_with_line_test() {
  formatter.render(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]), 80) |> should.equal("hello world")
}

// ============================================================================
// COMBINATOR TESTS
// ============================================================================

pub fn format_space_sep_test() {
  formatter.render(formatter.space_sep([
    formatter.text("a"),
    formatter.text("b"),
    formatter.text("c"),
  ]), 80) |> should.equal("a b c")
}

pub fn format_comma_sep_test() {
  formatter.render(formatter.comma_sep([
    formatter.text("a"),
    formatter.text("b"),
    formatter.text("c"),
  ]), 80) |> should.equal("a, b, c")
}

pub fn format_parens_test() {
  formatter.render(formatter.parens(formatter.text("x")), 80)
  |> should.equal("(x)")
}

pub fn format_braces_test() {
  formatter.render(formatter.braces(formatter.text("x")), 80)
  |> should.equal("{x}")
}

// ============================================================================
// JOIN TESTS
// ============================================================================

pub fn format_join_empty_test() {
  formatter.render(formatter.join(formatter.text(", "), []), 80)
  |> should.equal("")
}

pub fn format_join_single_test() {
  formatter.render(formatter.join(formatter.text(", "), [
    formatter.text("a"),
  ]), 80) |> should.equal("a")
}

pub fn format_join_multiple_test() {
  formatter.render(formatter.join(formatter.text(", "), [
    formatter.text("a"),
    formatter.text("b"),
    formatter.text("c"),
  ]), 80) |> should.equal("a, b, c")
}

// ============================================================================
// WIDTH TESTS
// ============================================================================

pub fn format_width_small_test() {
  // Small width should force breaks
  let doc = formatter.group(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]))
  formatter.render(doc, 5) |> should.equal("hello\nworld")
}

pub fn format_width_large_test() {
  // Large width should keep flat
  let doc = formatter.group(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]))
  formatter.render(doc, 1000) |> should.equal("hello world")
}

pub fn format_width_exact_test() {
  // Width exactly fitting should stay flat
  let doc = formatter.group(formatter.concat([
    formatter.text("hi"),
    formatter.line(),
    formatter.text("x"),
  ]))
  // "hi x" is 4 chars, width 4 should fit
  formatter.render(doc, 4) |> should.equal("hi x")
}

// ============================================================================
// RENDER MODES TESTS
// ============================================================================

pub fn render_default_test() {
  // render_default should use width 80
  formatter.render_default(formatter.text("hello"))
  |> should.equal("hello")
}

pub fn render_default_group_test() {
  let doc = formatter.group(formatter.concat([
    formatter.text("hello"),
    formatter.line(),
    formatter.text("world"),
  ]))
  formatter.render_default(doc) |> should.equal("hello world")
}

// ============================================================================
// COMPLEX DOCUMENT TESTS
// ============================================================================

pub fn format_complex_nested_test() {
  // Complex nested structure
  let inner = formatter.group(formatter.concat([
    formatter.text("a"),
    formatter.line(),
    formatter.text("b"),
  ]))
  let outer = formatter.group(formatter.concat([
    formatter.text("("),
    formatter.nest(2, formatter.concat([
      formatter.hardline(),
      inner,
    ])),
    formatter.hardline(),
    formatter.text(")"),
  ]))
  let result = formatter.render(outer, 80)
  string.contains(result, "(") |> should.be_true
  string.contains(result, ")") |> should.be_true
}

pub fn format_multiple_lines_test() {
  // Multiple hardlines
  let doc = formatter.concat([
    formatter.text("line1"),
    formatter.hardline(),
    formatter.text("line2"),
    formatter.hardline(),
    formatter.text("line3"),
  ])
  formatter.render(doc, 80) |> should.equal("line1\nline2\nline3")
}

pub fn format_mixed_separators_test() {
  // Mix of spaces and lines
  let doc = formatter.group(formatter.concat([
    formatter.text("a"),
    formatter.line(),
    formatter.text("b"),
    formatter.line(),
    formatter.text("c"),
  ]))
  formatter.render(doc, 80) |> should.equal("a b c")
}
