// ============================================================================
// FORMATTER TESTS (Simplified)
// ============================================================================

import gleeunit
import gleeunit/should
import formatter

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// BASIC CONSTRUCTOR TESTS
// ============================================================================

pub fn empty_test() {
  formatter.empty() |> should.equal(formatter.Empty)
}

pub fn text_test() {
  formatter.text("hello") |> should.equal(formatter.Text("hello"))
}

pub fn text_empty_test() {
  formatter.text("") |> should.equal(formatter.Empty)
}

pub fn space_test() {
  formatter.space() |> should.equal(formatter.Text(" "))
}

pub fn line_test() {
  formatter.line() |> should.equal(formatter.Line)
}

pub fn hardline_test() {
  formatter.hardline() |> should.equal(formatter.HardLine)
}

// ============================================================================
// COMBINATOR TESTS
// ============================================================================

pub fn concat_test() {
  let doc = formatter.concat([formatter.text("hello"), formatter.text("world")])
  doc |> should.equal(formatter.Concat([formatter.Text("hello"), formatter.Text("world")]))
}

pub fn concat_empty_test() {
  formatter.concat([]) |> should.equal(formatter.Empty)
}

pub fn concat_single_test() {
  formatter.concat([formatter.text("hello")]) |> should.equal(formatter.Text("hello"))
}

pub fn append_test() {
  let doc = formatter.append(formatter.text("hello"), formatter.text("world"))
  doc |> should.equal(formatter.Concat([formatter.Text("hello"), formatter.Text("world")]))
}

pub fn group_test() {
  let doc = formatter.group(formatter.text("hello"))
  doc |> should.equal(formatter.Group(formatter.Text("hello")))
}

pub fn nest_test() {
  let doc = formatter.nest(2, formatter.text("hello"))
  doc |> should.equal(formatter.Nest(2, formatter.Text("hello")))
}

pub fn join_test() {
  let doc = formatter.join(formatter.space(), [formatter.text("a"), formatter.text("b")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a b")
}

// ============================================================================
// CONVENIENCE COMBINATOR TESTS
// ============================================================================

pub fn hsep_test() {
  let doc = formatter.hsep([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a b c")
}

pub fn vsep_test() {
  let doc = formatter.vsep([formatter.text("a"), formatter.text("b")])
  let rendered = formatter.render_default(doc)
  // vsep uses hard line breaks with indentation
  rendered |> should.equal("a\n b")
}

pub fn comma_sep_test() {
  let doc = formatter.comma_sep([formatter.text("a"), formatter.text("b")])
  let rendered = formatter.render_default(doc)
  // Comma sep uses soft line breaks, so it renders on one line if it fits
  rendered |> should.equal("a, b")
}

pub fn parens_test() {
  let doc = formatter.parens(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("(x)")
}

pub fn braces_test() {
  let doc = formatter.braces(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  // Braces uses soft line breaks, so it renders on one line if it fits
  rendered |> should.equal("{ x }")
}

pub fn brackets_test() {
  let doc = formatter.brackets(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[x]")
}

pub fn block_test() {
  let doc = formatter.block(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  // Block uses soft line breaks, so it renders on one line if it fits
  rendered |> should.equal("{ x }")
}

pub fn block_empty_test() {
  let doc = formatter.block(formatter.empty())
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("{}")
}

pub fn kw_test() {
  let doc = formatter.kw("let")
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("let ")
}

pub fn opt_semi_true_test() {
  let doc = formatter.opt_semi(True)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal(";")
}

pub fn opt_semi_false_test() {
  let doc = formatter.opt_semi(False)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("")
}

// ============================================================================
// RENDERING TESTS
// ============================================================================

pub fn render_text_test() {
  let doc = formatter.text("hello")
  let rendered = formatter.render(doc, 80)
  rendered |> should.equal("hello")
}

pub fn render_concat_test() {
  let doc = formatter.concat([formatter.text("hello"), formatter.text(" world")])
  let rendered = formatter.render(doc, 80)
  rendered |> should.equal("hello world")
}

pub fn render_line_flat_test() {
  let doc = formatter.group(formatter.concat([formatter.text("hello"), formatter.line(), formatter.text("world")]))
  let rendered = formatter.render(doc, 80)
  rendered |> should.equal("hello world")
}

pub fn render_default_test() {
  let doc = formatter.text("test")
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("test")
}

// ============================================================================
// UTILITY TESTS
// ============================================================================

pub fn int_test() {
  let doc = formatter.int_doc(42)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("42")
}

pub fn float_test() {
  let doc = formatter.float_doc(3.14)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("3.14")
}

pub fn quoted_string_test() {
  let doc = formatter.quoted_string("hello")
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("\"hello\"")
}

pub fn is_empty_test() {
  formatter.is_empty(formatter.empty()) |> should.be_true
}

pub fn is_not_empty_test() {
  formatter.is_empty(formatter.text("x")) |> should.be_false
}

pub fn width_test() {
  formatter.width(formatter.text("hello")) |> should.equal(5)
}

// ============================================================================
// EXPRESSION FORMATTING TESTS
// ============================================================================

pub fn format_expr_no_parens_test() {
  let doc = formatter.format_expr(formatter.text("x"), 10, 5, formatter.Left)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("x")
}

pub fn format_expr_with_parens_test() {
  let doc = formatter.format_expr(formatter.text("x"), 5, 10, formatter.Left)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("(x)")
}

pub fn assoc_from_string_left_test() {
  formatter.assoc_from_string("left") |> should.equal(formatter.Left)
}

pub fn assoc_from_string_right_test() {
  formatter.assoc_from_string("right") |> should.equal(formatter.Right)
}

pub fn assoc_from_string_nonassoc_test() {
  formatter.assoc_from_string("other") |> should.equal(formatter.NonAssoc)
}
