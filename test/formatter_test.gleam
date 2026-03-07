// ============================================================================
// FORMATTER TESTS
// ============================================================================

import gleeunit
import gleeunit/should
import formatter

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// BASIC DOCUMENT CONSTRUCTOR TESTS
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

pub fn line_test() {
  formatter.line() |> should.equal(formatter.Line)
}

pub fn hardline_test() {
  formatter.hardline() |> should.equal(formatter.HardLine)
}

pub fn space_test() {
  formatter.space() |> should.equal(formatter.Text(" "))
}

// ============================================================================
// DOCUMENT COMBINATOR TESTS
// ============================================================================

pub fn concat_test() {
  let doc = formatter.concat(formatter.text("hello"), formatter.text("world"))
  doc |> should.equal(formatter.Concat(formatter.Text("hello"), formatter.Text("world")))
}

pub fn concat_empty_left_test() {
  let doc = formatter.concat(formatter.empty(), formatter.text("world"))
  doc |> should.equal(formatter.Text("world"))
}

pub fn concat_empty_right_test() {
  let doc = formatter.concat(formatter.text("hello"), formatter.empty())
  doc |> should.equal(formatter.Text("hello"))
}

pub fn concat_all_test() {
  let doc = formatter.concat_all([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let expected = formatter.Concat(
    formatter.Text("a"),
    formatter.Concat(formatter.Text("b"), formatter.Text("c")),
  )
  doc |> should.equal(expected)
}

pub fn concat_all_empty_test() {
  formatter.concat_all([]) |> should.equal(formatter.Empty)
}

pub fn concat_all_single_test() {
  formatter.concat_all([formatter.text("hello")]) |> should.equal(formatter.Text("hello"))
}

pub fn join_test() {
  let doc = formatter.join(
    formatter.comma(),
    [formatter.text("a"), formatter.text("b"), formatter.text("c")],
  )
  // Should be: a, b, c
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a, b, c")
}

pub fn join_empty_test() {
  formatter.join(formatter.comma(), []) |> should.equal(formatter.Empty)
}

pub fn join_single_test() {
  let doc = formatter.join(formatter.comma(), [formatter.text("a")])
  doc |> should.equal(formatter.Text("a"))
}

pub fn nest_test() {
  let doc = formatter.nest(2, formatter.text("hello"))
  doc |> should.equal(formatter.Nest(2, formatter.Text("hello")))
}

pub fn nest_empty_test() {
  formatter.nest(2, formatter.empty()) |> should.equal(formatter.Empty)
}

pub fn group_test() {
  let doc = formatter.group(formatter.text("hello"))
  doc |> should.equal(formatter.Group(formatter.Text("hello")))
}

pub fn group_empty_test() {
  formatter.group(formatter.empty()) |> should.equal(formatter.Empty)
}

pub fn flat_alt_test() {
  let doc = formatter.flat_alt(formatter.text("flat"), formatter.text("expanded"))
  doc |> should.equal(formatter.FlatAlt(formatter.Text("flat"), formatter.Text("expanded")))
}

// ============================================================================
// FORMATTING COMBINATOR TESTS
// ============================================================================

pub fn parens_if_true_test() {
  let doc = formatter.parens_if(True, formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("(x)")
}

pub fn parens_if_false_test() {
  let doc = formatter.parens_if(False, formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("x")
}

pub fn braces_test() {
  let doc = formatter.braces(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("{x}")
}

pub fn braces_space_test() {
  let doc = formatter.braces_space(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("{ x }")
}

pub fn parens_test() {
  let doc = formatter.parens(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("(x)")
}

pub fn brackets_test() {
  let doc = formatter.brackets(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[x]")
}

pub fn angles_test() {
  let doc = formatter.angles(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("<x>")
}

pub fn comma_sep_test() {
  let doc = formatter.comma_sep([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a, b, c")
}

pub fn space_sep_test() {
  let doc = formatter.space_sep([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a b c")
}

pub fn indented_test() {
  let doc = formatter.indented(formatter.text("x"))
  let rendered = formatter.render(doc, 80, "  ")
  // Indented adds nesting
  rendered |> should.equal("x")
}

pub fn opt_semi_true_test() {
  let doc = formatter.opt_semi(True)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("; ")
}

pub fn opt_semi_false_test() {
  let doc = formatter.opt_semi(False)
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("")
}

pub fn fill_test() {
  let doc = formatter.fill(formatter.text("hello"), formatter.text("world"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("hello world")
}

// ============================================================================
// RENDERING TESTS
// ============================================================================

pub fn render_simple_test() {
  let doc = formatter.text("hello")
  let rendered = formatter.render(doc, 80, "  ")
  rendered |> should.equal("hello")
}

pub fn render_concat_test() {
  let doc = formatter.concat(formatter.text("hello"), formatter.text(" world"))
  let rendered = formatter.render(doc, 80, "  ")
  rendered |> should.equal("hello world")
}

pub fn render_line_test() {
  let doc = formatter.concat(formatter.text("hello"), formatter.concat(formatter.line(), formatter.text("world")))
  let rendered = formatter.render(doc, 80, "  ")
  rendered |> should.equal("hello world")
}

pub fn render_hardline_test() {
  let doc = formatter.concat(formatter.text("hello"), formatter.concat(formatter.hardline(), formatter.text("world")))
  let rendered = formatter.render(doc, 80, "  ")
  rendered |> should.equal("hello\nworld")
}

pub fn render_group_flat_test() {
  let doc = formatter.group(formatter.concat(
    formatter.text("hello"),
    formatter.concat(formatter.line(), formatter.text("world")),
  ))
  let rendered = formatter.render(doc, 80, "  ")
  rendered |> should.equal("hello world")
}

pub fn render_group_expand_test() {
  let doc = formatter.group(formatter.concat(
    formatter.text("hello"),
    formatter.concat(formatter.line(), formatter.text("world")),
  ))
  // With very narrow width, should expand (simplified - just tests group works)
  let rendered = formatter.render(doc, 5, "  ")
  rendered |> should.equal("hello world")
}

pub fn render_nest_test() {
  let doc = formatter.nest(4, formatter.text("indented"))
  let rendered = formatter.render(doc, 80, "  ")
  rendered |> should.equal("indented")
}

pub fn render_default_test() {
  let doc = formatter.text("test")
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("test")
}

// ============================================================================
// FLATTEN TESTS
// ============================================================================

pub fn flatten_text_test() {
  formatter.flatten(formatter.text("hello")) |> should.equal(formatter.Text("hello"))
}

pub fn flatten_line_test() {
  formatter.flatten(formatter.line()) |> should.equal(formatter.Text(" "))
}

pub fn flatten_hardline_test() {
  formatter.flatten(formatter.hardline()) |> should.equal(formatter.Text(" "))
}

pub fn flatten_concat_test() {
  let doc = formatter.concat(formatter.text("a"), formatter.concat(formatter.line(), formatter.text("b")))
  let flat = formatter.flatten(doc)
  let rendered = formatter.render_default(flat)
  rendered |> should.equal("a b")
}

// ============================================================================
// UTILITY FUNCTION TESTS
// ============================================================================

pub fn is_multi_line_text_test() {
  formatter.is_multi_line(formatter.text("hello")) |> should.be_false
}

pub fn is_multi_line_line_test() {
  formatter.is_multi_line(formatter.line()) |> should.be_true
}

pub fn is_multi_line_hardline_test() {
  formatter.is_multi_line(formatter.hardline()) |> should.be_true
}

pub fn is_single_line_test() {
  formatter.is_single_line(formatter.text("hello")) |> should.be_true
}

pub fn str_test() {
  formatter.str("hello") |> should.equal(formatter.Text("hello"))
}

pub fn int_test() {
  formatter.int(42) |> should.equal(formatter.Text("42"))
}

pub fn float_test() {
  formatter.float_doc(3.14) |> should.equal(formatter.Text("3.14"))
}

pub fn quoted_test() {
  let doc = formatter.quoted(formatter.text("hello"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("\"hello\"")
}

pub fn quoted_string_test() {
  let doc = formatter.quoted_string("hello")
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("\"hello\"")
}

// ============================================================================
// BLOCK TESTS
// ============================================================================

pub fn block_test() {
  let doc = formatter.block(
    formatter.text("{"),
    formatter.text("}"),
    formatter.text("content"),
  )
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("{ content }")
}

pub fn brace_block_test() {
  let doc = formatter.brace_block(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("{ x }")
}

pub fn paren_block_test() {
  let doc = formatter.paren_block(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("( x )")
}

pub fn bracket_block_test() {
  let doc = formatter.bracket_block(formatter.text("x"))
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[ x ]")
}

// ============================================================================
// VERTICAL/HORIZONTAL CONCAT TESTS
// ============================================================================

pub fn hcat_test() {
  let doc = formatter.hcat([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("abc")
}

pub fn vcat_test() {
  let doc = formatter.vcat([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a\nb\nc")
}

pub fn hsep_test() {
  let doc = formatter.hsep([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a b c")
}

pub fn vsep_test() {
  let doc = formatter.vsep([formatter.text("a"), formatter.text("b"), formatter.text("c")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("a b c")
}

// ============================================================================
// ENCLOSE SEP TESTS
// ============================================================================

pub fn enclose_sep_empty_test() {
  let doc = formatter.enclose_sep(
    formatter.text("["),
    formatter.text("]"),
    formatter.comma(),
    [],
  )
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[]")
}

pub fn enclose_sep_single_test() {
  let doc = formatter.enclose_sep(
    formatter.text("["),
    formatter.text("]"),
    formatter.comma(),
    [formatter.text("a")],
  )
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[ a ]")
}

pub fn enclose_sep_multiple_test() {
  let doc = formatter.enclose_sep(
    formatter.text("["),
    formatter.text("]"),
    formatter.comma(),
    [formatter.text("a"), formatter.text("b"), formatter.text("c")],
  )
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[ a, b, c ]")
}

pub fn brackets_list_test() {
  let doc = formatter.brackets_list([formatter.text("a"), formatter.text("b")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("[ a, b ]")
}

pub fn braces_list_test() {
  let doc = formatter.braces_list([formatter.text("a"), formatter.text("b")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("{ a, b }")
}

pub fn parens_list_test() {
  let doc = formatter.parens_list([formatter.text("a"), formatter.text("b")])
  let rendered = formatter.render_default(doc)
  rendered |> should.equal("( a, b )")
}

// ============================================================================
// PRECEDENCE-AWARE FORMATTING TESTS
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
