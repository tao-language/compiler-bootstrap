// ============================================================================
// PARSER TESTS
// ============================================================================

import gleeunit
import gleeunit/should
import parser

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// BASIC PARSER TESTS
// ============================================================================

pub fn parse_token_test() {
  let p = parser.token("hello")
  case parser.parse_string(p, "hello") {
    Ok(parser.TreeToken("hello")) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_token_fail_test() {
  let p = parser.token("hello")
  parser.parse_string(p, "world") |> should.be_error
}

pub fn parse_empty_input_test() {
  let p = parser.token("hello")
  parser.parse_string(p, "") |> should.be_error
}

pub fn parse_any_token_test() {
  let p = parser.any_token()
  case parser.parse_string(p, "anything") {
    Ok(parser.TreeToken("anything")) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// SEQUENCE PARSER TESTS
// ============================================================================

pub fn parse_seq2_test() {
  let p = parser.seq2(parser.token("hello"), parser.token("world"))
  case parser.parse_string(p, "hello world") {
    Ok(parser.TreeNode(
      "Seq",
      [parser.TreeToken("hello"), parser.TreeToken("world")],
    )) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_seq2_fail_test() {
  let p = parser.seq2(parser.token("hello"), parser.token("world"))
  parser.parse_string(p, "hello") |> should.be_error
}

// ============================================================================
// CHOICE PARSER TESTS
// ============================================================================

pub fn parse_choice_first_test() {
  let p = parser.choice(parser.token("a"), parser.token("b"))
  case parser.parse_string(p, "a") {
    Ok(parser.TreeToken("a")) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_choice_second_test() {
  let p = parser.choice(parser.token("a"), parser.token("b"))
  case parser.parse_string(p, "b") {
    Ok(parser.TreeToken("b")) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_choice_fail_test() {
  let p = parser.choice(parser.token("a"), parser.token("b"))
  parser.parse_string(p, "c") |> should.be_error
}

// ============================================================================
// OPTIONAL PARSER TESTS
// ============================================================================

pub fn parse_opt_present_test() {
  let p = parser.opt(parser.token("opt"))
  case parser.parse_string(p, "opt") {
    Ok(parser.TreeToken("opt")) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_opt_absent_test() {
  let p = parser.opt(parser.token("opt"))
  case parser.parse_string(p, "") {
    Ok(parser.TreeToken("")) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// REPETITION PARSER TESTS
// ============================================================================

pub fn parse_rep_zero_test() {
  let p = parser.rep(parser.token("x"))
  case parser.parse_string(p, "") {
    Ok(parser.TreeNode("Rep", [])) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_rep_multiple_test() {
  let p = parser.rep(parser.token("x"))
  case parser.parse_string(p, "x x x") {
    Ok(parser.TreeNode(
      "Rep",
      [parser.TreeToken("x"), parser.TreeToken("x"), parser.TreeToken("x")],
    )) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_rep1_one_test() {
  let p = parser.rep1(parser.token("x"))
  case parser.parse_string(p, "x") {
    Ok(parser.TreeNode("Rep1", [parser.TreeToken("x")])) ->
      True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_rep1_zero_fail_test() {
  let p = parser.rep1(parser.token("x"))
  parser.parse_string(p, "") |> should.be_error
}

pub fn parse_rep1_multiple_test() {
  let p = parser.rep1(parser.token("x"))
  case parser.parse_string(p, "x x x") {
    Ok(parser.TreeNode(
      "Rep1",
      [parser.TreeToken("x"), parser.TreeToken("x"), parser.TreeToken("x")],
    )) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}
