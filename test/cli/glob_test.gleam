import cli/glob.{glob_to_regex}

pub fn glob_to_regex_double_star_test() {
  assert glob_to_regex("a**b") == "a.*?b"
}

pub fn glob_to_regex_star_test() {
  assert glob_to_regex("a*b") == "a[^/]*?b"
  assert glob_to_regex("a\\*b") == "a\\*b"
  assert glob_to_regex("a\\**b") == "a\\*[^/]*?b"
}

pub fn glob_to_regex_plus_test() {
  assert glob_to_regex("a+b") == "a\\+b"
}

pub fn glob_to_regex_question_test() {
  assert glob_to_regex("a?b") == "a\\?b"
}

pub fn glob_to_regex_dot_test() {
  assert glob_to_regex("a.b") == "a\\.b"
}

pub fn glob_to_regex_or_test() {
  assert glob_to_regex("a|b") == "a|b"
}

pub fn glob_to_regex_paren_test() {
  assert glob_to_regex("a(b)c") == "a\\(b\\)c"
}

pub fn glob_to_regex_bracket_test() {
  assert glob_to_regex("a[b]c") == "a\\[b\\]c"
}

pub fn glob_to_regex_caret_test() {
  assert glob_to_regex("a^b") == "a\\^b"
}

pub fn glob_to_regex_dollar_test() {
  assert glob_to_regex("a$b") == "a\\$b"
}

pub fn glob_to_regex_backslash_test() {
  assert glob_to_regex("a\\b") == "a\\\\b"
}
