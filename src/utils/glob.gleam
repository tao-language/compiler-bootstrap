import gleam/list
import gleam/regexp
import gleam/string

pub fn glob_compile(patterns: List(String)) -> regexp.Regexp {
  let pattern = list.map(patterns, glob_to_regex) |> string.join("|")
  let assert Ok(re) = regexp.from_string(pattern)
  re
}

pub fn glob_match(text: String, patterns: List(String)) -> Bool {
  let re = glob_compile(patterns)
  regexp.check(re, text)
}

pub fn glob_to_regex(pattern: String) -> String {
  pattern
  |> string.replace("\\", "\\\\")
  |> string.replace(".", "\\.")
  |> string.replace("^", "\\^")
  |> string.replace("$", "\\$")
  |> string.replace("?", "\\?")
  |> string.replace("+", "\\+")
  |> string.replace("(", "\\(")
  |> string.replace(")", "\\)")
  |> string.replace("[", "\\[")
  |> string.replace("]", "\\]")
  |> string.replace("*", "[^/]*?")
  |> string.replace("\\\\[^/]*?", "\\*")
  |> string.replace("[^/]*?[^/]*?", ".*?")
}
