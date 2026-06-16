import gleam/list
import gleam/regexp
import gleam/string

pub fn test_(paths: List(String), patterns: List(String)) {
  todo
}
// fn compile_patterns(patterns: List(String)) -> regexp.Regexp {
//   let str =
//     patterns
//     |> list.map(fn(p) { string.replace(p, "*", ".*?") })
//     |> string.join("|")
//   regexp.from_string()
//   todo
// }
