// Quick script to regenerate golden files for syntax_errors
import core/core.{type Error, SyntaxError, initial_state, infer}
import core/color.{no_color}
import core/error_formatter
import core/syntax
import gleam/list
import gleam/result
import gleam/string
import simplifile

pub fn main() {
  let files = [
    "examples/core/errors/syntax_errors/01_double_arrow.core.tao",
    "examples/core/errors/syntax_errors/01_unexpected_token.core.tao",
    "examples/core/errors/syntax_errors/02_leading_arrow.core.tao",
    "examples/core/errors/syntax_errors/02_malformed_match.core.tao",
    "examples/core/errors/syntax_errors/03_leading_colon.core.tao",
    "examples/core/errors/syntax_errors/04_bare_hash.core.tao",
    "examples/core/errors/syntax_errors/05_bare_dollar.core.tao",
    "examples/core/errors/syntax_errors/06_unclosed_paren.core.tao",
    "examples/core/errors/syntax_errors/07_unclosed_brace.core.tao",
  ]
  
  list.each(files, fn(file) {
    let output_file = string.replace(file, ".core.tao", ".output.txt")
    use source <- result.map_error(simplifile.read(file), fn(_) { "Failed to read " <> file })
    let parse_result = syntax.parse(source)
    let syntax_errors = parse_result.errors |> list.map(fn(e) {
      case e {
        syntax.ParseError(span, expected, got, context) -> {
          SyntaxError(span, expected, got, context)
        }
      }
    })
    
    let #(_value, _typ, state) = infer(initial_state, parse_result.ast)
    let all_errors = list.append(syntax_errors, state.errors)
    
    let output = all_errors
      |> list.map(fn(err) {
        error_formatter.format_error_with_config(err, source, file, no_color)
      })
      |> string.join("\n")
    
    case simplifile.write(output_file, output) {
      Ok(_) -> io.println("Generated: " <> output_file)
      Error(_) -> io.println("Failed to write: " <> output_file)
    }
  })
}
