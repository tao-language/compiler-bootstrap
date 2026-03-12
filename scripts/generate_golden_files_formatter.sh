#!/bin/bash
# Generate golden files for all E2E test examples using error_formatter
# 
# This script generates golden files that match the test output format.
# It uses the error_formatter module directly for consistent output.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_DIR"

echo "Generating golden files using error_formatter..."
echo ""

# Create a temporary Gleam script to generate golden files
cat > /tmp/gen_golden.gleam << 'GLEAM_SCRIPT'
import core/core.{type Error, SyntaxError, initial_state, infer}
import core/color.{no_color}
import core/error_formatter
import core/syntax
import gleam/list
import gleam/string
import simplifile

fn process_category(category: String, files: List(String)) {
  list.each(files, fn(file) {
    let output_file = string.replace(file, ".core.tao", ".output.txt")
    let assert Ok(source) = simplifile.read(file)
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
    
    case all_errors {
      [] -> {
        // Success case
        let output = "✓ Type checking " <> file <> "\n✓ Evaluating...\nResult: <term>"
        let assert Ok(_) = simplifile.write(output_file, output)
        io.println("Generated (success): " <> output_file)
      }
      errors -> {
        // Error case
        let output = errors
          |> list.map(fn(err) {
            error_formatter.format_error_with_config(err, source, file, no_color)
          })
          |> string.join("\n")
        let assert Ok(_) = simplifile.write(output_file, output)
        io.println("Generated (error): " <> output_file)
      }
    }
  })
}

pub fn main() {
  // Type errors
  process_category("type_errors", [
    "examples/core/errors/type_errors/01_param_type_mismatch.core.tao",
    "examples/core/errors/type_errors/02_annotation_mismatch.core.tao",
    "examples/core/errors/type_errors/03_not_a_function.core.tao",
    "examples/core/errors/type_errors/05_constructor.core.tao",
    "examples/core/errors/type_errors/07_hole.core.tao",
  ])
  
  // Syntax errors
  process_category("syntax_errors", [
    "examples/core/errors/syntax_errors/01_double_arrow.core.tao",
    "examples/core/errors/syntax_errors/01_unexpected_token.core.tao",
    "examples/core/errors/syntax_errors/02_leading_arrow.core.tao",
    "examples/core/errors/syntax_errors/02_malformed_match.core.tao",
    "examples/core/errors/syntax_errors/03_leading_colon.core.tao",
    "examples/core/errors/syntax_errors/04_bare_hash.core.tao",
    "examples/core/errors/syntax_errors/05_bare_dollar.core.tao",
    "examples/core/errors/syntax_errors/06_unclosed_paren.core.tao",
    "examples/core/errors/syntax_errors/07_unclosed_brace.core.tao",
  ])
  
  // Syntax recovery
  process_category("syntax_recovery", [
    "examples/core/errors/syntax_recovery/01_trailing_operator.core.tao",
    "examples/core/errors/syntax_recovery/02_extra_closing_paren.core.tao",
  ])
}
GLEAM_SCRIPT

# Run the script
gleam run /tmp/gen_golden.gleam 2>&1 | grep -E "(Generated|Error)"

# Clean up
rm -f /tmp/gen_golden.gleam

echo ""
echo "✅ Golden file generation complete!"
echo ""
echo "Review the changes with: git diff examples/core/"
