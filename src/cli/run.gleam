/// CLI Run Command — compile and evaluate Core programs
///
/// Usage:
///   compiler <filename.core>           # Run a Core file
///   compiler -c 'expression'           # Run an inline expression
///   compiler --help                    # Show help
///   compiler --debug <filename>        # Run with debug output

import core/eval.{evaluate}
import core/infer.{infer}
import core/quote.{quote}
import core/state.{initial_state, type Error, TypeMismatch, VarUndefined, HoleUnsolved, NotAFunction, CtrUndefined, MatchMissing, MatchRedundant, StepLimitExceeded, CtorArgTypeMismatch, CtorNotFound}
import core/syntax.{parse}
import gleam/int
import gleam/io
import gleam/list
import gleam/float
import gleam/string
import simplifile
import syntax/grammar.{type ParseError, ParseError as ParseErrorCtor}
import core/ast.{type Value, type Head, VLit, VNeut, VCtr, VPi, VLam, VRcd, VRcdT, VTyp, VTypeDef, VErr, HVar, HHole, Int, Float as AstFloat}
import gleam/option.{Some, None}

/// CLI command types.
pub type Command {
  Run(source: Source, verbose: Bool, debug: Bool)
  Check(source: Source, verbose: Bool, debug: Bool)
  Help
}

/// Where the source comes from.
pub type Source {
  File(path: String)
  Inline(expression: String)
}

/// Parse command-line arguments into a Command.
pub fn parse_args(args: List(String)) -> Result(Command, String) {
  case args {
    ["--help", .._] -> Ok(Help)
    ["--debug", path, ..rest] ->
      case rest {
        [] -> Ok(Run(File(path), False, True))
        _ -> Error("Too many arguments for --debug")
      }
    ["-c", expr, ..rest] ->
      case rest {
        [] -> Ok(Run(Inline(expr), False, False))
        _ -> Error("Too many arguments after -c expression")
      }
    [path, ..rest] ->
      case rest {
        [] -> Ok(Run(File(path), False, False))
        _ -> Error("Too many arguments")
      }
    _ -> Ok(Help)
  }
}

/// Show help message.
pub fn show_help() -> Nil {
  io.println("Compiler Bootstrap — Core language")
  io.println("")
  io.println("Usage:")
  io.println("  compiler <filename.core>        Run a Core file")
  io.println("  compiler -c 'expression'        Run an inline expression")
  io.println("  compiler --help                 Show this help")
  io.println("  compiler --debug <path>         Run with debug output")
}

/// Execute a command.
pub fn run_command(command: Command) -> Nil {
  case command {
    Help -> {
      show_help()
      cli_halt(0)
    }
    Run(source, _, _) -> run_source(source)
    Check(source, _, _) -> check_source(source)
  }
}

/// Run a source (parse, infer, evaluate, print).
pub fn run_source(source: Source) -> Nil {
  let result = execute(source)
  case result {
    Ok(value) -> {
      io.println(format_value(value))
      cli_halt(0)
    }
    Error(errors) -> {
      list.each(errors, fn(e) { io.println("Error: " <> e) })
      cli_halt(1)
    }
  }
}

/// Check (type-check only) a source without evaluating.
pub fn check_source(source: Source) -> Nil {
  let result = execute(source)
  case result {
    Ok(value) -> {
      let type_val = evaluate(initial_state([]), quote(value))
      io.println("Result type: " <> format_type(type_val))
      cli_halt(0)
    }
    Error(errors) -> {
      list.each(errors, fn(e) { io.println("Error: " <> e) })
      cli_halt(1)
    }
  }
}

/// Run the full pipeline: parse → infer → evaluate.
pub fn execute(source: Source) -> Result(Value, List(String)) {
  let contents = case source {
    File(path) -> load_file(path)
    Inline(expr) -> Ok(expr)
  }

  case contents {
    Error(msg) -> Error([msg])
    Ok(text) -> {
      let #(term, parse_errors) = parse(text)
      let error_msgs = format_parse_errors(parse_errors)
      let all_errors = case error_msgs {
        [] -> []
        errs -> {
          list.each(errs, fn(e) { io.println("Parse error: " <> e) })
          errs
        }
      }

      let state = initial_state([])
      let #(value, _, final_state) = infer(state, term)
      let type_errors = format_state_errors(final_state.errors)
      let all_errors = list.append(all_errors, type_errors)

      case all_errors {
        [] -> Ok(value)
        errs -> Error(errs)
      }
    }
  }
}

/// Load file contents from disk.
pub fn load_file(path: String) -> Result(String, String) {
  case simplifile.read(path) {
    Ok(contents) -> Ok(contents)
    Error(err) -> case err {
      simplifile.Enoent -> Error("File not found: " <> path)
      simplifile.Eacces -> Error("Permission denied: " <> path)
      _ -> Error("Cannot read file: " <> path)
    }
  }
}

fn format_parse_errors(errors: List(ParseError)) -> List(String) {
  list.map(errors, fn(e) {
    case e {
      ParseErrorCtor(expected: exp, got: got, span: _, context: _) ->
        "expected " <> exp <> ", got " <> got
    }
  })
}

fn format_state_errors(errors: List(Error)) -> List(String) {
  list.map(errors, fn(e) {
    case e {
      TypeMismatch(expected: _, got: _, span: _) -> "Type mismatch"
      VarUndefined(name: name, span: _) -> "Undefined variable: " <> name
      HoleUnsolved(id: id, span: _) -> "Unsolved hole: ?" <> int.to_string(id)
      NotAFunction(fun_type: _, span: _) -> "Not a function"
      CtrUndefined(tag: tag, span: _) -> "Undefined constructor: " <> tag
      MatchMissing(patterns: patterns, covered: _, span: _) ->
        "Missing match cases: " <> string.join(patterns, with: ", ")
      MatchRedundant(span: _) -> "Redundant match case"
      StepLimitExceeded(steps: s, span: _) -> "Step limit exceeded: " <> int.to_string(s)
      CtorArgTypeMismatch(tag: tag, ..) -> "Constructor '" <> tag <> "' argument type mismatch"
      CtorNotFound(tag: tag, span: _) -> "Constructor '" <> tag <> "' not found"
    }
  })
}

fn format_value(value: Value) -> String {
  case value {
    VLit(Int(v)) -> int.to_string(v)
    VLit(AstFloat(v)) -> float.to_string(v)
    VNeut(head, _) -> format_head(head)
    VPi(_env, _implicits, domain, codomain) ->
      "$pi(" <> domain.0 <> ": " <> format_type(domain.1) <> ") -> " <> format_type(codomain)
    VCtr(tag, arg) -> "#" <> tag <> "(" <> format_value(arg) <> ")"
    VRcd(fields) -> "{ " <> string.join(list.map(fields, fn(f) { f.0 <> ": " <> format_value(f.1) }), with: ", ") <> " }"
    VRcdT(fields) ->
      "${ " 
      <> string.join(
        list.map(fields, fn(f) {
          let field_str = f.0 <> ": " <> format_value(f.1)
          case f.2 {
            Some(d) -> field_str <> " = " <> format_value(d)
            None -> field_str
          }
        }),
        with: ", ",
      )
      <> " }"
    VLam(_env, _implicits, param, _) -> "$fn(" <> param.0 <> ") => <lambda>"
    VTypeDef(name: n, constructors: _) -> "<VTypeDef " <> n <> ">"
    VTyp(level) -> "$Type<" <> int.to_string(level) <> ">"
    VErr -> "<error>"
  }
}

fn format_head(head: Head) -> String {
  case head {
    HVar(level) -> "v" <> int.to_string(level)
    HHole(id) -> "?" <> int.to_string(id)
  }
}

fn format_type(type_val: Value) -> String {
  case type_val {
    VNeut(HVar(0), _) -> "$Type"
    VNeut(HVar(1), _) -> "$Int"
    VCtr(tag, arg) -> "#" <> tag <> "(" <> format_type(arg) <> ")"
    VPi(_env, _implicits, domain, codomain) ->
      "$pi(" <> domain.0 <> ": " <> format_type(domain.1) <> ") -> " <> format_type(codomain)
    VRcd(_) -> "{}"
    VLam(_, _, _, _) -> "<lambda>"
    VTypeDef(name: n, constructors: _) -> "<type " <> n <> ">"
    VErr -> "<error type>"
    _ -> "<type>"
  }
}

/// External: halt the Erlang VM with the given exit code.
@external(erlang, "erlang", "halt")
pub fn cli_halt(code: Int) -> a
