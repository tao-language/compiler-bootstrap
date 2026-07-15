import core/error as e
import gleam/list
import simplifile
import syntax/span.{type Span, Span}
import tao/ast.{type Stmt}
import tao/parse.{expression, statements}

fn read_error(file: String) -> e.Error {
  e.Error(
    e.SyntaxError("could not read file: " <> file),
    Span(file, 0, 0, 0, 0),
    [],
  )
}

pub fn module(file: String) -> #(List(Stmt), List(e.Error)) {
  let #(source, errors) = case simplifile.read(file) {
    Ok(source) -> #(source, [])
    Error(_) -> #("", [read_error(file)])
  }
  case statements(file, source) {
    Ok(stmts) -> #(stmts, errors)
    Error(parse_err) -> #([], list.append(errors, [parse_err]))
  }
}

pub fn package(
  files: List(String),
) -> #(List(#(String, List(Stmt))), List(e.Error)) {
  case files {
    [] -> #([], [])
    [file, ..files] -> {
      let #(stmts, e1) = module(file)
      let #(pkg, e2) = package(files)
      #([#(file, stmts), ..pkg], list.append(e1, e2))
    }
  }
}
