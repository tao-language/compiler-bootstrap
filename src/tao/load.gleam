import gleam/list
import simplifile
import tao/ast.{type Stmt}
import tao/error.{type Error}
import tao/parse.{expression}

pub fn module(file: String) -> #(List(Stmt), List(Error)) {
  let #(source, errors) = case simplifile.read(file) {
    Ok(source) -> #(source, [])
    Error(err) -> {
      echo #(file, err)
      todo
    }
  }
  case parse.statements(file, source) {
    Ok(expr) -> #(expr, errors)
    Error(err) -> {
      echo err
      todo
    }
  }
}

pub fn package(
  files: List(String),
) -> #(List(#(String, List(Stmt))), List(Error)) {
  case files {
    [] -> #([], [])
    [file, ..files] -> {
      let #(expr, e1) = module(file)
      let #(pkg, e2) = package(files)
      #([#(file, expr), ..pkg], list.append(e1, e2))
    }
  }
}
