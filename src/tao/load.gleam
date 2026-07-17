import core/error as e
import filepath
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/order
import gleam/string
import simplifile
import syntax/span.{type Span, Span}
import tao/ast.{type Module, type Stmt}
import tao/parse.{expression, statements}
import utils/fs

pub fn file(full_filename: String) -> #(List(Stmt), List(e.Error)) {
  let #(source, errors) = case simplifile.read(full_filename) {
    Ok(source) -> #(source, [])
    Error(err) -> #("", [
      read_error(simplifile.describe_error(err), full_filename),
    ])
  }
  let #(stmts, errors) = case statements(full_filename, source) {
    Ok(stmts) -> #(stmts, errors)
    Error(parse_err) -> #([], list.append(errors, [parse_err]))
  }
  #(stmts, errors)
}

pub fn module(
  paths: List(String),
  filename: String,
) -> #(Module, List(e.Error)) {
  let #(stmts, errors) = case find_file(paths, filename) {
    Some(full_filename) -> file(full_filename)
    None -> #([], [read_error("File not found", filename)])
  }
  let name = "/" <> filepath.strip_extension(filename)
  #(#(name, stmts), errors)
}

pub fn module_list(
  paths: List(String),
  filenames: List(String),
) -> #(List(#(String, List(Stmt))), List(e.Error)) {
  case filenames {
    [] -> #([], [])
    [filename, ..filenames] -> {
      let #(mod, e1) = module(paths, filename)
      let #(mods, e2) = module_list(paths, filenames)
      #([mod, ..mods], list.append(e1, e2))
    }
  }
}

pub fn directory(dir: String) -> #(List(Module), List(e.Error)) {
  let #(files, e1) = case fs.list_recursive(dir, string.ends_with(_, ".tao")) {
    Ok(files) -> #(files, [])
    Error(msg) -> #([], [read_error(msg, dir)])
  }
  let #(mods, e2) = module_list([dir], files)
  #(mods, list.append(e1, e2))
}

pub fn package(
  paths: List(String),
  name: String,
  version: Option(String),
) -> #(List(Module), List(e.Error)) {
  case find_dir(paths, name) {
    Some(pkg_base_dir) ->
      case find_version(pkg_base_dir, version) {
        Some(pkg_dir) -> {
          let #(mods, errors) = directory(pkg_dir)
          let mods =
            list.map(mods, fn(mod) {
              let #(mod_name, stmts) = mod
              #("/" <> name <> mod_name, stmts)
            })
          #(mods, errors)
        }
        None -> {
          let version_name = option.unwrap(version, "latest")
          let pkg_name = name <> ":" <> version_name
          #([], [read_error("package not found", pkg_name)])
        }
      }
    None -> #([], [read_error("package not found", name)])
  }
}

fn find_version(dir: String, opt_version: Option(String)) -> Option(String) {
  case opt_version {
    Some(version) -> {
      let full_dir = filepath.join(dir, version)
      case simplifile.is_directory(full_dir) {
        Ok(True) -> Some(full_dir)
        _ -> None
      }
    }
    None ->
      case simplifile.read_directory(dir) {
        Ok(versions) -> {
          case list.sort(versions, order.reverse(string.compare)) {
            [] -> None
            [version, ..] -> find_version(dir, Some(version))
          }
        }
        _ -> None
      }
  }
}

pub fn package_list(
  paths: List(String),
  packages: List(#(String, Option(String))),
) -> #(List(Module), List(e.Error)) {
  case packages {
    [] -> #([], [])
    [#(name, version), ..packages] -> {
      let #(mods1, err1) = package(paths, name, version)
      let #(mods2, err2) = package_list(paths, packages)
      #(list.append(mods1, mods2), list.append(err1, err2))
    }
  }
}

fn find_file(paths: List(String), filename: String) -> Option(String) {
  find_with(simplifile.is_file, paths, filename)
}

fn find_dir(paths: List(String), filename: String) -> Option(String) {
  find_with(simplifile.is_directory, paths, filename)
}

fn find_with(
  check: fn(String) -> Result(Bool, _),
  paths: List(String),
  filename: String,
) -> Option(String) {
  case paths {
    [] ->
      case check(filename) {
        Ok(True) -> Some(filename)
        _ -> None
      }
    [path, ..paths] -> {
      let full_filename = filepath.join(path, filename)
      case check(full_filename) {
        Ok(True) -> Some(full_filename)
        _ -> find_file(paths, filename)
      }
    }
  }
}

fn read_error(message: String, file: String) -> e.Error {
  e.Error(
    // TODO: use a proper error type
    e.SyntaxError(message <> ": " <> file),
    Span(file, 0, 0, 0, 0),
    [],
  )
}
