import core/error as e
import filepath
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/order
import gleam/string
import simplifile
import syntax/span.{Span}
import tao/ast.{type Module, type Stmt, Import, import_all}
import tao/parse.{statements}
import utils/fs

/// The alias of the implicit prelude imports. Names starting with `/` are
/// module paths, never definition names, so this alias cannot collide with
/// user code — and, unlike `""`, it is not positional in `pop_field`, so
/// module records never carry a `""` field.
const implicit_import_alias = "/__prelude__"

/// The name of the prelude package (the standard library). It is an
/// always-present dependency: every project compiles against it, and its
/// modules are implicitly imported into every non-prelude module.
pub const prelude_name = "prelude"

/// Ensure the prelude is in the package list (idempotent). The prelude is
/// an always-present dependency, so every command compiles against it.
pub fn with_prelude(
  packages: List(#(String, Option(String))),
) -> List(#(String, Option(String))) {
  case list.any(packages, fn(p) { p.0 == prelude_name }) {
    True -> packages
    False -> list.append(packages, [#(prelude_name, None)])
  }
}

/// True when a canonical module name belongs to the prelude package
/// (`/prelude` or `/prelude/<…>`).
pub fn is_prelude(name: String) -> Bool {
  name == "/" <> prelude_name
    || string.starts_with(name, "/" <> prelude_name <> "/")
}

/// The prelude modules from a loaded module list.
pub fn prelude_modules(mods: List(Module)) -> List(Module) {
  list.filter(mods, fn(m) { is_prelude(m.0) })
}

/// Append an implicit `import <path> *` to every module that is not itself
/// in `prelude` and does not already import it. The prelude (the standard
/// library) is implicitly imported into every other module, so its names
/// (e.g. the operators `+`, `-`, `*`) are in scope without an explicit
/// `import`. The prelude modules are imported in sorted name order so that
/// when several of them export the same name (e.g. the internal `_or`)
/// the winner is deterministic, not filesystem-order dependent.
pub fn implicit_prelude_imports(
  mods: List(Module),
  prelude: List(Module),
) -> List(Module) {
  let prelude = list.sort(prelude, fn(a, b) { string.compare(a.0, b.0) })
  let prelude_names = list.map(prelude, fn(m) { m.0 })
  list.map(mods, fn(mod) {
    let #(name, stmts) = mod
    case list.contains(prelude_names, name) {
      True -> mod
      False -> {
        let existing = imported_paths(stmts)
        let imports =
          list.filter_map(prelude, fn(m) {
            let path = m.0
            case list.contains(existing, path) {
              True -> Error(Nil)
              False ->
                Ok(
                  import_all(path, implicit_import_alias, Span(name, 0, 0, 0, 0)),
                )
            }
          })
        #(name, list.append(imports, stmts))
      }
    }
  })
}

/// The paths of the `import` statements in a module.
fn imported_paths(stmts: List(Stmt)) -> List(String) {
  list.flat_map(stmts, fn(stmt) {
    case stmt.data {
      Import(path, _, _) -> [path]
      _ -> []
    }
  })
}

/// Compute the canonical module name for a file path. If the file is
/// inside a known package directory (`<path>/<package>/<version>/…`), the
/// name is `/<package>/<relpath>` (version stripped). Otherwise the name
/// is `/` + the file path without extension.
pub fn canonical_name(
  paths: List(String),
  package_names: List(String),
  file: String,
) -> String {
  case find_package_prefix(paths, package_names, file) {
    Ok(#(pkg_name, prefix_len)) -> {
      let rel = string.drop_start(file, prefix_len)
      case string.split(rel, "/") {
        [_version, ..rest] -> {
          let relpath = string.join(rest, "/")
          "/" <> pkg_name <> "/" <> filepath.strip_extension(relpath)
        }
        _ -> "/" <> pkg_name
      }
    }
    Error(Nil) -> "/" <> filepath.strip_extension(file)
  }
}

fn find_package_prefix(
  paths: List(String),
  package_names: List(String),
  file: String,
) -> Result(#(String, Int), Nil) {
  case paths {
    [] -> Error(Nil)
    [path, ..rest] ->
      case find_in_path(path, package_names, file) {
        Ok(result) -> Ok(result)
        Error(Nil) -> find_package_prefix(rest, package_names, file)
      }
  }
}

fn find_in_path(
  path: String,
  package_names: List(String),
  file: String,
) -> Result(#(String, Int), Nil) {
  case package_names {
    [] -> Error(Nil)
    [name, ..rest] -> {
      let prefix = filepath.join(path, name) <> "/"
      case string.starts_with(file, prefix) {
        True -> Ok(#(name, string.length(prefix)))
        False -> find_in_path(path, rest, file)
      }
    }
  }
}

/// Load a project: the given files plus the given packages, with
/// canonical naming. Files that are inside a package directory are named
/// by their package path (e.g. `/prelude/bool`), not by their file path.
/// Duplicate modules (same canonical name) are loaded only once.
pub fn project(
  paths: List(String),
  files: List(String),
  packages: List(#(String, Option(String))),
) -> #(List(Module), List(e.Error)) {
  let pkg_names = list.map(packages, fn(p) { p.0 })
  let #(pkg_mods, pkg_errors) = package_list(paths, packages)
  let pkg_module_names = list.map(pkg_mods, fn(m) { m.0 })
  let #(file_mods, file_errors) =
    load_canonical_files(paths, pkg_names, files, pkg_module_names)
  #(
    list.append(file_mods, pkg_mods),
    list.append(file_errors, pkg_errors),
  )
}

fn load_canonical_files(
  paths: List(String),
  package_names: List(String),
  files: List(String),
  existing_names: List(String),
) -> #(List(Module), List(e.Error)) {
  case files {
    [] -> #([], [])
    [path, ..rest] -> {
      let name = canonical_name(paths, package_names, path)
      case list.contains(existing_names, name) {
        True -> load_canonical_files(paths, package_names, rest, existing_names)
        False -> {
          let #(stmts, errors) = file(path)
          let #(mods, rest_errors) =
            load_canonical_files(paths, package_names, rest, existing_names)
          #([#(name, stmts), ..mods], list.append(errors, rest_errors))
        }
      }
    }
  }
}

/// Read and parse one `.tao` file, collecting errors instead of failing.
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

/// Load one module; the module name is its file path without extension,
/// prefixed with `/` (module names always start with `/`).
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

/// Load a package from `paths`, at `version` or its newest version.
/// Module names are prefixed with the package name.
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
        _ -> find_with(check, paths, filename)
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
