import filepath
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import simplifile

const config_file = "tao.toml"

/// A package/project manifest (`tao.toml`).
pub type Config {
  Config(
    name: String,
    version: String,
    dependencies: List(Dependency),
  )
}

/// A dependency entry in a manifest.
pub type Dependency {
  Dependency(
    name: String,
    version: Option(String),
  )
}

/// Walk up from `path` looking for a `tao.toml` project marker file.
pub fn find_project_root(path: String) -> Option(String) {
  let filename = filepath.join(path, config_file)
  case simplifile.is_file(filename), path {
    Ok(True), _ -> Some(path)
    _, "" -> None
    _, _ -> find_project_root(filepath.directory_name(path))
  }
}

/// Read and parse a `tao.toml` at the given path.
pub fn load(path: String) -> Result(Config, String) {
  case simplifile.read(path) {
    Ok(source) -> parse(source)
    Error(err) -> Error(simplifile.describe_error(err))
  }
}

/// Parse a `tao.toml` source string into a Config.
///
/// Handles the constrained subset: top-level `key = "value"` string pairs
/// and a `dependencies` array of inline tables `{ key = "value", ... }`.
/// Unknown fields are ignored for forward-compatibility.
pub fn parse(source: String) -> Result(Config, String) {
  let lines = string.split(source, "\n")
  let acc = ParseAcc(name: "", version: "", deps: [], in_array: False)
  case parse_lines(lines, acc) {
    Ok(acc) ->
      case acc.name {
        "" -> Error("missing required field: name")
        _ -> Ok(Config(acc.name, acc.version, acc.deps))
      }
    Error(msg) -> Error(msg)
  }
}

type ParseAcc {
  ParseAcc(
    name: String,
    version: String,
    deps: List(Dependency),
    in_array: Bool,
  )
}

fn parse_lines(lines: List(String), acc: ParseAcc) -> Result(ParseAcc, String) {
  case lines {
    [] -> Ok(acc)
    [line, ..rest] -> {
      let trimmed = string.trim(line)
      let parsed =
        case trimmed {
          "" -> Ok(acc)
          "#" <> _ -> Ok(acc)
          _ -> parse_line(trimmed, acc)
        }
      case parsed {
        Ok(a) -> parse_lines(rest, a)
        Error(msg) -> Error(msg)
      }
    }
  }
}

fn parse_line(line: String, acc: ParseAcc) -> Result(ParseAcc, String) {
  case acc.in_array {
    True -> parse_array_item(line, acc)
    False -> parse_top_level(line, acc)
  }
}

fn parse_top_level(line: String, acc: ParseAcc) -> Result(ParseAcc, String) {
  case string.split_once(line, "=") {
    Ok(#(key, value)) -> {
      let key = string.trim(key)
      let value = string.trim(value)
      case key {
        "dependencies" ->
          case value {
            "[" -> Ok(ParseAcc(..acc, in_array: True))
            "[" <> tail -> parse_inline_array(tail, acc)
            "[]" -> Ok(ParseAcc(..acc, in_array: False))
            _ -> Error("expected [ after dependencies =")
          }
        "name" -> Ok(ParseAcc(..acc, name: unquote(value)))
        "version" -> Ok(ParseAcc(..acc, version: unquote(value)))
        _ -> Ok(acc)
      }
    }
    Error(Nil) -> Error("expected key = value: " <> line)
  }
}

fn parse_array_item(line: String, acc: ParseAcc) -> Result(ParseAcc, String) {
  case line {
    "]" -> Ok(ParseAcc(..acc, in_array: False))
    _ -> {
      case string.ends_with(line, "]") {
        True -> {
          let item = string.trim(string.drop_end(line, 1))
          parse_dep_item(item, acc)
          |> result.map(fn(a) { ParseAcc(..a, in_array: False) })
        }
        False -> {
          case string.contains(line, "}") {
            True -> parse_dep_item(line, acc)
            False -> Ok(acc)
          }
        }
      }
    }
  }
}

fn parse_dep_item(item: String, acc: ParseAcc) -> Result(ParseAcc, String) {
  let inner = string.trim(item)
  // Strip trailing comma (multi-line arrays use `}, ` between items)
  let inner =
    case string.ends_with(inner, ",") {
      True -> string.trim(string.drop_end(inner, 1))
      False -> inner
    }
  case inner {
    "" -> Ok(acc)
    "{" <> rest ->
      case string.ends_with(rest, "}") {
        True -> {
          let fields = string.drop_end(rest, 1)
          let deps = parse_dep_fields(fields, acc.deps)
          Ok(ParseAcc(..acc, deps: deps))
        }
        False -> Error("malformed inline table: " <> inner)
      }
    _ -> Ok(acc)
  }
}

fn parse_dep_fields(fields: String, deps: List(Dependency)) -> List(Dependency) {
  let name = extract_field(fields, "name")
  case name {
    Some(n) -> {
      let version = extract_field(fields, "version")
      let dep = Dependency(n, version)
      list.append(deps, [dep])
    }
    None -> deps
  }
}

fn extract_field(source: String, key: String) -> Option(String) {
  let pattern = key <> " = "
  case string.split_once(source, pattern) {
    Ok(#(_, rest)) -> {
      let value =
        case string.split_once(rest, ",") {
          Ok(#(v, _)) -> string.trim(v)
          Error(Nil) -> string.trim(rest)
        }
      case value {
        "" -> None
        v -> Some(unquote(v))
      }
    }
    Error(Nil) -> None
  }
}

fn unquote(s: String) -> String {
  let trimmed = string.trim(s)
  case trimmed {
    "\"" <> rest ->
      case string.ends_with(rest, "\"") {
        True -> string.drop_end(rest, 1)
        False -> rest
      }
    _ -> trimmed
  }
}

fn parse_inline_array(s: String, acc: ParseAcc) -> Result(ParseAcc, String) {
  let s = string.trim(s)
  let inner =
    case s {
      "]" -> ""
      "[" <> rest -> {
        let rest = string.trim(rest)
        case string.ends_with(rest, "]") {
          True -> string.trim(string.drop_end(rest, 1))
          False -> string.trim(rest)
        }
      }
      _ -> s
    }
  let deps = parse_dep_list(inner, acc.deps)
  Ok(ParseAcc(..acc, deps: deps, in_array: False))
}

fn parse_dep_list(s: String, deps: List(Dependency)) -> List(Dependency) {
  case string.trim(s) {
    "" -> deps
    _ -> {
      let items = string.split(s, "}")
      parse_dep_items(items, deps)
    }
  }
}

fn parse_dep_items(items: List(String), deps: List(Dependency)) -> List(Dependency) {
  case items {
    [] -> deps
    [item, ..rest] -> {
      let cleaned = string.trim(string.trim(string.drop_start(item, 0)))
      let cleaned =
        case cleaned {
          "," <> _ -> string.trim(cleaned)
          _ -> cleaned
        }
      case string.trim(cleaned) {
        "" -> parse_dep_items(rest, deps)
        _ -> {
          let dep =
            case extract_field(cleaned, "name") {
              Some(n) -> {
                let version = extract_field(cleaned, "version")
                Some(Dependency(n, version))
              }
              None -> None
            }
          let new_deps =
            case dep {
              Some(d) -> list.append(deps, [d])
              None -> deps
            }
          parse_dep_items(rest, new_deps)
        }
      }
    }
  }
}
