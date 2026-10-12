/// Shared argument parsing for the `check`/`run`/`test` commands: input
/// selection (file paths, `-e`, `-s`), `--trace` kinds, and package flags.
import core/context.{
  type TraceKind,
  TraceDefines,
  TraceDesugar,
  TraceEval,
  TraceHoles,
  TraceInfer,
  TraceModules,
  TraceParse,
  TraceResolve,
  TraceSolves,
  TraceTests,
}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string

/// What to compile: file/directory paths, a single expression, or a
/// statement list (an anonymous module).
pub type Input {
  InputFiles(List(String))
  InputExpr(String)
  InputStmts(String)
}

/// Parsed options for a main command.
pub type Opts {
  Opts(
    /// The input (paths, `-e`, or `-s`).
    input: Input,
    /// Enabled `--trace` kinds.
    trace: List(TraceKind),
    /// Package search dirs (`--path`); the pipeline defaults to `lib`.
    paths: List(String),
    /// Extra packages to load (`--add`).
    packages: List(#(String, Option(String))),
    /// `--dump-def <name>`.
    dump_def: Option(String),
    /// `--filter` patterns (test only).
    filter: List(String),
    /// `--skip` patterns (test only).
    skip: List(String),
    /// Per-file test name restrictions (`path:test1,test2`, test only).
    per_file: List(#(String, List(String))),
  )
}

type Parsed =
  #(
    Input,
    List(TraceKind),
    List(String),
    List(#(String, Option(String))),
    Option(String),
    List(String),
    List(String),
    List(#(String, List(String))),
  )

/// Parse the arguments after the command name.
pub fn parse(command: String, args: List(String)) -> Result(Opts, String) {
  case parse_loop(command, args, InputFiles([]), [], [], [], None, [], [], []) {
    Ok(#(input, trace, paths, packages, dump_def, filter, skip, per_file)) ->
      Ok(Opts(
        input: input,
        trace: trace,
        paths: paths,
        packages: packages,
        dump_def: dump_def,
        filter: filter,
        skip: skip,
        per_file: per_file,
      ))
    Error(msg) -> Error(msg)
  }
}

fn parse_loop(
  command: String,
  args: List(String),
  input: Input,
  trace: List(TraceKind),
  paths: List(String),
  packages: List(#(String, Option(String))),
  dump_def: Option(String),
  filter: List(String),
  skip: List(String),
  per_file: List(#(String, List(String))),
) -> Result(Parsed, String) {
  case args {
    [] -> Ok(#(input, trace, paths, packages, dump_def, filter, skip, per_file))
    ["-e", value, ..rest] ->
      set_input(command, rest, input, InputExpr(value), trace, paths, packages, dump_def, filter, skip, per_file)
    ["--expr", value, ..rest] ->
      set_input(command, rest, input, InputExpr(value), trace, paths, packages, dump_def, filter, skip, per_file)
    ["-s", value, ..rest] ->
      set_input(command, rest, input, InputStmts(value), trace, paths, packages, dump_def, filter, skip, per_file)
    ["--stmt", value, ..rest] ->
      set_input(command, rest, input, InputStmts(value), trace, paths, packages, dump_def, filter, skip, per_file)
    ["--trace", kind, ..rest] ->
      add_trace(command, rest, kind, input, trace, paths, packages, dump_def, filter, skip, per_file)
    ["--trace=" <> kind, ..rest] ->
      add_trace(command, rest, kind, input, trace, paths, packages, dump_def, filter, skip, per_file)
    ["--dump-def", name, ..rest] ->
      parse_loop(command, rest, input, trace, paths, packages, Some(name), filter, skip, per_file)
    ["--dump-def=" <> name, ..rest] ->
      parse_loop(command, rest, input, trace, paths, packages, Some(name), filter, skip, per_file)
    ["--path", dir, ..rest] ->
      parse_loop(command, rest, input, trace, list.append(paths, [dir]), packages, dump_def, filter, skip, per_file)
    ["--path=" <> dir, ..rest] ->
      parse_loop(command, rest, input, trace, list.append(paths, [dir]), packages, dump_def, filter, skip, per_file)
    ["--add", spec, ..rest] ->
      parse_loop(command, rest, input, trace, paths, list.append(packages, [package(spec)]), dump_def, filter, skip, per_file)
    ["--add=" <> spec, ..rest] ->
      parse_loop(command, rest, input, trace, paths, list.append(packages, [package(spec)]), dump_def, filter, skip, per_file)
    ["--filter", ..] | ["--filter=" <> _, ..] if command != "test" ->
      Error("--filter is only supported by test")
    ["--filter", pattern, ..rest] ->
      parse_loop(command, rest, input, trace, paths, packages, dump_def, [pattern, ..filter], skip, per_file)
    ["--filter=" <> pattern, ..rest] ->
      parse_loop(command, rest, input, trace, paths, packages, dump_def, [pattern, ..filter], skip, per_file)
    ["--skip", ..] | ["--skip=" <> _, ..] if command != "test" ->
      Error("--skip is only supported by test")
    ["--skip", pattern, ..rest] ->
      parse_loop(command, rest, input, trace, paths, packages, dump_def, filter, [pattern, ..skip], per_file)
    ["--skip=" <> pattern, ..rest] ->
      parse_loop(command, rest, input, trace, paths, packages, dump_def, filter, [pattern, ..skip], per_file)
    ["--filter"] -> Error("missing pattern for --filter")
    ["--skip"] -> Error("missing pattern for --skip")
    // A trailing flag with no value.
    ["-e"] | ["--expr"] -> Error("missing value for --expr")
    ["-s"] | ["--stmt"] -> Error("missing value for --stmt")
    ["--trace"] -> Error("missing kind for --trace")
    ["--dump-def"] -> Error("missing name for --dump-def")
    ["--path"] -> Error("missing dir for --path")
    ["--add"] -> Error("missing package for --add")
    [arg, ..rest] ->
      case arg {
        "--" <> _ -> Error("unknown flag: " <> arg)
        _ ->
          // A `test` positional may restrict that file's tests.
          case command == "test", string.split_once(arg, ":") {
            True, Ok(#(path, names)) -> {
              let path = normalize(path)
              case add_file(input, path) {
                Error(msg) -> Error(msg)
                Ok(new_input) -> {
                  let per_file =
                    list.append(per_file, [#(path, test_names(names))])
                  parse_loop(command, rest, new_input, trace, paths, packages, dump_def, filter, skip, per_file)
                }
              }
            }
            _, _ ->
              case add_file(input, arg) {
                Error(msg) -> Error(msg)
                Ok(new_input) ->
                  parse_loop(command, rest, new_input, trace, paths, packages, dump_def, filter, skip, per_file)
              }
          }
      }
  }
}

fn set_input(
  command: String,
  rest: List(String),
  current: Input,
  new: Input,
  trace: List(TraceKind),
  paths: List(String),
  packages: List(#(String, Option(String))),
  dump_def: Option(String),
  filter: List(String),
  skip: List(String),
  per_file: List(#(String, List(String))),
) -> Result(Parsed, String) {
  case set_inline(current, new) {
    Error(msg) -> Error(msg)
    Ok(input) ->
      parse_loop(command, rest, input, trace, paths, packages, dump_def, filter, skip, per_file)
  }
}

fn add_trace(
  command: String,
  rest: List(String),
  kind: String,
  input: Input,
  trace: List(TraceKind),
  paths: List(String),
  packages: List(#(String, Option(String))),
  dump_def: Option(String),
  filter: List(String),
  skip: List(String),
  per_file: List(#(String, List(String))),
) -> Result(Parsed, String) {
  case trace_kind(kind) {
    Error(msg) -> Error(msg)
    Ok(k) ->
      parse_loop(command, rest, input, list.append(trace, [k]), paths, packages, dump_def, filter, skip, per_file)
  }
}

/// Set an inline input, rejecting a mix with files or a second inline input.
fn set_inline(current: Input, new: Input) -> Result(Input, String) {
  case current {
    InputFiles([]) -> Ok(new)
    InputFiles(_) -> Error("cannot mix file paths with " <> flag_of(new))
    _ -> Error("cannot combine " <> flag_of(current) <> " and " <> flag_of(new))
  }
}

/// Append a file path to a files input.
fn add_file(input: Input, file: String) -> Result(Input, String) {
  case input {
    InputFiles(files) -> Ok(InputFiles(list.append(files, [file])))
    _ -> Error("cannot mix file paths with " <> flag_of(input))
  }
}

fn flag_of(input: Input) -> String {
  case input {
    InputExpr(..) -> "-e"
    InputStmts(..) -> "-s"
    InputFiles(..) -> "file paths"
  }
}

/// Parse a `--trace` kind name.
fn trace_kind(kind: String) -> Result(TraceKind, String) {
  case kind {
    "parse" -> Ok(TraceParse)
    "modules" -> Ok(TraceModules)
    "defines" -> Ok(TraceDefines)
    "holes" -> Ok(TraceHoles)
    "solves" -> Ok(TraceSolves)
    "desugar" -> Ok(TraceDesugar)
    "infer" -> Ok(TraceInfer)
    "resolve" -> Ok(TraceResolve)
    "eval" -> Ok(TraceEval)
    "tests" -> Ok(TraceTests)
    _ -> Error("unknown trace kind: " <> kind)
  }
}

/// Parse a `--add` package spec: `name` or `name:version`.
fn package(spec: String) -> #(String, Option(String)) {
  case string.split_once(spec, ":") {
    Ok(#(name, version)) -> #(name, Some(version))
    Error(Nil) -> #(spec, None)
  }
}

/// Split a `path:test1,test2` restriction into test names.
fn test_names(names: String) -> List(String) {
  list.filter_map(string.split(names, ","), fn(name) {
    case string.length(name) {
      0 -> Error(Nil)
      _ -> Ok(name)
    }
  })
}

/// Strip a leading `./` from a path.
fn normalize(path: String) -> String {
  case path {
    "./" <> rest -> rest
    _ -> path
  }
}
