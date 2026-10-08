import cli/check.{check}
import cli/debug_core.{debug_core}
import cli/debug_expr.{debug_expr}
import cli/debug_file.{debug_file}
import cli/debug_src.{debug_src}
import cli/run.{run}
import cli/run_tests.{parse_test_args, run_tests}
import core/context.{type TraceKind, TraceModules}
import gleam/io
import gleam/list
import gleam/option.{None, Some}
import gleam/result
import gleam/string

const format_width = 40

const help = "Tao compiler bootstrap\n\nUsage:\n  tao check [paths...]                  Type-check .tao files (default: .)\n  tao run <file>                        Compile and run a .tao file\n  tao test [paths...]                   Run tests in .tao files (default: .)\n                                        --filter <pattern>  only run matching tests (repeatable)\n                                        --skip <pattern>    skip matching tests (repeatable)\n  tao debug-expr 'expression'           Debug a Tao expression (prelude auto-imported)\n                                        --path <dir>    extra package path (repeatable, default: lib)\n                                        --add <name>    extra package to load (repeatable)\n  tao debug-src 'source'                Debug inline Tao source (prelude compiled in, per-phase timing, subst dump)
                                        --trace-solves  print every hole solve/merge as it happens
                                        --dump-def <name>  print <name>'s inferred type with de Bruijn indices, then stop\n  tao debug-file <filename>             Debug a Tao module\n  tao debug-core 'core-term'            Debug a Core term\n  tao --help                            Show this help\n\ncheck and test accept file and directory paths; directories are searched\nrecursively for .tao files. If no paths are given, the current directory\nis used. test also accepts <path>:<test1,test2> to restrict the tests run\nin that file, and the --filter/--skip patterns match a test name or a\nmodule path with a test name (module/path.tao:test_name), with * and **\nglob wildcards.\n"

/// The CLI entry point. Commands: `check`, `run`, `test`, `debug-expr`,
/// `debug-file`, `debug-core`, `--help`. The REPL is TODO.
pub fn entrypoint(args: List(String)) {
  case args {
    [] -> todo as "TODO: CLI repl"
    ["--help", ..] -> {
      io.println(help)
      exit(0)
    }
    ["check", ..args] -> {
      case split_trace(args) {
        Error(msg) -> {
          io.println_error("error: " <> msg)
          exit(1)
        }
        Ok(#(paths, trace_kinds)) -> check(paths, trace_kinds)
      }
    }
    ["run", ..args] -> {
      case split_trace(args) {
        Error(msg) -> {
          io.println_error("error: " <> msg)
          exit(1)
        }
        Ok(#(files, trace_kinds)) -> run(files, trace_kinds)
      }
    }
    ["test", ..args] ->
      case parse_test_args(args) {
        Error(msg) -> {
          io.println_error("error: " <> msg)
          io.println(help)
          exit(1)
        }
        Ok(parsed) -> run_tests(parsed)
      }
    // ["-c", expr, ..rest] ->
    //   case rest {
    //     [] -> Ok(Run(Inline(expr), False, False))
    //     _ -> Error("Too many arguments after -c expression")
    //   }
    ["debug-expr", source, ..args] -> {
      let paths =
        list.filter_map(args, fn(arg) {
          case arg {
            "--path=" <> path -> Ok(path)
            _ -> Error(Nil)
          }
        })
        |> list.append(["lib"])
        |> list.unique
      let dependencies =
        list.filter_map(args, fn(arg) {
          case arg {
            "--add=" <> name ->
              case string.split_once(name, ":") {
                Ok(#(name, version)) -> Ok(#(name, Some(version)))
                Error(Nil) -> Ok(#(name, None))
              }
            _ -> Error(Nil)
          }
        })
      debug_expr(paths, dependencies, source, format_width)
    }
    ["debug-file", ..args] -> {
      let root =
        list.find_map(args, fn(arg) {
          case arg {
            "--root=" <> root -> Ok(root)
            _ -> Error(Nil)
          }
        })
        |> result.unwrap("")
      let paths =
        list.filter_map(args, fn(arg) {
          case arg {
            "--path=" <> path -> Ok(path)
            _ -> Error(Nil)
          }
        })
        |> list.append(["lib"])
        |> list.unique
      let dependencies =
        list.filter_map(args, fn(arg) {
          case arg {
            "--add=" <> name ->
              case string.split_once(name, ":") {
                Ok(#(name, version)) -> Ok(#(name, Some(version)))
                Error(Nil) -> Ok(#(name, None))
              }
            _ -> Error(Nil)
          }
        })
      let filename_result =
        list.filter(args, fn(arg) { !string.starts_with(arg, "--") })
        |> list.first
      case filename_result {
        Ok(filename) ->
          debug_file(root, paths, dependencies, filename, format_width)
        Error(Nil) -> {
          io.println_error("error: no filename provided")
          io.println(help)
          exit(1)
        }
      }
    }
    ["debug-src", source, ..args] -> {
      let paths =
        list.filter_map(args, fn(arg) {
          case arg {
            "--path=" <> path -> Ok(path)
            _ -> Error(Nil)
          }
        })
        |> list.append(["lib"])
        |> list.unique
      let dependencies =
        list.filter_map(args, fn(arg) {
          case arg {
            "--add=" <> name ->
              case string.split_once(name, ":") {
                Ok(#(name, version)) -> Ok(#(name, Some(version)))
                Error(Nil) -> Ok(#(name, None))
              }
            _ -> Error(Nil)
          }
        })
      let trace_solves = list.contains(args, "--trace-solves")
      let dump_def =
        case list.filter_map(args, fn(arg) {
          case arg {
            "--dump-def=" <> name -> Ok(name)
            _ -> Error(Nil)
          }
        }) {
          [name, ..] -> Some(name)
          [] -> None
        }
      debug_src(paths, dependencies, source, format_width, trace_solves, dump_def)
    }
    ["debug-core", source, ..] -> debug_core(source, format_width)
    // [path, ..rest] ->
    //   case rest {
    //     [] -> Ok(Run(File(path), False, False))
    //     _ -> Error("Too many arguments")
    //   }
    _ -> {
      io.println_error("error: unknown command")
      io.println(help)
      exit(1)
    }
  }
}

// /// Execute a command.
// pub fn run_command(command: Command) -> Nil {
//   case command {
//     Help -> {
//       show_help()
//       cli_halt(0)
//     }
//     Run(source, _, _) -> run_source(source)
//     Check(source, _, _) -> check_source(source)
//     DebugCore(expr, trace_parser, trace_infer) ->
//       debug_core.run(expr, trace_parser, trace_infer)
//   }
// }

/// Split args into positional args and `--trace=<kind>` flags.
fn split_trace(
  args: List(String),
) -> Result(#(List(String), List(TraceKind)), String) {
  case args {
    [] -> Ok(#([], []))
    ["--trace=modules", ..rest] ->
      case split_trace(rest) {
        Ok(#(paths, kinds)) -> Ok(#(paths, [TraceModules, ..kinds]))
        Error(e) -> Error(e)
      }
    ["--trace=" <> kind, ..] -> Error("unknown trace kind: " <> kind)
    [arg, ..rest] ->
      case split_trace(rest) {
        Ok(#(paths, kinds)) -> Ok(#([arg, ..paths], kinds))
        Error(e) -> Error(e)
      }
  }
}

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
