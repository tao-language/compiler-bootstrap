import core/context.{Context, new_ctx}
import core/error
import core/eval.{eval}
import core/ffi
import core/format
import core/resolve
import core/unwrap
import core/value as v
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import tao/ast.{type Module, type Stmt} as tao
import tao/compile
import tao/desugar
import tao/discover
import tao/load
import utils/fs

pub fn debug_file(
  src_dir: String,
  paths: List(String),
  packages: List(#(String, Option(String))),
  filename: String,
  width: Int,
) {
  io.println("src_dir: " <> string.inspect(src_dir))
  io.println("paths: " <> string.inspect(paths))
  io.println("packages: " <> string.inspect(packages))
  io.println("filename: " <> filename)
  io.println("")

  echo "> load.module(filename)"
  let #(mod, errors) = load.module([src_dir], filename)
  let #(mods, errors) = case src_dir {
    "" -> #([mod], errors)
    _ -> {
      echo "> load.directory(src_dir)"
      let #(mods, err) = load.directory(src_dir)
      #([mod, ..mods], list.append(errors, err))
    }
  }
  echo "> load.package_list(paths, packages)"
  let #(pkg_mods, pkg_errors) = load.package_list(paths, packages)
  let #(mods, errors) = #(
    list.append(mods, pkg_mods),
    list.append(errors, pkg_errors),
  )
  let mods = topological_sort(mods)
  io.println("modules loaded: " <> int.to_string(list.length(mods)))
  list.map(mods, fn(mod) { io.println("- " <> mod.0) })
  io.println("")

  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println_error("---- SYNTAX ERRORS ----")
      list.map(errors, fn(err) {
        let msg = error.display_syntax(err)
        io.println_error("❌ " <> msg)
      })
      io.println("")
      io.println_error(int.to_string(n) <> " syntax errors")
      exit(1)
    }
  }

  echo "> stmts = load.module(filename)"
  let #(#(name, stmts), errors) = load.module(paths, filename)
  io.println("module name: " <> string.inspect(name))
  case list.length(errors) {
    0 -> Nil
    n -> {
      io.println_error("---- SYNTAX ERRORS ----")
      list.map(errors, fn(err) {
        let msg = error.display_syntax(err)
        io.println_error("❌ " <> msg)
      })
      io.println("")
      io.println_error(int.to_string(n) <> " syntax errors")
      exit(1)
    }
  }

  let exports = discover.definitions(stmts)
  io.println("exports: " <> int.to_string(list.length(exports)) <> " length")
  list.map(exports, fn(name) { io.println("- " <> name) })
  io.println("")

  echo "> exports, ctx = compile.declarations(ctx, mods)"
  let ctx = Context(..new_ctx, ffi: ffi.build)
  let env = v.env_push(ctx.env, list.length(mods))
  let #(exports, ctx) = compile.declarations(ctx, env, mods)

  // Define helpers to print and format.
  let names = list.map(ctx.types, fn(x) { x.0 })
  let fmt_expr = fn(expr) { format.expr(expr, width, 2) }
  let fmt_term = fn(term) { format.term(names, term, width, 2) }
  let fmt_value = fn(val) { format.value(ffi.build, names, val, width, 2) }
  let fmt_pattern = fn(pat) { format.pattern(pat, width, 2) }

  list.map(list.zip(ctx.types, ctx.env), fn(entry) {
    let #(#(name, mod_type), mod_value) = entry
    io.print("ctx.env[" <> string.inspect(name) <> "]: ")
    io.println(fmt_value(mod_value))
    io.print("ctx.types[" <> string.inspect(name) <> "]: ")
    io.println(fmt_value(mod_type))
    io.println("")
  })

  echo "> ctx = compile.definitions(ctx, exports, mods)"
  let ctx = compile.definitions(ctx, exports, mods)
  io.println(
    "// ctx.subst: " <> int.to_string(list.length(ctx.subst)) <> " solved holes",
  )
  let solved = list.map(ctx.subst, fn(kv) { kv.0 }) |> list.sort(int.compare)
  io.println("// solved: " <> string.inspect(solved))
  let unsolved =
    int.range(ctx.hole_counter - 1, -1, [], list.prepend)
    |> list.filter(fn(id) { !list.contains(solved, id) })
    |> list.map(int.to_string)
  io.println("// unsolved: " <> string.inspect(unsolved))
  // Uncomment to see the solved holes values in the order they were solved.
  list.map(ctx.subst, fn(entry) {
    let #(id, value) = entry
    // TODO: save ctx.types.names in ctx.subst to display var names.
    let fmt_subst = format.value(ctx.ffi, [], value, width, 2)
    io.println("- " <> int.to_string(id) <> ": " <> fmt_subst)
  })
  io.println("")

  echo "> resolve.context(ctx)"
  let ctx = resolve.context(ctx)
  list.index_map(list.zip(ctx.types, ctx.env), fn(entry, index) {
    let #(#(name, mod_type), mod_value) = entry
    let idx = int.to_string(index)
    io.println("// " <> idx <> ": ctx.env[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_value))
    io.println("// " <> idx <> ": ctx.types[" <> string.inspect(name) <> "]")
    io.println(fmt_value(mod_type))
    io.println("")
  })

  case ctx.errors {
    [] -> io.println("0 build errors")
    errors -> {
      let n = list.length(errors)
      io.println_error("---- BUILD ERRORS ----")
      list.map(ctx.errors, fn(err) {
        let msg = error.display(ctx.ffi, ctx.types, err)
        io.println_error("❌ " <> msg)
      })
      io.println("")
      io.println_error(int.to_string(n) <> " build errors")
      exit(1)
    }
  }
  io.println("")

  echo "> tests = compile.tests(mod)"
  let tests = compile.tests(ctx, [mod])
  let test_results =
    list.map(tests, fn(t) {
      let core_expr = desugar.expr(exports, t.expr)
      let core_expect = desugar.pattern(t.expect)
      let value = eval(ctx.ffi, ctx.env, t.term)
      io.println("/// " <> t.name)
      io.println(">>> " <> fmt_expr(core_expr))
      io.println("expect: " <> fmt_pattern(core_expect))
      io.println("result: " <> fmt_value(value))
      io.println("test_term: " <> fmt_term(t.term))
      io.println("")
      value
    })

  let #(passed, failed, unknown) =
    list.fold(test_results, #(0, 0, 0), fn(acc, value) {
      let #(passed, failed, unknown) = acc
      case value {
        v.Ctr("Pass", _) -> #(passed + 1, failed, unknown)
        v.Ctr("Fail", _) -> #(passed, failed + 1, unknown)
        _ -> #(passed, failed, unknown + 1)
      }
    })

  io.println("test results")
  io.println("- " <> int.to_string(list.length(test_results)) <> " total")
  io.println("- " <> int.to_string(passed) <> " passed")
  io.println("- " <> int.to_string(failed) <> " failed")
  case unknown {
    0 -> Nil
    _ -> io.println("- " <> int.to_string(unknown) <> " unkown result state")
  }
  io.println("")
}

// ============================================================================
// Topological sort for module dependency ordering
// ============================================================================

/// Extract the set of module names this module imports from its statements.
fn module_deps(stmts: List(Stmt)) -> List(String) {
  list.flat_map(stmts, fn(stmt) {
    case stmt.data {
      tao.Import(path, _, _) -> ["/" <> path]
      tao.ImportAll(path, _) -> ["/" <> path]
      _ -> []
    }
  })
}

/// Topologically sort modules so that dependencies come before dependents.
/// Uses Kahn's algorithm.
fn topological_sort(mods: List(Module)) -> List(Module) {
  let names = list.map(mods, fn(m) { m.0 })
  // Build adjacency: (module_name, [dependency_names_in_graph])
  let adj: List(#(String, List(String))) =
    list.map(mods, fn(m) {
      let #(name, stmts) = m
      let deps = module_deps(stmts)
      #(name, list.filter(deps, fn(d) { list.contains(names, d) }))
    })
  topological_sort_loop(adj, mods, names, [])
}

fn topological_sort_loop(
  adj: List(#(String, List(String))),
  mods: List(Module),
  names: List(String),
  sorted: List(Module),
) -> List(Module) {
  // Find nodes with zero in-degree: modules not listed as a dependency
  // by any other remaining module
  let zero_in =
    list.filter(names, fn(n) {
      !list.any(adj, fn(entry) { list.contains(entry.1, n) })
    })

  case zero_in {
    [] -> list.reverse(sorted)
    [node, ..] -> {
      // Remove this node from adjacency list
      let new_adj = list.filter(adj, fn(entry) { entry.0 != node })
      // Remove node from dependency lists of remaining entries
      let new_adj =
        list.map(new_adj, fn(entry) {
          #(entry.0, list.filter(entry.1, fn(d) { d != node }))
        })
      let new_names = list.filter(names, fn(n) { n != node })
      // Find the module for this node and add to sorted
      let module = case list.find(mods, fn(m) { m.0 == node }) {
        Ok(m) -> m
        Error(_) -> panic as "module not found in topological sort"
      }
      topological_sort_loop(new_adj, mods, new_names, [module, ..sorted])
    }
  }
}

// Declare the external Erlang halt function
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
