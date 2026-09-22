/// `tao debug-src` — run inline Tao source through the full pipeline
/// (prelude compiled in, like `debug-file`) with per-phase timing and a
/// full hole-substitution dump. Faster bisection than writing /tmp
/// files and running `debug-file`.
import core/context.{Context, new_ctx}
import core/error
import core/ffi
import core/format
import core/resolve
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option}
import gleam/string
import tao/ast.{type Module}
import tao/compile
import tao/declare
import tao/define
import tao/load
import tao/parse as p
import tao/tests

@external(erlang, "tao_trace", "now")
fn now() -> Int

pub fn debug_src(
  paths: List(String),
  dependencies: List(#(String, Option(String))),
  source: String,
  width: Int,
) -> Nil {
  case p.statements("scratch", source) {
    Error(err) -> {
      io.println_error("PARSE ERROR: " <> error.display_syntax(err))
      exit(1)
    }
    Ok(stmts) -> {
      io.println(
        "source: " <> string.inspect(source)
          <> " packages: " <> string.inspect(dependencies),
      )
      let #(pkg_mods, pkg_errors) = load.package_list(paths, dependencies)
      let mods: List(Module) =
        list.append([#("scratch", stmts)], pkg_mods)
        |> load.implicit_prelude_imports(pkg_mods)
      case list.length(pkg_errors) {
        0 -> Nil
        _ -> {
          let _ =
            list.map(pkg_errors, fn(err) {
              io.println_error("❌ " <> error.display_syntax(err))
            })
          exit(1)
        }
      }
      let ctx = Context(..new_ctx, ffi: ffi.build)
      let names = list.map(ctx.types, fn(x) { x.0 })
      let fmt_value = fn(val) { format.value(ffi.build, names, val, width, 2) }

      let defs = declare.modules(mods)
      let t0 = now()
      let ctx = define.types(ctx, defs)
      io.println(
        "define.types: "
          <> int.to_string(now() - t0)
          <> "ms holes="
          <> int.to_string(ctx.hole_counter),
      )
      let t1 = now()
      let ctx = define.values(ctx, defs)
      io.println(
        "define.values: "
          <> int.to_string(now() - t1)
          <> "ms holes="
          <> int.to_string(ctx.hole_counter),
      )

      let subst = list.sort(ctx.subst, fn(a, b) { int.compare(a.0, b.0) })
      io.println(
        "// subst="
          <> int.to_string(list.length(subst))
          <> " holes="
          <> int.to_string(ctx.hole_counter)
          <> " deferred="
          <> int.to_string(list.length(ctx.deferred)),
      )
      let _ =
        list.map(subst, fn(entry) {
          let #(id, #(env, value)) = entry
          io.println(
            "h"
              <> int.to_string(id)
              <> " (envlen="
              <> int.to_string(list.length(env))
              <> "): "
              <> string.slice(fmt_value(value), 0, 200),
          )
        })

      let t2 = now()
      let ctx = resolve.context(ctx)
      io.println(
        "resolve.context: "
          <> int.to_string(now() - t2)
          <> "ms",
      )

      case ctx.errors {
        [] -> Nil
        errors -> {
          let _ =
            list.map(errors, fn(err) {
              io.println_error("❌ " <> error.display(ctx.ffi, ctx.types, err))
            })
          io.println_error(int.to_string(list.length(errors)) <> " errors")
          exit(1)
        }
      }

      let #(test_defs, ctx) = compile.tests(ctx, [#("scratch", stmts)])
      let results =
        list.map(test_defs, fn(t) {
          io.println("term: " <> format.term(names, t.term, width, 2))
          let res = tests.run(ctx, t)
          case res {
            tests.TestPass(name) -> io.println("✓ " <> name)
            tests.TestFail(name, got, _, _) -> {
              io.println_error("✗ " <> name)
              io.println_error("  got: " <> fmt_value(got))
            }
            tests.TestNeutral(name, got, _, _) -> {
              io.println("? " <> name)
              io.println("  got: " <> fmt_value(got))
            }
          }
          res
        })
      let #(passed, failed, neutral) =
        list.fold(results, #(0, 0, 0), fn(acc, res) {
          let #(passed, failed, neutral) = acc
          case res {
            tests.TestPass(..) -> #(passed + 1, failed, neutral)
            tests.TestFail(..) -> #(passed, failed + 1, neutral)
            tests.TestNeutral(..) -> #(passed, failed, neutral + 1)
          }
        })
      io.println(
        "tests: "
          <> int.to_string(list.length(results))
          <> " total, "
          <> int.to_string(passed)
          <> " passed, "
          <> int.to_string(failed)
          <> " failed"
          <> case neutral {
            0 -> ""
            _ -> ", " <> int.to_string(neutral) <> " stuck"
          },
      )
      case failed {
        0 -> Nil
        _ -> exit(1)
      }
    }
  }
}

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
