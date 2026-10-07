/// `tao debug-src` — run inline Tao source through the full pipeline
/// (prelude compiled in, like `debug-file`) with per-phase timing and a
/// full hole-substitution dump. Faster bisection than writing /tmp
/// files and running `debug-file`.
import cli/common
import core/context.{Context, new_ctx}
import core/error
import core/ffi
import core/format
import core/resolve
import core/value as v
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import tao/ast.{type Module}
import tao/compile
import tao/declare
import tao/define
import tao/load
import tao/parse as p
import tao/tests

@external(erlang, "erlang", "system_time")
fn now_ns() -> Int

fn now() -> Int {
  now_ns() / 1_000_000
}

pub fn debug_src(
  paths: List(String),
  dependencies: List(#(String, Option(String))),
  source: String,
  width: Int,
  trace_solves: Bool,
  dump_def: Option(String),
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
      let #(pkg_mods, pkg_errors) =
        load.package_list(paths, common.with_prelude(dependencies))
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
      let ctx = Context(..new_ctx, ffi: ffi.build, trace_solves: trace_solves)
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
      // Solutions carry NVar levels relative to their captured solve env,
      // so each one is displayed against that env's length, not `names`.
      let fmt_sol = fn(env, value) {
        let env_names =
          int.range(from: 0, to: list.length(env) - 1, with: [], run: list.prepend)
          |> list.map(fn(i) { "$" <> int.to_string(i) })
        format.value(ffi.build, env_names, value, width, 2)
      }
      let _ =
        list.map(subst, fn(entry) {
          let #(id, #(env, value)) = entry
          io.println(
            "h"
              <> int.to_string(id)
              <> " (envlen="
              <> int.to_string(list.length(env))
              <> "): "
              <> string.slice(fmt_sol(env, value), 0, 200),
          )
        })

      // `--dump-def NAME`: print the named definition's type value with its
      // de Bruijn structure (quantifier bodies via format.term). The canonical
      // way to inspect a function's inferred type for a de Bruijn frame
      // mismatch (see docs/plan.md §15): the `for`/`pi` bodies are lifted
      // with a flat names list, so each `Var` shows the index it addresses.
      case dump_def {
        Some(name) -> {
          case define.get_var(ctx, "scratch", name) {
            Some(#(_, typ)) -> {
              let names =
                list.map(int.range(from: 0, to: 15, with: [], run: list.prepend), fn(i) {
                  "n" <> int.to_string(i)
                })
              io.println("// type of " <> name <> " (names n0..n15 are de Bruijn indices)")
              dump_type_value(typ, 0, names, width)
            }
            None -> io.println_error("definition not found: " <> name)
          }
          exit(0)
        }
        None -> Nil
      }

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

/// Print a type value's de Bruijn structure: `For`/`Pi` bodies are lifted
/// via `format.term` (a flat names list, so each `Var` shows the index it
/// addresses); other values are sketched one level deep. Cycles through
/// captured envs are never followed, so it terminates on any value.
fn dump_type_value(value: v.Value, depth: Int, names: List(String), width: Int) -> Nil {
  let pad = string.join(list.repeat("  ", depth), "")
  case value {
    v.For(env, #(name, _), body) -> {
      let header = pad <> "FOR " <> name <> " (envlen=" <> int.to_string(list.length(env)) <> ")"
      let _ = io.println(header)
      let _ = io.println(pad <> "  body:\n" <> format.term(names, body, width, 2))
    }
    v.Pi(env, #(_, domain), codomain) -> {
      let _ =
        io.println(
          pad <> "PI (envlen=" <> int.to_string(list.length(env)) <> ") domain=" <> dump_sketch(domain),
        )
      let _ = io.println(pad <> "  codomain:\n" <> format.term(names, codomain, width, 2))
    }
    other -> {
      let _ = io.println(pad <> dump_sketch(other))
    }
  }
}

/// One-level sketch (safe on cyclic values; never follows captured envs).
fn dump_sketch(value: v.Value) -> String {
  case value {
    v.Neut(v.NVar(l)) -> "NVar("
      <> int.to_string(l)
      <> ")"
    v.Neut(v.NHole(_, Some(i))) -> "NHole(h" <> int.to_string(i) <> ")"
    v.Neut(v.NHole(_, None)) -> "NHole"
    v.Neut(v.NApp(..)) -> "NApp"
    v.Neut(v.NCall(..)) -> "NCall"
    v.Neut(v.NMatch(..)) -> "NMatch"
    v.Rcd(fields, tail) -> {
      let inner =
        list.map(fields, fn(field) {
          let #(_, #(fv, _)) = field
          field.0 <> ":" <> dump_sketch(fv)
        })
        |> list.fold("", fn(acc, s) { acc <> "|" <> s })
      "Rcd["
        <> inner
        <> "]"
        <> case tail {
          Some(t) -> "/" <> dump_sketch(t)
          None -> "/_"
        }
    }
    v.Typ(u) -> "Typ("
      <> int.to_string(u)
      <> ")"
    v.Lit(_) -> "Lit"
    v.LitT(_) -> "LitT"
    v.Ctr(tag, arg) -> "Ctr("
      <> tag
      <> ", "
      <> dump_sketch(arg)
      <> ")"
    v.For(..) -> "For"
    v.Lam(..) -> "Lam"
    v.Pi(..) -> "Pi"
    v.Fix(..) -> "Fix"
    v.TypeDef(..) -> "TypeDef"
    v.Err -> "Err"
  }
}

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
