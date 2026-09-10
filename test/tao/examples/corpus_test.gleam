/// Corpus validation: compile the whole example corpus (the gallery
/// modules plus the prelude package, exactly as the `debug-file` CLI
/// loads them) through the full pipeline and run every `>>> test`
/// statement. This is the in-repo regression for the prelude/overload
/// machinery: the overloaded operators' dependent dispatches leave
/// deferred constraints (e.g. `NVar ~ Rcd`) that must *not* become
/// errors at resolve time, and every prelude test must still evaluate.
import core/context.{Context, new_ctx}
import core/ffi
import gleam/list
import gleam/option.{None}
import tao/compile
import tao/load
import tao/tests

/// The gallery + prelude compile with zero type errors.
pub fn corpus_compiles_test() {
  let #(gallery, e1) = load.directory("examples/tao/gallery")
  let #(prelude, e2) = load.package_list(["lib"], [#("prelude", None)])
  assert e1 == []
  assert e2 == []
  assert list.length(gallery) >= 1
  assert list.length(prelude) >= 1
  // As in the `debug-file` CLI: the prelude modules are compiled *and*
  // implicitly imported into the gallery modules.
  let mods =
    list.append(gallery, prelude)
    |> load.implicit_prelude_imports(prelude)
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> compile.modules(mods)
  assert ctx.errors == []
}

/// Every `>>> test` in the corpus evaluates to `Pass` (or stays neutral —
/// a test whose scrutinee cannot reduce; none should fail).
pub fn corpus_tests_pass_test() {
  let #(gallery, _e1) = load.directory("examples/tao/gallery")
  let #(prelude, _e2) = load.package_list(["lib"], [#("prelude", None)])
  let mods =
    list.append(gallery, prelude)
    |> load.implicit_prelude_imports(prelude)
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> compile.modules(mods)
  let #(test_defs, _ctx) = compile.tests(ctx, mods)
  assert list.length(test_defs) >= 9
  let summary = tests.run_all(ctx, test_defs)
  assert summary.num_fail == 0
  assert summary.num_pass >= 9
}
