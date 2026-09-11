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

pub fn examples_prelude_test() {
  let #(prelude, e) = load.package_list(["lib"], [#("prelude", None)])
  assert e == []
  assert list.length(prelude) >= 1
  let mods = prelude
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> compile.modules(mods)
  assert ctx.errors == []
  let #(test_defs, ctx) = compile.tests(ctx, prelude)
  assert list.length(test_defs) >= 1
  let summary = tests.run_all(ctx, test_defs)
  assert summary.num_fail == 0
}

pub fn examples_gallery_test() {
  let #(gallery, e1) = load.directory("examples/tao/gallery")
  let #(prelude, e2) = load.package_list(["lib"], [#("prelude", None)])
  assert e1 == []
  assert e2 == []
  assert list.length(gallery) >= 1
  assert list.length(prelude) >= 1
  let mods =
    list.append(gallery, prelude)
    |> load.implicit_prelude_imports(prelude)
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> compile.modules(mods)
  assert ctx.errors == []
  let #(test_defs, ctx) = compile.tests(ctx, gallery)
  assert list.length(test_defs) >= 1
  let summary = tests.run_all(ctx, test_defs)
  assert summary.num_fail == 0
}
