import gleam/option.{None}
import gleam/string
import syntax/span.{Span}
import tao/ast as tao
import tao/trace

const s = Span("trace_test", 0, 0, 0, 0)

pub fn module_trace_empty_test() {
  let result = trace.module_trace_string([], [])
  assert string.contains(result, "---- MODULE TRACE ----")
  assert string.contains(result, "Modules:")
  assert string.contains(result, "Import edges:")
}

pub fn module_trace_two_modules_test() {
  let import_a = tao.import_all("/a", "a", s)
  let let_x = tao.let_var("x", None, tao.int(1, s), s)
  let mods = [
    #("/a", [let_x]),
    #("/b", [import_a]),
  ]
  let result = trace.module_trace_string(mods, [])
  assert string.contains(result, "/a")
  assert string.contains(result, "/b")
  assert string.contains(result, "/b → /a")
  assert string.contains(result, "alias: a")
}
