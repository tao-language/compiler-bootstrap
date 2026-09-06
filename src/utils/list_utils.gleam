import gleam/option.{type Option, None, Some}

/// Element at an index from the head; out-of-range (including negative)
/// indices give None. Negative indices must not be silently bound to the
/// head: they indicate a corrupted de Bruijn index (e.g. a level that was
/// not representable in the quoting env), and failing loudly keeps such
/// bugs visible instead of silently rebinding the reference.
pub fn at(list: List(a), index: Int) -> Option(a) {
  case list {
    [head, ..] if index == 0 -> Some(head)
    [_, ..tail] if index > 0 -> at(tail, index - 1)
    _ -> None
  }
}

/// Replace the first entry with `key`, or append a new one at the end
/// (unlike `context.set_var`, which prepends).
pub fn set(list: List(#(k, v)), key: k, value: v) -> List(#(k, v)) {
  case list {
    [] -> [#(key, value)]
    [#(k, _), ..list] if k == key -> [#(key, value), ..list]
    [kv, ..list] -> [kv, ..set(list, key, value)]
  }
}
