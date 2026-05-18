import gleam/option.{type Option, None, Some}

pub fn list_at(list: List(a), index: Int) -> Option(a) {
  case list {
    [head, ..] if index <= 0 -> Some(head)
    [_, ..tail] -> list_at(tail, index - 1)
    [] -> None
  }
}

pub fn list_lookup(list: List(#(k, v)), key: k) -> Option(v) {
  case list {
    [#(k, v), ..] if k == key -> Some(v)
    [_, ..tail] -> list_lookup(tail, key)
    [] -> None
  }
}
