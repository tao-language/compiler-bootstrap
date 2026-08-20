import gleam/option.{type Option, None, Some}

pub fn at(list: List(a), index: Int) -> Option(a) {
  case list {
    [head, ..] if index <= 0 -> Some(head)
    [_, ..tail] -> at(tail, index - 1)
    [] -> None
  }
}

pub fn set(list: List(#(k, v)), key: k, value: v) -> List(#(k, v)) {
  case list {
    [] -> [#(key, value)]
    [#(k, _), ..list] if k == key -> [#(key, value), ..list]
    [kv, ..list] -> [kv, ..set(list, key, value)]
  }
}
