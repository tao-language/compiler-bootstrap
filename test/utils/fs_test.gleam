import gleam/list
import gleam/result
import gleam/string
import utils/fs
import utils/glob.{glob_compile}

pub fn fs_list_test() {
  assert result.map(fs.list("test/data"), list.sort(_, string.compare))
    == Ok([
      "dir",
      "f1.txt",
      "f2.txt",
      "tao.toml",
    ])
}

pub fn fs_list_recursive_test() {
  let results =
    fs.list_recursive("test/data", fn(_) { True })
    |> result.map(list.sort(_, string.compare))
  assert results
    == Ok([
      "dir/a.txt",
      "dir/subdir/b.txt",
      "f1.txt",
      "f2.txt",
      "tao.toml",
    ])
}
// pub fn fs_find_test() {
//   assert fs.find(".", glob_compile([])) == []
// }
