import gleam/list
import gleam/result
import gleam/string
import utils/fs
import utils/glob.{glob_compile}

pub fn fs_list_test() {
  assert result.map(fs.list("test/data"), list.sort(_, string.compare))
    == Ok([
      "test/data/dir",
      "test/data/f1.txt",
      "test/data/f2.txt",
      "test/data/tao.toml",
    ])
}

pub fn fs_list_recursive_test() {
  let results =
    fs.list_recursive("test/data", fn(_) { True })
    |> result.map(list.sort(_, string.compare))
  assert results
    == Ok([
      "test/data/dir/a.txt",
      "test/data/dir/subdir/b.txt",
      "test/data/f1.txt",
      "test/data/f2.txt",
      "test/data/tao.toml",
    ])
}
// pub fn fs_find_test() {
//   assert fs.find(".", glob_compile([])) == []
// }
