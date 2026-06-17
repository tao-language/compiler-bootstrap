import gleam/list
import gleam/result
import gleam/string
import utils/fs
import utils/glob.{glob_compile}

pub fn fs_list_test() {
  assert result.map(fs.list("test/data"), list.sort(_, string.compare))
    == Ok(["test/data/dir", "test/data/f1.txt", "test/data/f2.txt"])
}

pub fn fs_list_recursive_test() {
  assert result.map(fs.list_recursive("test/data"), list.sort(_, string.compare))
    == Ok([
      "test/data/dir/a.txt",
      "test/data/dir/subdir/b.txt",
      "test/data/f1.txt",
      "test/data/f2.txt",
    ])
}
// pub fn fs_find_test() {
//   assert fs.find(".", glob_compile([])) == []
// }
