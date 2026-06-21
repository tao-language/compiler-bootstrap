import gleam/option.{None, Some}
import tao/config

pub fn find_project_root_test() {
  assert config.find_project_root("") == None
  assert config.find_project_root(".") == None
  assert config.find_project_root("test") == None
  assert config.find_project_root("test/data") == Some("test/data")
  assert config.find_project_root("test/data/f1.txt") == Some("test/data")
  assert config.find_project_root("test/data/dir/subdir/b.txt")
    == Some("test/data")
}
