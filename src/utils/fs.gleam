import filepath
import gleam/list
import gleam/regexp.{type Regexp}
import gleam/result.{try}
import simplifile

pub fn list(dir: String) -> Result(List(String), String) {
  case simplifile.read_directory(dir) {
    Ok(files) -> Ok(files)
    Error(err) -> Error(simplifile.describe_error(err))
  }
}

pub fn list_recursive(
  dir: String,
  filter: fn(String) -> Bool,
) -> Result(List(String), String) {
  use paths <- try(list(dir))
  use subpaths <- try(
    list.try_map(paths, fn(path) {
      use is_dir <- try(is_directory(path))
      case is_dir {
        True -> list_recursive(path, filter)
        False ->
          case filter(path) {
            True -> Ok([path])
            False -> Ok([])
          }
      }
    }),
  )
  Ok(list.flatten(subpaths))
}

pub fn is_directory(path: String) -> Result(Bool, String) {
  case simplifile.is_directory(path) {
    Ok(is_dir) -> Ok(is_dir)
    Error(err) -> Error(simplifile.describe_error(err))
  }
}

pub fn find(dir: String, match: Regexp) -> List(String) {
  todo
}
