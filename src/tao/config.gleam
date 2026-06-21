import filepath
import gleam/option.{type Option, None, Some}
import simplifile

const config_file = "tao.toml"

pub fn find_project_root(path: String) -> Option(String) {
  let filename = filepath.join(path, config_file)
  case simplifile.is_file(filename), path {
    Ok(True), _ -> Some(path)
    _, "" -> None
    _, _ -> find_project_root(filepath.directory_name(path))
  }
}
