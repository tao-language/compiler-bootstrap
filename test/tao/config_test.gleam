import gleam/option.{None, Some}
import tao/config.{Config, Dependency}

pub fn parse_minimal() {
  let source = "name = \"foo\"\n"
  assert Ok(Config("foo", "", [])) == config.parse(source)
}

pub fn parse_with_version() {
  let source = "name = \"foo\"\nversion = \"0.0.1\"\n"
  assert Ok(Config("foo", "0.0.1", [])) == config.parse(source)
}

pub fn parse_with_dependencies_multi_line() {
  let source =
    "name = \"foo\"\nversion = \"0.0.1\"\ndependencies = [\n  { name = \"prelude\" },\n  { name = \"bar\", version = \"0.0.1\" },\n]\n"
  let expected = Config(
    "foo",
    "0.0.1",
    [
      Dependency("prelude", None),
      Dependency("bar", Some("0.0.1")),
    ],
  )
  assert Ok(expected) == config.parse(source)
}

pub fn parse_with_dependencies_single_line() {
  let source =
    "name = \"foo\"\ndependencies = [{ name = \"prelude\" }, { name = \"bar\" }]\n"
  let expected = Config(
    "foo",
    "",
    [
      Dependency("prelude", None),
      Dependency("bar", None),
    ],
  )
  assert Ok(expected) == config.parse(source)
}

pub fn parse_empty_dependencies() {
  let source = "name = \"foo\"\ndependencies = []\n"
  assert Ok(Config("foo", "", [])) == config.parse(source)
}

pub fn parse_no_dependencies() {
  let source = "name = \"foo\"\nversion = \"1.0.0\"\n"
  assert Ok(Config("foo", "1.0.0", [])) == config.parse(source)
}

pub fn parse_unknown_fields_ignored() {
  let source =
    "name = \"foo\"\nversion = \"0.0.1\"\nsome_future_field = \"blah\"\ndependencies = []\n"
  assert Ok(Config("foo", "0.0.1", [])) == config.parse(source)
}

pub fn parse_missing_name_error() {
  let source = "version = \"0.0.1\"\n"
  assert Error("missing required field: name") == config.parse(source)
}

pub fn parse_empty_source_error() {
  assert Error("missing required field: name") == config.parse("")
}

pub fn parse_comments_ignored() {
  let source = "# a comment\nname = \"foo\"\n# another\nversion = \"0.0.1\"\n"
  assert Ok(Config("foo", "0.0.1", [])) == config.parse(source)
}

pub fn parse_dependency_with_version() {
  let source =
    "name = \"proj\"\ndependencies = [\n  { name = \"lib\", version = \"2.0.0\" },\n]\n"
  let expected = Config("proj", "", [Dependency("lib", Some("2.0.0"))])
  assert Ok(expected) == config.parse(source)
}

pub fn parse_no_trailing_newline() {
  let source = "name = \"foo\"\nversion = \"0.0.1\""
  assert Ok(Config("foo", "0.0.1", [])) == config.parse(source)
}

pub fn parse_dep_trailing_comma() {
  // Multi-line arrays use trailing commas after each item
  let source =
    "name = \"foo\"\ndependencies = [\n  { name = \"a\" },\n  { name = \"b\", version = \"1.0\" },\n]\n"
  let expected = Config(
    "foo",
    "",
    [
      Dependency("a", None),
      Dependency("b", Some("1.0")),
    ],
  )
  assert Ok(expected) == config.parse(source)
}

pub fn find_project_root_test() {
  assert config.find_project_root("") == None
  assert config.find_project_root(".") == None
  assert config.find_project_root("test") == None
  assert config.find_project_root("test/data") == Some("test/data")
  assert config.find_project_root("test/data/f1.txt") == Some("test/data")
  assert config.find_project_root("test/data/dir/subdir/b.txt")
    == Some("test/data")
}
