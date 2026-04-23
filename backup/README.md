# compiler_bootstrap

[![Package Version](https://img.shields.io/hexpm/v/compiler_bootstrap)](https://hex.pm/packages/compiler_bootstrap)
[![Hex Docs](https://img.shields.io/badge/hex-docs-ffaff3)](https://hexdocs.pm/compiler_bootstrap/)

```sh
gleam add compiler_bootstrap@1
```

```gleam
import compiler_bootstrap

pub fn main() -> Nil {
  // TODO: An example of the project in use
}
```

Further documentation can be found at <https://hexdocs.pm/compiler_bootstrap>.

## Development

```sh
gleam run   # Run the project
gleam test  # Run the tests
```

If you have `fswatch` installed, you can run tests as files change with:

```sh
fswatch -or src test | xargs -n1 -I{} gleam test
```
