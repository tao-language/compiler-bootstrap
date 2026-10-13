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
./tao --help  # Run the compiler (main entry point)
gleam test    # Run the tests
```

`./tao` runs the standalone binary in `build/tao` under a timeout (override
the 2 s default with `TAO_TIMEOUT`, e.g. `TAO_TIMEOUT=20 ./tao test big.tao`).
The binary is rebuilt automatically when it is missing or older than any
source file (`rm build/tao` forces a rebuild).

If you have `fswatch` installed, you can run tests as files change with:

```sh
fswatch -or src test | xargs -n1 -I{} gleam test
```
