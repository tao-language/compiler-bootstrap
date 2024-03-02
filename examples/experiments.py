from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass


@dataclass
class Result[ok, err]:
    def and_then(self, f: Callable[[ok], Result[ok, err]]) -> Result[ok, err]:
        raise NotImplementedError


@dataclass
class Ok[ok, err](Result[ok, err]):
    value: ok

    def and_then(self, f: Callable[[ok], Result[ok, err]]) -> Result[ok, err]:
        return f(self.value)


@dataclass
class Err[ok, err](Result[ok, err]):
    value: err

    def and_then(self, f: Callable[[ok], Result[ok, err]]) -> Result[ok, err]:
        return self


# r1 = Result().and_then(lambda x: Ok(x + 1))

r1 = Ok(42)
print(f"{r1.value=}")

r1.and_then(lambda x: Ok(x + 1))

# r1.and_then(lambda x: Err("this is an error"))
(
    r1.and_then(lambda x: Ok(x + 1))
    .and_then(lambda x: Err("this is an error"))
    .and_then(lambda x: Ok(x + 1))
)
