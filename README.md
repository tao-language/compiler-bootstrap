# ☯ Tao compiler bootstrap

> ⚠️ This documentation is outdated!

Compiler bootstrap for the Tao language.

## Before you begin

Use [GHCup](https://www.haskell.org/ghcup/) to install Haskell and `stack`.

## Running a script

```sh
stack run example/factorial.tao 5
```

## Running tests

```sh
stack test
```

## Compiling the compiler

```sh
stack build
$(stack path --local-install-root)/bin/tao-bootstrap example/factorial.tao 5
```

## Notes

Lambda calculus:
- https://github.com/mroman42/mikrokosmos
- https://github.com/mroman42/mikrokosmos/blob/master/source/Lambda.hs      -- Core language
- https://github.com/mroman42/mikrokosmos/blob/master/source/Stlc/Types.hs  -- Type inference

More on pattern matching in Haskell:
- https://www.politesi.polimi.it/bitstream/10589/140161/1/Tesi.pdf
- f (x := 5) = x --> f (x as 5) = x --> f x = 5 ---> always returns 5
- f (x + 1) = x --> ??

More on type inference:
- https://crypto.stanford.edu/~blynn/lambda/pts.html
- https://youtu.be/ytPAlhnAKro

Dependent types:
- http://strictlypositive.org/Easy.pdf

Bidirectional type checking:
- https://www.youtube.com/live/utyBNDj7s2w?feature=share
- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
