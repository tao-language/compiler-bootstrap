# Examples testing

All examples in the `examples/` directory should be tested. These examples should showcase the end-to-end usage of the CLI compiler.

The CLI should:
- `check`: Which does type checking and exhaustiveness checks, returns a failure exit code if it fails. It should output properly formatted errors.
- `run`: It first checks the program (type checking and exhaustiveness checks), same as `check`. It should also output the result value of `infer`, which contains the NbE normalized term. It should output the result regardless of whether checks suceeded or failed. If checks failed, it returns a failure exit code.

## Success example

File: `examples/core/i32_add.core.tao`
```
%call i32_add(1, 2)
```

Expected output: `examples/core/i32_add.output.txt`
```
3
```

This should be the exact same output as if you run: `gleam run -- run examples/core/i32_add.core.tao`

## Failure example

File: `examples/core/errors/type_errors/type_mismatch.core.tao`
```
// This type annotation doesn't match the value's type.
1 : $Type
```

Expected output: `examples/core/errors/type_errors/type_mismatch.output.txt`
```
❌ error[E0101]: Type mismatch
   ┌─ src/main.tao:5:10
   │
 1 │ // This type annotation doesn't match the value's type.
 2 │ 1 : $Type
   │     ^~~~~ value is Int, but it should be $Type
   │
   💡 The value 1 is of type Int
   💡 The type annotation expects a value of type $Type
   📝 note: Int and $Type are incompatible types
   🔧 help: Did you mean? `1 : Int`
-----------------------------------------------------------
1
```

This should be the exact same output as if you run: `gleam run -- run examples/core/errors/type_errors/type_mismatch.core.tao`

Note that it shows the error, which should be written to `stderr`, then it shows a horizontal line (or some other ASCII art delimiter), then it shows the result after NbE, which `1 : $Type` should still evaluate to `1`, even with the type error. The result output should be written to `stdout` as normal. However, since there were errors, the whole thing should return a failure exit code.
