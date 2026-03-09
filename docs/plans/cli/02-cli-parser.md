# CLI Parser Specification

> **Goal**: Command-line argument parsing for compiler CLI
> **Status**: ✅ Implemented - Basic argument parsing
> **Date**: March 2025

---

## Status

### What's Working

- Command-line argument parsing with `argv` library
- Command types (`Check`, `Run`, `Help`)
- File type detection (`.core.tao` vs `.tao`)
- Verbose mode (`-v`, `--verbose`)
- Debug mode (`--debug`)
- Help command (`-h`, `--help`)

### What's Pending

- Full file I/O (Gleam stdlib limitation)
- Exit codes for different error types
- Better error messages for invalid arguments

### Related

- See **[01-overview.md](./01-overview.md)** for overall CLI status
- See **[03-error-reporter.md](./03-error-reporter.md)** for error formatting

---

## Command Types

```gleam
pub type Command {
  /// check <file> [--verbose] [--debug]
  Check(file: String, verbose: Bool, debug: Bool)
  
  /// run <file> [--verbose] [--debug]
  Run(file: String, verbose: Bool, debug: Bool)
  
  /// --help, -h
  Help
}
```

---

## Argument Parsing

### Usage

```
compiler-bootstrap <command> <file> [options]

Commands:
  check <file>    Type-check a file
  run <file>      Type-check and evaluate a file

Options:
  -h, --help      Show help
  -v, --verbose   Verbose output
  --debug         Debug mode (print AST)
```

### Parser Implementation

```gleam
pub fn parse_args(args: List(String)) -> Result(Command, String) {
  case args {
    ["--help"] | ["-h"] -> Ok(Help)
    ["check", file, ..rest] -> parse_check(file, rest)
    ["run", file, ..rest] -> parse_run(file, rest)
    [] -> Error("No command provided")
    [unknown, ..] -> Error("Unknown command: " <> unknown)
  }
}

fn parse_check(file: String, options: List(String)) -> Result(Command, String) {
  let verbose = list.contains(options, "-v") || list.contains(options, "--verbose")
  let debug = list.contains(options, "--debug")
  Ok(Check(file, verbose, debug))
}

fn parse_run(file: String, options: List(String)) -> Result(Command, String) {
  let verbose = list.contains(options, "-v") || list.contains(options, "--verbose")
  let debug = list.contains(options, "--debug")
  Ok(Run(file, verbose, debug))
}
```

---

## File Type Detection

```gleam
pub type FileType {
  Core  // .core.tao
  Tao   // .tao (future)
}

pub fn detect_file_type(path: String) -> Result(FileType, String) {
  case string.ends_with(path, ".core.tao") {
    True -> Ok(Core)
    False -> {
      case string.ends_with(path, ".tao") {
        True -> Ok(Tao)
        False -> Error("Unknown file type: " <> path)
      }
    }
  }
}
```

---

## Exit Codes

| Code | Meaning | When |
|------|---------|------|
| 0 | Success | Type checking passed, evaluation succeeded |
| 1 | Type/Parse Error | Type error or parse error found |
| 2 | Runtime Error | Evaluation failed (division by zero, etc.) |
| 3 | File Not Found | File doesn't exist |
| 4 | Invalid Arguments | Unknown command, missing file, etc. |

### Exit Code Implementation

```gleam
pub fn main() {
  let args = command_line.args() |> list.drop(1)
  let command = parse_args(args)
  
  case command {
    Ok(Help) -> {
      print_help()
      exit(0)
    }
    Ok(Check(file, verbose, debug)) -> {
      let result = run_check(file, verbose, debug)
      case result {
        Ok(_) -> exit(0)
        Error(ParseError) -> exit(1)
        Error(TypeError) -> exit(1)
        Error(FileNotFound) -> exit(3)
      }
    }
    Ok(Run(file, verbose, debug)) -> {
      let result = run_eval(file, verbose, debug)
      case result {
        Ok(_) -> exit(0)
        Error(ParseError) -> exit(1)
        Error(TypeError) -> exit(1)
        Error(RuntimeError) -> exit(2)
        Error(FileNotFound) -> exit(3)
      }
    }
    Error(msg) -> {
      io.println("Error: " <> msg)
      exit(4)
    }
  }
}
```

---

## Verbose Mode

When `--verbose` or `-v` is passed, print detailed progress:

```gleam
pub fn verbose_print(verbose: Bool, message: String) {
  case verbose {
    True -> io.println(message)
    False -> Nil
  }
}

// Usage
verbose_print(verbose, "✓ Loading " <> file)
verbose_print(verbose, "✓ Parsing...")
verbose_print(verbose, "  AST: " <> inspect(ast))
verbose_print(verbose, "✓ Type checking...")
verbose_print(verbose, "  Inferred type: " <> inspect(typ))
```

---

## Debug Mode

When `--debug` is passed, print AST and type information:

```gleam
pub fn debug_print(debug: Bool, title: String, value: a) {
  case debug {
    True -> {
      io.println(title)
      io.println(inspect(value))
      io.println("")
    }
    False -> Nil
  }
}

// Usage
debug_print(debug, "AST:", ast)
debug_print(debug, "Type:", typ)
debug_print(debug, "Value:", value)
```

---

## Error Handling

### Invalid Arguments

```
Error: No command provided
Usage: gleam run <command> <file>
```

```
Error: Unknown command: foo
Usage: gleam run <command> <file>
```

```
Error: Missing file argument
Usage: gleam run check <file>
```

### File Not Found

```
✗ File not found: nonexistent.core.tao
```

---

## Testing

### Argument Parsing Tests

```gleam
pub fn parse_help_test() {
  parse_args(["--help"]) |> should.equal(Ok(Help))
  parse_args(["-h"]) |> should.equal(Ok(Help))
}

pub fn parse_check_test() {
  parse_args(["check", "file.core.tao"]) 
  |> should.equal(Ok(Check("file.core.tao", False, False)))
}

pub fn parse_check_verbose_test() {
  parse_args(["check", "file.core.tao", "--verbose"]) 
  |> should.equal(Ok(Check("file.core.tao", True, False)))
}

pub fn parse_check_debug_test() {
  parse_args(["check", "file.core.tao", "--debug"]) 
  |> should.equal(Ok(Check("file.core.tao", False, True)))
}

pub fn parse_run_test() {
  parse_args(["run", "file.core.tao"]) 
  |> should.equal(Ok(Run("file.core.tao", False, False)))
}

pub fn parse_unknown_command_test() {
  parse_args(["foo", "file.core.tao"]) 
  |> should.be_error
}

pub fn parse_no_command_test() {
  parse_args([]) 
  |> should.be_error
}
```

### File Type Detection Tests

```gleam
pub fn detect_core_test() {
  detect_file_type("example.core.tao") 
  |> should.equal(Ok(Core))
}

pub fn detect_tao_test() {
  detect_file_type("example.tao") 
  |> should.equal(Ok(Tao))
}

pub fn detect_unknown_test() {
  detect_file_type("example.txt") 
  |> should.be_error
}
```

---

## See Also

- **[01-overview.md](./01-overview.md)** - CLI overview
- **[03-error-reporter.md](./03-error-reporter.md)** - Error reporting
