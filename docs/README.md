# Documentation Index

> **Purpose**: Central index for all project documentation
> **Last Updated**: March 2025

---

## Quick Start

| Document | Description |
|----------|-------------|
| **[README.md](../README.md)** | Project overview and quick start |
| **[docs/cli.md](./cli.md)** | CLI usage and examples |
| **[docs/syntax-library.md](./syntax-library.md)** | Syntax library documentation |
| **[docs/core.md](./core.md)** | Core language specification |
| **[docs/lessons-learned.md](./lessons-learned.md)** | Key lessons from development |

---

## User Documentation

### Getting Started

- **[README.md](../README.md)** - Project overview, installation, quick start
- **[docs/cli.md](./cli.md)** - CLI commands, options, examples, error reporting

### Language Reference

- **[docs/core.md](./core.md)** - Core language specification
  - Type system, normalization by evaluation, bidirectional type checking
  - Exhaustiveness checking, comptime evaluation, FFI support
- **[docs/syntax-library.md](./syntax-library.md)** - Syntax library usage
  - Grammar DSL, parser combinators, formatter combinators
  - Error reporting with source snippets

### Examples

- **[src/examples/calc.gleam](../src/examples/calc.gleam)** - Calculator example
- **[test/](../test/)** - Comprehensive test suite with examples

---

## Development Documentation

### Implementation Plans

#### Syntax Library

- **[docs/plans/syntax/01-overview.md](./plans/syntax/01-overview.md)** - Syntax library overview
- **[docs/plans/syntax/02-grammar-dsl.md](./plans/syntax/02-grammar-dsl.md)** - Grammar DSL specification
- **[docs/plans/syntax/03-parser-library.md](./plans/syntax/03-parser-library.md)** - Parser implementation
- **[docs/plans/syntax/04-formatter-library.md](./plans/syntax/04-formatter-library.md)** - Formatter implementation
- **[docs/plans/syntax/05-source-location-tracking.md](./plans/syntax/05-source-location-tracking.md)** - Source location tracking
- **[docs/plans/syntax/06-automatic-formatter-analysis.md](./plans/syntax/06-automatic-formatter-analysis.md)** - Why full automation not feasible
- **[docs/plans/syntax/08-grammar-derived-formatter-plan.md](./plans/syntax/08-grammar-derived-formatter-plan.md)** - Grammar-derived formatter (✅ COMPLETE)

#### Core Language

- **[docs/plans/core/01-overview.md](./plans/core/01-overview.md)** - Core language overview
- **[docs/plans/core/02-syntax.md](./plans/core/02-syntax.md)** - Core syntax specification
- **[docs/plans/core/03-evaluator.md](./plans/core/03-evaluator.md)** - Evaluator implementation
- **[docs/plans/core/04-tao-integration.md](./plans/core/04-tao-integration.md)** - Tao integration plan

#### Tao Language

- **[docs/plans/tao/01-overview.md](./plans/tao/01-overview.md)** - Tao language overview
- **[docs/plans/tao/02-syntax.md](./plans/tao/02-syntax.md)** - Tao syntax specification
- **[docs/plans/tao/03-desugaring.md](./plans/tao/03-desugaring.md)** - Desugaring rules
- **[docs/plans/tao/04-standard-library.md](./plans/tao/04-standard-library.md)** - Standard library design
- **[docs/plans/tao/05-comprehensive-analysis.md](./plans/tao/05-comprehensive-analysis.md)** - Comprehensive analysis
- **[docs/plans/tao/06-implementation-plan.md](./plans/tao/06-implementation-plan.md)** - Implementation plan
- **[docs/plans/tao/07-desugaring-specification.md](./plans/tao/07-desugaring-specification.md)** - Desugaring specification

#### CLI

- **[docs/plans/cli/01-overview.md](./plans/cli/01-overview.md)** - CLI overview
- **[docs/plans/cli/02-cli-parser.md](./plans/cli/02-cli-parser.md)** - CLI parser specification
- **[docs/plans/cli/03-error-reporter.md](./plans/cli/03-error-reporter.md)** - Error reporter specification

#### Maintenance

- **[docs/plans/maintenance/01-overview.md](./plans/maintenance/01-overview.md)** - Maintenance overview
- **[docs/plans/maintenance/02-quick-wins.md](./plans/maintenance/02-quick-wins.md)** - Quick wins (refactoring)
- **[docs/plans/maintenance/03-warning-analysis.md](./plans/maintenance/03-warning-analysis.md)** - Warning analysis
- **[docs/plans/maintenance/04-unused-variable-safety-review.md](./plans/maintenance/04-unused-variable-safety-review.md)** - Safety review
- **[docs/plans/maintenance/05-warning-cleanup-complete.md](./plans/maintenance/05-warning-cleanup-complete.md)** - Warning cleanup report (45 → 0)

---

## Key Learnings

### Lessons Learned

- **[docs/lessons-learned.md](./lessons-learned.md)** - Core principles from development
  - Correctness over cleanliness
  - Some "dead code" is essential
  - Read the full warning message
  - Unreachable code after panic = bug
  - Test variables need context

### Warning Cleanup

- **[docs/plans/maintenance/05-warning-cleanup-complete.md](./plans/maintenance/05-warning-cleanup-complete.md)** - Complete report
  - 45 warnings → 0 warnings (100% reduction)
  - 401 tests passing
  - No regressions

---

## Architecture

### Module Structure

```
src/
├── compiler_bootstrap.gleam  # CLI entry point
├── syntax/
│   ├── grammar.gleam         # Grammar DSL (~950 lines)
│   ├── lexer.gleam           # Tokenizer (~400 lines)
│   ├── formatter.gleam       # Document algebra (~440 lines)
│   ├── source_snippet.gleam  # Source snippet (~260 lines)
│   └── error_reporter.gleam  # Error reporting (~220 lines)
├── core/
│   ├── syntax.gleam          # Core syntax (~1150 lines)
│   └── core.gleam            # Core language (~1800 lines)
├── tao/
│   ├── ast.gleam             # Tao AST (~430 lines)
│   ├── desugar.gleam         # Desugarer (TODO)
│   └── resugar.gleam         # Resugarer (~380 lines)
└── examples/
    └── calc.gleam            # Calculator example
```

### Data Flow

```
Tao Source → Lexer → Parser → Tao AST → Desugarer → Core Term
                                                      ↓
Core Term ← Type Checker ← Normalizer ← Evaluator ← Core Term
    ↓
Formatter → Output
```

---

## Testing

### Test Structure

```
test/
├── compiler_bootstrap_test.gleam  # CLI tests
├── syntax/
│   ├── grammar_test.gleam         # Grammar DSL tests
│   ├── lexer_test.gleam           # Lexer tests
│   └── formatter_test.gleam       # Formatter tests
├── core/
│   ├── core_test.gleam            # Core language tests
│   └── syntax_test.gleam          # Core syntax tests
└── README.md                      # Testing guide
```

### Running Tests

```bash
# Run all tests
gleam test

# Continuous testing (requires fswatch)
fswatch -or src test | xargs -n1 -I{} gleam test
```

### Test Results

- **401 tests passing**
- **0 warnings**
- **0 failures**

---

## Contributing

### Getting Started

1. Read **[README.md](../README.md)** for project overview
2. Read **[docs/lessons-learned.md](./lessons-learned.md)** for key principles
3. Pick an issue from the implementation plans
4. Make changes and run tests: `gleam test`

### Code Style

- **[src/README.md](../src/README.md)** - Code style guide
- **[test/README.md](../test/README.md)** - Testing guide

### Documentation

- Update relevant documentation when making changes
- Add tests for new features
- Update implementation plans when completing tasks

---

## Related Projects

- [Gleam](https://gleam.run/) - The programming language we're built on
- [Normalization by Evaluation](https://www.cs.ru.nl/~wouters/thesis.pdf) - Key evaluation technique
- [Maranget's Algorithm](https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf) - Exhaustiveness checking

---

## Contact

- **GitHub**: [your-org/compiler-bootstrap](https://github.com/your-org/compiler-bootstrap)
- **Issues**: [GitHub Issues](https://github.com/your-org/compiler-bootstrap/issues)

---

## License

See [LICENSE](../LICENSE) for details.
