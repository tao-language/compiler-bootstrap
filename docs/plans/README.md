# Plans Directory - Organized Structure

> **Last Reorganized**: March 2026
> **Status**: ✅ All plans renumbered sequentially with accurate status
> **Total Tests**: 519 passing (100%)

---

## Directory Structure

```
docs/plans/
├── README.md                        # This file
├── retrospective.md                 # Comprehensive retrospective (1,800+ lines)
├── session-summary-2026-03-17.md    # Session notes
├── evaluation-timeout-analysis.md   # Bug analysis (quote re-evaluation)
├── fix-recursion-timeout.md         # Bug fix implementation plan
├── type-inference-fixes.md          # Type inference fix plan
├── REORGANIZATION-PLAN.md           # Reorganization proposal
│
├── cli/                             # CLI implementation (✅ Complete)
│   ├── 01-overview.md
│   ├── 02-cli-parser.md
│   ├── 03-error-reporter.md
│   ├── 04-check-run-commands.md
│   └── archive/
│
├── core/                            # Core language (✅ Complete)
│   ├── 01-overview.md
│   ├── 02-syntax.md
│   ├── 03-ffi-comptime.md
│   ├── 05-variable-shadowing.md
│   ├── 06-match-type-inference.md
│   ├── 07-tao-integration.md
│   ├── 08-production-ready.md
│   ├── 09-fix-match-parsing.md
│   ├── 10-type-checker-integration.md
│   ├── 11-syntax-keyword-changes.md
│   ├── 12-fix-match-parsing-debug.md
│   ├── 13-language-enhancements.md
│   ├── 14-let-bindings.md
│   ├── 15-hole-inference.md
│   ├── 16-golden-samples.md
│   ├── 17-type-application.md
│   └── archive/
│
├── syntax/                          # Syntax library (✅ Complete)
│   ├── 01-overview.md
│   ├── 02-grammar-dsl.md
│   ├── 03-parser-library.md
│   ├── 04-formatter-library.md
│   ├── 05-source-location-tracking.md
│   ├── 06-automatic-formatter-analysis.md
│   ├── 07-records-with-fields.md
│   ├── 08-formatter-ux-improvements.md
│   ├── 09-grammar-derived-formatter.md
│   ├── 10-comprehensive-refactoring-plan.md
│   └── archive/
│
├── tao/                             # Tao language (✅ Complete)
│   ├── 01-tao-implementation.md
│   ├── 02-overview.md
│   ├── 03-syntax.md
│   ├── 04-desugaring.md
│   ├── 05-standard-library.md
│   ├── 06-comprehensive-analysis.md
│   ├── 07-implementation-plan.md
│   ├── 08-desugaring-specification.md
│   ├── 09-mvp-plan.md
│   ├── 10-overloading-design.md
│   ├── 11-examples-plan.md
│   ├── 12-fix-plan.md
│   ├── 13-let-binding-fix.md
│   ├── 14-let-binding-status.md
│   ├── 15-syntax-test-plan.md
│   ├── 16-syntax-test-status.md
│   └── archive/
│
├── error-reporting/                 # Error reporting (✅ Complete)
│   ├── 01-overview.md
│   ├── 02-error-types.md
│   ├── 03-source-snippets.md
│   ├── 04-cli-integration.md
│   ├── 05-parse-error-panic-fix.md
│   ├── 06-error-message-design.md
│   └── archive/
│
├── stdlib/                          # Standard library (📋 Planned)
│   ├── 01-overview.md
│   ├── 02-prelude.md
│   ├── 03-numeric.md
│   ├── 04-import-system.md
│   ├── 05-polymorphic-constructors.md
│   ├── 06-constructor-patterns.md
│   └── archive/
│
├── maintenance/                     # Maintenance (✅ Complete)
│   ├── 02-overview.md
│   ├── 03-quick-wins.md
│   ├── 04-warning-analysis.md
│   ├── 05-unused-variable-review.md
│   ├── 06-warning-cleanup-complete.md
│   ├── 07-code-quality-analysis.md
│   ├── 08-warnings-cleanup-plan.md
│   └── archive/
│
└── testing/                         # Testing infrastructure (✅ Complete)
    ├── 01-overview.md
    ├── 02-e2e-enhancement.md
    ├── 03-examples-testing.md
    ├── 04-cli-golden-files.md
    └── archive/
```

---

## Status Summary

| Component | Status | Tests | Notes |
|-----------|--------|-------|-------|
| **CLI** | ✅ Complete | 519 | File type detection, error reporting, check/run commands |
| **Core Language** | ✅ Complete | 519 | All 13 Term variants, NbE, bidirectional typing, exhaustiveness |
| **Syntax Library** | ✅ Complete | 519 | Grammar DSL, parser, formatter with document algebra |
| **Tao Language** | ✅ Complete | 519 | Expr, Stmt, imports, test framework, overloading |
| **Error Reporting** | ✅ Complete | 519 | Source snippets, error codes, hints |
| **Stdlib** | 📋 Planned | 0 | Not yet implemented |
| **Maintenance** | ✅ Complete | 519 | Warning cleanup (45 → 0), code quality |
| **Testing** | ✅ Complete | 519 | E2E tests, example tests, golden files |

---

## File Naming Convention

Files are numbered sequentially in order of creation:

- `01-overview.md` - Entry point with overall status
- `02-*.md` - Second document created
- `03-*.md` - Third document created
- etc.

**Archive**: Obsolete/superseded plans are moved to `archive/` subdirectory.

---

## Status Icons

- ✅ **Complete** - Feature implemented and tested
- ⏳ **In Progress** - Currently being worked on
- 📋 **Planned** - Designed but not started
- 🗄️ **Historical** - In archive (superseded or abandoned)

---

## Quick Links by Component

### CLI
- **[01-overview.md](./cli/01-overview.md)** - CLI overview and status
- **[04-check-run-commands.md](./cli/04-check-run-commands.md)** - Check/run command implementation

### Core Language
- **[01-overview.md](./core/01-overview.md)** - Core language overview
- **[02-syntax.md](./core/02-syntax.md)** - Syntax specification
- **[03-ffi-comptime.md](./core/03-ffi-comptime.md)** - FFI and comptime evaluation
- **[07-tao-integration.md](./core/07-tao-integration.md)** - Tao integration

### Syntax Library
- **[01-overview.md](./syntax/01-overview.md)** - Syntax library overview
- **[02-grammar-dsl.md](./syntax/02-grammar-dsl.md)** - Grammar DSL specification
- **[03-parser-library.md](./syntax/03-parser-library.md)** - Parser implementation
- **[04-formatter-library.md](./syntax/04-formatter-library.md)** - Formatter implementation

### Tao Language
- **[02-overview.md](./tao/02-overview.md)** - Tao language overview
- **[03-syntax.md](./tao/03-syntax.md)** - Tao syntax specification
- **[04-desugaring.md](./tao/04-desugaring.md)** - Desugaring rules
- **[10-overloading-design.md](./tao/10-overloading-design.md)** - Overloading design

### Error Reporting
- **[01-overview.md](./error-reporting/01-overview.md)** - Error reporting overview
- **[06-error-message-design.md](./error-reporting/06-error-message-design.md)** - Error message design

### Maintenance
- **[02-overview.md](./maintenance/02-overview.md)** - Maintenance overview
- **[06-warning-cleanup-complete.md](./maintenance/06-warning-cleanup-complete.md)** - Warning cleanup report (45 → 0)

### Testing
- **[01-overview.md](./testing/01-overview.md)** - Testing overview
- **[04-cli-golden-files.md](./testing/04-cli-golden-files.md)** - CLI golden file tests

---

## Major Bug Fixes (March 2026)

These documents capture critical bugs that were fixed:

1. **[evaluation-timeout-analysis.md](./evaluation-timeout-analysis.md)** - Root cause analysis of factorial timeout
2. **[fix-recursion-timeout.md](./fix-recursion-timeout.md)** - Implementation plan for quote re-evaluation fix
3. **[type-inference-fixes.md](./type-inference-fixes.md)** - Type inference and pattern matching fixes

**Key Fixes**:
- Quote was re-evaluating lambda bodies (exponential blowup)
- `do_match` missing FFI parameter (builtins stuck in match)
- Parser not consuming semicolons (error recovery broken)
- Step counters for eval/quote (infinite loop protection)

---

## Comprehensive Documentation

For a complete retrospective including:
- What worked well
- What would be changed
- Debugging strategies
- Tool recommendations
- Type theory lessons

**See**: **[retrospective.md](./retrospective.md)** (1,800+ lines)

---

## Maintenance Going Forward

### When Creating New Plans

1. Check existing files for next number
2. Use kebab-case naming: `NN-feature-name.md`
3. Add status section at top
4. Link from overview file

### When Completing Features

1. Update status in relevant plan file
2. Update overview file with test count
3. Move obsolete plans to `archive/`

### Quarterly Review

1. Verify status accuracy
2. Check for duplicate numbers
3. Move obsolete plans to archive
4. Update this README

---

## Related Documents

- **[docs/README.md](../README.md)** - Documentation index
- **[docs/lessons-learned.md](../lessons-learned.md)** - Key insights from development
- **[src/README.md](../../src/README.md)** - Code style guide
- **[test/README.md](../../test/README.md)** - Testing guide
