# Maintenance Plans Overview

> **Goal**: Track codebase health, refactoring opportunities, and technical debt
> **Status**: ✅ Warning Cleanup Complete (45 → 0), ⏳ Ongoing maintenance
> **Date**: March 2025

---

## Core Insight

**Technical debt compounds**. Addressing issues early prevents them from becoming critical blockers. This maintenance plan tracks simplification opportunities, overengineering, and refactoring needs.

**IMPORTANT**: Some "simplifications" break correctness. Always understand before refactoring.

**Key Learning**: `EMatch` looked unused but is ESSENTIAL for normalization by evaluation. Never remove core algorithm components without understanding their role.

---

## Architecture

### Maintenance Document Structure

```
docs/plans/maintenance/
├── 01-overview.md                    # This file - status and priorities
├── 02-quick-wins.md                  # Safe refactoring plan
├── 03-warning-analysis.md            # Warning categorization
├── 04-unused-variable-safety-review.md # Safety-critical review
├── 05-warning-cleanup-complete.md    # Final report (45 → 0)
└── ...                               # Additional analysis as needed
```

### Priority Levels

| Priority | Icon | Response Time | Examples |
|----------|------|---------------|----------|
| **Critical** | 🔴 | Immediate | CLI doesn't work, no exit codes |
| **High** | 🟠 | 2 weeks | Missing integration, unused features |
| **Medium** | 🟡 | 1 month | Code organization, documentation |
| **Low** | 🟢 | As time permits | Naming, comments, style |

---

## Implementation Status

### ✅ Complete: Warning Cleanup (45 → 0)

**Analysis**:
- ✅ Full codebase review completed
- ✅ 45 warnings categorized and fixed
- ✅ 100% warning reduction achieved
- ✅ 0 test regressions

**Documents Created**:
- ✅ **[01-codebase-analysis.md](./01-codebase-analysis.md)** - Comprehensive analysis
- ✅ **[02-quick-wins.md](./02-quick-wins.md)** - Safe refactoring plan
- ✅ **[03-warning-analysis.md](./03-warning-analysis.md)** - Warning categorization
- ✅ **[04-unused-variable-safety-review.md](./04-unused-variable-safety-review.md)** - Safety-critical review
- ✅ **[05-warning-cleanup-complete.md](./05-warning-cleanup-complete.md)** - Final report
- ✅ **[../../docs/lessons-learned.md](../../docs/lessons-learned.md)** - Key lessons learned
- ✅ **[../../src/README.md](../../src/README.md)** - Code style guide

**Changes Applied**:
- ✅ Span helper functions added (`dummy_span()`, `mk_span()`)
- ✅ CLI flag helper added (`has_flag()`)
- ✅ 11 unused imports removed
- ✅ 2 dead functions removed (`fold_operators`, `parse_value_to_term`)
- ✅ 3 unreachable code blocks fixed (panic + return contradiction)
- ✅ 3 unreachable patterns removed (redundant catch-alls)
- ✅ 15 unused variables prefixed with `_`
- ✅ 2 genuinely unused parameters removed (`env`, `bindings`)
- ✅ 1 duplicate import removed
- ✅ Streamlined documentation (brief comments + links to docs)
- ✅ Standardized error messages
- ✅ Standardized module headers
- ✅ **401 tests passing** - no regressions!

**Warning Breakdown**:
| Category | Count | Action |
|----------|-------|--------|
| Unused imports | 11 | Removed |
| Dead code | 2 | Removed |
| Unreachable code | 3 | Fixed (panic contradiction) |
| Unreachable patterns | 3 | Removed |
| Unused variables | 15 | Prefixed with `_` |
| Unused parameters | 2 | Removed entirely |
| Duplicate imports | 1 | Removed |
| Unused constructors | 5 | Removed from imports |
| **Total** | **45** | **All fixed** |

### ⏳ Ongoing Maintenance

**As Needed**:
- [ ] Address new warnings as they appear
- [ ] Update documentation as code evolves
- [ ] Review and update lessons learned

---

## Key Learnings

### 1. Read The Full Warning Message

Gleam's warnings provide crucial context:
- "This variable is never used" → Prefix with `_`
- "This argument is passed when recursing, but never used for anything" → Remove entirely
- "This code is unreachable because the previous one always panics" → Fix contradictory logic

### 2. Unreachable Code After Panic = Bug

If you see unreachable code after `panic`, you're likely both panicking AND returning a value. Restructure so panic IS the return value.

### 3. Test Variables Need Context

Variables that look unused in tests may be used in subsequent `case` expressions or function calls. Always read the full test.

### 4. Some Parameters Are Genuinely Useless

If a parameter is passed recursively but never consulted in ANY branch (not even passed to other functions), it's genuinely unused and should be removed.

### 5. EMatch is Essential

What looks like "unused" code in compilers may be critical for correctness. `EMatch` stores pending match operations on neutral terms - essential for NbE.

---

## Code Quality Metrics

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Warnings | 45 | 0 | -45 (100%) |
| Test failures | 0 | 0 | No regressions |
| Dead code | 2 functions | 0 | Removed |
| Unused imports | 11 | 0 | Removed |
| Documentation | Verbose | Concise + linked | Improved |

---

## Related Documents

- **[05-warning-cleanup-complete.md](./05-warning-cleanup-complete.md)** - Final cleanup report
- **[04-unused-variable-safety-review.md](./04-unused-variable-safety-review.md)** - Safety-critical review
- **[03-warning-analysis.md](./03-warning-analysis.md)** - Warning categorization
- **[02-quick-wins.md](./02-quick-wins.md)** - Safe refactoring plan
- **[../../docs/lessons-learned.md](../../docs/lessons-learned.md)** - Key lessons learned
- **[../../src/README.md](../../src/README.md)** - Code style guide
- **[../../test/README.md](../../test/README.md)** - Testing guide

---

## Quick Reference

### Priority Icons

- 🔴 **Critical** - Fix immediately (broken functionality)
- 🟠 **High** - Fix within 2 weeks (blocks progress)
- 🟡 **Medium** - Fix within 1 month (code quality)
- 🟢 **Low** - Fix as time permits (polish)

### Status Icons

- ✅ **Complete** - Done and tested
- ⏳ **In Progress** - Currently being worked on
- 📋 **Planned** - Scheduled but not started
- ❌ **Rejected** - Would break correctness

---

## See Also

- **[docs/plans/README.md](../README.md)** - Plans directory structure
- **[test/README.md](../../test/README.md)** - Testing guide
- **[CONTRIBUTING.md](../../CONTRIBUTING.md)** - Contribution guidelines (if exists)

---

## References

- [Codebase Analysis](./01-codebase-analysis.md)
- [Warning Cleanup](./05-warning-cleanup-complete.md)
- [Lessons Learned](../../docs/lessons-learned.md)
- [Core Language](../../src/core/core.gleam)
- [Syntax Library](../../src/syntax/grammar.gleam)
- [Tao Language](../../src/tao/ast.gleam)
- [CLI](../../src/compiler_bootstrap.gleam)
