# Maintenance Plans Overview

> **Goal**: Track codebase health, refactoring opportunities, and technical debt
> **Status**: ✅ 5 Quick Wins Complete, ⏳ Cosmetic Polish Planned
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
├── 01-overview.md              # This file - status and priorities
├── 02-quick-wins.md            # Safe refactoring plan (CORRECTED)
├── 03-refactoring-log.md       # Completed refactorings
└── ...                         # Additional analysis as needed
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

### ✅ Complete

**Analysis**:
- ✅ Full codebase review completed
- ✅ Issues categorized by priority
- ✅ Effort estimates provided
- ✅ Refactoring order recommended
- ✅ 5 safe quick wins implemented

**Documents Created**:
- ✅ **[01-codebase-analysis.md](./01-codebase-analysis.md)** - Comprehensive analysis
- ✅ **[02-quick-wins.md](./02-quick-wins.md)** - Safe refactoring plan (corrected)

**Quick Wins Implemented**:
- ✅ Span helper functions added (`dummy_span()`, `mk_span()`)
- ✅ CLI flag helper added (`has_flag()`)
- ✅ Unused imports removed
- ✅ NbE documentation added for eliminators
- ✅ Term documentation enhanced
- ✅ **401 tests passing** - no regressions

**Documentation Improvements**:
- ✅ Added comprehensive NbE explanation for `Elim` type
- ✅ Explained why `EMatch` is essential (must NEVER be removed)
- ✅ Enhanced documentation for all `TermData` constructors
- ✅ Added syntax vs. semantics distinction
- ✅ Added De Bruijn indices vs. levels explanation

### ⏳ In Progress / Planned

**Cosmetic Polish** (Week 1 - cosmetic only):
- [ ] Standardize error messages (20 min)
- [ ] Use `if` instead of `case` for booleans (15 min)
- [ ] Remove verbose type annotations (20 min)
- [ ] Standardize module headers (20 min)

**DO NOT IMPLEMENT** (Would break correctness):
- ❌ Remove Type alias (`pub type Type = Value`) - semantically correct (dependent type theory)
- ❌ Remove `EMatch` constructor - breaks normalization by evaluation
- ❌ Remove documentation comments - explain semantics, not just syntax

### 📋 Pending Analysis

- [ ] Performance profiling
- [ ] Memory usage analysis
- [ ] Build time optimization opportunities
- [ ] Dependency audit (unused dependencies)

---

## Code Quality Metrics

### Current State

| Metric | Value | Target | Status |
|--------|-------|--------|--------|
| Total Lines | ~6500 | - | - |
| Test Coverage | ~65% | 80% | ⚠️ Below target |
| Public Functions | ~200 | - | - |
| Documented Functions | ~60% | 90% | ⚠️ Improved |
| Average Function Length | 25 lines | <20 | ⚠️ Above target |
| Max Function Length | 200+ lines | <50 | 🔴 Critical |
| Critical Issues | 0 | 0 | ✅ Fixed |
| High Priority Issues | 3 | 0 | 🟠 Behind |

### Trend

| Month | Coverage | Documented | Issues |
|-------|----------|------------|--------|
| March 2025 | 65% | 60% | 38 |
| Target | 80% | 90% | 0 |

---

## Refactoring Principles

### When to Refactor

✅ **Do refactor when**:
- Adding a new feature and touching related code
- Fixing a bug and the code is confusing
- Preparing for a major change
- Code is duplicated in 3+ places
- Function is >50 lines

❌ **Don't refactor when**:
- Code is working and stable
- Deadline is imminent
- No tests exist (write tests first!)
- Just for the sake of refactoring
- **Don't understand the algorithm**

### Refactoring Process

1. **Identify** - Find issue via analysis or PR review
2. **Document** - Add to this plan with priority
3. **Understand** - Research algorithm/semantics BEFORE changing
4. **Test** - Ensure tests exist (write if missing)
5. **Refactor** - Make the change
6. **Verify** - Run tests, check performance
7. **Update** - Mark as complete in this plan

---

## Technical Debt Tracking

### Debt Incurred

| Date | Issue | Reason | Planned Fix |
|------|-------|--------|-------------|
| 2025-03 | CLI doesn't type check | Rapid prototyping | Week 1 |
| 2025-03 | No exit codes | Gleam stdlib limits | N/A (not available) |
| 2025-03 | Tao not integrated | In progress | Week 1 |
| 2025-03 | Overengineered imports | Anticipating features | Week 2 |

### Debt Repaid

| Date | Issue | Fix | Actual Effort |
|------|-------|-----|---------------|
| 2025-03 | Missing span helpers | Added `dummy_span()`, `mk_span()` | 15 min |
| 2025-03 | Repetitive CLI code | Added `has_flag()` helper | 15 min |
| 2025-03 | Unused imports | Removed `import gleam/option` | 5 min |
| 2025-03 | Missing NbE docs | Added comprehensive eliminators docs | 30 min |
| 2025-03 | Sparse term docs | Enhanced all TermData docs | 45 min |

---

## Maintenance Checklist

### Weekly

- [ ] Review new code for issues
- [ ] Update this plan with new findings
- [ ] Check test coverage trend
- [ ] Review open PRs for refactoring opportunities

### Monthly

- [ ] Run full codebase analysis
- [ ] Update metrics
- [ ] Prioritize backlog
- [ ] Review technical debt

### Quarterly

- [ ] Major refactoring sprint
- [ ] Performance profiling
- [ ] Dependency audit
- [ ] Documentation review

---

## Related Documents

- **[01-codebase-analysis.md](./01-codebase-analysis.md)** - Full analysis with findings
- **[02-quick-wins.md](./02-quick-wins.md)** - Safe refactoring plan (corrected)
- **[../core/01-overview.md](../core/01-overview.md)** - Core language status
- **[../grammar/01-overview.md](../grammar/01-overview.md)** - Grammar library status
- **[../tao/01-overview.md](../tao/01-overview.md)** - Tao language status
- **[../cli/01-overview.md](../cli/01-overview.md)** - CLI status

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

### Effort Estimates

- ⚡ **Quick** - <15 minutes
- 🕐 **Short** - 15-30 minutes
- 📅 **Medium** - 1-2 hours
- 📆 **Long** - 1+ day

---

## See Also

- **[docs/plans/README.md](../README.md)** - Plans directory structure
- **[test/README.md](../../test/README.md)** - Testing guide
- **[CONTRIBUTING.md](../../CONTRIBUTING.md)** - Contribution guidelines (if exists)

---

## References

- [Codebase Analysis](./01-codebase-analysis.md)
- [Quick Wins](./02-quick-wins.md)
- [Core Language](../../src/core/core.gleam)
- [Syntax Library](../../src/syntax/grammar.gleam)
- [Tao Language](../../src/tao/ast.gleam)
- [CLI](../../src/compiler_bootstrap.gleam)
