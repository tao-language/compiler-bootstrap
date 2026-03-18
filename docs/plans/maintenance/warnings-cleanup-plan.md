# Compiler Warnings Cleanup Plan

**Date**: 2026-03-17  
**Status**: 📋 **Planned**  
**Total Warnings**: 218

---

## Philosophy

From [lessons-learned.md](../../docs/lessons-learned.md):

> **Correctness over cleanliness** - Don't blindly apply compiler warnings

Some "unused" code is intentional:
- Spine structures for type theory
- Neutral terms for normalization
- Error handling placeholders
- Test variables for pattern matching

---

## Warning Breakdown

| Category | Count | Priority | Notes |
|----------|-------|----------|-------|
| Unused imported item | 50 | HIGH | Easy fixes, remove or use |
| Unused variable | 37 | MEDIUM | Check if intentional |
| Unused imported type | 36 | HIGH | Easy fixes |
| Unused private function | 23 | MEDIUM | Review each case |
| Unused function argument | 22 | LOW | May be required by interface |
| Unused imported value | 20 | HIGH | Easy fixes |
| Unreachable pattern | 12 | MEDIUM | Review for bugs |
| Unused imported module | 7 | HIGH | Easy fixes |
| Unused private constant | 5 | LOW | May be documentation |
| Redundant tuple | 3 | LOW | Minor optimization |

---

## Cleanup Strategy

### Phase 1: Easy Wins (30 minutes)

**Target**: Unused imports (113 warnings)

These are safe to remove without affecting functionality:

```bash
# Find all unused import warnings
gleam build 2>&1 | grep "Unused imported" > /tmp/unused_imports.txt
```

**Action**: Remove unused imports from:
- Test files (most common)
- Source files

### Phase 2: Review Unreachable Patterns (1 hour)

**Target**: 12 unreachable pattern warnings

Some may indicate bugs (unreachable code after panic = bug per lessons-learned.md).

**Action**: 
1. Review each case
2. Remove if truly unreachable
3. Fix logic if contradictory

### Phase 3: Review Unused Variables (2 hours)

**Target**: 37 unused variable warnings

**Categories**:
- Loop variables (intentional): Keep with `_` prefix
- Test pattern variables: May be needed
- Debug leftovers: Remove

**Action**:
1. Add `_` prefix for intentional unused
2. Remove truly unused
3. Keep if semantically important

### Phase 4: Review Unused Functions/Constants (2 hours)

**Target**: 28 unused private function/constant warnings

**Action**:
1. Check if part of public API
2. Check if used in tests only
3. Remove dead code
4. Keep if documentation value

---

## Files with Most Warnings

```bash
# Find files with most warnings
gleam build 2>&1 | grep "┌─" | cut -d'─' -f2 | cut -d':' -f1 | sort | uniq -c | sort -rn | head -20
```

Expected top offenders:
- Test files (test/tao/*.gleam)
- Large implementation files (src/core/core.gleam)
- Syntax files (src/tao/syntax.gleam)

---

## Automated Cleanup Script

```bash
#!/bin/bash
# scripts/cleanup-warnings.sh

# Run build and capture warnings
gleam build 2>&1 | grep "^warning:" > /tmp/warnings.txt

# Count by category
echo "Warning categories:"
cat /tmp/warnings.txt | sort | uniq -c | sort -rn

# List files with warnings
echo -e "\nFiles with most warnings:"
gleam build 2>&1 | grep "┌─" | cut -d'─' -f2 | cut -d':' -f1 | sort | uniq -c | sort -rn | head -20
```

---

## Guidelines

### When to Remove

✅ **Remove if**:
- Clearly dead code
- Import never used
- Replaced by better implementation
- Test-only code in source files

### When to Keep

✅ **Keep if**:
- Part of type theory implementation
- Required for pattern matching
- Documentation value
- Used in error messages
- Part of public API (even if not used internally)

### When to Rename

✅ **Add `_` prefix if**:
- Required by interface but not used
- Used for pattern matching but value not needed
- Intentional placeholder

---

## Success Criteria

- [ ] 0 unused import warnings
- [ ] 0 unreachable pattern warnings (or documented)
- [ ] < 50 unused variable warnings (down from 37)
- [ ] All tests still pass
- [ ] No functionality changes

**Target**: Reduce from 218 to < 100 warnings

---

## Estimated Effort

- **Phase 1** (Imports): 30 minutes
- **Phase 2** (Unreachable): 1 hour
- **Phase 3** (Variables): 2 hours
- **Phase 4** (Functions): 2 hours
- **Testing**: 30 minutes
- **Total**: ~6 hours

---

## Risks

| Risk | Mitigation |
|------|------------|
| Removing intentional code | Review each case carefully |
| Breaking tests | Run full test suite after each phase |
| Losing documentation | Check if constant has doc value |
| Wasting time on low-value cleanup | Stop at 100 warnings, focus on features |

---

## Recommendation

**Do Phase 1 only** (unused imports) for quick wins, then focus on features.

The remaining warnings are mostly in:
1. Test files (cosmetic)
2. Implementation code (may be intentional)

Time is better spent on:
- Function type parsing (unblocks higher-order functions)
- Control flow desugaring (completes core features)
- Test/Run statements (improves UX)

---

**Status**: Plan created, Phase 1 ready to execute  
**Next**: Execute Phase 1 or defer to focus on features
