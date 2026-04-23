# Plans Directory - Reorganization Plan

> **Date**: March 2026
> **Status**: 📋 Proposed reorganization
> **Goal**: Clean, chronological numbering with accurate status

---

## Current Issues

1. **Duplicate numbers**: Multiple files with same prefix (e.g., `03-*.md`, `04-*.md`, `15-*.md`)
2. **Non-chronological order**: Files not ordered by creation date
3. **Outdated status**: Many files show "Pending" when features are complete
4. **No archive policy**: Old/obsolete plans mixed with active ones
5. **Inconsistent naming**: Some use kebab-case, some use underscores

---

## Reorganization Principles

### 1. Chronological Numbering

Files should be numbered in order of creation, not by importance:
- `01-` = First document created (overview)
- `02-` = Second document created
- etc.

### 2. Status Accuracy

Every file should have accurate status:
- ✅ **Complete** - Feature implemented and tested
- ⏳ **In Progress** - Actively being worked on
- 📋 **Planned** - Designed but not started
- 🗄️ **Historical** - Superseded or archived

### 3. Archive Policy

Move to `archive/` when:
- Approach was abandoned
- Design was completely superseded
- It's historical context only

Keep when:
- Still relevant to current implementation
- Documents active future work
- Provides important context

### 4. Consistent Naming

Use kebab-case for all new files:
- `01-overview.md` ✅
- `01_overview.md` ❌
- `typeInference.md` ❌

---

## Proposed New Structure

### Root Level (`docs/plans/`)

```
docs/plans/
├── README.md                        # This guide
├── retrospective.md                 # Comprehensive retrospective (KEEP)
├── session-summary-2026-03-17.md    # Session notes (KEEP)
├── evaluation-timeout-analysis.md   # Bug analysis (KEEP)
├── fix-recursion-timeout.md         # Bug fix plan (KEEP)
├── type-inference-fixes.md          # Bug fix plan (KEEP)
└── archive/                         # Archived root-level docs
    └── ...
```

### CLI (`docs/plans/cli/`)

**Status**: ✅ Complete - CLI fully functional

```
cli/
├── 01-overview.md                   # ✅ Complete
├── 02-cli-parser.md                 # ✅ Complete
├── 03-error-reporter.md             # ✅ Complete
├── 04-check-run-commands.md         # ✅ Complete
└── archive/
```

**Action**: Renumber sequentially, mark all as complete

### Core (`docs/plans/core/`)

**Status**: ✅ Complete - All features working

```
core/
├── 01-overview.md                   # ✅ Complete (was 01)
├── 02-syntax.md                     # ✅ Complete (was 02)
├── 03-ffi-comptime.md               # ✅ Complete (was 03)
├── 04-tao-integration.md            # ✅ Complete (was 04)
├── 05-production-ready.md           # ✅ Complete (was 06)
├── 06-hole-inference.md             # ✅ Complete (was 13)
├── 07-type-application.md           # ✅ Complete (was 15)
├── 08-implicit-arguments.md         # ✅ Complete (was 16)
├── 09-variable-shadowing.md         # ✅ Complete (was 03-dup)
├── 10-match-type-inference.md       # ✅ Complete (was 04-dup)
├── 11-fix-match-parsing.md          # ✅ Complete (was 07)
├── 12-debug-match-parsing.md        # ✅ Complete (was 10)
├── 13-language-enhancements.md      # ✅ Complete (was 11)
├── 14-let-bindings.md               # ✅ Complete (was 12)
├── 15-golden-samples.md             # ✅ Complete (was 14)
├── 16-syntax-keyword-changes.md     # ✅ Complete (was 09)
├── 17-remaining-fixes.md            # ✅ Complete (was 16-dup)
└── archive/
    ├── 15-type-inference-fixes.md   # Superseded by implementation
    └── ...
```

**Action**: 
- Renumber sequentially
- Move superseded plans to archive
- Update all status to ✅ Complete

### Syntax (`docs/plans/syntax/`)

**Status**: ✅ Complete - All features working

```
syntax/
├── 01-overview.md                   # ✅ Complete
├── 02-grammar-dsl.md                # ✅ Complete
├── 03-parser-library.md             # ✅ Complete
├── 04-formatter-library.md          # ✅ Complete
├── 05-source-location-tracking.md   # ✅ Complete
├── 06-automatic-formatter-analysis.md # ✅ Complete
├── 07-grammar-derived-formatter.md  # ✅ Complete (was 08)
├── 08-records-with-fields.md        # ✅ Complete (was 06-dup)
├── 09-formatter-ux-improvements.md  # ✅ Complete (was 07)
├── 10-comprehensive-analysis.md     # ✅ Complete (was 09-dup)
├── 11-operator-metadata-api.md      # ✅ Complete (was 09-dup)
├── 12-refactoring-plan.md           # ✅ Complete (was 10)
└── archive/
```

**Action**: Renumber sequentially, mark all as complete

### Tao (`docs/plans/tao/`)

**Status**: ⏳ In Progress - Core working, advanced features pending

```
tao/
├── 01-tao-implementation.md         # ✅ Complete (was 00)
├── 02-overview.md                   # ⏳ In Progress (was 01)
├── 03-syntax.md                     # ✅ Complete (was 02)
├── 04-desugaring.md                 # ✅ Complete (was 03)
├── 05-standard-library.md           # 📋 Planned (was 04)
├── 06-comprehensive-analysis.md     # ✅ Complete (was 05)
├── 07-implementation-plan.md        # ✅ Complete (was 06)
├── 08-desugaring-specification.md   # ✅ Complete (was 07)
├── 09-tao-mvp-plan.md               # ✅ Complete (was 09)
├── 10-overloading-design.md         # ✅ Complete (was 10)
├── 11-test-system.md                # ✅ Complete (was 11)
├── 12-import-system.md              # ✅ Complete (was 12)
├── 13-stmt-system.md                # ✅ Complete (was 13)
├── 14-examples-plan.md              # ✅ Complete (was 14)
├── 15-fix-plan.md                   # ✅ Complete (was 14-dup)
├── 16-stmt-run-test.md              # ✅ Complete (was 14-dup)
├── 17-let-binding-fix.md            # ✅ Complete (was 15)
├── 18-remaining-issues.md           # ✅ Complete (was 15-dup)
├── 19-hole-investigation.md         # ✅ Complete (was 16)
├── 20-let-binding-status.md         # ✅ Complete (was 16-dup)
├── 21-comprehensive-issues.md       # ✅ Complete (was 17)
├── 22-syntax-test-plan.md           # ✅ Complete (was 17-dup)
├── 23-error-message-improvements.md # ✅ Complete (was 18)
├── 24-syntax-test-status.md         # ✅ Complete (was 18-dup)
├── 25-evaluation-fix-plan.md        # ✅ Complete (was standalone)
├── 26-function-type-parsing.md      # ✅ Complete (was standalone)
├── 27-match-expression-fix.md       # ✅ Complete (was standalone)
├── 28-source-snippets-plan.md       # ✅ Complete (was standalone)
├── 29-tao-status.md                 # ✅ Complete (was standalone)
├── 30-enhanced-test-framework.md    # ✅ Complete (was standalone)
└── archive/
    ├── 11-overloading-implementation.md
    ├── 12-overloading-implementation-guide.md
    └── 13-tao-status.md (old version)
```

**Action**: 
- Renumber sequentially
- Move old versions to archive
- Update status based on current implementation

### Error Reporting (`docs/plans/error-reporting/`)

**Status**: ✅ Complete - Error reporting fully functional

```
error-reporting/
├── 01-overview.md                   # ✅ Complete
├── 02-error-types.md                # ✅ Complete
├── 03-source-snippets.md            # ✅ Complete
├── 04-cli-integration.md            # ✅ Complete
├── 05-parse-error-panic-fix.md      # ✅ Complete
├── 06-error-message-design.md       # ✅ Complete
└── archive/
```

**Action**: Mark all as complete

### Stdlib (`docs/plans/stdlib/`)

**Status**: 📋 Planned - Not yet implemented

```
stdlib/
├── 01-overview.md                   # 📋 Planned
├── 02-prelude.md                    # 📋 Planned
├── 03-numeric.md                    # 📋 Planned
├── 04-import-system.md              # 📋 Planned
├── 05-polymorphic-constructors.md   # 📋 Planned
├── 06-constructor-patterns.md       # 📋 Planned
└── archive/
```

**Action**: No changes needed, status is accurate

### Maintenance (`docs/plans/maintenance/`)

**Status**: ✅ Complete - Warning cleanup done

```
maintenance/
├── 01-overview.md                   # ✅ Complete (was 01-dup)
├── 02-codebase-analysis.md          # ✅ Complete (was 01-dup)
├── 03-quick-wins.md                 # ✅ Complete
├── 04-warning-analysis.md           # ✅ Complete
├── 05-unused-variable-review.md     # ✅ Complete
├── 06-warning-cleanup-complete.md   # ✅ Complete
├── 07-code-quality-analysis.md      # ✅ Complete
├── 08-warnings-cleanup-plan.md      # ✅ Complete (was standalone)
└── archive/
```

**Action**: Renumber sequentially, mark all as complete

### Testing (`docs/plans/testing/`)

**Status**: ✅ Complete - Test framework functional

```
testing/
├── 01-overview.md                   # ✅ Complete
├── 02-e2e-test-enhancement.md       # ✅ Complete
├── 03-examples-testing.md           # ✅ Complete
├── 04-cli-golden-files.md           # ✅ Complete
├── 05-e2e-test-plan.md              # ✅ Complete (was standalone)
├── 06-examples-testing-plan.md      # ✅ Complete (was standalone)
└── archive/
    ├── 05-error-message-improvements.md
    ├── 06-error-message-enhancement-plan.md
    ├── 07-error-message-analysis.md
    └── 08-error-message-improvements-phase2.md
```

**Action**: 
- Move error-message files to archive (they're about error reporting, not testing)
- Renumber sequentially

---

## Implementation Steps

### Phase 1: Create Archive Directories (5 minutes)

```bash
mkdir -p docs/plans/{cli,core,syntax,tao,error-reporting,stdlib,maintenance,testing}/archive
```

### Phase 2: Move Obsolete Files to Archive (10 minutes)

Files to archive:
- Duplicate numbering
- Superseded designs
- Historical context only

### Phase 3: Renumber Remaining Files (15 minutes)

Rename files in chronological order within each directory.

### Phase 4: Update Status in Each File (30 minutes)

Add/update status section at top of each file:
```markdown
> **Status**: ✅ Complete / ⏳ In Progress / 📋 Planned / 🗄️ Historical
> **Last Updated**: Month Year
```

### Phase 5: Update README Files (15 minutes)

Update each directory's overview file with:
- Current status
- What's working
- What's pending
- Test counts

### Phase 6: Update Root README (10 minutes)

Update `docs/plans/README.md` with new structure.

---

## Total Estimated Time

**85 minutes** (~1.5 hours)

---

## Verification Checklist

After reorganization:

- [ ] No duplicate numbers within directories
- [ ] All files have accurate status
- [ ] Archive directories contain obsolete plans
- [ ] README files updated
- [ ] Cross-references still work
- [ ] Links in other docs still valid

---

## Maintenance Going Forward

### When Creating New Plans

1. Check existing files for next number
2. Use kebab-case naming
3. Add status section at top
4. Link from overview file

### When Completing Features

1. Update status in relevant plan file
2. Update overview file
3. Add test count if applicable

### Quarterly Review

1. Check for duplicate numbers
2. Verify status accuracy
3. Move obsolete plans to archive
4. Update README files

---

## Success Metrics

- ✅ No duplicate numbers
- ✅ All files have accurate status
- ✅ Archive contains only historical docs
- ✅ New contributors can find relevant plans
- ✅ Status matches implementation

---

## Related Documents

- **[docs/plans/README.md](./README.md)** - Original structure guide
- **[docs/plans/retrospective.md](./retrospective.md)** - Comprehensive retrospective
- **[docs/README.md](../README.md)** - Documentation index
