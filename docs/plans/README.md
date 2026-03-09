# Plans Directory Structure

This directory contains implementation plans and design documents for the compiler. Each subdirectory represents a major component with its own set of plans.

---

## Directory Structure

```
docs/plans/
├── README.md              # This file - structure guide
├── grammar/               # Grammar system plans
│   ├── 01-overview.md     # Entry point with overall status
│   ├── 02-grammar-dsl.md  # Grammar DSL specification
│   ├── 03-parser-library.md
│   └── 04-formatter-library.md
└── core/                  # Core language plans
    ├── 01-overview.md     # Entry point with overall status
    ├── 02-syntax.md       # Syntax specification
    └── 03-ffi-comptime.md # FFI and comptime
```

---

## File Naming Convention

Use numbered prefixes to control sort order:

- `01-overview.md` - **Required** - Entry point with overall status
- `02-*.md` - Core specification/design
- `03-*.md` - Supporting libraries/components
- `04-*.md` - Additional components
- ...

This ensures the overview file appears first in file listings.

---

## Required Structure for Each Plan File

Every plan file should have a **Status section** near the top:

```markdown
# Component Name

> **Goal**: One-sentence description
> **Status**: ✅ Implemented / ⏳ In Progress / 📋 Planned
> **Date**: Month Day Year

---

## Status

### What's Working

- Feature 1
- Feature 2
- **X tests passing** (if applicable)

### What's Pending

- Pending feature 1
- Pending feature 2

### Related

- See **[01-overview.md](./01-overview.md)** for overall status
- See **[03-other-component.md](./03-other-component.md)** for related details

---

## Rest of Document

...
```

### Status Icons

- ✅ **Implemented** - Working and tested
- ⏳ **In Progress** - Currently being worked on
- 📋 **Planned** - Designed but not started
- ❌ **Blocked** - Waiting on something

---

## Overview File (01-overview.md)

The overview file is the **entry point** for each plan directory. It should contain:

1. **Core Principle/Insight** - What problem does this solve?
2. **Architecture Diagram** - High-level structure
3. **Design Principles** - Guiding decisions
4. **Implementation Status** - What's working vs pending
5. **Key Concepts** - Important ideas with examples
6. **Example Usage** - Code showing how it works
7. **Related Documents** - Links to other plans

Keep it **scannable** - use tables, code blocks, and bullet points.

---

## Low-Effort Status Tracking

### Minimal Viable Updates

When making changes, update status in this order:

1. **After completing a feature**: Update "What's Working" in the relevant plan file
2. **After finishing a phase**: Update the overview file's status section
3. **When tests pass**: Add test count (e.g., "**238 tests passing**")

### What NOT to Do

- ❌ Don't maintain a separate changelog
- ❌ Don't update status for every small commit
- ❌ Don't write detailed progress reports
- ❌ Don't track individual tasks (use issues/PRs for that)

### What TO Do

- ✅ Update status when something **works end-to-end**
- ✅ Add test counts when tests pass
- ✅ Move items from "Pending" to "Working" when done
- ✅ Add new pending items when you discover them

---

## Cross-References

Link between related documents:

```markdown
### Related

- See **[01-overview.md](./01-overview.md)** for overall status
- See **[02-other-plan.md](./02-other-plan.md)** for details
- See **[../other-dir/01-overview.md](../other-dir/01-overview.md)** for related component
```

This creates a navigable web of documents.

---

## When to Create New Plan Files

Create a new plan file when:

- ✅ A component is large enough to need its own spec
- ✅ There are implementation details that don't fit elsewhere
- ✅ Future work needs to be documented

Don't create a new file when:

- ❌ A few paragraphs would suffice
- ❌ It's a small change to an existing component
- ❌ It's a temporary experiment

---

## When to Archive Plans

Move plans to an `archive/` subdirectory when:

- ✅ The approach was abandoned
- ✅ The design was completely superseded
- ✅ It's historical context only

Keep plans when:

- ❌ They're still relevant
- ❌ They document current implementation
- ❌ They describe future work

---

## Example Status Updates

### Before Implementation

```markdown
### What's Pending

- Parser implementation
- Formatter implementation
- Round-trip tests
```

### After Implementation

```markdown
### What's Working

- ✅ Parser implementation (all pattern types)
- ✅ Formatter with precedence-based parenthesization
- ✅ Round-trip tests
- **238 tests passing**
```

### Key Points

- Be specific about what works
- Include test counts when applicable
- Use checkmarks for visual scanning
- Move items (don't just add new ones)

### Things to inclue

- Current status at the very top
- Overview, goal, and motivation
- Design decisions
- Known issues and tradeoffs
- Alternatives considered with pros and cons
- Open questions
- Implementation details
- Testing strategy
- Future work

### Things to exclude

- Detailed code snippets
- Technical jargon
- Unrelated context

## Quick Reference

| When | Action | Effort |
|------|--------|--------|
| Starting new feature | Add to "What's Pending" | 30 seconds |
| Feature works | Move to "What's Working" | 30 seconds |
| Tests pass | Add/update test count | 10 seconds |
| Finished phase | Update overview status | 2 minutes |
| Creating new plan | Add Status section | 1 minute |

**Total maintenance**: ~5 minutes per feature

---

## See Also

- [Grammar Plans](./grammar/01-overview.md)
- [Core Plans](./core/01-overview.md)
