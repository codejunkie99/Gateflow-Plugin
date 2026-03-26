---
name: gf-detect
description: Scan codebase for missing IP blocks, stubs, and CDC issues
argument-hint: "[--auto-fill] [--cdc-only] [path]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - AskUserQuestion
---

# GateFlow IP Detection Command

Scan your hardware codebase for missing modules, IP opportunities, and CDC violations.

## Usage

```
/gf-detect                    # Full scan of rtl/ directory
/gf-detect --auto-fill        # Scan and auto-fill with user approval
/gf-detect --cdc-only         # Only check for CDC violations
/gf-detect src/               # Scan specific directory
```

## What It Finds

1. **Missing modules** — Instantiated but never defined
2. **Stub modules** — Defined but empty (TODO/FIXME markers)
3. **IP opportunities** — Ad-hoc code that could use verified IP blocks
4. **CDC violations** — Clock domain crossings without synchronizers
5. **Vendor IP** — Vendor primitives that have open-source alternatives

## Output

Shows a report with:
- Module dependency graph
- Missing implementations with suggested IP blocks
- CDC issues ranked by severity
- Auto-fill options (if --auto-fill flag)

## Auto-Fill Mode

With `--auto-fill`, after showing the report:
1. Presents each gap with a suggested action
2. Asks user to approve/skip each one
3. Dispatches agents to implement approved actions
4. Runs lint on all new code
5. Reports final status
