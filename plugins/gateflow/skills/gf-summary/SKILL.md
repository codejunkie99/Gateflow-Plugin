---
name: gf-summary
description: Summarize Verilator/lint output in a readable format
user-invocable: true
allowed-tools:
  - Bash
  - Read
---

# GateFlow Summary Skill

Summarizes Verilator lint and simulation output into a clean, readable report.

## Instructions

When invoked, analyze the most recent Verilator output or run a new lint check and present results as:

### Summary Format

```
## Lint Summary: <filename>

| Status | Count |
|--------|-------|
| Errors | X |
| Warnings | X |
| Clean | Yes/No |

### Issues Found

#### Errors
- **Line X**: <error description> - <fix suggestion>

#### Warnings
- **Line X**: <warning description> - <fix suggestion>

### Recommendations
1. <prioritized fix>
2. <next fix>
```

## Trigger Patterns

Activate when user says:
- "summarize lint"
- "lint summary"
- "what's wrong with"
- "show lint results"

## Example

**Input:** Verilator output with WIDTH and UNUSED warnings

**Output:**
```
## Lint Summary: sync_fifo.sv

| Status | Count |
|--------|-------|
| Errors | 0 |
| Warnings | 2 |
| Clean | No |

### Warnings
- **Line 15**: WIDTH - Signal 'count' width mismatch (8 vs 4 bits)
  - Fix: Change `logic [7:0] count` to `logic [3:0] count`

- **Line 32**: UNUSED - Signal 'debug_flag' is never used
  - Fix: Remove the signal or add `/* verilator lint_off UNUSED */`

### Recommendations
1. Fix WIDTH warning first (affects functionality)
2. Clean up UNUSED signals
```

## Usage

```
/gf-summary                    # Summarize last lint output
/gf-summary sync_fifo.sv       # Run lint and summarize for specific file
```

When given a file path, run:
```bash
verilator --lint-only -Wall <file> 2>&1
```

Then parse and present the summary.
