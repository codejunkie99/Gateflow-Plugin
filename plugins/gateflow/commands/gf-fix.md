---
name: gf-fix
description: Fix lint
argument-hint: "<file>"
allowed-tools:
  - Bash
  - Read
  - Edit
  - Write
---

# GateFlow Fix Command

Automatically fix lint errors in a SystemVerilog file using iterative lint-fix cycles.

## Instructions

1. **Initial lint**: Run Verilator on the specified file:
   ```bash
   verilator --lint-only -Wall <file> 2>&1
   ```

2. **Parse errors**: Extract all errors and warnings from output

3. **Fix loop** (max 5 iterations):
   - Read the file content
   - For each error, apply the appropriate fix:
     - `UNUSED`: Remove unused signals or add `/* verilator lint_off UNUSED */`
     - `UNDRIVEN`: Initialize the signal or connect it properly
     - `WIDTH`: Adjust bit widths to match
     - `CASEINCOMPLETE`: Add missing case items or default
     - `BLKSEQ`: Change `=` to `<=` in always_ff blocks
   - Use Edit tool to apply fixes
   - Re-run lint to verify

4. **Report results**:
   - Show before/after error counts
   - List all fixes applied
   - Note any remaining issues that need manual review

5. **Safety**: Always show diffs before applying changes. Never auto-approve destructive changes.
