---
name: gf-lint
description: Run lint
argument-hint: "[files...]"
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Lint Command

Run Verilator lint checks to find errors and warnings in SystemVerilog code.

> **Note:** The `/gf` orchestrator uses `skills/gf-lint` internally, which provides
> structured output (GATEFLOW-RESULT blocks) for automated processing. This command
> version is for direct user invocation and provides human-friendly output.

## Instructions

1. If specific files are provided, lint those files:
   ```bash
   verilator --lint-only -Wall <files>
   ```

2. If no files specified, find and lint all SV files:
   ```bash
   verilator --lint-only -Wall *.sv
   ```

3. Parse the output and categorize issues:
   - **Errors**: Must be fixed before simulation
   - **Warnings**: Should be reviewed and addressed
   - **Style**: Optional improvements

4. For each issue found:
   - Show the file and line number
   - Explain what the error means
   - Suggest how to fix it

5. Common Verilator warnings to explain:
   - `UNUSED`: Unused signal or variable
   - `UNDRIVEN`: Signal never assigned
   - `WIDTH`: Bit width mismatch
   - `CASEINCOMPLETE`: Missing case items
   - `BLKSEQ`: Blocking assignment in sequential block
