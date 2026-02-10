---
name: gf-lint
description: >
  SystemVerilog lint checker with structured output for orchestration.
  Runs Verilator lint, categorizes errors/warnings, explains issues,
  and returns a parseable result block for /gf orchestration.
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GF Lint Skill

Lint SystemVerilog files with structured output for orchestration.

## Instructions

### 1. Identify Files to Lint

**If files specified in args:**
Use the provided file paths.

**If no files specified:**
Auto-detect SV files:
```bash
ls *.sv rtl/*.sv 2>/dev/null | head -20
```

### 2. Run Verilator Lint

```bash
verilator --lint-only -Wall <files>
```

### 3. Parse and Categorize Output

Count issues by category:
- **ERRORS**: `%Error:` lines - must be fixed
- **WARNINGS**: `%Warning-*:` lines - should be reviewed

### 4. Explain Common Warnings

For each warning type found, explain:

| Warning | Meaning | Fix |
|---------|---------|-----|
| UNUSED | Signal declared but not used | Remove signal or suppress with `/* verilator lint_off UNUSED */` |
| UNDRIVEN | Signal never assigned a value | Assign the signal or connect it |
| WIDTH | Bit width mismatch in operation | Add explicit sizing: `[7:0]` |
| CASEINCOMPLETE | Case statement missing items | Add `default:` branch |
| LATCH | Inferred latch from incomplete if/case | Add default assignment at start of always_comb |
| BLKSEQ | Blocking assignment in always_ff | Use `<=` (non-blocking) in sequential blocks |
| PINCONNECTEMPTY | Module port left unconnected | Connect or explicitly mark as `.*` |
| IMPLICIT | Implicit wire declaration | Declare with `logic` or `wire` |

### 5. Return Structured Result

**ALWAYS end your response with this exact block format:**

```
---GATEFLOW-RESULT---
STATUS: PASS|FAIL|ERROR
ERRORS: <count>
WARNINGS: <count>
FILES: <comma-separated list>
DETAILS: <one-line summary>
---END-GATEFLOW-RESULT---
```

**Status definitions:**
- `PASS`: No errors, warnings OK (0-N warnings acceptable)
- `FAIL`: One or more errors found
- `ERROR`: Could not run lint (missing files, tool error)

### 6. Example Output

```
Running lint on: rtl/fifo.sv, rtl/uart.sv

$ verilator --lint-only -Wall rtl/fifo.sv rtl/uart.sv

%Warning-UNUSED: rtl/fifo.sv:25: Signal 'debug_flag' is not used
%Warning-WIDTH: rtl/uart.sv:42: Operator ASSIGN expects 8 bits but got 16

## Summary

**Files:** 2 | **Errors:** 0 | **Warnings:** 2

### Warnings Explained

1. **UNUSED** (rtl/fifo.sv:25): `debug_flag` is declared but never read
   - Fix: Remove if unneeded, or suppress with lint pragma

2. **WIDTH** (rtl/uart.sv:42): Assigning 16-bit value to 8-bit signal
   - Fix: Truncate explicitly `data[7:0]` or widen the target

---GATEFLOW-RESULT---
STATUS: PASS
ERRORS: 0
WARNINGS: 2
FILES: rtl/fifo.sv,rtl/uart.sv
DETAILS: Lint passed with 2 warnings
---END-GATEFLOW-RESULT---
```

### 7. Error Case Example

```
$ verilator --lint-only -Wall rtl/broken.sv

%Error: rtl/broken.sv:10: syntax error, unexpected IDENTIFIER

---GATEFLOW-RESULT---
STATUS: FAIL
ERRORS: 1
WARNINGS: 0
FILES: rtl/broken.sv
DETAILS: Syntax error on line 10
---END-GATEFLOW-RESULT---
```

## Usage by /gf Orchestrator

The `/gf` skill uses this skill internally and parses the result block:

```
Parse ---GATEFLOW-RESULT--- block:
- STATUS: PASS -> proceed to next step
- STATUS: FAIL -> spawn sv-refactor agent with error context
- STATUS: ERROR -> report issue to user
```
