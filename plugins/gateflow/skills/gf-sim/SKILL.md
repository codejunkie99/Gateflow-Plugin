---
name: gf-sim
description: >
  SystemVerilog simulator with structured output for orchestration.
  Auto-detects DUT vs testbench, compiles with Verilator, runs simulation,
  and returns a parseable result block for /gf orchestration.
allowed-tools:
  - Bash
  - Read
  - Glob
  - Grep
---

# GF Sim Skill

Compile and run SystemVerilog simulation with structured output.

## Instructions

### 1. Identify Files

**If files specified in args:**
Use provided paths. First file is typically the testbench.

**If no files specified:**
Auto-detect by scanning for SV files:

```bash
ls *.sv rtl/*.sv tb/*.sv 2>/dev/null
```

### 2. Classify Files: DUT vs Testbench

**Testbench indicators** (has any of):
- `initial begin`
- `$display`, `$monitor`
- `$finish`, `$fatal`
- `$dumpfile`, `$dumpvars`
- Clock generation: `always #N clk = ~clk`
- File in `tb/` directory or named `*_tb.sv`, `tb_*.sv`

**DUT indicators** (has any of):
- `always_ff`, `always_comb`
- Synthesizable constructs only
- No `$` system tasks (except assertions)
- File in `rtl/` directory

**Quick classification:**
```bash
# Files with testbench markers
grep -l '\$display\|\$finish\|initial begin' *.sv 2>/dev/null

# Files with DUT markers
grep -l 'always_ff\|always_comb' *.sv 2>/dev/null
```

### 3. Compile with Verilator

```bash
verilator --binary -j 0 -Wall --trace <dut-files> <testbench> -o sim
```

**Notes:**
- DUT files listed first, testbench last
- `--trace` enables VCD waveform generation
- `-o sim` names the output executable

**If multiple top modules detected:**
```bash
verilator --binary -j 0 -Wall --trace --top-module <tb_name> <files> -o sim
```

### 4. Run Simulation

```bash
./obj_dir/sim
```

Or if named differently:
```bash
./obj_dir/V<top_module>
```

### 5. Parse Results

**Check output for:**
- `PASS`, `SUCCESS`, `All tests passed` -> PASS
- `FAIL`, `ERROR`, `MISMATCH`, `ASSERT` -> FAIL
- `$fatal` or non-zero exit code -> FAIL
- `$finish` reached without errors -> PASS

**Check exit code:**
```bash
./obj_dir/sim
echo "Exit code: $?"
```
- Exit 0: Success
- Non-zero: Failure

### 6. Return Structured Result

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
- `PASS`: Simulation completed, tests passed
- `FAIL`: Simulation failed (compile error, assertion failure, test failure)
- `ERROR`: Could not run simulation (missing files, setup error)

### 7. Example: Successful Run

```
## File Classification

| File | Type | Reason |
|------|------|--------|
| rtl/fifo.sv | DUT | has always_ff, no $display |
| tb/tb_fifo.sv | TB | has $display, $finish, initial |

## Compilation

$ verilator --binary -j 0 -Wall --trace rtl/fifo.sv tb/tb_fifo.sv -o sim

(compilation output...)

## Simulation

$ ./obj_dir/sim

Test 1: Write single item... PASS
Test 2: Fill FIFO... PASS
Test 3: Overflow check... PASS
All tests passed!

---GATEFLOW-RESULT---
STATUS: PASS
ERRORS: 0
WARNINGS: 0
FILES: rtl/fifo.sv,tb/tb_fifo.sv
DETAILS: All 3 tests passed
---END-GATEFLOW-RESULT---
```

### 8. Example: Failed Run

```
## Simulation

$ ./obj_dir/sim

Test 1: Write single item... PASS
Test 2: Read back... FAIL
  Expected: 0xAB
  Got: 0x00
$fatal called at tb_fifo.sv:87

---GATEFLOW-RESULT---
STATUS: FAIL
ERRORS: 1
WARNINGS: 0
FILES: rtl/fifo.sv,tb/tb_fifo.sv
DETAILS: Test 2 failed - read data mismatch at line 87
---END-GATEFLOW-RESULT---
```

### 9. Example: Compile Error

```
$ verilator --binary -j 0 -Wall rtl/fifo.sv tb/tb_fifo.sv -o sim

%Error: rtl/fifo.sv:45: Cannot find: fifo_mem

---GATEFLOW-RESULT---
STATUS: FAIL
ERRORS: 1
WARNINGS: 0
FILES: rtl/fifo.sv,tb/tb_fifo.sv
DETAILS: Compile error - undefined reference to fifo_mem
---END-GATEFLOW-RESULT---
```

## Common Issues and Solutions

| Issue | Symptom | Solution |
|-------|---------|----------|
| Multiple tops | "Multiple top modules" | Add `--top-module <name>` |
| Missing module | "Cannot find: X" | Include file defining X |
| X-values | Output shows X | Check reset coverage |
| Timeout | Simulation hangs | Add timeout or fix FSM |
| No $finish | Runs forever | Ensure TB calls $finish |

## Usage by /gf Orchestrator

The `/gf` skill uses this skill internally and parses the result block:

```
Parse ---GATEFLOW-RESULT--- block:
- STATUS: PASS -> report success, done
- STATUS: FAIL -> spawn sv-debug agent with failure context
- STATUS: ERROR -> report setup issue to user
```
