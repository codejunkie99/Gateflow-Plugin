---
name: gf-sim
description: Run sim
argument-hint: "<testbench> [dut-files...]"
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Simulate Command

Compile and run a SystemVerilog simulation using Verilator.

> **Note:** The `/gf` orchestrator uses `skills/gf-sim` internally, which provides
> structured output (GATEFLOW-RESULT blocks) for automated processing. This command
> version is for direct user invocation and provides human-friendly output.

## Instructions

1. **Identify files**:
   - Testbench file (usually `*_tb.sv`)
   - DUT files (modules being tested)
   - If not specified, auto-detect from testbench includes

2. **Compile with Verilator**:
   ```bash
   verilator --binary -Wall <dut-files> <testbench>
   ```

3. **Run simulation**:
   ```bash
   ./obj_dir/V<top_module>
   ```

4. **Check results**:
   - Look for $display output
   - Check for $error or $fatal calls
   - Verify $finish was reached

5. **Report outcome**:
   - PASS: Simulation completed without errors
   - FAIL: Errors detected, show relevant output

## Common Issues

- **Unresolved module**: Missing file in compilation
- **Multiple tops**: Specify --top-module
