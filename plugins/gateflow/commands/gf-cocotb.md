---
name: gf-cocotb
description: Generate Python testbench using Cocotb
argument-hint: "<module> [test-description]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
---

# GateFlow Cocotb Command

Generate Python-based testbenches using Cocotb.

## Usage

```
/gf-cocotb rtl/counter.sv                      # Auto-generate tests
/gf-cocotb rtl/fifo.sv "test full and empty"    # Specific test focus
```

## Output

- `test_<module>.py` — Cocotb test file
- `Makefile` — Cocotb simulation makefile

Requires: `pip install cocotb`
