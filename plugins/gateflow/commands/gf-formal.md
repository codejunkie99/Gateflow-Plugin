---
name: gf-formal
description: Run formal verification
argument-hint: "[files...] [--property 'description']"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
---

# GateFlow Formal Verification Command

## Usage

```
/gf-formal rtl/fifo.sv                            # Auto-generate and prove properties
/gf-formal rtl/fifo.sv --property "never overflows"  # Prove specific property
/gf-formal formal/fifo.sby                          # Run existing .sby config
```

## Execution

1. If argument is `.sby` file: run directly with `sby -f <file>.sby`
2. If argument is `.sv` file:
   a. Read the module
   b. Generate SVA properties (or use --property hint)
   c. Create `.sby` configuration
   d. Run SymbiYosys
   e. Report with 3-layer error translation
3. If no arguments: find `.sby` configs in `formal/` and run all
