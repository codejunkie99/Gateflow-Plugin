---
name: gf-synth
description: >
  Synthesize SystemVerilog/Verilog with Yosys. Reports area, timing,
  and resource utilization. Warns about unsupported SV constructs.
  Example: "synthesize my design for iCE40"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
---

# GF-Synth — Yosys Synthesis Skill

## Tool Detection

```bash
which yosys
```

If not found:
```
---GATEFLOW-RESULT---
STATUS: ERROR
DETAILS: Yosys not installed. Install to enable synthesis.
  macOS: brew install yosys
  Linux: sudo apt install yosys
---END-GATEFLOW-RESULT---
```

## Pre-Synthesis SV Subset Check

Before synthesis, scan for unsupported constructs:
```bash
grep -rn "^\s*interface\s\|^\s*modport\s\|^\s*class\s\|^\s*bind\s" <files>
```

If found, warn user. Do NOT proceed — it will produce confusing errors.

## Workflow

1. Check project context (`.gateflow/project.yaml`) for target
2. Pre-synthesis lint for unsupported SV constructs
3. Map board to Yosys synth target
4. Run synthesis via sv-synth agent or directly
5. Parse stat output for LUT/FF/BRAM/DSP
6. Report structured result

## Result Format

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
RESOURCES:
  LUTs: N
  FFs: N
  BRAM: N
  DSP: N
TARGET: ice40 | ecp5 | gowin | xilinx | generic
FILES: [synth output files]
DETAILS: [summary or error explanation]
---END-GATEFLOW-RESULT---
```
