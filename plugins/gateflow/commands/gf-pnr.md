---
name: gf-pnr
description: Run place and route
argument-hint: "[--target ice40|ecp5|gowin]"
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Place & Route Command

Run nextpnr place and route for open-source FPGA targets.

## Usage
```
/gf-pnr                          # Use target from project.yaml
/gf-pnr --target ice40           # Explicit target
```

## Requires
- Yosys synthesis output (synth.json)
- Constraint file (.pcf/.lpf/.cst)
- nextpnr installed for target family
