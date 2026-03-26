---
name: gf-pnr
description: >
  Place and route with nextpnr for open-source FPGA targets.
  Supports iCE40, ECP5, and Gowin devices.
  Example: "place and route for iCEBreaker", "run P&R targeting ice40"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
---

# GF-PNR — Place & Route Skill

## Supported Targets

| FPGA Family | Tool | Command |
|------------|------|---------|
| Lattice iCE40 | nextpnr-ice40 | `nextpnr-ice40 --up5k --package sg48 --json synth.json --pcf constraints.pcf --asc output.asc` |
| Lattice ECP5 | nextpnr-ecp5 | `nextpnr-ecp5 --85k --package CABGA381 --json synth.json --lpf constraints.lpf --textcfg output.config` |
| Gowin | nextpnr-gowin | `nextpnr-gowin --device GW1NR-LV9QN88PC6/I5 --json synth.json --cst constraints.cst` |

**NOT Supported**: Xilinx (use Vivado), Intel (use Quartus). For these, GateFlow generates TCL scripts instead.

## Tool Detection

```bash
which nextpnr-ice40 || which nextpnr-ecp5 || which nextpnr-gowin
```

If not found:
```
---GATEFLOW-RESULT---
STATUS: ERROR
DETAILS: nextpnr not installed. Install for place & route.
  macOS: brew install nextpnr
  Linux: see https://github.com/YosysHQ/nextpnr
---END-GATEFLOW-RESULT---
```

## Workflow

1. Check project target (board.yaml → pnr_target)
2. Verify synthesis output exists (synth.json from Yosys)
3. Verify constraint file exists
4. Run nextpnr with correct flags
5. Report timing and utilization
6. Generate bitstream if P&R succeeds

## Bitstream Generation

After P&R:
- iCE40: `icepack output.asc output.bin`
- ECP5: `ecppack output.config output.bit`
- Gowin: built into nextpnr-gowin output

## Result Format

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
TIMING:
  Fmax: 125.3 MHz
  Slack: +2.1 ns
UTILIZATION:
  LUTs: 142 / 5280 (2.7%)
  FFs: 87 / 5280 (1.6%)
FILES: [output files]
DETAILS: [summary or timing violations]
---END-GATEFLOW-RESULT---
```
