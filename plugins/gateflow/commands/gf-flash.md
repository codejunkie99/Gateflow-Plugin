---
name: gf-flash
description: Flash bitstream to FPGA board
argument-hint: "[bitstream-file]"
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Flash Command

Program an FPGA board using openFPGALoader.

## Usage
```
/gf-flash                        # Auto-detect board and bitstream
/gf-flash output.bin             # Flash specific file
/gf-flash --board arty output.bit  # Specify board
```

## Execution

1. Check for openFPGALoader: `which openFPGALoader`
2. Read board from `.gateflow/project.yaml` or argument
3. Find bitstream file (.bin, .bit, .config)
4. Flash: `openFPGALoader -b <board> <bitstream>`

## Tool Detection

If openFPGALoader not installed:
```
openFPGALoader not found. Install to flash FPGA boards.
  macOS: brew install openfpgaloader
  Linux: see https://github.com/trabucayre/openFPGALoader
```
