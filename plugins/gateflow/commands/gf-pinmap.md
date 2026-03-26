---
name: gf-pinmap
description: Generate pin constraint file for target board
argument-hint: "<board> [peripheral] [connector]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - WebSearch
---

# GateFlow Pin Mapping Command

Generate FPGA constraint files with correct pin assignments.

## Usage

```
/gf-pinmap arty-a7-35t                          # Full constraints for board
/gf-pinmap arty-a7-35t spi pmod-ja              # Map SPI to PMOD JA
/gf-pinmap icebreaker uart                       # Map UART on iCEBreaker
```

## Output

Generates constraint file in correct format:
- Xilinx: `.xdc` with PACKAGE_PIN + IOSTANDARD
- Lattice iCE40: `.pcf` with set_io
- Gowin: `.cst` with IO_LOC
- Lattice ECP5: `.lpf` with LOCATE + IOBUF

Safety: curated database first, web search requires user confirmation.
