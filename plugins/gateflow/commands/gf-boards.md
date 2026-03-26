---
name: gf-boards
description: List supported boards and query pinouts
argument-hint: "[board-name] [connector]"
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Boards Command

## Usage

```
/gf-boards                        # List all supported boards
/gf-boards arty-a7-35t            # Show board details and pinout
/gf-boards arty-a7-35t pmod-ja    # Show specific connector pins
```

## Execution

1. **No arguments**: List all directories in `${CLAUDE_PLUGIN_ROOT}/boards/`, read each `board.yaml`, display name + FPGA + clock
2. **Board name**: Read `boards/<name>/board.yaml`, display full details including clock, connectors, LEDs, buttons
3. **Board + connector**: Show pin-level detail for that connector with I/O standards

## Output Format

```
Arty A7-35T (Digilent)
  FPGA:    xc7a35ticsg324-1L (Xilinx 7-series)
  Clock:   E3 @ 100MHz (LVCMOS33)
  LEDs:    H5, J5, T9, T10
  Buttons: D9, C9, B9, B8
  PMODs:   JA, JB, JC, JD
  Synth:   synth_xilinx
  Flash:   openFPGALoader -b arty
```
