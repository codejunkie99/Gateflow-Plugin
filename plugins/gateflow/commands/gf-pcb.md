---
name: gf-pcb
description: Generate KiCad schematic and PCB (AI-verified draft)
argument-hint: "[description]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - WebSearch
---

# GateFlow PCB Design Command

Generate KiCad schematics and PCB layouts as AI-verified drafts.

## Usage

```
/gf-pcb "iCE40 breakout with SPI flash and 2 PMODs"
/gf-pcb "sensor board with I2C temperature sensor and OLED"
```

## Output

- `schematic.kicad_sch` — KiCad schematic
- `board.kicad_pcb` — PCB layout (simple boards only)
- `bom.csv` — Bill of materials
- `verification_report.md` — DRC/ERC/AI review results

All files include AI-generated disclaimer. Manual review required.
