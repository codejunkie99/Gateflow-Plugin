---
name: gf-pcb
description: >
  KiCad schematic and PCB generation from natural language.
  AI-verified drafts with DRC/ERC/AI review loop.
  Example: "design a breakout board for iCE40 with SPI flash and 2 PMODs"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - WebSearch
  - WebFetch
---

# GF-PCB — KiCad Schematic & PCB Generation

## Tool Detection

```bash
which kicad-cli
```

If not found:
```
---GATEFLOW-RESULT---
STATUS: ERROR
DETAILS: KiCad not installed. Install for PCB design.
  macOS: brew install --cask kicad
  Linux: sudo apt install kicad
  Download: https://www.kicad.org/download/
---END-GATEFLOW-RESULT---
```

## Workflow

1. **Parse request** — What board? Components? Constraints?
2. **Web search** — Reference designs, datasheets, footprints
3. **Spawn pcb-designer agent** — Generate schematic + PCB
4. **Run verification loop**:
   a. KiCad DRC (Design Rule Check)
   b. KiCad ERC (Electrical Rule Check)
   c. AI Review (power, decoupling, floating pins, voltages)
   d. If errors → fix and re-verify (max 3 iterations)
5. **Label output** with verification status and confidence
6. **Deliver** with mandatory disclaimer

## Output Files

```
project/
├── schematic.kicad_sch     # Schematic (S-expression)
├── board.kicad_pcb         # PCB layout
├── bom.csv                 # Bill of materials
└── verification_report.md  # DRC/ERC/AI review results
```

## Result Format

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
CONFIDENCE: high | medium | low
VERIFICATION:
  DRC: PASS/FAIL (N errors, M warnings)
  ERC: PASS/FAIL (N errors, M warnings)
  AI_REVIEW: PASS/FAIL (N/M checks passed)
FILES: [generated files]
DETAILS: [summary]
---END-GATEFLOW-RESULT---
```
