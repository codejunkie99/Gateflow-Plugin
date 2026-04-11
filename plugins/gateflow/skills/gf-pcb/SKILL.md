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

## KiCad CLI Quick Reference

```bash
# DRC
kicad-cli pcb drc --format json --severity-all --exit-code-violations --output drc.json board.kicad_pcb

# ERC
kicad-cli sch erc --format json --severity-all --exit-code-violations --output erc.json design.kicad_sch

# BOM
kicad-cli sch export bom --fields "Reference,Value,Footprint,${QUANTITY},Manufacturer,MPN" \
  --group-by "Value,Footprint" --exclude-dnp --output bom.csv design.kicad_sch

# Gerbers + Drill
kicad-cli pcb export gerbers --output gerbers/ board.kicad_pcb
kicad-cli pcb export drill --output gerbers/ --format excellon board.kicad_pcb

# 3D Model
kicad-cli pcb export step --output board.step board.kicad_pcb
```

Exit codes: 0 = clean, 5 = violations found.

## DRC/ERC Interpretation

### Common DRC Errors
| Error | Meaning | Fix |
|---|---|---|
| clearance_violation | Items too close | Increase spacing |
| shorting_items | Different nets touching | Reroute traces |
| courtyards_overlap | Components too close | Move apart |
| track_width | Outside allowed range | Adjust width |
| annular_width | Via ring too small | Increase via size |
| copper_sliver | Thin copper (mfg risk) | Adjust pour |
| hole_near_hole | Drilled holes too close | Increase spacing |

### Common ERC Errors
| Error | Fix |
|---|---|
| Input power pin not driven | Add PWR_FLAG |
| Pin not connected | Connect or add no-connect X |
| Conflicting pin types | Check symbol pin types |
| Duplicate reference | Re-annotate schematic |

## AI Review Checklist

### Decoupling
- [ ] Every IC: 100nF cap within 5mm of power pins
- [ ] Bulk caps near power entry
- [ ] Current path: Supply -> Cap -> IC pin

### Power
- [ ] Continuous ground plane
- [ ] No signal traces cutting ground under high-speed signals
- [ ] Adequate copper weight for current

### High-Speed
- [ ] Controlled impedance for >50MHz signals
- [ ] Length matching for differential pairs
- [ ] Via stitching along high-speed paths

### Thermal
- [ ] Thermal vias under exposed pads (min 4-9)
- [ ] Heat sources away from temp-sensitive components

### Manufacturing
- [ ] Board outline closed on Edge.Cuts
- [ ] Min trace >= 0.1mm, min drill >= 0.2mm
- [ ] Silkscreen not over pads
- [ ] Fiducials present (min 3)

## Confidence Scoring

| Level | Criteria | DRC Expectation |
|---|---|---|
| HIGH | <50 components, 2-layer, <10MHz | Zero violations |
| MEDIUM | 50-200 components, 2-4 layer, <100MHz | May need adjustments |
| LOW | >200 components, 4+ layers, high-speed/RF/power | Expert review required |

Override to LOW if: RF/antenna, DDR/PCIe/USB3+, SMPS >5W, BGA >100 pins.

## Manufacturing Package Script

```bash
mkdir -p output/{gerbers,assembly,docs}
kicad-cli pcb export gerbers --output output/gerbers/ board.kicad_pcb
kicad-cli pcb export drill --output output/gerbers/ --format excellon board.kicad_pcb
kicad-cli pcb export pos --format csv --output output/assembly/positions.csv board.kicad_pcb
kicad-cli sch export bom --exclude-dnp --output output/assembly/bom.csv design.kicad_sch
kicad-cli sch export pdf --output output/docs/schematic.pdf design.kicad_sch
kicad-cli pcb export step --output output/docs/board.step board.kicad_pcb
```
