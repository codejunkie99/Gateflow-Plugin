# KiCad CLI Reference

## PCB Export Commands

### Gerbers
```bash
kicad-cli pcb export gerbers \
  --output gerbers/ \
  --layers "F.Cu,B.Cu,F.SilkS,B.SilkS,F.Mask,B.Mask,Edge.Cuts,F.Paste,B.Paste" \
  --subtract-soldermask \
  board.kicad_pcb
```

### Drill Files
```bash
# Excellon format (most common)
kicad-cli pcb export drill \
  --output gerbers/ \
  --format excellon \
  --excellon-units mm \
  --generate-map --map-format gerber \
  board.kicad_pcb
```

### Pick and Place (Component Position)
```bash
kicad-cli pcb export pos \
  --output board-pos.csv \
  --format csv \
  --units mm \
  --side both \
  board.kicad_pcb
```

### 3D Model (STEP)
```bash
kicad-cli pcb export step \
  --output board.step \
  --subst-models \
  board.kicad_pcb
```

### SVG
```bash
kicad-cli pcb export svg \
  --output board.svg \
  --layers "F.Cu,B.Cu,Edge.Cuts" \
  --page-size-mode 2 \
  board.kicad_pcb
```

### PDF
```bash
kicad-cli pcb export pdf \
  --output board.pdf \
  --layers "F.Cu,B.Cu,F.SilkS,Edge.Cuts" \
  board.kicad_pcb
```

### DXF
```bash
kicad-cli pcb export dxf \
  --output board.dxf \
  --layers "Edge.Cuts" \
  board.kicad_pcb
```

### VRML (3D)
```bash
kicad-cli pcb export vrml \
  --output board.wrl \
  board.kicad_pcb
```

## Schematic Export Commands

### BOM
```bash
kicad-cli sch export bom \
  --fields "Reference,Value,Footprint,\${QUANTITY},Manufacturer,MPN" \
  --group-by "Value,Footprint" \
  --exclude-dnp \
  --output bom.csv \
  design.kicad_sch
```

### Netlist
```bash
kicad-cli sch export netlist \
  --output design.net \
  --format kicadxml \
  design.kicad_sch
```

### Schematic PDF
```bash
kicad-cli sch export pdf \
  --output schematic.pdf \
  design.kicad_sch
```

### Schematic SVG
```bash
kicad-cli sch export svg \
  --output schematic-svg/ \
  design.kicad_sch
```

## DRC / ERC Commands

### DRC
```bash
kicad-cli pcb drc \
  --format json \
  --severity-all \
  --exit-code-violations \
  --output drc.json \
  board.kicad_pcb
```

### ERC
```bash
kicad-cli sch erc \
  --format json \
  --severity-all \
  --exit-code-violations \
  --output erc.json \
  design.kicad_sch
```

Exit codes: 0 = clean, 5 = violations found.

## DRC JSON Report Format

```json
{
  "source": "board.kicad_pcb",
  "date": "2024-01-15T10:30:00",
  "kicad_version": "8.0.0",
  "violations": [
    {
      "type": "clearance_violation",
      "severity": "error",
      "description": "Clearance violation (0.15mm < 0.2mm)",
      "items": [
        {
          "type": "track",
          "description": "Track on F.Cu",
          "net": "VCC",
          "pos": { "x": 100.0, "y": 50.0 }
        },
        {
          "type": "track",
          "description": "Track on F.Cu",
          "net": "GND",
          "pos": { "x": 100.15, "y": 50.0 }
        }
      ]
    }
  ],
  "unconnected_items": [],
  "schematic_parity": []
}
```

### Full DRC Violation Types

| Type | Severity | Description |
|---|---|---|
| clearance_violation | error | Items closer than design rule minimum |
| shorting_items | error | Different nets electrically touching |
| tracks_crossing | error | Tracks on same layer crossing |
| unconnected_items | error | Pads in same net not routed |
| courtyards_overlap | error | Component courtyards intersecting |
| missing_courtyard | warning | Footprint has no courtyard |
| track_width | error | Track width outside allowed range |
| annular_width | error | Via annular ring below minimum |
| drill_too_small | error | Drill diameter below fab minimum |
| via_diameter | error | Via outer diameter out of range |
| copper_sliver | warning | Thin copper area (manufacturing risk) |
| starved_thermal | warning | Thermal relief with insufficient spokes |
| pad_near_pad | error | Pads from different nets too close |
| hole_near_hole | error | Drill holes too close together |
| zone_has_empty_net | warning | Copper zone assigned to empty net |
| isolated_copper | warning | Copper island not connected to any net |
| silk_over_pads | warning | Silkscreen overlapping SMD pads |
| text_height | warning | Text smaller than fab minimum |
| board_edge_clearance | error | Copper too close to board edge |
| footprint_type_mismatch | warning | SMD footprint on wrong side |
| extra_footprint | error | Footprint not in schematic |
| missing_footprint | error | Schematic symbol missing from board |
| net_conflict | error | Net assignment mismatch board vs schematic |

## Minimal .kicad_sch Template

```lisp
(kicad_sch
  (version 20231120)
  (generator "gateflow")
  (uuid "00000000-0000-0000-0000-000000000001")
  (paper "A4")

  (lib_symbols
    ;; Symbol definitions go here
    (symbol "Device:R"
      (pin_numbers hide)
      (pin_names (offset 0) hide)
      (exclude_from_sim no)
      (in_bom yes)
      (on_board yes)
      (property "Reference" "R" (at 2.032 0 90) (effects (font (size 1.27 1.27))))
      (property "Value" "R" (at -2.032 0 90) (effects (font (size 1.27 1.27))))
      (property "Footprint" "" (at -1.778 0 90) (effects (font (size 1.27 1.27)) hide))
      (symbol "R_0_1"
        (rectangle (start -1.016 -2.54) (end 1.016 2.54)
          (stroke (width 0.254) (type default))
          (fill (type none))))
      (symbol "R_1_1"
        (pin passive line (at 0 3.81 270) (length 1.27) (name "~" (effects (font (size 1.27 1.27)))) (number "1" (effects (font (size 1.27 1.27)))))
        (pin passive line (at 0 -3.81 90) (length 1.27) (name "~" (effects (font (size 1.27 1.27)))) (number "2" (effects (font (size 1.27 1.27)))))))
  )

  ;; Global labels, power symbols
  (power_port "VCC" (at 100 20 0)
    (effects (font (size 1.27 1.27)))
    (uuid "00000000-0000-0000-0000-000000000010")
    (property "Reference" "#PWR01" (at 100 24 0) (effects (font (size 1.27 1.27)) hide))
    (property "Value" "VCC" (at 100 16 0) (effects (font (size 1.27 1.27)))))

  ;; Component instances
  (symbol
    (lib_id "Device:R")
    (at 120 40 0)
    (uuid "00000000-0000-0000-0000-000000000020")
    (property "Reference" "R1" (at 122 40 0) (effects (font (size 1.27 1.27))))
    (property "Value" "10k" (at 118 40 0) (effects (font (size 1.27 1.27))))
    (property "Footprint" "Resistor_SMD:R_0402_1005Metric" (at 120 40 0) (effects (font (size 1.27 1.27)) hide))
    (pin "1" (uuid "00000000-0000-0000-0000-000000000021"))
    (pin "2" (uuid "00000000-0000-0000-0000-000000000022")))

  ;; Wires
  (wire (pts (xy 100 20) (xy 120 20))
    (stroke (width 0) (type default))
    (uuid "00000000-0000-0000-0000-000000000030"))
)
```

## Minimal .kicad_pcb Template

```lisp
(kicad_pcb
  (version 20240108)
  (generator "gateflow")
  (general
    (thickness 1.6)
    (legacy_teardrops no))

  (paper "A4")

  (layers
    (0 "F.Cu" signal)
    (31 "B.Cu" signal)
    (32 "B.Adhes" user "B.Adhesive")
    (33 "F.Adhes" user "F.Adhesive")
    (34 "B.Paste" user)
    (35 "F.Paste" user)
    (36 "B.SilkS" user "B.Silkscreen")
    (37 "F.SilkS" user "F.Silkscreen")
    (38 "B.Mask" user "B.Mask")
    (39 "F.Mask" user "F.Mask")
    (44 "Edge.Cuts" user)
    (45 "Margin" user)
    (46 "B.CrtYd" user "B.Courtyard")
    (47 "F.CrtYd" user "F.Courtyard")
    (48 "B.Fab" user "B.Fabrication")
    (49 "F.Fab" user "F.Fabrication"))

  (setup
    (pad_to_mask_clearance 0)
    (allow_soldermask_bridges_in_footprints no)
    (pcbplotparams
      (layerselection 0x00010fc_ffffffff)
      (plot_on_all_layers_selection 0x0000000_00000000)
      (disableapertmacros no)
      (usegerberextensions yes)
      (usegerberattributes yes)
      (usegerberadvancedattributes yes)
      (creategerberjobfile yes)
      (svgprecision 4)
      (plotframeref no)
      (viasonmask no)
      (mode 1)
      (useauxorigin no)
      (hpglpennumber 1)
      (hpglpenspeed 20)
      (hpglpendiameter 15.000000)
      (pdf_front_fp_property_popups yes)
      (pdf_back_fp_property_popups yes)
      (dxfpolygonmode yes)
      (dxfimperialunits yes)
      (dxfusepcbnewfonts yes)
      (psnegative no)
      (psa4output no)
      (plotreference yes)
      (plotvalue yes)
      (plotfptext yes)
      (plotinvisibletext no)
      (sketchpadsonfab no)
      (subtractmaskfromsilk yes)
      (outputformat 1)
      (mirror no)
      (drillshape 1)
      (scaleselection 1)
      (outputdirectory "")))

  ;; Design rules
  (net 0 "")
  (net 1 "GND")
  (net 2 "VCC")

  ;; Board outline
  (gr_rect (start 90 30) (end 160 100)
    (stroke (width 0.1) (type default))
    (fill none)
    (layer "Edge.Cuts")
    (uuid "00000000-0000-0000-0000-000000000100"))

  ;; Footprint example (0402 resistor)
  (footprint "Resistor_SMD:R_0402_1005Metric"
    (layer "F.Cu")
    (uuid "00000000-0000-0000-0000-000000000200")
    (at 120 60)
    (property "Reference" "R1" (at 0 -1.5 0) (layer "F.SilkS") (uuid "00000000-0000-0000-0000-000000000201") (effects (font (size 1 1) (thickness 0.15))))
    (property "Value" "10k" (at 0 1.5 0) (layer "F.Fab") (uuid "00000000-0000-0000-0000-000000000202") (effects (font (size 1 1) (thickness 0.15))))
    (pad "1" smd roundrect
      (at -0.51 0)
      (size 0.54 0.64)
      (layers "F.Cu" "F.Paste" "F.Mask")
      (roundrect_rratio 0.25)
      (net 2 "VCC")
      (uuid "00000000-0000-0000-0000-000000000210"))
    (pad "2" smd roundrect
      (at 0.51 0)
      (size 0.54 0.64)
      (layers "F.Cu" "F.Paste" "F.Mask")
      (roundrect_rratio 0.25)
      (net 1 "GND")
      (uuid "00000000-0000-0000-0000-000000000211")))

  ;; Track example
  (segment
    (start 120.51 60) (end 140 60)
    (width 0.25) (layer "F.Cu") (net 1)
    (uuid "00000000-0000-0000-0000-000000000300"))

  ;; Via example
  (via
    (at 140 60)
    (size 0.6) (drill 0.3)
    (layers "F.Cu" "B.Cu") (net 1)
    (uuid "00000000-0000-0000-0000-000000000400"))

  ;; Copper zone (ground pour)
  (zone
    (net 1) (net_name "GND")
    (layer "B.Cu")
    (uuid "00000000-0000-0000-0000-000000000500")
    (hatch edge 0.5)
    (connect_pads (clearance 0.2))
    (min_thickness 0.2)
    (fill yes (thermal_gap 0.3) (thermal_bridge_width 0.3))
    (polygon (pts
      (xy 90 30) (xy 160 30) (xy 160 100) (xy 90 100))))
)
```

## Key S-Expression Primitives

| Primitive | Usage | Example |
|---|---|---|
| `(footprint ...)` | Component on PCB | `(footprint "Package_SO:SOIC-8" (layer "F.Cu") (at 100 50) ...)` |
| `(pad ...)` | Copper pad | `(pad "1" smd roundrect (at 0 0) (size 1.0 1.2) (layers "F.Cu" "F.Paste" "F.Mask") (net 1 "VCC"))` |
| `(segment ...)` | Copper trace | `(segment (start 100 50) (end 120 50) (width 0.25) (layer "F.Cu") (net 1))` |
| `(via ...)` | Through-hole via | `(via (at 110 50) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 1))` |
| `(zone ...)` | Copper pour | `(zone (net 1) (net_name "GND") (layer "F.Cu") ...)` |
| `(gr_line ...)` | Board edge / graphic | `(gr_line (start 90 30) (end 160 30) (stroke (width 0.1)) (layer "Edge.Cuts"))` |
| `(gr_rect ...)` | Rectangle graphic | `(gr_rect (start 90 30) (end 160 100) (layer "Edge.Cuts"))` |
| `(gr_circle ...)` | Circle graphic | `(gr_circle (center 100 50) (end 105 50) (layer "Edge.Cuts"))` |
| `(symbol ...)` | Component in schematic | `(symbol (lib_id "Device:C") (at 100 50 0) ...)` |
| `(wire ...)` | Schematic wire | `(wire (pts (xy 100 50) (xy 120 50)))` |
| `(label ...)` | Net label | `(label "SDA" (at 100 50 0))` |
| `(global_label ...)` | Global net label | `(global_label "VCC" (at 100 20 0) (shape input))` |

## Manufacturing Package Script

```bash
#!/bin/bash
# generate-manufacturing-package.sh
# Generates a complete manufacturing package from KiCad project files

set -euo pipefail

PROJECT_DIR="${1:-.}"
OUTPUT_DIR="${PROJECT_DIR}/manufacturing"
BOARD="${PROJECT_DIR}/board.kicad_pcb"
SCHEMATIC="${PROJECT_DIR}/schematic.kicad_sch"

if [ ! -f "$BOARD" ]; then
    echo "ERROR: board.kicad_pcb not found in ${PROJECT_DIR}"
    exit 1
fi

mkdir -p "${OUTPUT_DIR}/gerbers"
mkdir -p "${OUTPUT_DIR}/assembly"
mkdir -p "${OUTPUT_DIR}/docs"

echo "=== Generating Manufacturing Package ==="

# Gerbers
echo "[1/7] Exporting Gerbers..."
kicad-cli pcb export gerbers \
  --output "${OUTPUT_DIR}/gerbers/" \
  --layers "F.Cu,B.Cu,F.SilkS,B.SilkS,F.Mask,B.Mask,Edge.Cuts,F.Paste,B.Paste" \
  --subtract-soldermask \
  "$BOARD"

# Drill files
echo "[2/7] Exporting Drill files..."
kicad-cli pcb export drill \
  --output "${OUTPUT_DIR}/gerbers/" \
  --format excellon \
  --excellon-units mm \
  --generate-map --map-format gerber \
  "$BOARD"

# Pick and place
echo "[3/7] Exporting Pick & Place..."
kicad-cli pcb export pos \
  --output "${OUTPUT_DIR}/assembly/board-pos.csv" \
  --format csv \
  --units mm \
  --side both \
  "$BOARD"

# BOM
if [ -f "$SCHEMATIC" ]; then
    echo "[4/7] Exporting BOM..."
    kicad-cli sch export bom \
      --fields "Reference,Value,Footprint,\${QUANTITY},Manufacturer,MPN" \
      --group-by "Value,Footprint" \
      --exclude-dnp \
      --output "${OUTPUT_DIR}/assembly/bom.csv" \
      "$SCHEMATIC"

    echo "[5/7] Exporting Schematic PDF..."
    kicad-cli sch export pdf \
      --output "${OUTPUT_DIR}/docs/schematic.pdf" \
      "$SCHEMATIC"
else
    echo "[4/7] SKIP: No schematic found"
    echo "[5/7] SKIP: No schematic found"
fi

# Board PDF
echo "[6/7] Exporting Board PDF..."
kicad-cli pcb export pdf \
  --output "${OUTPUT_DIR}/docs/board-layout.pdf" \
  --layers "F.Cu,B.Cu,F.SilkS,B.SilkS,Edge.Cuts" \
  "$BOARD"

# 3D model
echo "[7/7] Exporting 3D model..."
kicad-cli pcb export step \
  --output "${OUTPUT_DIR}/docs/board.step" \
  --subst-models \
  "$BOARD" 2>/dev/null || echo "  WARN: STEP export failed (missing 3D models?)"

# Create zip for fab house
echo "=== Creating Gerber archive ==="
(cd "${OUTPUT_DIR}/gerbers" && zip -q ../gerbers.zip ./*.* 2>/dev/null) || echo "  WARN: zip not available"

echo ""
echo "=== Manufacturing Package Complete ==="
echo "Output: ${OUTPUT_DIR}/"
echo "  gerbers/       - Gerber + drill files (send to fab)"
echo "  gerbers.zip    - Zipped gerbers for upload"
echo "  assembly/      - BOM + pick-and-place (send to assembler)"
echo "  docs/          - Schematic PDF, board PDF, 3D model"
```

## CI/CD Validation Pipeline Script

```bash
#!/bin/bash
# validate-kicad.sh
# CI/CD validation pipeline for KiCad projects
# Exit code: 0 = all checks pass, 1 = failures found

set -euo pipefail

PROJECT_DIR="${1:-.}"
BOARD="${PROJECT_DIR}/board.kicad_pcb"
SCHEMATIC="${PROJECT_DIR}/schematic.kicad_sch"
REPORT_DIR="${PROJECT_DIR}/reports"
FAILURES=0

mkdir -p "$REPORT_DIR"

echo "=== KiCad CI Validation ==="
echo "Project: ${PROJECT_DIR}"
echo ""

# Check files exist
if [ ! -f "$BOARD" ]; then
    echo "FAIL: board.kicad_pcb not found"
    exit 1
fi

# DRC
echo "[1/4] Running DRC..."
if kicad-cli pcb drc \
    --format json \
    --severity-all \
    --exit-code-violations \
    --output "${REPORT_DIR}/drc.json" \
    "$BOARD" 2>/dev/null; then
    echo "  PASS: DRC clean"
else
    DRC_EXIT=$?
    if [ "$DRC_EXIT" -eq 5 ]; then
        ERRORS=$(python3 -c "
import json, sys
with open('${REPORT_DIR}/drc.json') as f:
    d = json.load(f)
errors = [v for v in d.get('violations', []) if v.get('severity') == 'error']
warnings = [v for v in d.get('violations', []) if v.get('severity') == 'warning']
print(f'{len(errors)} errors, {len(warnings)} warnings')
" 2>/dev/null || echo "unknown count")
        echo "  FAIL: DRC violations (${ERRORS})"
        FAILURES=$((FAILURES + 1))
    else
        echo "  ERROR: DRC crashed (exit ${DRC_EXIT})"
        FAILURES=$((FAILURES + 1))
    fi
fi

# ERC
if [ -f "$SCHEMATIC" ]; then
    echo "[2/4] Running ERC..."
    if kicad-cli sch erc \
        --format json \
        --severity-all \
        --exit-code-violations \
        --output "${REPORT_DIR}/erc.json" \
        "$SCHEMATIC" 2>/dev/null; then
        echo "  PASS: ERC clean"
    else
        ERC_EXIT=$?
        if [ "$ERC_EXIT" -eq 5 ]; then
            echo "  FAIL: ERC violations found"
            FAILURES=$((FAILURES + 1))
        else
            echo "  ERROR: ERC crashed (exit ${ERC_EXIT})"
            FAILURES=$((FAILURES + 1))
        fi
    fi
else
    echo "[2/4] SKIP: No schematic found"
fi

# BOM validation
if [ -f "$SCHEMATIC" ]; then
    echo "[3/4] Validating BOM..."
    kicad-cli sch export bom \
      --fields "Reference,Value,Footprint" \
      --output "${REPORT_DIR}/bom-check.csv" \
      "$SCHEMATIC" 2>/dev/null
    if [ -f "${REPORT_DIR}/bom-check.csv" ]; then
        EMPTY_FP=$(awk -F',' 'NR>1 && $3=="" {count++} END {print count+0}' "${REPORT_DIR}/bom-check.csv")
        if [ "$EMPTY_FP" -gt 0 ]; then
            echo "  WARN: ${EMPTY_FP} components missing footprints"
        else
            echo "  PASS: All components have footprints"
        fi
    fi
else
    echo "[3/4] SKIP: No schematic found"
fi

# Board edge check
echo "[4/4] Checking board outline..."
if grep -q "Edge.Cuts" "$BOARD"; then
    echo "  PASS: Edge.Cuts layer present"
else
    echo "  FAIL: No board outline on Edge.Cuts"
    FAILURES=$((FAILURES + 1))
fi

echo ""
echo "=== Results ==="
if [ "$FAILURES" -eq 0 ]; then
    echo "ALL CHECKS PASSED"
    exit 0
else
    echo "${FAILURES} CHECK(S) FAILED"
    echo "Reports: ${REPORT_DIR}/"
    exit 1
fi
```
