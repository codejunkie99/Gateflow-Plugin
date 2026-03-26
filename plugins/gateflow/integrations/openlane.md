# OpenLane Integration — ASIC Tapeout

OpenLane is the complete RTL-to-GDSII flow for free chip fabrication
via Efabless. Enables "natural language → verified RTL → silicon."

## What This Enables

- ASIC tapeout targeting SKY130 (SkyWater 130nm) and GF180 (GlobalFoundries 180nm)
- Full flow: RTL → synthesis → floorplan → placement → routing → signoff → GDSII
- Free fabrication through Efabless shuttle runs

## The Ultimate Demo

"I described a chip in English and taped it out for free."

## Setup

```bash
# Install OpenLane
pip install openlane
# Or Docker: docker pull efabless/openlane2

# Install PDK
volare enable --pdk sky130 <version>
```

## Usage with GateFlow (Future)

```
/gf-tapeout rtl/top.sv --pdk sky130 --die-area "0 0 500 500"
```

## Status: Phase 5+ (Future)

This integration requires:
- OpenLane expertise and careful validation
- PDK-specific design rules
- Timing closure at ASIC scale
- Extensive DRC/LVS verification
