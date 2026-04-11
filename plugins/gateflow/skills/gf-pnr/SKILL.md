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
  - AskUserQuestion
---

# GF-PNR -- Place & Route Skill

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

1. Check project target (board.yaml -> pnr_target)
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

## Common Flags

| Flag | Purpose |
|---|---|
| `--freq <mhz>` | Target frequency |
| `--seed <n>` / `-r` | RNG seed / randomize |
| `--opt-timing` | Post-placement timing opt |
| `--report <file>` | JSON timing/utilization |
| `--timing-allow-fail` | Proceed despite violations |
| `--router2-heatmap <prefix>` | Congestion heatmaps |
| `--placer heap` | Heap placer (default) |

## Target Details

### iCE40
Devices: `--lp1k`, `--lp8k`, `--hx1k`, `--hx8k`, `--up5k`
Output: `--asc <file>` | Constraints: `--pcf <file>`
Full pipeline: `yosys -p "synth_ice40 -json out.json" design.v && nextpnr-ice40 --hx8k --package ct256 --json out.json --pcf pins.pcf --asc out.asc && icepack out.asc out.bin`

### ECP5
Devices: `--12k`, `--25k`, `--45k`, `--85k`
Output: `--textcfg <file>` | Constraints: `--lpf <file>`, `--sdc <file>`
Full pipeline: `yosys -p "synth_ecp5 -json out.json" design.v && nextpnr-ecp5 --25k --package CABGA256 --json out.json --lpf pins.lpf --textcfg out.config && ecppack out.config out.bit`

### Gowin
Device: `--device <part>` (e.g., `GW1NR-LV9QN88PC6/I5`)
Family: `--vopt family=<fam>` (for C-silicon, e.g., `GW1N-9C`)
Constraints: `--vopt cst=<file>` (mandatory)
Full pipeline: `yosys -p "synth_gowin -json out.json" design.v && nextpnr-himbaechel --device GW1NR-LV9QN88PC6/I5 --vopt family=GW1N-9C --vopt cst=pins.cst --json out.json --write routed.json && gowin_pack -d GW1N-9C -o out.fs routed.json`

## Timing Analysis

### Fmax
- Maximum frequency from worst-case critical path
- Use `--freq 0` for auto-determine, `--freq N` for target

### Slack
- Positive = timing met | Negative = violation | Zero = exact
- Critical path = path with worst slack

### Improving Fmax
1. Pipeline long combinational paths
2. `--opt-timing` for post-placement optimization
3. Different seeds (`-r`) for better placement
4. Increase `--placer-heap-timingweight` (20-50)
5. `--router2-tmg-ripup` for timing-driven rerouting
6. Yosys: `-nowidelut` for ECP5 (big Fmax improvement)

## Utilization Thresholds

| Usage | Status |
|---|---|
| < 50% | Comfortable |
| 50-70% | Normal |
| 70-80% | Tight |
| > 80% | Warning: congestion likely |
| > 95% | May fail to route |

## Common Failures

| Failure | Fix |
|---|---|
| Routing congestion | Larger device, optimize synth, different seed |
| Timing violations | Pipeline, `--opt-timing`, different seed |
| Placement failure | Check constraints, try `--placer sa` |
| Combinatorial loops | Break with register, or `--ignore-loops` |

## Constraint Formats

### PCF (iCE40)
```
set_io clk 21
set_io led[0] 99
set_frequency clk 48
```

### LPF (ECP5)
```
LOCATE COMP "clk" SITE "P6";
IOBUF PORT "clk" IO_TYPE=LVCMOS33;
FREQUENCY PORT "clk" 48000000.0 HZ;
```

### CST (Gowin)
```
IO_LOC "clk" 52;
IO_PORT "clk" IO_TYPE=LVCMOS33;
```
