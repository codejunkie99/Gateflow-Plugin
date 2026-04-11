---
name: gf-project
description: >
  Manages .gateflow/project.yaml for project-specific configuration.
  Auto-detects project settings or prompts user for board, HDL, and target.
  Used internally by other skills — not typically invoked directly.
user-invocable: false
---

# GF Project — Project Context Management

## Project File Location

`.gateflow/project.yaml` in the project root.

## Schema

```yaml
name: my-project
top_module: top
hdl: systemverilog  # systemverilog | verilog | vhdl
target:
  board: null       # arty-a7-35t, icebreaker, etc.
  device: null      # xc7a35ticsg324-1L, ice40hx8k, etc.
  clock_freq: null  # 100MHz, 12MHz, etc.
sources: []         # auto-populated by gf-scan
constraints: null   # path to constraint file
ip_blocks: []       # installed IP block names
```

## Auto-Detection

When this skill is invoked, it:

1. Checks if `.gateflow/project.yaml` exists
2. If not, creates it with defaults by scanning:
   - HDL: check file extensions in project (`.sv` = systemverilog, `.v` = verilog, `.vhd` = vhdl)
   - Sources: glob for `**/*.sv`, `**/*.v`, `**/*.vhd`
   - Top module: find modules not instantiated by others
3. If board is not set and user mentions a board, update it

## Usage by Other Skills

Any skill that needs project context should:

```bash
cat .gateflow/project.yaml 2>/dev/null
```

If the file doesn't exist, invoke this skill to create it.

## Board Memory

When a user mentions a board name in natural language (e.g., "I'm using an Arty A7"),
persist it to `.gateflow/project.yaml` under `target.board`. Do not ask again unless
the user switches boards or starts a new project.

Board memory is per-project, not global. Different projects target different boards.

## GATEFLOW-RESULT Format

```
---GATEFLOW-RESULT---
STATUS: CREATED | UPDATED | VALID | INVALID | ERROR
PROJECT: <name>
FILE: .gateflow/project.yaml
BOARD: <board or null>
HDL: systemverilog | verilog | vhdl
TOP_MODULE: <module>
SOURCES: <count>
DETAILS: <summary>
---END-GATEFLOW-RESULT---
```

## Extended Schema

```yaml
simulation:
  tool: verilator        # verilator | iverilog | vcs
  timeout: 100000        # max cycles
  trace_format: fst      # vcd | fst
  defines: []            # compile-time defines

synthesis:
  tool: yosys            # yosys | vivado | quartus
  target_family: null    # ice40 | ecp5 | gowin | xilinx
  optimization: area     # area | speed | balanced

verification:
  formal_engine: sby
  formal_depth: 50
  coverage_goal: 90
  lint_tool: verilator
```

## Project Templates

### iCE40 FPGA
```yaml
name: my-project
top_module: top
hdl: systemverilog
target: {board: icebreaker, device: ice40up5k-sg48, clock_freq: 12MHz}
simulation: {tool: verilator, trace_format: fst}
synthesis: {tool: yosys, target_family: ice40, optimization: area}
```

### Simulation Only
```yaml
name: sim-project
top_module: top
hdl: systemverilog
target: {board: null}
simulation: {tool: verilator, timeout: 500000, trace_format: fst, defines: [SIMULATION, DEBUG]}
synthesis: {tool: null}
```

## Health Check

| Check | Pass Condition |
|---|---|
| Schema valid | name, top_module, hdl exist |
| Sources exist | All listed files found |
| Top module found | grep for `module <top>` in sources |
| Constraints match target | .xdc for Xilinx, .pcf for iCE40, .lpf for ECP5, .cst for Gowin |
| Tools installed | which <sim_tool>, which <synth_tool> |
