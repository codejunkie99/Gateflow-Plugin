---
name: gf-fusesoc
description: >
  FuseSoC build system integration. Generates .core files and drives
  synthesis/simulation through Edalize backends (Vivado, Quartus, open-source).
  Example: "create a FuseSoC core file", "build with Edalize"
user-invocable: true
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - AskUserQuestion
---

# GF-FuseSoC -- Build System Integration

Generate FuseSoC .core files and drive builds through Edalize backends.

## .core File Template

```yaml
CAPI=2:
name: ::my_project:1.0.0
filesets:
  rtl:
    files: [rtl/top.sv, rtl/fifo.sv]
    file_type: systemVerilogSource
  tb:
    files: [tb/tb_top.sv]
    file_type: systemVerilogSource
  constraints:
    files:
      - constraints/arty_a7.xdc: {file_type: xdc}
targets:
  sim:
    filesets: [rtl, tb]
    toplevel: tb_top
    default_tool: verilator
  synth:
    filesets: [rtl, constraints]
    toplevel: top
    default_tool: vivado
    tools:
      vivado:
        part: xc7a35ticsg324-1L
```

## Complete .core Schema

```yaml
CAPI=2
name: vendor:library:name:version    # VLNV identifier (required)
description: "Brief description"

filesets:
  rtl:
    file_type: systemVerilogSource
    files:
      - rtl/top.sv
      - rtl/core.sv
    depend:
      - ">=vendor:lib:dep:1.0"
  tb:
    files: [tb/tb_top.sv]
    file_type: systemVerilogSource
  constraints_ice40:
    files: [constraints/ice40.pcf]
    file_type: PCF
  constraints_ecp5:
    files: [constraints/ecp5.lpf]
    file_type: LPF

targets:
  default:
    filesets: [rtl]
    toplevel: top
  sim:
    default_tool: verilator
    filesets: [rtl, tb]
    toplevel: tb_top
    tools:
      verilator:
        mode: cc
        verilator_options: [--trace, --coverage]
      icarus:
        iverilog_options: [-g2012]
  synth_ice40:
    default_tool: icestorm
    filesets: [rtl, constraints_ice40]
    toplevel: top
    tools:
      icestorm:
        pnr: next
        nextpnr_options: [--hx8k, --package, ct256, --freq, "48"]
  synth_ecp5:
    default_tool: trellis
    filesets: [rtl, constraints_ecp5]
    toplevel: top
    tools:
      trellis:
        nextpnr_options: [--25k, --package, CABGA256]
  synth_vivado:
    default_tool: vivado
    filesets: [rtl]
    toplevel: top
    tools:
      vivado:
        part: xc7a35tcpg236-1
  lint:
    default_tool: verilator
    filesets: [rtl]
    toplevel: top
    tools:
      verilator:
        mode: lint-only

parameters:
  WIDTH:
    datatype: int
    paramtype: vlogparam
    default: 8
    description: "Data width"
```

## File Types

| Type | Extensions |
|---|---|
| `verilogSource` | .v, .vh |
| `systemVerilogSource` | .sv, .svh |
| `vhdlSource` | .vhd, .vhdl |
| `xdc` | Vivado constraints |
| `PCF` | iCE40 constraints |
| `LPF` | ECP5 constraints |
| `CST` | Gowin constraints |

## Edalize Backends

| Backend | Tool | Use Case |
|---------|------|----------|
| verilator | Verilator | Simulation + lint |
| icarus | Icarus Verilog | Simulation |
| vivado | Xilinx Vivado | Synth + P&R |
| quartus | Intel Quartus | Synth + P&R |
| yosys | Yosys | Open-source synth |

## Dependency Management

```yaml
depend:
  - vendor:lib:uart:1.0         # Exact
  - ">=vendor:lib:spi:2.0"     # Minimum
  - "^vendor:lib:i2c:1.2"      # Semver compatible
  - "~vendor:lib:fifo:1.2.3"   # Patch only
```

| Operator | Meaning |
|---|---|
| `=` (default) | Exact match |
| `>=` | At least |
| `^` | Semver compatible (>=X.Y.Z, <X+1.0.0) |
| `~` | Patch only (>=X.Y.Z, <X.Y+1.0) |

## Running FuseSoC

```bash
fusesoc run --target=sim vendor:lib:design           # Simulate
fusesoc run --target=sim --tool=icarus vendor:lib:design  # Specific simulator
fusesoc run --target=synth_ice40 vendor:lib:design    # Synthesize
fusesoc run --target=lint vendor:lib:design           # Lint only
fusesoc core list                                      # List cores
fusesoc library add name https://github.com/org/repo  # Add library
```

## Tool Backend Options

### icestorm
- `pnr`: `next` (nextpnr) or `arachne`
- `nextpnr_options`: CLI args for nextpnr-ice40
- `yosys_synth_options`: Extra synth_ice40 options

### trellis (ECP5)
- `nextpnr_options`: CLI args for nextpnr-ecp5
- `yosys_synth_options`: Extra synth_ecp5 options

### verilator
- `mode`: `binary`, `cc`, `lint-only`
- `verilator_options`: Extra CLI args

### vivado
- `part`: FPGA part number
- `synth`: `vivado` or `yosys`

## Auto-Generation

Scans project, reads `.gateflow/project.yaml`, generates .core file.

## GATEFLOW-RESULT Integration

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
FILES: [generated .core file]
DETAILS: [summary]
---END-GATEFLOW-RESULT---
```
