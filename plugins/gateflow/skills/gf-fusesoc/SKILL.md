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
---

# GF-FuseSoC — Build System Integration

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

## Edalize Backends

| Backend | Tool | Use Case |
|---------|------|----------|
| verilator | Verilator | Simulation + lint |
| icarus | Icarus Verilog | Simulation |
| vivado | Xilinx Vivado | Synth + P&R |
| quartus | Intel Quartus | Synth + P&R |
| yosys | Yosys | Open-source synth |

## Auto-Generation

Scans project, reads `.gateflow/project.yaml`, generates .core file.
