---
name: gf-ip
description: >
  IP block library manager. Install, list, and query verified drop-in
  hardware components. Each block includes RTL, testbench, formal
  properties, and documentation.
  Example: "add a FIFO to my project", "/gf-ip add uart"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
---

# GF-IP — IP Block Library

## Commands

- `add <block>` — Copy IP block into current project
- `list` — Show all available IP blocks
- `info <block>` — Show block details, ports, parameters

## Available Blocks

| Block | Description | Verified |
|-------|-------------|----------|
| fifo_sync | Synchronous FIFO (parameterized width/depth) | lint + sim + formal |
| fifo_async | Async FIFO with Gray code pointers (CDC) | lint + sim + formal |
| cdc_2ff | 2-flip-flop synchronizer | lint + sim + formal |
| cdc_handshake | Multi-bit handshake synchronizer | lint + sim + formal |
| uart | UART TX+RX with configurable baud | lint + sim + formal |
| spi_master | SPI master (all 4 CPOL/CPHA modes) | lint + sim + formal |
| axi4lite_slave | AXI4-Lite register slave | lint + sim + formal |
| debouncer | Button debouncer with edge detection | lint + sim + formal |

## Block Structure

Each block lives in `${CLAUDE_PLUGIN_ROOT}/ip/<name>/`:
```
<name>/
  rtl/<name>.sv           # RTL source
  tb/tb_<name>.sv         # Self-checking testbench
  formal/<name>_props.sv  # SVA properties
  formal/<name>.sby       # SymbiYosys config
  block.yaml              # Metadata
  README.md               # Usage guide
```

## Add Flow

When user says "add a FIFO" or runs `/gf-ip add fifo_sync`:
1. Read block.yaml for metadata and parameters
2. Copy RTL to `rtl/` (or user-specified directory)
3. Copy testbench to `tb/`
4. Copy formal properties to `formal/`
5. Update `.gateflow/project.yaml` — add to `ip_blocks`
6. Show instantiation example from README.md

## Block Metadata Schema (block.yaml)

```yaml
name: fifo_sync
version: 1.0.0
description: Synchronous FIFO with parameterized width and depth
parameters:
  WIDTH: { type: int, default: 8, description: "Data width in bits" }
  DEPTH: { type: int, default: 16, description: "FIFO depth (entries)" }
ports:
  - { name: clk, dir: input, width: 1 }
  - { name: rst_n, dir: input, width: 1 }
  - { name: wr_en, dir: input, width: 1 }
  - { name: wr_data, dir: input, width: WIDTH }
  - { name: rd_en, dir: input, width: 1 }
  - { name: rd_data, dir: output, width: WIDTH }
  - { name: full, dir: output, width: 1 }
  - { name: empty, dir: output, width: 1 }
formal_proofs:
  - p_no_overflow: "FIFO never accepts writes when full"
  - p_no_underflow: "FIFO never allows reads when empty"
dependencies: []
```
