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

## Instantiation Examples

### fifo_sync
```systemverilog
fifo_sync #(.WIDTH(8), .DEPTH(32)) u_fifo (.clk(sys_clk), .rst_n(sys_rst_n), .wr_en(wr_valid && !fifo_full), .wr_data(wr_data), .rd_en(rd_consume), .rd_data(rd_out), .full(fifo_full), .empty(fifo_empty));
```

### fifo_async
```systemverilog
fifo_async #(.WIDTH(32), .DEPTH(16)) u_cdc (.wr_clk(clk_fast), .wr_rst_n(rst_fast_n), .wr_en(producer_valid), .wr_data(producer_data), .wr_full(full), .rd_clk(clk_slow), .rd_rst_n(rst_slow_n), .rd_en(consumer_ready), .rd_data(consumer_data), .rd_empty(empty));
```

### cdc_2ff
```systemverilog
cdc_2ff u_sync (.clk(clk_dst), .rst_n(rst_dst_n), .d(async_signal), .q(synced_signal));
```

### uart
```systemverilog
uart #(.CLK_FREQ(100_000_000), .BAUD_RATE(115200)) u_uart (.clk, .rst_n, .tx_data(tx_byte), .tx_valid(tx_start), .tx_ready(tx_idle), .tx(uart_tx_pin), .rx(uart_rx_pin), .rx_data(rx_byte), .rx_valid(rx_ready));
```

### spi_master
```systemverilog
spi_master #(.CLK_DIV(8)) u_spi (.clk, .rst_n, .cpol(1'b0), .cpha(1'b0), .tx_data(spi_tx), .tx_valid(spi_start), .tx_ready(spi_idle), .rx_data(spi_rx), .rx_valid(spi_done), .sclk(spi_sclk), .mosi(spi_mosi), .miso(spi_miso), .cs_n(spi_cs_n));
```

## IP Block Comparison

| Need | Use | Not | Why |
|---|---|---|---|
| Same-clock buffering | fifo_sync | fifo_async | Async has Gray code overhead |
| Cross-domain stream | fifo_async | cdc_2ff | 2FF only handles 1-bit |
| Cross-domain 1-bit flag | cdc_2ff | fifo_async | FIFO overkill for 1-bit |
| Cross-domain multi-bit (infrequent) | cdc_handshake | fifo_async | Handshake smaller |
| Cross-domain multi-bit (streaming) | fifo_async | cdc_handshake | Handshake blocks |

## GATEFLOW-RESULT Format

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | NEEDS_ACTION
OPERATION: add | list | info
BLOCK: <name>
VERSION: <version>
FILES: [copied files]
DETAILS: [summary]
---END-GATEFLOW-RESULT---
```
