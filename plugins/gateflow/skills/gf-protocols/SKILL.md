---
name: gf-protocols
description: >
  Protocol scaffolding library. Generates correct, readable protocol
  interface scaffolds (AXI4-Lite, SPI, UART, I2C, AXI4-Full, AXI-Stream,
  Wishbone) with testbench templates and integration examples.
  Example: "create an I2C master interface", "scaffold AXI-Stream source"
allowed-tools:
  - Read
  - Write
  - Glob
  - Grep
  - Task
---

# GF-Protocols — Protocol Scaffolding Library

Not production IP cores. Correct, readable scaffolds that engineers customize.
Plus the testbenches and integration code — that's where the real time goes.

## Available Protocols

| Protocol | Priority | Scaffold Includes |
|----------|----------|-------------------|
| AXI4-Lite | 1 | Slave register interface + master BFM + TB |
| SPI | 2 | Master + slave + loopback TB |
| UART | 3 | TX + RX + loopback TB |
| I2C | 4 | Master + slave model + TB |
| AXI4-Full | 5 | Slave + burst master BFM + TB |
| AXI-Stream | 6 | Source + sink + passthrough + TB |
| Wishbone | 7 | Slave + master + TB |

## Usage

When user requests a protocol interface:
1. Check if the IP library has a complete block (`/gf-ip list`)
2. If available as IP: suggest `/gf-ip add <block>` instead
3. If not available or user wants custom: generate scaffold

## Scaffold Generation

Each scaffold includes:
- RTL skeleton with correct port names and widths
- Signal timing comments (when to assert/deassert)
- Testbench template with BFM (Bus Functional Model)
- Integration example showing how to wire into a design

## Protocol References

Detailed protocol specifications are in `references/`:
- `references/axi4-lite.md` — AXI4-Lite signal list, timing, rules
- `references/spi.md` — SPI modes, timing, signal descriptions
- `references/i2c.md` — I2C protocol, addressing, clock stretching

When generating scaffolds, ALWAYS read the reference first for correct
signal names, widths, and timing requirements.

---

## AXI4-Lite Slave Scaffold

```systemverilog
module axi4lite_slave_regs #(parameter int ADDR_WIDTH=4, DATA_WIDTH=32) (
    input  logic clk, rst_n,
    input  logic [ADDR_WIDTH-1:0] s_axi_awaddr, input logic s_axi_awvalid, output logic s_axi_awready,
    input  logic [DATA_WIDTH-1:0] s_axi_wdata, input logic [DATA_WIDTH/8-1:0] s_axi_wstrb,
    input  logic s_axi_wvalid, output logic s_axi_wready,
    output logic [1:0] s_axi_bresp, output logic s_axi_bvalid, input logic s_axi_bready,
    input  logic [ADDR_WIDTH-1:0] s_axi_araddr, input logic s_axi_arvalid, output logic s_axi_arready,
    output logic [DATA_WIDTH-1:0] s_axi_rdata, output logic [1:0] s_axi_rresp,
    output logic s_axi_rvalid, input logic s_axi_rready,
    output logic [DATA_WIDTH-1:0] reg0_out, reg1_out,
    input  logic [DATA_WIDTH-1:0] reg2_in, reg3_in
);
    // Write: accept AW+W, write register via wstrb, respond B
    // Read: accept AR, return register data on R
    // Customize: add registers, change address decode width
endmodule
```

## SPI Master Scaffold

```systemverilog
module spi_master_scaffold #(parameter int CLK_DIV=4) (
    input  logic clk, rst_n, cpol, cpha,
    input  logic [7:0] tx_data, input logic tx_valid, output logic tx_ready,
    output logic [7:0] rx_data, output logic rx_valid,
    output logic sclk, mosi, input logic miso, output logic cs_n
);
    // FSM: IDLE -> LEAD -> ACTIVE (8 bits MSB first) -> TRAIL -> DONE
    // Clock divider generates sclk from clk/(2*CLK_DIV)
    // CPOL/CPHA configure polarity and sample/shift edges
    // Customize: add multi-byte, variable width, DMA interface
endmodule
```

## UART TX Scaffold

```systemverilog
module uart_tx_scaffold #(parameter int CLK_FREQ=100_000_000, BAUD_RATE=115_200) (
    input  logic clk, rst_n,
    input  logic [7:0] tx_data, input logic tx_valid, output logic tx_ready,
    output logic tx
);
    // Baud generator: counter to CLK_FREQ/BAUD_RATE
    // FSM: IDLE -> START (1 low bit) -> DATA (8 bits LSB first) -> STOP (1 high bit)
    // tx_ready when IDLE
    // Customize: add parity, configurable data bits, RX companion
endmodule
```

## I2C Master Scaffold

```systemverilog
module i2c_master_scaffold #(parameter int CLK_FREQ=100_000_000, I2C_FREQ=100_000) (
    input  logic clk, rst_n,
    input  logic [6:0] slave_addr, input logic rw, input logic [7:0] wr_data,
    input  logic start, output logic [7:0] rd_data, output logic done, ack_err, busy,
    output logic scl_oen, sda_oen, input logic scl_i, sda_i
);
    // Quarter-period counter for I2C timing
    // FSM: IDLE -> START -> ADDR_BIT(8) -> ADDR_ACK -> WR/RD_BIT(8) -> WR/RD_ACK -> STOP
    // Open-drain: oen=0 drives low, oen=1 releases high via external pull-up
    // Customize: multi-byte transfers, clock stretching, repeated start
endmodule
```

## GATEFLOW-RESULT Integration

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
PROTOCOL: axi4lite | spi | uart | i2c | wishbone | axi_stream
FILES: [generated files]
DETAILS: [summary]
---END-GATEFLOW-RESULT---
```
