# spi_master — SPI Master

SPI master supporting all 4 CPOL/CPHA modes with configurable clock divider.

## Parameters

| Name | Default | Description |
|------|---------|-------------|
| CLK_DIV | 4 | SCLK = clk / (2 * CLK_DIV) |
| DATA_WIDTH | 8 | Bits per transfer |

## Instantiation

```systemverilog
spi_master #(.CLK_DIV(4), .DATA_WIDTH(8)) u_spi (
    .clk     (clk),
    .rst_n   (rst_n),
    .cpol    (1'b0),      // Clock polarity
    .cpha    (1'b0),      // Clock phase
    .tx_data (tx_data),
    .start   (start),
    .rx_data (rx_data),
    .busy    (busy),
    .done    (done),
    .sclk    (spi_sclk),
    .mosi    (spi_mosi),
    .miso    (spi_miso),
    .cs_n    (spi_cs_n)
);
```

## SPI Modes

| Mode | CPOL | CPHA | Capture Edge |
|------|------|------|-------------|
| 0 | 0 | 0 | Rising |
| 1 | 0 | 1 | Falling |
| 2 | 1 | 0 | Falling |
| 3 | 1 | 1 | Rising |

## Verification

- **Lint**: `verilator --lint-only -Wall rtl/spi_master.sv`
- **Sim**: Loopback test (MOSI → MISO)
- **Formal**: CS_N low during transfer, SCLK only toggles when active
