# uart — UART TX+RX

Configurable baud rate UART with 8N1 format.

## Instantiation
```systemverilog
uart_tx #(.CLK_FREQ(100_000_000), .BAUD_RATE(115200)) u_tx (
    .clk(clk), .rst_n(rst_n),
    .tx_data(tx_data), .tx_valid(tx_valid),
    .tx_ready(tx_ready), .tx_out(uart_txd)
);
```
