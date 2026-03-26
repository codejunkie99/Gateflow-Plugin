# spi_master — SPI Master
All 4 SPI modes via CPOL/CPHA parameters.
## Instantiation
```systemverilog
spi_master #(.CLK_DIV(4), .DATA_WIDTH(8)) u_spi (
    .clk(clk), .rst_n(rst_n), .cpol(1'b0), .cpha(1'b0),
    .tx_data(tx_data), .start(start), .rx_data(rx_data),
    .busy(busy), .done(done),
    .sclk(sclk), .mosi(mosi), .miso(miso), .cs_n(cs_n)
);
```
