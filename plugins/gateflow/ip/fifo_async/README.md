# fifo_async — Asynchronous FIFO

Dual-clock FIFO with Gray code pointer synchronization for safe CDC.

## Parameters

| Name | Default | Description |
|------|---------|-------------|
| WIDTH | 8 | Data width in bits |
| DEPTH | 8 | FIFO depth (power of 2) |

## Instantiation

```systemverilog
fifo_async #(.WIDTH(8), .DEPTH(8)) u_afifo (
    .wr_clk   (clk_fast),
    .wr_rst_n (rst_fast_n),
    .wr_en    (wr_en),
    .wr_data  (wr_data),
    .full     (full),
    .rd_clk   (clk_slow),
    .rd_rst_n (rst_slow_n),
    .rd_en    (rd_en),
    .rd_data  (rd_data),
    .empty    (empty)
);
```

## How It Works

- Write and read pointers are converted to Gray code
- Gray code pointers are synchronized across domains via 2FF
- Full/empty detected by comparing Gray code pointers
- Gray code ensures only 1 bit changes per clock — safe for CDC

## Verification

- **Lint**: `verilator --lint-only -Wall rtl/fifo_async.sv`
- **Sim**: Dual-clock testbench with different frequencies
- **Formal**: No overflow when full
