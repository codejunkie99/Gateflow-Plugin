# cdc_2ff — 2-Flip-Flop Synchronizer

Single-bit clock domain crossing synchronizer.

## Instantiation
```systemverilog
cdc_2ff #(.STAGES(2)) u_sync (
    .clk      (dest_clk),
    .rst_n    (rst_n),
    .async_in (src_signal),
    .sync_out (synced_signal)
);
```
