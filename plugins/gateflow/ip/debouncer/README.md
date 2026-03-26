# debouncer — Button Debouncer

Counter-based debouncer with edge detection outputs.

## Instantiation
```systemverilog
debouncer #(.CLK_FREQ(100_000_000), .DEBOUNCE_MS(20)) u_btn (
    .clk      (clk),
    .rst_n    (rst_n),
    .btn_in   (btn_raw),
    .btn_out  (btn_clean),
    .btn_rise (btn_pressed),
    .btn_fall (btn_released)
);
```
