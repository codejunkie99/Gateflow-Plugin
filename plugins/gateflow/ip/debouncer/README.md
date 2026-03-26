# debouncer — Button Debouncer

Counter-based debouncer with clean output and single-cycle edge detection.

## Parameters

| Name | Default | Description |
|------|---------|-------------|
| CLK_FREQ | 100_000_000 | Clock frequency in Hz |
| DEBOUNCE_MS | 20 | Debounce time in milliseconds |

## Instantiation

```systemverilog
debouncer #(
    .CLK_FREQ    (100_000_000),
    .DEBOUNCE_MS (20)
) u_btn (
    .clk      (clk),
    .rst_n    (rst_n),
    .btn_in   (btn_raw),
    .btn_out  (btn_clean),
    .btn_rise (btn_pressed),   // Single-cycle pulse on press
    .btn_fall (btn_released)   // Single-cycle pulse on release
);
```

## How It Works

1. Input goes through 2FF synchronizer (CDC-safe)
2. Counter increments while input differs from output
3. When counter reaches threshold, output switches
4. Edge detection generates single-cycle rise/fall pulses

## Verification

- **Lint**: `verilator --lint-only -Wall rtl/debouncer.sv`
- **Sim**: Bouncy input test with rapid toggles
- **Formal**: Edges are single-cycle, no simultaneous rise+fall
