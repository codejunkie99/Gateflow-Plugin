# cdc_handshake — Multi-Bit Handshake Synchronizer

Req/ack protocol for safely crossing multi-bit data between clock domains.

## Parameters

| Name | Default | Description |
|------|---------|-------------|
| WIDTH | 8 | Data width in bits |

## Instantiation

```systemverilog
cdc_handshake #(.WIDTH(8)) u_cdc (
    .src_clk   (clk_a),
    .src_rst_n (rst_a_n),
    .src_data  (src_data),
    .src_valid (src_valid),
    .src_ready (src_ready),
    .dst_clk   (clk_b),
    .dst_rst_n (rst_b_n),
    .dst_data  (dst_data),
    .dst_valid (dst_valid)
);
```

## How It Works

1. Source presents data + asserts `src_valid`
2. When `src_ready` is high, data is captured and req toggles
3. Req crosses to destination domain via 2FF synchronizer
4. Destination captures data, pulses `dst_valid`, sends ack back
5. Ack crosses back, `src_ready` re-asserts

## Verification

- **Lint**: `verilator --lint-only -Wall rtl/cdc_handshake.sv`
- **Sim**: Cross-domain data transfer test
- **Formal**: Backpressure and data stability properties
