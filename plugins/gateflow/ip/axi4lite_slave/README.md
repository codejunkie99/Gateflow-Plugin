# axi4lite_slave — AXI4-Lite Register Slave

Parameterized register file with full AXI4-Lite interface and byte strobes.

## Parameters

| Name | Default | Description |
|------|---------|-------------|
| ADDR_WIDTH | 8 | Address bus width |
| DATA_WIDTH | 32 | Data bus width |
| NUM_REGS | 16 | Number of registers |

## Instantiation

```systemverilog
axi4lite_slave #(
    .ADDR_WIDTH (8),
    .DATA_WIDTH (32),
    .NUM_REGS   (16)
) u_regs (
    .clk     (clk),
    .rst_n   (rst_n),
    .awaddr  (awaddr),
    .awvalid (awvalid),
    .awready (awready),
    .wdata   (wdata),
    .wstrb   (wstrb),
    .wvalid  (wvalid),
    .wready  (wready),
    .bresp   (bresp),
    .bvalid  (bvalid),
    .bready  (bready),
    .araddr  (araddr),
    .arvalid (arvalid),
    .arready (arready),
    .rdata   (rdata),
    .rresp   (rresp),
    .rvalid  (rvalid),
    .rready  (rready)
);
```

## Verification

- **Lint**: `verilator --lint-only -Wall rtl/axi4lite_slave.sv`
- **Sim**: Self-checking testbench with read-after-write verification
- **Formal**: Write response follows write completion
