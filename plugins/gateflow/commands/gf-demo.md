---
name: gf-demo
description: One-command demo - generates, lints, and simulates a working project
allowed-tools:
  - Bash
  - Write
  - Read
  - Glob
---

# GateFlow Demo

Generate a complete working project to showcase GateFlow's capabilities. Zero user input needed.

## What This Does

1. Creates a parameterized 4-bit counter with enable and reset
2. Creates a self-checking testbench
3. Runs Verilator lint (if available)
4. Runs simulation (if Verilator available)
5. Reports results

## Execution

### Step 1: Create project structure

```bash
mkdir -p rtl tb
```

### Step 2: Generate counter module

Write to `rtl/counter.sv`:

```systemverilog
module counter #(
    parameter int WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] count
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (enable)
            count <= count + 1'b1;
    end

endmodule
```

### Step 3: Generate self-checking testbench

Write to `tb/tb_counter.sv`:

```systemverilog
module tb_counter;
    parameter int WIDTH = 4;
    parameter int CLK_PERIOD = 10;

    logic             clk = 0;
    logic             rst_n = 0;
    logic             enable = 0;
    logic [WIDTH-1:0] count;

    int pass_count = 0;
    int fail_count = 0;

    counter #(.WIDTH(WIDTH)) u_dut (.*);

    always #(CLK_PERIOD/2) clk = ~clk;

    task check(string name, logic [WIDTH-1:0] expected);
        if (count !== expected) begin
            $display("FAIL: %s - got %0d, expected %0d", name, count, expected);
            fail_count++;
        end else begin
            $display("PASS: %s - count = %0d", name, count);
            pass_count++;
        end
    endtask

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_counter);

        // Reset
        rst_n = 0; enable = 0;
        repeat(3) @(posedge clk);
        check("Reset holds zero", '0);

        // Release reset
        rst_n = 1;
        @(posedge clk);
        check("After reset release (no enable)", '0);

        // Enable counting
        enable = 1;
        repeat(5) @(posedge clk);
        check("Count to 5", 4'd5);

        // Disable counting
        enable = 0;
        repeat(3) @(posedge clk);
        check("Holds at 5 when disabled", 4'd5);

        // Re-enable
        enable = 1;
        repeat(11) @(posedge clk);
        check("Wraps around (5+11=0)", 4'd0);

        // Assert reset during count
        rst_n = 0;
        @(posedge clk);
        check("Reset clears count", '0);

        // Summary
        $display("");
        $display("================================");
        $display("  Results: %0d passed, %0d failed", pass_count, fail_count);
        $display("================================");

        if (fail_count > 0) begin
            $display("SIMULATION FAILED");
            $finish(1);
        end else begin
            $display("ALL TESTS PASSED");
            $finish(0);
        end
    end
endmodule
```

### Step 4: Run lint (if Verilator available)

```bash
if command -v verilator &>/dev/null; then
    verilator --lint-only -Wall rtl/counter.sv 2>&1
else
    echo "Verilator not installed - skipping lint. Install: brew install verilator"
fi
```

Report lint results.

### Step 5: Run simulation (if Verilator available)

```bash
if command -v verilator &>/dev/null; then
    verilator --binary -j 0 --trace -Wall \
        --top-module tb_counter \
        -Irtl tb/tb_counter.sv rtl/counter.sv 2>&1 && \
    ./obj_dir/Vtb_counter 2>&1
else
    echo "Verilator not installed - skipping simulation. Install: brew install verilator"
fi
```

### Step 6: Report results

Display a summary:

```
GateFlow Demo Complete!

Created:
  rtl/counter.sv    - 4-bit parameterized counter with enable
  tb/tb_counter.sv  - Self-checking testbench (6 checks)

Lint:   [PASS or SKIP]
Sim:    [PASS with N checks or SKIP]

Next steps:
  "Create a FIFO and test it"     - Try a more complex design
  "Plan a UART controller"        - See design planning in action
  /gf-doctor                      - Check your full environment
```
