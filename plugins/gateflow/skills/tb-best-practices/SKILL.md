---
name: tb-best-practices
description: >
  Testbench verification best practices and patterns.
  This skill should be used when the user needs testbench architecture guidance,
  verification methodology, or wants to write professional-quality testbenches.
  Example requests: "testbench best practices", "how to structure TB", "verification patterns"
allowed-tools:
  - Grep
  - Glob
  - Read
  - Write
  - Edit
  - Bash
  - WebFetch
  - Task
---

# Testbench Best Practices

Professional verification patterns for SystemVerilog testbenches.

## Layered Testbench Architecture

```
┌─────────────────────────────────────────┐
│              Test Layer                 │  ← Test scenarios
├─────────────────────────────────────────┤
│           Environment Layer             │  ← Agent coordination
├──────────────┬──────────────────────────┤
│    Agent     │    Agent                 │  ← Protocol-specific
│  ┌────────┐  │  ┌────────┐              │
│  │ Driver │  │  │Monitor │              │
│  └────────┘  │  └────────┘              │
│  ┌────────┐  │  ┌────────┐              │
│  │Sequencer│ │  │Scoreboard│            │
│  └────────┘  │  └────────┘              │
├──────────────┴──────────────────────────┤
│           Interface Layer               │  ← Signal abstraction
├─────────────────────────────────────────┤
│               DUT                       │
└─────────────────────────────────────────┘
```

---

## 1. Testbench Structure

### Basic Self-Checking TB
```systemverilog
module tb_dut;
    // Clock and reset
    logic clk = 0;
    logic rst_n = 0;
    always #5 clk = ~clk;

    // DUT signals
    logic [7:0] data_in, data_out;
    logic valid_in, valid_out;

    // DUT instance
    dut u_dut (.*);

    // Test
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_dut);

        // Reset
        rst_n = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;

        // Stimulus + Check
        for (int i = 0; i < 100; i++) begin
            @(posedge clk);
            data_in <= $urandom();
            valid_in <= 1;

            @(posedge clk);
            valid_in <= 0;

            // Wait for output
            wait(valid_out);
            check_result(data_in, data_out);
        end

        $display("TEST PASSED");
        $finish;
    end

    // Checker
    function void check_result(input [7:0] expected, input [7:0] actual);
        assert(actual == expected)
            else $error("Mismatch: expected %0h, got %0h", expected, actual);
    endfunction
endmodule
```

---

## 2. Transaction Class

### Best Practice: Separate data from timing
```systemverilog
class Transaction;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit [3:0]  burst_len;
    rand bit        write;

    // Constraints
    constraint c_aligned { addr[1:0] == 2'b00; }
    constraint c_burst   { burst_len inside {1, 4, 8, 16}; }

    // Copy
    function Transaction copy();
        Transaction t = new();
        t.addr = this.addr;
        t.data = this.data;
        t.burst_len = this.burst_len;
        t.write = this.write;
        return t;
    endfunction

    // Display
    function void display(string prefix = "");
        $display("%s addr=%08h data=%08h burst=%0d %s",
            prefix, addr, data, burst_len, write ? "WR" : "RD");
    endfunction
endclass
```

---

## 3. Driver

### Best Practice: Drive interface, not signals
```systemverilog
class Driver;
    virtual bus_if.master vif;
    mailbox #(Transaction) mbx;

    function new(virtual bus_if.master vif, mailbox #(Transaction) mbx);
        this.vif = vif;
        this.mbx = mbx;
    endfunction

    task run();
        Transaction t;
        forever begin
            mbx.get(t);
            drive(t);
        end
    endtask

    task drive(Transaction t);
        @(posedge vif.clk);
        vif.addr  <= t.addr;
        vif.data  <= t.data;
        vif.valid <= 1;

        @(posedge vif.clk);
        while (!vif.ready) @(posedge vif.clk);
        vif.valid <= 0;
    endtask
endclass
```

---

## 4. Monitor

### Best Practice: Passive observation only
```systemverilog
class Monitor;
    virtual bus_if.monitor vif;
    mailbox #(Transaction) mbx;  // To scoreboard

    function new(virtual bus_if.monitor vif, mailbox #(Transaction) mbx);
        this.vif = vif;
        this.mbx = mbx;
    endfunction

    task run();
        Transaction t;
        forever begin
            @(posedge vif.clk);
            if (vif.valid && vif.ready) begin
                t = new();
                t.addr = vif.addr;
                t.data = vif.data;
                mbx.put(t);
            end
        end
    endtask
endclass
```

---

## 5. Scoreboard

### Best Practice: Compare expected vs actual
```systemverilog
class Scoreboard;
    mailbox #(Transaction) expected_mbx;
    mailbox #(Transaction) actual_mbx;
    int pass_count, fail_count;

    function new(mailbox #(Transaction) expected_mbx, mailbox #(Transaction) actual_mbx);
        this.expected_mbx = expected_mbx;
        this.actual_mbx = actual_mbx;
    endfunction

    task run();
        Transaction expected, actual;
        forever begin
            expected_mbx.get(expected);
            actual_mbx.get(actual);
            compare(expected, actual);
        end
    endtask

    function void compare(Transaction expected, Transaction actual);
        if (expected.data == actual.data) begin
            pass_count++;
        end else begin
            fail_count++;
            $error("MISMATCH: expected=%08h actual=%08h", expected.data, actual.data);
        end
    endfunction

    function void report();
        $display("=============================");
        $display("Scoreboard: PASS=%0d FAIL=%0d", pass_count, fail_count);
        $display("=============================");
    endfunction
endclass
```

---

## 6. Randomization Best Practices

### Constraint Layering
```systemverilog
class Transaction;
    rand bit [31:0] addr;
    rand bit [7:0] data;

    // Base constraint
    constraint c_valid_addr { addr < 32'h1000_0000; }

    // Can be overridden in extended class
    constraint c_mode { soft data > 0; }
endclass

class ErrorTransaction extends Transaction;
    // Override to inject errors
    constraint c_mode { data == 0; }
endclass
```

### Weighted Distribution
```systemverilog
class Packet;
    rand bit [1:0] pkt_type;

    constraint c_type_dist {
        pkt_type dist {
            0 := 60,  // 60% normal
            1 := 30,  // 30% error
            2 := 10   // 10% special
        };
    }
endclass
```

### Solve Before
```systemverilog
class Packet;
    rand bit [7:0] length;
    rand bit [7:0] payload[];

    constraint c_size {
        payload.size() == length;
        length inside {[1:64]};
        solve length before payload;
    }
endclass
```

---

## 7. Coverage Best Practices

### Functional Coverage
```systemverilog
class Coverage;
    Transaction t;

    covergroup cg_trans @(posedge clk);
        // Coverpoints
        cp_addr: coverpoint t.addr[31:28] {
            bins low  = {[0:3]};
            bins mid  = {[4:11]};
            bins high = {[12:15]};
        }

        cp_write: coverpoint t.write;

        cp_burst: coverpoint t.burst_len {
            bins single = {1};
            bins burst4 = {4};
            bins burst8 = {8};
            bins burst16 = {16};
            illegal_bins bad = default;
        }

        // Cross coverage
        cross_addr_write: cross cp_addr, cp_write;
    endgroup

    function new();
        cg_trans = new();
    endfunction

    function void sample(Transaction t);
        this.t = t;
        cg_trans.sample();
    endfunction
endclass
```

### Coverage Goals
| Coverage Type | Target |
|---------------|--------|
| Line | >95% |
| Branch | >90% |
| FSM State | 100% |
| FSM Transition | >95% |
| Functional | >98% |

---

## 8. Threading Patterns

### Fork/Join
```systemverilog
// Parallel - wait for all
fork
    driver.run();
    monitor.run();
    scoreboard.run();
join

// Parallel - wait for any (with cleanup)
fork
    driver.run();
    monitor.run();
    timeout_check();
join_any
disable fork;

// Parallel - don't wait
fork
    background_task();
join_none
```

### Timeout Pattern
```systemverilog
task run_with_timeout(int cycles);
    fork
        begin
            run_test();
        end
        begin
            repeat(cycles) @(posedge clk);
            $error("TIMEOUT after %0d cycles", cycles);
            $finish;
        end
    join_any
    disable fork;
endtask
```

---

## 9. Interface Best Practices

### Parameterized Interface
```systemverilog
interface axi_if #(
    parameter int ADDR_W = 32,
    parameter int DATA_W = 32
) (
    input logic clk,
    input logic rst_n
);
    logic [ADDR_W-1:0] awaddr;
    logic [DATA_W-1:0] wdata;
    logic              awvalid, awready;
    logic              wvalid, wready;
    logic [1:0]        bresp;
    logic              bvalid, bready;

    modport master (
        output awaddr, awvalid, wdata, wvalid, bready,
        input  awready, wready, bresp, bvalid
    );

    modport slave (
        input  awaddr, awvalid, wdata, wvalid, bready,
        output awready, wready, bresp, bvalid
    );

    modport monitor (
        input awaddr, awvalid, awready, wdata, wvalid, wready,
              bresp, bvalid, bready
    );

    // Clocking block for TB
    clocking cb @(posedge clk);
        default input #1 output #1;
        output awaddr, awvalid, wdata, wvalid, bready;
        input  awready, wready, bresp, bvalid;
    endclocking
endinterface
```

### Virtual Interface in Class
```systemverilog
class Agent;
    virtual axi_if vif;

    function new(virtual axi_if vif);
        this.vif = vif;
    endfunction
endclass
```

---

## 10. Assertions in Testbench

### Protocol Checks
```systemverilog
// In interface or bind module
property p_valid_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> valid && $stable(data);
endproperty
assert property (p_valid_stable) else $error("Valid dropped before ready");

property p_handshake;
    @(posedge clk) disable iff (!rst_n)
    valid |-> ##[1:100] ready;
endproperty
assert property (p_handshake) else $error("No ready within 100 cycles");
```

---

## 11. Test Organization

### Test Base Class
```systemverilog
virtual class BaseTest;
    Environment env;

    function new(Environment env);
        this.env = env;
    endfunction

    pure virtual task run();

    task pre_test();
        env.reset();
    endtask

    task post_test();
        env.report();
    endtask
endclass

class SmokeTest extends BaseTest;
    virtual task run();
        Transaction t = new();
        repeat(10) begin
            assert(t.randomize());
            env.driver_mbx.put(t);
        end
    endtask
endclass
```

---

## 12. Checklist

### Before Starting
- [ ] Define verification plan
- [ ] Identify coverage goals
- [ ] List test scenarios
- [ ] Design TB architecture

### During Development
- [ ] Use transactions, not raw signals
- [ ] Separate driver/monitor/scoreboard
- [ ] Use virtual interfaces
- [ ] Add functional coverage
- [ ] Include protocol assertions

### Before Signoff
- [ ] All tests pass
- [ ] Coverage goals met
- [ ] No X/Z in simulation
- [ ] Edge cases tested
- [ ] Error injection tested

---

## Reference

```
[SystemVerilog for Verification, 3rd ed. — Spear/Tumbush]
|url: https://picture.iczhiku.com/resource/eetop/wYIEDKFRorpoPvvV.pdf
|relevant: Ch 5 (OOP), Ch 6 (Rand), Ch 7 (Threads), Ch 8 (Advanced OOP), Ch 9 (Coverage), Ch 11 (Complete TB)
```
