# GateFlow - SystemVerilog Development Assistant

> **CRITICAL: Intent Routing Protocol**
>
> For ALL SystemVerilog requests, you MUST follow this routing protocol:
>
> ## Step 1: Classify Intent Semantically
> Analyze the user's GOAL, not keywords. Ask yourself:
> - What is the user trying to accomplish?
> - Is this creating, debugging, understanding, or verifying?
> - Does this need multiple steps (orchestration)?
>
> ## Step 2: Assess Confidence (0.0 - 1.0)
> - **>= 0.85**: Direct handoff to target
> - **0.70 - 0.85**: EXPAND MODE - ask 2-3 questions first
> - **< 0.70**: Ask user to clarify
>
> ## Step 3: Route to Target (NEVER answer directly for these)
>
> | User Intent | Target | Invoke Via |
> |-------------|--------|------------|
> | Create new RTL/module | `sv-codegen` | Task tool |
> | Create testbench | `sv-testbench` | Task tool |
> | Debug failure/X-values | `sv-debug` | Task tool |
> | Add assertions/coverage | `sv-verification` | Task tool |
> | Understand existing code | `sv-understanding` | Task tool |
> | Refactor/fix lint | `sv-refactor` | Task tool |
> | Multi-file development | `sv-developer` | Task tool |
> | Learning/exercises | `sv-tutor` | Task tool |
> | End-to-end (create+test) | `gf` | Skill tool |
> | Design/plan first | `gf-plan` | Skill tool |
> | Lint check | `gf-lint` | Skill tool |
> | Run simulation | `gf-sim` | Skill tool |
> | Map codebase | `gf-architect` | Skill tool |
> | Learn/practice | `gf-learn` | Skill tool |
>
> ## Expand Mode (confidence 0.70-0.85)
> Ask clarifying questions BEFORE routing:
> - **Creation**: "What interface protocol? Include testbench?"
> - **Debug**: "What behavior do you see vs expect?"
> - **Planning**: "Any constraints? Integration needs?"
>
> Present options with trade-offs, then handoff with enriched context.
>
> ## Handle Directly (ONLY these)
> - Quick syntax questions
> - Pattern lookups from this file
> - Running simple commands
> - Clarifying questions

GateFlow provides specialized RTL development capabilities. This reference is always available in context.

## Quick Reference

### Always Blocks
| Purpose | Construct | Assignment |
|---------|-----------|------------|
| Flip-flops | `always_ff @(posedge clk or negedge rst_n)` | `<=` (non-blocking) |
| Combinational | `always_comb` | `=` (blocking) |
| Latches (avoid) | `always_latch` | `=` (blocking) |

### Signal Types
```systemverilog
logic [7:0] data;              // Use logic for all signals
typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;  // FSM states
typedef struct packed { logic [7:0] addr; logic [31:0] data; } req_t;
```

### Port Style (ANSI)
```systemverilog
module example #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,      // Active-low async reset
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
```

## Core Patterns

### FSM (Two-Process)
```systemverilog
typedef enum logic [1:0] {IDLE, ACTIVE, DONE} state_t;
state_t state, next_state;

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) state <= IDLE;
    else        state <= next_state;

always_comb begin
    next_state = state;  // Default: hold
    unique case (state)
        IDLE:   if (start) next_state = ACTIVE;
        ACTIVE: if (done)  next_state = DONE;
        DONE:   next_state = IDLE;
        default: next_state = IDLE;
    endcase
end
```

### Valid/Ready Handshake
```systemverilog
// Transfer when: valid && ready
// Producer holds valid+data until ready
// Consumer asserts ready when can accept
wire transfer = valid && ready;

always_ff @(posedge clk)
    if (transfer) captured_data <= data_in;
```

### Pipeline Stage
```systemverilog
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) begin
        data_q  <= '0;
        valid_q <= 1'b0;
    end else if (ready_out || !valid_q) begin
        data_q  <= data_in;
        valid_q <= valid_in;
    end

assign ready_out = !valid_q || ready_in;  // Accept if empty or downstream ready
```

### 2FF Synchronizer (CDC)
```systemverilog
logic [1:0] sync_reg;
always_ff @(posedge clk_dst or negedge rst_n)
    if (!rst_n) sync_reg <= '0;
    else        sync_reg <= {sync_reg[0], async_in};
assign sync_out = sync_reg[1];
```

### Parameterized FIFO Skeleton
```systemverilog
module fifo #(parameter int WIDTH=8, DEPTH=16) (
    input  logic clk, rst_n,
    input  logic [WIDTH-1:0] wr_data,
    input  logic wr_en, rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic full, empty
);
    localparam ADDR_W = $clog2(DEPTH);
    logic [WIDTH-1:0] mem [DEPTH];
    logic [ADDR_W:0] wr_ptr, rd_ptr;  // Extra bit for full/empty

    assign full  = (wr_ptr[ADDR_W] != rd_ptr[ADDR_W]) &&
                   (wr_ptr[ADDR_W-1:0] == rd_ptr[ADDR_W-1:0]);
    assign empty = (wr_ptr == rd_ptr);
    // ... write/read logic
endmodule
```

## Synthesis Rules

### Do
- `always_ff` / `always_comb` (clear intent)
- `unique case` / `priority case` with `default`
- `'0` / `'1` for reset (flexible width)
- Explicit bit widths: `8'd255` not `255`
- Named port connections: `.clk(sys_clk)`

### Don't
- `initial` blocks (simulation only)
- `#` delays in RTL
- Incomplete case/if (infers latch)
- Blocking in `always_ff`
- Non-blocking in `always_comb`

### Latch Prevention
```systemverilog
// BAD - latch inferred
always_comb
    if (sel) y = a;  // Missing else!

// GOOD - default first
always_comb begin
    y = '0;          // Default
    if (sel) y = a;
end
```

## Common Pitfalls

| Issue | Symptom | Fix |
|-------|---------|-----|
| Inferred latch | Synth warning, unexpected behavior | Default assignment or complete if/case |
| CDC violation | Metastability, random failures | 2FF sync or async FIFO |
| Blocking in seq | Race conditions | Use `<=` in `always_ff` |
| X-propagation | Sim works, synth fails | Check reset coverage |
| Width mismatch | Truncation, sign extension | Explicit sizing |
| Missing reset | X in simulation | Reset all state registers |

## Verilator Lint Fixes

| Warning | Fix |
|---------|-----|
| `UNUSED` | Remove signal or `/* verilator lint_off UNUSED */` |
| `UNDRIVEN` | Assign the signal |
| `WIDTH` | Explicit sizing: `a[7:0]` |
| `CASEINCOMPLETE` | Add `default:` |
| `LATCH` | Complete all branches |
| `BLKSEQ` | Use `<=` in `always_ff` |

## GateFlow Agents

Use specialized agents for complex SystemVerilog tasks:

| Agent | Expertise | Use When User Says |
|-------|-----------|-------------------|
| `gateflow:sv-codegen` | RTL architect | "create module", "write FSM", "generate FIFO" |
| `gateflow:sv-testbench` | Verification engineer | "write testbench", "create TB", "test this" |
| `gateflow:sv-debug` | Debug specialist | "why X values", "debug", "not working" |
| `gateflow:sv-verification` | Verification methodologist | "add assertions", "SVA", "coverage" |
| `gateflow:sv-understanding` | RTL analyst | "explain this", "how does it work" |
| `gateflow:sv-refactor` | Code quality | "fix lint", "refactor", "clean up" |
| `gateflow:sv-developer` | Full-stack RTL | "implement feature", "multi-file change" |

**Handle directly:** Quick fixes, simple questions, running lint/sim commands.

### Codebase Map Handoff

Before routing to `sv-understanding` or `sv-developer` for **codebase-wide** tasks, check if a map exists:

```bash
ls .gateflow/map/CODEBASE.md 2>/dev/null
```

| Map Exists? | Action |
|-------------|--------|
| Yes | Route to agent normally, map provides context |
| No | Run `/gf-architect` first, then route to agent |

**Codebase-wide tasks** (need map): "understand this project", "how does X connect to Y", "implement feature across modules"

**Single-file tasks** (no map needed): "explain this module", "fix this bug", "add assertion here"

### Agent Handoff Pattern

After an agent creates SV files, run verification via Bash:

| After | You Run | If Issues |
|-------|---------|-----------|
| sv-codegen | `verilator --lint-only -Wall *.sv` | → sv-refactor |
| sv-testbench | `verilator --binary -j 0 -Wall --trace <dut>.sv <tb>.sv -o sim && ./obj_dir/sim` | → sv-debug |
| sv-refactor | lint to verify | done |
| sv-debug | rerun sim | verify fix |

**If unsure which file is DUT vs TB:**
- TB has: `initial begin`, `$display`, `$finish`, `$dumpfile`, clock generation
- DUT has: `always_ff`, `always_comb`, synthesizable logic, no `$` tasks
- TB instantiates the DUT module

## Testbench Quick Reference

```systemverilog
module tb_dut();
    parameter CLK_PERIOD = 10;
    logic clk = 0;
    logic rst_n = 0;

    always #(CLK_PERIOD/2) clk = ~clk;

    dut u_dut (.*);

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, tb_dut);

        // Reset
        rst_n = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;

        // Test stimulus
        @(posedge clk);
        // ... tests ...

        $display("Test passed!");
        $finish;
    end
endmodule
```

## SVA Quick Reference

```systemverilog
// Immediate assertion
assert (count <= MAX) else $error("Overflow");

// Concurrent assertion
property p_handshake;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:5] ack;
endproperty
assert property (p_handshake);

// Useful functions
$rose(sig)      // Signal rose this cycle
$fell(sig)      // Signal fell
$stable(sig)    // Signal unchanged
$past(sig, N)   // Value N cycles ago
$onehot(vec)    // Exactly one bit set
```

## Tool Commands

```bash
# Verilator lint
verilator --lint-only -Wall *.sv

# Verible format
verible-verilog-format --inplace *.sv

# Verible lint
verible-verilog-lint *.sv

# Verible syntax check
verible-verilog-syntax *.sv
```

## Naming Conventions

| Element | Convention | Example |
|---------|------------|---------|
| Modules | snake_case | `uart_tx`, `fifo_sync` |
| Signals | snake_case | `data_valid`, `wr_ptr` |
| Parameters | UPPER_SNAKE | `DATA_WIDTH`, `DEPTH` |
| Types | _t suffix | `state_t`, `opcode_t` |
| Active-low | _n suffix | `rst_n`, `cs_n` |
| Clocks | clk prefix | `clk`, `clk_100mhz` |
| Registers | _q or _reg suffix | `data_q`, `count_reg` |
| Next-state | _next or _d suffix | `state_next`, `data_d` |

## External References

```
[SystemVerilog for Verification, 3rd ed. — Spear/Tumbush]
|source: PDF (2012), ~500 pages
|scope: verification-focused SV (OOP testbenches, randomization, coverage, DPI)
|url: https://picture.iczhiku.com/resource/eetop/wYIEDKFRorpoPvvV.pdf
|chapters:
|1 Verification Guidelines (p.2)
|2 Data Types (p.26)
|3 Procedural Statements and Routines (p.70)
|4 Connecting the Testbench and Design (p.90)
|5 Basic OOP (p.132)
|6 Randomization (p.170)
|7 Threads and Interprocess Communication (p.266)
|8 Advanced OOP and Testbench Guidelines (p.274)
|9 Functional Coverage (p.324)
|10 Advanced Interfaces (p.364)
|11 A Complete SystemVerilog Testbench (p.386)
|12 Interfacing with C/C++ (p.416)
```
