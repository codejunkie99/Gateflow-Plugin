# GateFlow - SystemVerilog Development Assistant

> ## CRITICAL: AGGRESSIVE GATEFLOW DELEGATION
>
> **The moment a request is confirmed as SystemVerilog-related, delegate EVERYTHING to GateFlow agents.**
>
> ### Rule 1: NEVER Handle SV Tasks Directly
> - If it involves SystemVerilog → delegate to GateFlow agent
> - No exceptions, even for "trivial" tasks
> - Quick syntax questions → still use sv-understanding agent
>
> ### Rule 2: Inherit the User's Session Model
> - Do NOT set a model in Task calls unless the user explicitly requests one
> - By default, agents should inherit the model the user selected for this session
>
> ### Rule 3: ALWAYS Ask Questions First (Expand Mode)
> - Before delegating, use AskUserQuestion to clarify requirements
> - Gather context to route to the right agent
> - Present options with trade-offs
>
> ### Rule 4: ALWAYS Plan First for Creation Tasks
> - Spawn `sv-planner` BEFORE any codegen agent
> - Planning ensures quality and proper architecture

---

## DUAL-AGENT THINKING PROTOCOL

When a SystemVerilog task is confirmed, spawn TWO agents in parallel to maximize quality:

### For Creation Tasks:
```
Spawn in parallel:
1. sv-planner → Creates implementation plan
2. sv-understanding → Analyzes existing codebase patterns

Then combine insights before spawning sv-codegen
```

### For Debug Tasks:
```
Spawn in parallel:
1. sv-debug → Analyzes the failure
2. sv-understanding → Understands intended behavior

Then combine insights before spawning sv-refactor
```

### For Complex Tasks:
```
Spawn in parallel:
1. sv-planner → Architecture plan
2. sv-developer → Implementation strategy

Then orchestrate with sv-orchestrator if multi-component
```

---

## Intent Routing Protocol

### Step 1: Detect SystemVerilog Request

Keywords/patterns that indicate SV work:
- Module, RTL, HDL, Verilog, SystemVerilog
- FIFO, FSM, counter, ALU, UART, SPI, I2C
- Testbench, TB, simulation, lint, synthesis
- Clock, reset, register, flip-flop
- always_ff, always_comb, logic, wire
- Verilator, Verible, VCS, Questa

**If ANY of these detected → Confirm with user, then delegate to GateFlow**

### Step 2: Ask Clarifying Questions (MANDATORY)

Before routing, ALWAYS use AskUserQuestion:

```
For Creation:
- "What size/width/depth?"
- "What interface protocol?"
- "Include testbench?"
- "Any constraints (area, timing, power)?"

For Debug:
- "What symptom do you see?"
- "What's the expected behavior?"
- "Any specific signals to check?"

For Understanding:
- "Which aspect to focus on?"
- "How deep should the analysis go?"
```

### Step 3: Route to Target (ALWAYS delegate, NEVER handle directly)

| User Intent | Primary Agent | Secondary Agent (parallel) | Model |
|-------------|---------------|---------------------------|-------|
| Create new RTL/module | `sv-planner` first, then `sv-codegen` | `sv-understanding` | session |
| Create testbench | `sv-testbench` | `sv-understanding` | session |
| Debug failure/X-values | `sv-debug` | `sv-understanding` | session |
| Add assertions/coverage | `sv-verification` | `sv-understanding` | session |
| Understand existing code | `sv-understanding` | - | session |
| Refactor/fix lint | `sv-refactor` | `sv-understanding` | session |
| Multi-file development | `sv-developer` | `sv-planner` | session |
| Learning/exercises | `sv-tutor` | - | session |
| Complex multi-component | `sv-orchestrator` | `sv-planner` | session |
| End-to-end (create+test) | `/gf` skill | - | session |
| Parallel component build | `/gf-build` skill | - | session |
| Design/plan first | `/gf-plan` skill | - | session |
| Lint check | `/gf-lint` skill | - | - |
| Run simulation | `/gf-sim` skill | - | - |
| Map codebase | `/gf-architect` skill | - | session |
| Learn/practice | `/gf-learn` skill | - | session |
| Visualize codebase | `/gf-viz` skill or `sv-viz` agent | - | session |

### Step 4: NEVER Handle These Directly

Even these "simple" tasks should go to agents:

| Task | Agent |
|------|-------|
| Syntax question | sv-understanding |
| Quick fix | sv-refactor |
| One-line change | sv-refactor |
| Explain a line | sv-understanding |
| Check if valid SV | sv-understanding |

---

## Spawning Pattern - Inherit Session Model

```
Use Task tool:
  subagent_type: "gateflow:sv-codegen"  (or other agent)
  prompt: |
    [Clear description]
    [Context from user answers]
    [Constraints]
    [File paths]
```

### Parallel Spawning Example

```
Use Task tool (call 1):
  subagent_type: "gateflow:sv-planner"
  prompt: "Plan implementation for FIFO with..."

Use Task tool (call 2 - same message, parallel):
  subagent_type: "gateflow:sv-understanding"
  prompt: "Analyze existing codebase for FIFO patterns..."
```

---

## GateFlow Agents Reference

| Agent | Expertise | Trigger Phrases |
|-------|-----------|-----------------|
| `gateflow:sv-codegen` | RTL architect | "create", "write", "generate", "implement module" |
| `gateflow:sv-testbench` | Verification engineer | "testbench", "TB", "test this", "verify" |
| `gateflow:sv-debug` | Debug specialist | "X values", "debug", "not working", "fails" |
| `gateflow:sv-verification` | Verification methodologist | "assertions", "SVA", "coverage", "formal" |
| `gateflow:sv-understanding` | RTL analyst | "explain", "how does", "understand", "analyze" |
| `gateflow:sv-planner` | Architecture planner | "plan", "design", "architect", "strategy" |
| `gateflow:sv-refactor` | Code quality | "fix", "refactor", "clean up", "lint" |
| `gateflow:sv-developer` | Full-stack RTL | "implement feature", "multi-file", "large change" |
| `gateflow:sv-orchestrator` | Parallel builder | "build CPU", "create SoC", "multi-component" |
| `gateflow:sv-tutor` | Teacher | "teach", "learn", "exercise", "practice" |
| `gateflow:sv-viz` | Terminal visualizer | "visualize", "show hierarchy", "show FSM", "show module" |

---

## Verification Loop

After any agent creates/modifies code:

```
1. Run gf-lint skill
2. If FAIL → spawn sv-refactor
3. Run gf-sim skill
4. If FAIL → spawn sv-debug, then sv-refactor
5. Repeat until PASS
```

---

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

## Codebase Map Handoff

Before routing to `sv-understanding` or `sv-developer` for **codebase-wide** tasks, check if a map exists:

```bash
ls .gateflow/map/CODEBASE.md 2>/dev/null
```

| Map Exists? | Action |
|-------------|--------|
| Yes | Route to agent normally, map provides context |
| No | Run `/gf-architect` first, then route to agent |

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
