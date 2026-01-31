---
name: gf-plan
description: |
  Hardware design planner - Creates comprehensive RTL implementation plans.
  This skill should be used when the user wants to plan a new design, architect
  a complex feature, or understand how to implement hardware before coding.
  Example requests: "plan a DMA controller", "design a UART", "architect the memory subsystem"
allowed-tools:
  - Grep
  - Glob
  - Read
  - Write
  - Bash
  - Task
  - WebFetch
  - AskUserQuestion
  - Skill
---

# GF Plan - Hardware Design Planner

You create comprehensive, professional RTL implementation plans. Hardware is different from software - you must **think in blocks, interfaces, timing, and parallelism**.

**CRITICAL:** Planning happens BEFORE coding. Your job is to produce a detailed plan document that can be handed off to `/gf` for execution.

## When to Trigger

Activate when user asks to:
- "Plan a [module/feature]"
- "Design a [component]"
- "Architect [subsystem]"
- "How should I implement [feature]?"
- "I need to add [capability] to my design"

## Optional Intake Agent

If requirements are unclear or you need a structured intake (response language + 3 clarifying questions),
spawn the planning agent and use its output as the final plan:

```
Use Task tool:
  subagent_type: "gateflow:sv-planner"
```

## Planning Workflow

```
┌─────────────────────────────────────────────────────────────────┐
│  PHASE 1: UNDERSTAND                                            │
│  • Parse requirements                                           │
│  • Ask clarifying questions (interfaces, constraints, timing)   │
│  • Identify what exists vs. what's new                          │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  PHASE 2: ANALYZE EXISTING (if applicable)                      │
│  • Invoke /gf-architect to map codebase                         │
│  • Find integration points                                      │
│  • Identify existing interfaces, clocks, resets                 │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  PHASE 3: ARCHITECT                                             │
│  • Draw block diagrams (Mermaid)                                │
│  • Design module hierarchy                                      │
│  • Specify interfaces and protocols                             │
│  • Plan clock domains and resets                                │
│  • Design FSMs with state diagrams                              │
│  • Plan pipelines and data paths                                │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  PHASE 4: SPECIFY                                               │
│  • Define all ports and parameters                              │
│  • Document protocols and timing                                │
│  • Specify register maps (if applicable)                        │
│  • Plan verification strategy                                   │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  PHASE 5: PLAN IMPLEMENTATION                                   │
│  • Break into phases                                            │
│  • List files to create/modify                                  │
│  • Identify dependencies                                        │
│  • Specify which agents handle each part                        │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│  PHASE 6: OUTPUT & HANDOFF                                      │
│  • Write plan to .gateflow/plans/<name>.md                      │
│  • Present summary to user                                      │
│  • On approval → handoff to /gf for execution                   │
└─────────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Understanding Requirements

### Questions to Ask (use AskUserQuestion)

**Interface Questions:**
- What bus protocol? (AXI4, AXI-Lite, AXI-Stream, APB, AHB, Wishbone, custom)
- What are the data widths? (8, 16, 32, 64 bits)
- How many channels/ports?
- What's the throughput requirement?

**Timing Questions:**
- Target clock frequency?
- Latency budget (cycles)?
- Single or multiple clock domains?

**Constraint Questions:**
- FPGA or ASIC target?
- Area constraints?
- Power considerations?

**Integration Questions:**
- Does this connect to existing modules?
- What interfaces already exist?
- Any existing packages/types to reuse?

### Requirement Parsing

Extract from user's request:
- **What** they want (functional requirements)
- **Why** they need it (context, use case)
- **Constraints** (performance, area, power)
- **Integration points** (existing code to connect to)

---

## Phase 2: Analyze Existing Codebase

**If user has existing code:**

1. Check for existing map:
```bash
ls .gateflow/map/CODEBASE.md 2>/dev/null
```

2. If no map, invoke architect:
```
Use Skill tool: gf-architect
```

3. From the map, extract:
   - Existing module hierarchy
   - Available interfaces
   - Clock domains in use
   - Package definitions (types, constants)
   - Integration points for new design

4. Document what exists:
```markdown
## Existing Infrastructure

### Clock Domains
- clk_sys (100MHz) - main system clock
- clk_mem (200MHz) - memory interface

### Available Interfaces
- AXI-Lite slave port on soc_top
- Memory interface via mem_if

### Packages to Reuse
- common_pkg: data types, constants
- axi_pkg: AXI type definitions
```

---

## Phase 3: Architecture Design

### Block Diagram (REQUIRED)

Every plan MUST include a block diagram:

```markdown
## Block Diagram

​```mermaid
flowchart TB
    subgraph TOP[module_name]
        direction TB

        subgraph CTRL[Control Path]
            FSM[State Machine]
            REG[Config Registers]
        end

        subgraph DATA[Data Path]
            FIFO_IN[Input FIFO]
            PROC[Processing Unit]
            FIFO_OUT[Output FIFO]
        end

        FSM --> PROC
        REG --> FSM
    end

    EXT_IN[External Input] --> FIFO_IN
    FIFO_IN --> PROC
    PROC --> FIFO_OUT
    FIFO_OUT --> EXT_OUT[External Output]

    CPU[CPU/Host] <-->|AXI-Lite| REG
​```
```

### Module Hierarchy

```markdown
## Module Hierarchy

​```
dma_top                      # Top-level DMA controller
├── dma_reg_if              # AXI-Lite register interface
│   └── dma_reg_block       # Register storage
├── dma_engine              # Main DMA engine
│   ├── dma_descriptor      # Descriptor fetch/decode
│   ├── dma_channel[N]      # Per-channel logic
│   │   ├── dma_fsm         # Channel state machine
│   │   └── dma_counter     # Transfer counter
│   └── dma_arbiter         # Channel arbiter
└── dma_axi_master          # AXI master interface
​```
```

### Interface Design

**Standard Protocols:**

| Protocol | Use Case | Signals |
|----------|----------|---------|
| AXI4-Full | High-performance memory | 5 channels (AW, W, B, AR, R) |
| AXI4-Lite | Register access | Simplified 5 channels |
| AXI4-Stream | Streaming data | TVALID, TREADY, TDATA, TLAST |
| APB | Simple peripherals | PSEL, PENABLE, PWRITE, PADDR, PWDATA, PRDATA |
| Valid/Ready | Generic handshake | valid, ready, data |

**Interface Specification Template:**

```markdown
## Interfaces

### AXI-Lite Slave (Configuration)
| Signal | Dir | Width | Description |
|--------|-----|-------|-------------|
| s_axi_aclk | in | 1 | AXI clock |
| s_axi_aresetn | in | 1 | AXI reset (active-low) |
| s_axi_awaddr | in | 12 | Write address |
| s_axi_awvalid | in | 1 | Write address valid |
| s_axi_awready | out | 1 | Write address ready |
| ... | ... | ... | ... |

### AXI Master (Memory Access)
| Signal | Dir | Width | Description |
|--------|-----|-------|-------------|
| m_axi_* | ... | ... | Full AXI4 master |

### Interrupt
| Signal | Dir | Width | Description |
|--------|-----|-------|-------------|
| irq | out | 1 | Interrupt (level, active-high) |
```

### Clock Domain Planning

```markdown
## Clock Domains

### Clocks
| Clock | Frequency | Domain | Modules |
|-------|-----------|--------|---------|
| clk | 100 MHz | CORE | All except mem_if |
| clk_mem | 200 MHz | MEM | mem_if, async_fifo |

### Clock Domain Crossings
| Signal | From | To | Sync Method |
|--------|------|-----|-------------|
| cmd_valid | CORE | MEM | 2FF + handshake |
| data[31:0] | MEM | CORE | Async FIFO |

### CDC Diagram
​```mermaid
flowchart LR
    subgraph CORE["clk domain"]
        ctrl[Controller]
    end
    subgraph MEM["clk_mem domain"]
        mem[Memory IF]
    end
    ctrl -->|"2FF sync"| mem
    mem -->|"Async FIFO"| ctrl
​```
```

### Reset Strategy

```markdown
## Reset Strategy

| Reset | Type | Polarity | Scope |
|-------|------|----------|-------|
| rst_n | Async assert, sync deassert | Active-low | All modules |
| mem_rst_n | Async | Active-low | Memory domain |

### Reset Synchronization
- rst_n synchronized to each clock domain
- 2FF synchronizer for async reset release
- All registers have reset

### Reset Sequence
1. Assert rst_n (asynchronous)
2. Hold for minimum 10 cycles
3. Deassert synchronously to clk
4. Wait for PLL lock before operation
```

### FSM Design

For EVERY state machine, provide:

```markdown
## FSM: dma_channel_fsm

### States
| State | Encoding | Description |
|-------|----------|-------------|
| IDLE | 3'b000 | Waiting for start |
| FETCH_DESC | 3'b001 | Fetching descriptor |
| CALC_ADDR | 3'b010 | Calculate transfer address |
| XFER | 3'b011 | Performing transfer |
| UPDATE | 3'b100 | Update descriptor |
| DONE | 3'b101 | Transfer complete |
| ERROR | 3'b110 | Error state |

### State Diagram
​```mermaid
stateDiagram-v2
    [*] --> IDLE
    IDLE --> FETCH_DESC: start && desc_avail
    FETCH_DESC --> CALC_ADDR: desc_valid
    FETCH_DESC --> ERROR: desc_error
    CALC_ADDR --> XFER: addr_ready
    XFER --> XFER: !xfer_done
    XFER --> UPDATE: xfer_done && !last
    XFER --> DONE: xfer_done && last
    UPDATE --> FETCH_DESC: update_done
    DONE --> IDLE: clear
    ERROR --> IDLE: clear
​```

### Transitions
| From | To | Condition | Actions |
|------|-----|-----------|---------|
| IDLE | FETCH_DESC | start && desc_avail | Load desc_ptr |
| FETCH_DESC | CALC_ADDR | desc_valid | Store descriptor |
| XFER | UPDATE | xfer_done && !last | Increment count |
| XFER | DONE | xfer_done && last | Assert irq |

### Outputs per State
| State | busy | xfer_en | irq | error |
|-------|------|---------|-----|-------|
| IDLE | 0 | 0 | 0 | 0 |
| FETCH_DESC | 1 | 0 | 0 | 0 |
| XFER | 1 | 1 | 0 | 0 |
| DONE | 0 | 0 | 1 | 0 |
| ERROR | 0 | 0 | 1 | 1 |
```

### Pipeline Design

```markdown
## Pipeline: data_processor

### Pipeline Stages
| Stage | Latency | Function | Inputs | Outputs |
|-------|---------|----------|--------|---------|
| S0 | 1 | Input register | data_in | data_s0 |
| S1 | 1 | Transform | data_s0 | data_s1 |
| S2 | 1 | Output register | data_s1 | data_out |

### Pipeline Diagram
​```mermaid
flowchart LR
    subgraph S0[Stage 0]
        R0[Input Reg]
    end
    subgraph S1[Stage 1]
        ALU[Transform]
    end
    subgraph S2[Stage 2]
        R2[Output Reg]
    end

    IN[data_in] --> R0
    R0 --> ALU
    ALU --> R2
    R2 --> OUT[data_out]

    V0[valid_s0] --> V1[valid_s1] --> V2[valid_out]
    R2 -.->|ready| ALU -.->|ready| R0
​```

### Backpressure Handling
- Valid propagates forward
- Ready propagates backward
- Skid buffer at output for timing
```

---

## Phase 4: Detailed Specification

### Port Specification

```markdown
## Module: dma_top

### Parameters
| Name | Type | Default | Description |
|------|------|---------|-------------|
| NUM_CHANNELS | int | 4 | Number of DMA channels |
| DATA_WIDTH | int | 32 | Data bus width |
| ADDR_WIDTH | int | 32 | Address width |
| DESC_DEPTH | int | 16 | Descriptor FIFO depth |

### Ports
| Name | Dir | Width | Description |
|------|-----|-------|-------------|
| clk | in | 1 | System clock |
| rst_n | in | 1 | Active-low async reset |
| s_axi_* | in/out | - | AXI-Lite slave (config) |
| m_axi_* | in/out | - | AXI master (memory) |
| irq | out | NUM_CHANNELS | Per-channel interrupt |
```

### Register Map (if applicable)

```markdown
## Register Map

Base Address: 0x0000

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x00 | CTRL | RW | 0x0 | Control register |
| 0x04 | STATUS | RO | 0x0 | Status register |
| 0x08 | IRQ_EN | RW | 0x0 | Interrupt enable |
| 0x0C | IRQ_STATUS | RW1C | 0x0 | Interrupt status |
| 0x10 | DESC_PTR | RW | 0x0 | Descriptor pointer |

### CTRL Register (0x00)
| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | EN | RW | 0 | DMA enable |
| 1 | START | RW | 0 | Start transfer (auto-clear) |
| 7:4 | CH_SEL | RW | 0 | Channel select |
| 31:8 | RSVD | RO | 0 | Reserved |
```

### Timing Diagrams

```markdown
## Timing: Write Transaction

​```wavedrom
{ signal: [
  { name: 'clk',     wave: 'P........' },
  { name: 'valid',   wave: '0.1....0.' },
  { name: 'ready',   wave: '0..1.0.1.' },
  { name: 'data',    wave: 'x.3....x.', data: ['D0'] },
  { name: 'transfer',wave: '0...1..0.' }
]}
​```

**Rules:**
- Data stable while valid high
- Transfer occurs when valid AND ready
- Producer holds valid until ready
```

### Protocol Specification

```markdown
## Protocol: Descriptor Format

### Descriptor Word 0 (Control)
| Bits | Field | Description |
|------|-------|-------------|
| 0 | VALID | Descriptor valid |
| 1 | LAST | Last descriptor in chain |
| 2 | IRQ_EN | Generate interrupt on complete |
| 15:8 | BURST_LEN | Burst length (0 = 1 beat) |
| 31:16 | RSVD | Reserved |

### Descriptor Word 1 (Source Address)
| Bits | Field | Description |
|------|-------|-------------|
| 31:0 | SRC_ADDR | Source address |

### Descriptor Word 2 (Destination Address)
| Bits | Field | Description |
|------|-------|-------------|
| 31:0 | DST_ADDR | Destination address |

### Descriptor Word 3 (Next Pointer)
| Bits | Field | Description |
|------|-------|-------------|
| 31:0 | NEXT_PTR | Next descriptor address (0 = end) |
```

---

## Phase 5: Implementation Plan

### File List

```markdown
## Files to Create

| File | Type | Agent | Phase | Description |
|------|------|-------|-------|-------------|
| rtl/dma_pkg.sv | Package | sv-codegen | 1 | Types, constants |
| rtl/dma_reg_if.sv | Module | sv-codegen | 1 | Register interface |
| rtl/dma_channel.sv | Module | sv-codegen | 2 | Single channel |
| rtl/dma_arbiter.sv | Module | sv-codegen | 2 | Channel arbiter |
| rtl/dma_engine.sv | Module | sv-codegen | 3 | Main engine |
| rtl/dma_axi_master.sv | Module | sv-codegen | 3 | AXI master |
| rtl/dma_top.sv | Module | sv-codegen | 4 | Top-level |
| tb/tb_dma_channel.sv | TB | sv-testbench | 2 | Channel TB |
| tb/tb_dma_top.sv | TB | sv-testbench | 4 | System TB |
| rtl/dma_sva.sv | SVA | sv-verification | 4 | Assertions |

## Files to Modify

| File | Change | Agent | Phase |
|------|--------|-------|-------|
| rtl/soc_top.sv | Add DMA instance | sv-codegen | 5 |
| rtl/soc_pkg.sv | Add DMA types | sv-codegen | 1 |
```

### Implementation Phases

```markdown
## Implementation Phases

### Phase 1: Foundation
**Goal:** Package and register interface
**Files:** dma_pkg.sv, dma_reg_if.sv
**Verification:** Lint clean, basic reg read/write test
**Agent:** sv-codegen → lint → sv-testbench

### Phase 2: Core Logic
**Goal:** Single channel working
**Files:** dma_channel.sv, dma_arbiter.sv
**Verification:** Channel testbench, FSM coverage
**Agent:** sv-codegen → lint → sv-testbench → sim

### Phase 3: Bus Interface
**Goal:** AXI master integration
**Files:** dma_engine.sv, dma_axi_master.sv
**Verification:** AXI protocol checks
**Agent:** sv-codegen → lint → sv-verification (protocol assertions)

### Phase 4: Integration
**Goal:** Complete DMA controller
**Files:** dma_top.sv, tb_dma_top.sv, dma_sva.sv
**Verification:** Full system test, assertion coverage
**Agent:** sv-codegen → sv-testbench → sv-verification → sim

### Phase 5: System Integration
**Goal:** DMA in SoC
**Files:** soc_top.sv (modify)
**Verification:** System-level test
**Agent:** sv-developer
```

### Dependencies

```markdown
## Dependencies

​```mermaid
flowchart TD
    PKG[dma_pkg.sv] --> REG[dma_reg_if.sv]
    PKG --> CH[dma_channel.sv]
    PKG --> ARB[dma_arbiter.sv]
    PKG --> AXI[dma_axi_master.sv]

    CH --> ENG[dma_engine.sv]
    ARB --> ENG
    AXI --> ENG

    REG --> TOP[dma_top.sv]
    ENG --> TOP

    TOP --> SOC[soc_top.sv]
​```

**Build Order:**
1. dma_pkg.sv (no deps)
2. dma_reg_if.sv, dma_channel.sv, dma_arbiter.sv, dma_axi_master.sv (parallel)
3. dma_engine.sv
4. dma_top.sv
5. soc_top.sv integration
```

### Verification Strategy

```markdown
## Verification Strategy

### Unit Tests (per module)
| Module | Test Focus | Coverage Goal |
|--------|------------|---------------|
| dma_channel | FSM transitions, counter | 100% state, 90% transition |
| dma_arbiter | Fairness, priority | All grant patterns |
| dma_axi_master | Protocol compliance | AXI assertions pass |

### Integration Tests
| Test | Description | Pass Criteria |
|------|-------------|---------------|
| basic_xfer | Single descriptor transfer | Data matches |
| chain_xfer | Linked descriptor chain | All descriptors complete |
| multi_ch | Multiple channels active | Fair arbitration |
| error_inject | Invalid descriptor | Error flag, no hang |

### Assertions
| Property | Module | Type |
|----------|--------|------|
| AXI handshake | axi_master | Protocol |
| No descriptor overrun | channel | Safety |
| FSM no deadlock | channel | Liveness |
| FIFO no overflow | engine | Safety |

### Coverage Goals
- Line coverage: >95%
- Branch coverage: >90%
- FSM state coverage: 100%
- FSM transition coverage: >95%
- Functional coverage: >98%
```

---

## Phase 6: Output

### Plan Document Location

Write plan to: `.gateflow/plans/<design_name>.md`

### Plan Template

```markdown
# Design Plan: [Name]

**Created:** [Date]
**Author:** GateFlow Planner
**Status:** Draft | Approved | In Progress | Complete

## Overview
[Brief description of what this design does]

## Requirements
- [Requirement 1]
- [Requirement 2]

## Block Diagram
[Mermaid diagram]

## Module Hierarchy
[Tree structure]

## Interfaces
[Port tables]

## Clock Domains
[Clock/CDC info]

## FSMs
[State diagrams for each FSM]

## Register Map
[If applicable]

## Implementation Phases
[Phase breakdown]

## File List
[Files to create/modify]

## Verification Strategy
[Test plan]

## Approval
- [ ] Architecture reviewed
- [ ] Interfaces approved
- [ ] Ready for implementation

---
*Generated by GateFlow Planner*
```

### Handoff to Execution

After user approves:

```markdown
Plan approved! Starting implementation...

Handing off to /gf for execution:
- Phase 1: Creating foundation (dma_pkg.sv, dma_reg_if.sv)
- Will verify each phase before proceeding
- Estimated files: 10
```

Then invoke the gf skill to execute the plan.

---

## Design Patterns Reference

### Valid/Ready Handshake
```systemverilog
// Producer
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) valid <= 1'b0;
    else if (new_data) valid <= 1'b1;
    else if (ready) valid <= 1'b0;

// Consumer
assign ready = !full;
wire transfer = valid && ready;
```

### Skid Buffer
```systemverilog
// Allows ready to deassert without losing data
logic [WIDTH-1:0] skid_data;
logic skid_valid;

assign out_valid = in_valid || skid_valid;
assign out_data = skid_valid ? skid_data : in_data;
assign in_ready = !skid_valid;

always_ff @(posedge clk)
    if (in_valid && !out_ready && !skid_valid) begin
        skid_data <= in_data;
        skid_valid <= 1'b1;
    end else if (out_ready) begin
        skid_valid <= 1'b0;
    end
```

### 2FF Synchronizer
```systemverilog
logic [1:0] sync_ff;
always_ff @(posedge clk_dst or negedge rst_n)
    if (!rst_n) sync_ff <= '0;
    else sync_ff <= {sync_ff[0], async_in};
assign sync_out = sync_ff[1];
```

### Round-Robin Arbiter
```systemverilog
logic [$clog2(N)-1:0] last_grant;
logic [N-1:0] grant;

always_comb begin
    grant = '0;
    for (int i = 0; i < N; i++) begin
        int idx = (last_grant + 1 + i) % N;
        if (req[idx] && grant == '0) grant[idx] = 1'b1;
    end
end
```

### Async FIFO Pointers
```systemverilog
// Gray code conversion
function automatic [ADDR_W:0] bin2gray(input [ADDR_W:0] bin);
    return bin ^ (bin >> 1);
endfunction

// Pointer comparison (Gray domain)
assign full = (wr_gray[ADDR_W] != rd_gray_sync[ADDR_W]) &&
              (wr_gray[ADDR_W-1:0] == rd_gray_sync[ADDR_W-1:0]);
assign empty = (rd_gray == wr_gray_sync);
```

### Synchronous FIFO
```systemverilog
module sync_fifo #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 16
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             wr_en,
    input  logic [WIDTH-1:0] wr_data,
    input  logic             rd_en,
    output logic [WIDTH-1:0] rd_data,
    output logic             full,
    output logic             empty,
    output logic [$clog2(DEPTH):0] count
);
    localparam ADDR_W = $clog2(DEPTH);

    logic [WIDTH-1:0] mem [DEPTH];
    logic [ADDR_W:0] wr_ptr, rd_ptr;

    assign full  = (wr_ptr[ADDR_W] != rd_ptr[ADDR_W]) &&
                   (wr_ptr[ADDR_W-1:0] == rd_ptr[ADDR_W-1:0]);
    assign empty = (wr_ptr == rd_ptr);
    assign count = wr_ptr - rd_ptr;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= '0;
            rd_ptr <= '0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr[ADDR_W-1:0]] <= wr_data;
                wr_ptr <= wr_ptr + 1;
            end
            if (rd_en && !empty) begin
                rd_ptr <= rd_ptr + 1;
            end
        end
    end

    assign rd_data = mem[rd_ptr[ADDR_W-1:0]];
endmodule
```

### Dual-Port RAM
```systemverilog
module dual_port_ram #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 1024
) (
    // Port A
    input  logic             clk_a,
    input  logic             en_a,
    input  logic             we_a,
    input  logic [$clog2(DEPTH)-1:0] addr_a,
    input  logic [WIDTH-1:0] din_a,
    output logic [WIDTH-1:0] dout_a,
    // Port B
    input  logic             clk_b,
    input  logic             en_b,
    input  logic             we_b,
    input  logic [$clog2(DEPTH)-1:0] addr_b,
    input  logic [WIDTH-1:0] din_b,
    output logic [WIDTH-1:0] dout_b
);
    (* ram_style = "block" *)
    logic [WIDTH-1:0] mem [DEPTH];

    // Port A
    always_ff @(posedge clk_a) begin
        if (en_a) begin
            if (we_a) mem[addr_a] <= din_a;
            dout_a <= mem[addr_a];
        end
    end

    // Port B
    always_ff @(posedge clk_b) begin
        if (en_b) begin
            if (we_b) mem[addr_b] <= din_b;
            dout_b <= mem[addr_b];
        end
    end
endmodule
```

### ROM with Initialization
```systemverilog
module rom #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 256,
    parameter string INIT_FILE = "rom_init.mem"
) (
    input  logic             clk,
    input  logic             en,
    input  logic [$clog2(DEPTH)-1:0] addr,
    output logic [WIDTH-1:0] data
);
    (* rom_style = "block" *)
    logic [WIDTH-1:0] mem [DEPTH];

    initial begin
        $readmemh(INIT_FILE, mem);
    end

    always_ff @(posedge clk) begin
        if (en) data <= mem[addr];
    end
endmodule
```

### Register File
```systemverilog
module reg_file #(
    parameter int WIDTH = 32,
    parameter int DEPTH = 32,
    parameter int RD_PORTS = 2,
    parameter int WR_PORTS = 1
) (
    input  logic             clk,
    input  logic             rst_n,
    // Write ports
    input  logic [WR_PORTS-1:0]             wr_en,
    input  logic [WR_PORTS-1:0][$clog2(DEPTH)-1:0] wr_addr,
    input  logic [WR_PORTS-1:0][WIDTH-1:0]  wr_data,
    // Read ports
    input  logic [RD_PORTS-1:0][$clog2(DEPTH)-1:0] rd_addr,
    output logic [RD_PORTS-1:0][WIDTH-1:0]  rd_data
);
    logic [WIDTH-1:0] regs [DEPTH];

    // Writes
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < DEPTH; i++) regs[i] <= '0;
        end else begin
            for (int w = 0; w < WR_PORTS; w++) begin
                if (wr_en[w]) regs[wr_addr[w]] <= wr_data[w];
            end
        end
    end

    // Reads (combinational with bypass)
    always_comb begin
        for (int r = 0; r < RD_PORTS; r++) begin
            rd_data[r] = regs[rd_addr[r]];
            // Write-through bypass
            for (int w = 0; w < WR_PORTS; w++) begin
                if (wr_en[w] && (wr_addr[w] == rd_addr[r]))
                    rd_data[r] = wr_data[w];
            end
        end
    end
endmodule
```

---

## Error Handling & Fault Tolerance

### Planning Error Handling

```markdown
## Error Handling Plan

### Error Detection
| Mechanism | Use Case | Overhead |
|-----------|----------|----------|
| Parity | Single-bit errors | 1 bit per word |
| ECC (SECDED) | Memory protection | 7 bits per 64b |
| CRC | Packet integrity | 8-32 bits |
| Watchdog | System liveness | Timer logic |
| TMR | Critical paths | 3x area |

### Error Response
| Error Type | Detection | Response |
|------------|-----------|----------|
| Correctable | ECC/parity | Fix + log |
| Uncorrectable | ECC/CRC | Interrupt + flag |
| Timeout | Watchdog | Reset + recover |
| Protocol | Assertions | Error state |
```

### SECDED (Single Error Correct, Double Error Detect)
```systemverilog
module secded_encoder #(
    parameter int DATA_W = 64
) (
    input  logic [DATA_W-1:0] data_in,
    output logic [DATA_W+7:0] data_out  // 64 data + 8 check bits
);
    logic [7:0] check;

    // Hamming code calculation
    always_comb begin
        check[0] = ^(data_in & 64'h56AA_AD5B_56AA_AD5B);
        check[1] = ^(data_in & 64'h9B33_366C_D999_B366);
        check[2] = ^(data_in & 64'hE3C3_C78F_1E1E_3C78);
        check[3] = ^(data_in & 64'h03FC_07F0_0FE0_1FC0);
        check[4] = ^(data_in & 64'h03FF_F800_0FFF_E000);
        check[5] = ^(data_in & 64'hFC00_0000_FFFF_0000);
        check[6] = ^(data_in & 64'hFFFF_FFFF_0000_0000);
        check[7] = ^{data_in, check[6:0]};  // Overall parity
    end

    assign data_out = {check, data_in};
endmodule

module secded_decoder #(
    parameter int DATA_W = 64
) (
    input  logic [DATA_W+7:0] data_in,
    output logic [DATA_W-1:0] data_out,
    output logic              corrected,   // Single-bit error corrected
    output logic              error        // Double-bit error detected
);
    logic [7:0] syndrome;
    logic [DATA_W-1:0] data_corrected;
    logic parity_error;

    // Syndrome calculation (same as encoder)
    always_comb begin
        syndrome[0] = ^(data_in[DATA_W-1:0] & 64'h56AA_AD5B_56AA_AD5B) ^ data_in[DATA_W];
        syndrome[1] = ^(data_in[DATA_W-1:0] & 64'h9B33_366C_D999_B366) ^ data_in[DATA_W+1];
        syndrome[2] = ^(data_in[DATA_W-1:0] & 64'hE3C3_C78F_1E1E_3C78) ^ data_in[DATA_W+2];
        syndrome[3] = ^(data_in[DATA_W-1:0] & 64'h03FC_07F0_0FE0_1FC0) ^ data_in[DATA_W+3];
        syndrome[4] = ^(data_in[DATA_W-1:0] & 64'h03FF_F800_0FFF_E000) ^ data_in[DATA_W+4];
        syndrome[5] = ^(data_in[DATA_W-1:0] & 64'hFC00_0000_FFFF_0000) ^ data_in[DATA_W+5];
        syndrome[6] = ^(data_in[DATA_W-1:0] & 64'hFFFF_FFFF_0000_0000) ^ data_in[DATA_W+6];
        parity_error = ^data_in;
    end

    // Correct single-bit error
    always_comb begin
        data_corrected = data_in[DATA_W-1:0];
        if (syndrome != '0 && parity_error)
            data_corrected[syndrome[6:0]] = ~data_in[syndrome[6:0]];
    end

    assign data_out = data_corrected;
    assign corrected = (syndrome != '0) && parity_error;
    assign error = (syndrome != '0) && !parity_error;
endmodule
```

### Watchdog Timer
```systemverilog
module watchdog #(
    parameter int WIDTH = 24,
    parameter int WARN_THRESHOLD = 24'h800000,
    parameter int RESET_THRESHOLD = 24'hFFFFFF
) (
    input  logic clk,
    input  logic rst_n,
    input  logic kick,      // Reset counter
    input  logic enable,
    output logic warning,   // Counter near limit
    output logic timeout    // Counter expired
);
    logic [WIDTH-1:0] counter;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= '0;
        end else if (kick || !enable) begin
            counter <= '0;
        end else if (counter != RESET_THRESHOLD) begin
            counter <= counter + 1;
        end
    end

    assign warning = (counter >= WARN_THRESHOLD);
    assign timeout = (counter >= RESET_THRESHOLD);
endmodule
```

### Triple Modular Redundancy (TMR)
```systemverilog
module tmr_voter #(
    parameter int WIDTH = 32
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic [WIDTH-1:0] c,
    output logic [WIDTH-1:0] out,
    output logic             error  // Mismatch detected
);
    always_comb begin
        // Bitwise majority voting
        out = (a & b) | (b & c) | (a & c);
        error = (a != b) || (b != c) || (a != c);
    end
endmodule

module tmr_register #(
    parameter int WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             en,
    input  logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q,
    output logic             error
);
    logic [WIDTH-1:0] q_a, q_b, q_c;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q_a <= '0;
            q_b <= '0;
            q_c <= '0;
        end else if (en) begin
            q_a <= d;
            q_b <= d;
            q_c <= d;
        end
    end

    tmr_voter #(.WIDTH(WIDTH)) u_voter (
        .a(q_a), .b(q_b), .c(q_c),
        .out(q), .error(error)
    );
endmodule
```

---

## DFT & Testability Planning

### DFT Strategy

```markdown
## DFT Plan

### Test Methods
| Method | Coverage | Overhead | Usage |
|--------|----------|----------|-------|
| Scan chain | Stuck-at faults | 5-15% area | Production test |
| BIST | Logic self-test | 10-20% area | Field test |
| Memory BIST | Memory defects | 3-5% area | Memory test |
| JTAG | Debug/boundary | Minimal | Debug access |

### Scan Planning
| Block | Scan Chains | Length | Clock |
|-------|-------------|--------|-------|
| CPU | 4 | ~2500 | clk_cpu |
| DMA | 2 | ~800 | clk_sys |
| Total | 6 | - | - |
```

### Scan Chain Wrapper
```systemverilog
module scan_ff (
    input  logic clk,
    input  logic rst_n,
    input  logic scan_en,
    input  logic scan_in,
    input  logic d,
    output logic q,
    output logic scan_out
);
    logic mux_out;

    assign mux_out = scan_en ? scan_in : d;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= 1'b0;
        else        q <= mux_out;
    end

    assign scan_out = q;
endmodule
```

### JTAG TAP Controller
```systemverilog
module jtag_tap (
    input  logic tck,
    input  logic trst_n,
    input  logic tms,
    input  logic tdi,
    output logic tdo,
    output logic tdo_en,
    // Internal scan interface
    output logic shift_dr,
    output logic capture_dr,
    output logic update_dr,
    output logic [3:0] ir_out
);
    typedef enum logic [3:0] {
        TEST_LOGIC_RESET = 4'hF,
        RUN_TEST_IDLE    = 4'hC,
        SELECT_DR_SCAN   = 4'h7,
        CAPTURE_DR       = 4'h6,
        SHIFT_DR         = 4'h2,
        EXIT1_DR         = 4'h1,
        PAUSE_DR         = 4'h3,
        EXIT2_DR         = 4'h0,
        UPDATE_DR        = 4'h5,
        SELECT_IR_SCAN   = 4'h4,
        CAPTURE_IR       = 4'hE,
        SHIFT_IR         = 4'hA,
        EXIT1_IR         = 4'h9,
        PAUSE_IR         = 4'hB,
        EXIT2_IR         = 4'h8,
        UPDATE_IR        = 4'hD
    } tap_state_t;

    tap_state_t state, next_state;
    logic [3:0] ir_reg;

    // State machine
    always_ff @(posedge tck or negedge trst_n) begin
        if (!trst_n) state <= TEST_LOGIC_RESET;
        else         state <= next_state;
    end

    always_comb begin
        case (state)
            TEST_LOGIC_RESET: next_state = tms ? TEST_LOGIC_RESET : RUN_TEST_IDLE;
            RUN_TEST_IDLE:    next_state = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            SELECT_DR_SCAN:   next_state = tms ? SELECT_IR_SCAN : CAPTURE_DR;
            CAPTURE_DR:       next_state = tms ? EXIT1_DR : SHIFT_DR;
            SHIFT_DR:         next_state = tms ? EXIT1_DR : SHIFT_DR;
            EXIT1_DR:         next_state = tms ? UPDATE_DR : PAUSE_DR;
            PAUSE_DR:         next_state = tms ? EXIT2_DR : PAUSE_DR;
            EXIT2_DR:         next_state = tms ? UPDATE_DR : SHIFT_DR;
            UPDATE_DR:        next_state = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            SELECT_IR_SCAN:   next_state = tms ? TEST_LOGIC_RESET : CAPTURE_IR;
            CAPTURE_IR:       next_state = tms ? EXIT1_IR : SHIFT_IR;
            SHIFT_IR:         next_state = tms ? EXIT1_IR : SHIFT_IR;
            EXIT1_IR:         next_state = tms ? UPDATE_IR : PAUSE_IR;
            PAUSE_IR:         next_state = tms ? EXIT2_IR : PAUSE_IR;
            EXIT2_IR:         next_state = tms ? UPDATE_IR : SHIFT_IR;
            UPDATE_IR:        next_state = tms ? SELECT_DR_SCAN : RUN_TEST_IDLE;
            default:          next_state = TEST_LOGIC_RESET;
        endcase
    end

    // IR shift register
    always_ff @(posedge tck or negedge trst_n) begin
        if (!trst_n) ir_reg <= 4'b0001;  // IDCODE
        else if (state == CAPTURE_IR) ir_reg <= 4'b0001;
        else if (state == SHIFT_IR) ir_reg <= {tdi, ir_reg[3:1]};
    end

    always_ff @(posedge tck) begin
        if (state == UPDATE_IR) ir_out <= ir_reg;
    end

    assign shift_dr = (state == SHIFT_DR);
    assign capture_dr = (state == CAPTURE_DR);
    assign update_dr = (state == UPDATE_DR);
    assign tdo_en = (state == SHIFT_DR) || (state == SHIFT_IR);
endmodule
```

### Memory BIST
```systemverilog
module mbist_controller #(
    parameter int ADDR_W = 10,
    parameter int DATA_W = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             start,
    output logic             done,
    output logic             pass,
    output logic [ADDR_W-1:0] fail_addr,
    // Memory interface
    output logic             mem_en,
    output logic             mem_we,
    output logic [ADDR_W-1:0] mem_addr,
    output logic [DATA_W-1:0] mem_wdata,
    input  logic [DATA_W-1:0] mem_rdata
);
    typedef enum logic [2:0] {
        IDLE,
        WRITE_ZEROS,
        READ_ZEROS,
        WRITE_ONES,
        READ_ONES,
        WRITE_PATTERN,
        READ_PATTERN,
        DONE_STATE
    } state_t;

    state_t state;
    logic [ADDR_W-1:0] addr;
    logic [DATA_W-1:0] expected;
    logic error_flag;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            addr <= '0;
            done <= 1'b0;
            pass <= 1'b0;
            error_flag <= 1'b0;
        end else begin
            case (state)
                IDLE: begin
                    if (start) begin
                        state <= WRITE_ZEROS;
                        addr <= '0;
                        error_flag <= 1'b0;
                    end
                end

                WRITE_ZEROS, WRITE_ONES, WRITE_PATTERN: begin
                    if (addr == {ADDR_W{1'b1}}) begin
                        addr <= '0;
                        state <= state_t'(state + 1);
                    end else begin
                        addr <= addr + 1;
                    end
                end

                READ_ZEROS, READ_ONES, READ_PATTERN: begin
                    if (mem_rdata != expected) begin
                        error_flag <= 1'b1;
                        fail_addr <= addr;
                    end
                    if (addr == {ADDR_W{1'b1}}) begin
                        addr <= '0;
                        state <= state_t'(state + 1);
                    end else begin
                        addr <= addr + 1;
                    end
                end

                DONE_STATE: begin
                    done <= 1'b1;
                    pass <= !error_flag;
                end
            endcase
        end
    end

    assign mem_en = (state != IDLE) && (state != DONE_STATE);
    assign mem_we = (state == WRITE_ZEROS) || (state == WRITE_ONES) || (state == WRITE_PATTERN);
    assign mem_addr = addr;

    always_comb begin
        case (state)
            WRITE_ZEROS, READ_ZEROS: begin
                mem_wdata = '0;
                expected = '0;
            end
            WRITE_ONES, READ_ONES: begin
                mem_wdata = '1;
                expected = '1;
            end
            default: begin  // Checkerboard pattern
                mem_wdata = {DATA_W/2{2'b10}};
                expected = {DATA_W/2{2'b10}};
            end
        endcase
    end
endmodule
```

---

## Timing Closure Strategies

### Timing Planning

```markdown
## Timing Closure Plan

### Critical Paths
| Path | From | To | Slack | Fix |
|------|------|----|-------|-----|
| path_1 | reg_a | reg_b | -0.5ns | Pipeline |
| path_2 | mux | reg_c | -0.2ns | Restructure |

### Timing Techniques
| Technique | When to Use | Impact |
|-----------|-------------|--------|
| Pipelining | Long combinational paths | +1 cycle latency |
| Retiming | Balance register stages | Neutral latency |
| Logic restructuring | Deep logic cones | May increase area |
| False path | Truly async paths | Removes constraint |
| Multicycle | Slow paths by design | Relaxes timing |
```

### Retiming Example
```systemverilog
// BEFORE: All logic in one stage
// always_ff @(posedge clk) result <= (a * b) + (c * d);

// AFTER: Retimed with pipeline
module retimed_mac (
    input  logic        clk,
    input  logic [15:0] a, b, c, d,
    output logic [31:0] result
);
    logic [31:0] prod_ab, prod_cd;

    // Stage 1: Multiplies
    always_ff @(posedge clk) begin
        prod_ab <= a * b;
        prod_cd <= c * d;
    end

    // Stage 2: Add
    always_ff @(posedge clk) begin
        result <= prod_ab + prod_cd;
    end
endmodule
```

### Logic Restructuring
```systemverilog
// BEFORE: Deep mux tree (slow)
// assign out = sel[3] ? (sel[2] ? ... ) : ...;

// AFTER: Balanced structure
module balanced_mux8 #(parameter WIDTH = 32) (
    input  logic [7:0][WIDTH-1:0] in,
    input  logic [2:0] sel,
    output logic [WIDTH-1:0] out
);
    logic [WIDTH-1:0] stage1 [3:0];
    logic [WIDTH-1:0] stage2 [1:0];

    // Stage 1: 2:1 muxes
    always_comb begin
        stage1[0] = sel[0] ? in[1] : in[0];
        stage1[1] = sel[0] ? in[3] : in[2];
        stage1[2] = sel[0] ? in[5] : in[4];
        stage1[3] = sel[0] ? in[7] : in[6];
    end

    // Stage 2: 2:1 muxes
    always_comb begin
        stage2[0] = sel[1] ? stage1[1] : stage1[0];
        stage2[1] = sel[1] ? stage1[3] : stage1[2];
    end

    // Stage 3: Final mux
    assign out = sel[2] ? stage2[1] : stage2[0];
endmodule
```

### SDC Timing Exceptions
```tcl
# False path - truly asynchronous
set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]
set_false_path -from [get_ports rst_n]
set_false_path -through [get_pins u_sync/sync_ff_reg[0]/D]

# Multicycle path - slow by design
# Data valid every 2 cycles
set_multicycle_path 2 -setup -from [get_pins u_slow/data_reg*/Q]
set_multicycle_path 1 -hold  -from [get_pins u_slow/data_reg*/Q]

# Max delay - I/O constraints
set_max_delay 5.0 -from [get_ports data_in*] -to [get_pins u_input/reg*/D]

# Clock groups - unrelated clocks
set_clock_groups -asynchronous \
    -group [get_clocks clk_sys] \
    -group [get_clocks clk_ext]
```

---

## RTL Review Checklist

### Common RTL Bugs

```markdown
## RTL Bug Checklist

### Latch Inference
- [ ] All `always_comb` blocks have default assignments
- [ ] All `case` statements have `default:`
- [ ] All `if` statements have `else`
- [ ] No incomplete conditional assignments

### Clock Domain Issues
- [ ] All CDC paths use proper synchronizers
- [ ] Gray code for multi-bit CDC counters
- [ ] Async FIFOs for bulk data transfer
- [ ] Reset synchronized to each domain

### Reset Issues
- [ ] All state registers have reset
- [ ] Async reset, sync deassert pattern used
- [ ] Reset polarity consistent (active-low)
- [ ] No combinational paths from reset

### FSM Issues
- [ ] All states reachable
- [ ] No deadlock states
- [ ] Default state transition defined
- [ ] One-hot encoding for fast FPGAs
- [ ] Binary encoding for small FSMs
```

### Synthesis Warning Checklist
```markdown
## Synthesis Warning Categories

### Critical (Must Fix)
- [ ] Latch inferred (LATCH)
- [ ] Multiple drivers (MULTIDRIVEN)
- [ ] Combinational loop (COMBLOOP)
- [ ] Unconnected port (UNCONNECTED on outputs)

### Important (Should Fix)
- [ ] Width mismatch (WIDTH)
- [ ] Unused signal (UNUSED)
- [ ] Undriven signal (UNDRIVEN)
- [ ] Case not full (CASEINCOMPLETE)

### Review (May Be Intentional)
- [ ] Unsigned comparison with signed
- [ ] Implicit wire declarations
- [ ] Non-synthesizable constructs
```

### CDC Review Checklist
```markdown
## CDC Review

### Single-Bit Signals
- [ ] Uses 2FF or 3FF synchronizer
- [ ] Source signal is registered
- [ ] Destination samples at safe rate
- [ ] No combinational logic before sync

### Multi-Bit Signals
- [ ] Gray code encoding
- [ ] MCP (multi-cycle path) or handshake
- [ ] Async FIFO for data streams
- [ ] Proper empty/full synchronization

### Control Signals
- [ ] Pulse synchronizer for strobes
- [ ] Handshake protocol for commands
- [ ] Level synchronizer for enables
- [ ] Proper acknowledgment
```

### FSM Review Checklist
```markdown
## FSM Review

### Structure
- [ ] Enum type with explicit encoding
- [ ] Separate sequential and combinational
- [ ] Default next_state assignment
- [ ] `unique case` or `default:`

### Behavior
- [ ] All states have defined outputs
- [ ] No floating outputs in any state
- [ ] Error state reachable and recoverable
- [ ] Reset goes to known safe state

### Coverage
- [ ] All states reachable from reset
- [ ] All transitions exercised
- [ ] No dead-end states
- [ ] Timeout for stuck states
```

### Coding Style Checklist
```markdown
## Coding Style

### Naming
- [ ] Modules: snake_case
- [ ] Signals: snake_case
- [ ] Parameters: UPPER_SNAKE
- [ ] Types: _t suffix
- [ ] Active-low: _n suffix
- [ ] Clocks: clk prefix
- [ ] Registers: _q or _reg suffix

### Structure
- [ ] ANSI port declarations
- [ ] Parameters before ports
- [ ] Inputs before outputs
- [ ] Logic declaration (not wire/reg)
- [ ] always_ff/always_comb (not always)

### Organization
- [ ] One module per file
- [ ] File name matches module name
- [ ] Consistent indentation (spaces)
- [ ] No trailing whitespace
```

---

## SystemVerilog Constructs Reference

Every plan should consider which of these constructs are needed:

### Packages

```markdown
## Package Design: <name>_pkg

### Purpose
[What this package provides]

### Contents
| Item | Type | Description |
|------|------|-------------|
| DATA_WIDTH | parameter | Bus width |
| state_t | enum | FSM states |
| request_t | struct | Request format |
| encode() | function | Encoding helper |

### Dependencies
- Imports: [other packages]
- Imported by: [modules using this]
```

**Package Template:**
```systemverilog
package dma_pkg;
    // Parameters
    parameter int DATA_WIDTH = 32;
    parameter int ADDR_WIDTH = 32;

    // Types
    typedef enum logic [2:0] {
        IDLE    = 3'b000,
        FETCH   = 3'b001,
        XFER    = 3'b010,
        DONE    = 3'b011,
        ERROR   = 3'b100
    } state_t;

    typedef struct packed {
        logic [ADDR_WIDTH-1:0] addr;
        logic [DATA_WIDTH-1:0] data;
        logic                  valid;
    } request_t;

    // Functions
    function automatic logic [7:0] crc8(input logic [7:0] data);
        // CRC calculation
    endfunction
endpackage
```

### Type Definitions

```markdown
## Type Definitions

### Enums
| Name | Values | Width | Usage |
|------|--------|-------|-------|
| state_t | IDLE, RUN, DONE | 2-bit | FSM state |
| opcode_t | ADD, SUB, MUL, DIV | 2-bit | ALU operations |

### Structs
| Name | Fields | Width | Usage |
|------|--------|-------|-------|
| request_t | addr[31:0], data[31:0], valid | 65 bits | Bus request |
| response_t | data[31:0], error, valid | 34 bits | Bus response |

### Unions (rare, use carefully)
| Name | Members | Usage |
|------|---------|-------|
| data_u | bytes[3:0], word | Byte/word access |

### Typedefs
| Alias | Base | Usage |
|-------|------|-------|
| data_t | logic[31:0] | Data bus |
| addr_t | logic[31:0] | Address |
```

**Type Templates:**
```systemverilog
// Enum with explicit encoding
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    ACTIVE = 2'b01,
    DONE   = 2'b10
} state_t;

// Packed struct (synthesizable, bit-addressable)
typedef struct packed {
    logic [7:0]  tag;
    logic [23:0] addr;
    logic [31:0] data;
} transaction_t;  // 64 bits total

// Unpacked struct (simulation, flexible)
typedef struct {
    string       name;
    int          count;
    logic [31:0] data;
} debug_info_t;

// Union (byte/word access)
typedef union packed {
    logic [31:0]     word;
    logic [3:0][7:0] bytes;
} data_u;

// Simple typedef
typedef logic [31:0] data_t;
typedef logic [11:0] addr_t;
```

### Macros and Preprocessor

```markdown
## Preprocessor Directives

### Defines
| Macro | Value | File | Usage |
|-------|-------|------|-------|
| DATA_WIDTH | 32 | defines.svh | Global width |
| DEBUG | (flag) | defines.svh | Debug mode |
| ASSERT_ON | (flag) | defines.svh | Enable assertions |

### Include Structure
​```
include/
├── defines.svh      # Global defines
├── types.svh        # Type definitions
└── macros.svh       # Utility macros
​```

### Conditional Compilation
| Condition | Purpose | Files |
|-----------|---------|-------|
| `ifdef SIMULATION | Sim-only code | tb/*.sv |
| `ifdef SYNTHESIS | Synth-only code | rtl/*.sv |
| `ifdef FPGA | FPGA-specific | rtl/*.sv |
```

**Macro Templates:**
```systemverilog
// defines.svh
`ifndef DEFINES_SVH
`define DEFINES_SVH

`define DATA_WIDTH 32
`define ADDR_WIDTH 32

// Utility macros
`define FF(clk, rst_n, q, d) \
    always_ff @(posedge clk or negedge rst_n) \
        if (!rst_n) q <= '0; \
        else q <= d

// Conditional
`ifdef SIMULATION
    `define DELAY #1
`else
    `define DELAY
`endif

`endif // DEFINES_SVH
```

### Interfaces and Modports

```markdown
## Interface Design

### <name>_if
**Purpose:** [What this interface encapsulates]
**Parameters:** [Configurable widths, depths]

### Signals
| Signal | Type | Width | Description |
|--------|------|-------|-------------|
| clk | logic | 1 | Clock |
| valid | logic | 1 | Data valid |
| data | logic | [WIDTH-1:0] | Payload |
| ready | logic | 1 | Ready to accept |

### Modports
| Name | Direction | Signals |
|------|-----------|---------|
| master | output | valid, data; input ready |
| slave | input | valid, data; output ready |
| monitor | input | all (passive) |
```

**Interface Template:**
```systemverilog
interface stream_if #(
    parameter int WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);
    logic             valid;
    logic             ready;
    logic [WIDTH-1:0] data;
    logic             last;

    modport master (
        output valid, data, last,
        input  ready
    );

    modport slave (
        input  valid, data, last,
        output ready
    );

    modport monitor (
        input valid, ready, data, last
    );

    // Optional: clocking blocks for TB
    clocking cb @(posedge clk);
        default input #1 output #1;
        output valid, data, last;
        input  ready;
    endclocking

    // Optional: assertions
    property p_handshake;
        @(posedge clk) disable iff (!rst_n)
        valid && !ready |=> valid && $stable(data);
    endproperty
    assert property (p_handshake);

endinterface
```

### Generate Blocks

```markdown
## Generate Blocks

### Loop Generate
| Genvar | Range | Creates | Purpose |
|--------|-------|---------|---------|
| i | 0:N-1 | u_channel[i] | Per-channel logic |
| j | 0:M-1 | mem_bank[j] | Memory banks |

### Conditional Generate
| Condition | True Block | False Block |
|-----------|------------|-------------|
| USE_FIFO | fifo_impl | reg_impl |
| WIDTH > 32 | wide_path | narrow_path |
```

**Generate Templates:**
```systemverilog
// Loop generate - multiple instances
genvar i;
generate
    for (i = 0; i < NUM_CHANNELS; i++) begin : gen_channel
        dma_channel #(
            .ID(i)
        ) u_channel (
            .clk    (clk),
            .rst_n  (rst_n),
            .req    (req[i]),
            .grant  (grant[i])
        );
    end
endgenerate

// Conditional generate
generate
    if (USE_FIFO) begin : gen_fifo
        sync_fifo #(.DEPTH(FIFO_DEPTH)) u_fifo (...);
    end else begin : gen_reg
        register_bank u_regs (...);
    end
endgenerate

// Case generate
generate
    case (IMPL_TYPE)
        "FAST": begin : gen_fast
            fast_impl u_impl (...);
        end
        "SMALL": begin : gen_small
            small_impl u_impl (...);
        end
        default: begin : gen_default
            default_impl u_impl (...);
        end
    endcase
endgenerate
```

### Functions and Tasks

```markdown
## Functions and Tasks

### Functions (combinational, no timing)
| Name | Return | Args | Purpose |
|------|--------|------|---------|
| crc8 | logic[7:0] | data[7:0] | CRC calculation |
| encode | logic[3:0] | onehot[15:0] | Priority encode |
| parity | logic | data[31:0] | Parity bit |

### Tasks (can have timing, for TB)
| Name | Args | Purpose |
|------|------|---------|
| send_packet | data[], len | Send test packet |
| wait_ready | timeout | Wait for ready signal |
| check_result | expected | Verify output |
```

**Function/Task Templates:**
```systemverilog
// Pure function (synthesizable)
function automatic logic [7:0] gray_encode(input logic [7:0] bin);
    return bin ^ (bin >> 1);
endfunction

// Function with local variables
function automatic logic [$clog2(N)-1:0] priority_encode(
    input logic [N-1:0] onehot
);
    for (int i = 0; i < N; i++) begin
        if (onehot[i]) return i[$clog2(N)-1:0];
    end
    return '0;
endfunction

// Task for testbench (with timing)
task automatic send_byte(input logic [7:0] data);
    @(posedge clk);
    tx_valid <= 1'b1;
    tx_data  <= data;
    @(posedge clk);
    while (!tx_ready) @(posedge clk);
    tx_valid <= 1'b0;
endtask

// Task with timeout
task automatic wait_for_done(input int timeout_cycles);
    int count = 0;
    while (!done && count < timeout_cycles) begin
        @(posedge clk);
        count++;
    end
    if (!done) $error("Timeout waiting for done");
endtask
```

### Instantiation Patterns

```markdown
## Module Instantiation

### Instance Table
| Instance | Module | Parameters | Connection |
|----------|--------|------------|------------|
| u_fifo | sync_fifo | .DEPTH(16) | Internal signals |
| u_arb | arbiter | .N(4) | Request/grant |
| u_if | axi_if | default | External port |

### Port Connections
- Named: `.port(signal)` (preferred)
- Positional: Avoid except for simple cases
- Wildcard: `.*` with explicit overrides
```

**Instantiation Templates:**
```systemverilog
// Named port connection (preferred)
sync_fifo #(
    .WIDTH (DATA_WIDTH),
    .DEPTH (FIFO_DEPTH)
) u_fifo (
    .clk     (clk),
    .rst_n   (rst_n),
    .wr_en   (fifo_wr),
    .wr_data (fifo_din),
    .rd_en   (fifo_rd),
    .rd_data (fifo_dout),
    .full    (fifo_full),
    .empty   (fifo_empty)
);

// Wildcard with explicit overrides
dma_channel u_channel (
    .*,                    // Connect matching names
    .data_in  (ch_data),   // Override specific
    .data_out (out_data)
);

// Interface connection
axi_if u_axi_if (.clk(clk), .rst_n(rst_n));

axi_master u_master (
    .clk   (clk),
    .rst_n (rst_n),
    .m_axi (u_axi_if.master)  // Interface modport
);

// Array of instances (with generate)
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_ch
        channel u_ch (
            .id   (i),
            .req  (req[i]),
            .data (data[i])
        );
    end
endgenerate
```

### Assertions (SVA)

```markdown
## Assertion Plan

### Immediate Assertions
| Location | Check | Severity |
|----------|-------|----------|
| FSM default | Invalid state | $error |
| FIFO write | Not full | $error |
| Counter | No overflow | $warning |

### Concurrent Assertions
| Property | Type | Description |
|----------|------|-------------|
| p_handshake | assert | valid stable until ready |
| p_no_overflow | assert | count <= MAX |
| p_eventually_ready | assert | req |-> ##[1:100] ack |
| c_all_states | cover | Visit all FSM states |

### Assertion Bind
| Target | Checker | File |
|--------|---------|------|
| dma_channel | dma_sva | rtl/dma_sva.sv |
| axi_master | axi_protocol_check | rtl/axi_sva.sv |
```

**SVA Templates:**
```systemverilog
// Immediate assertion
always_comb begin
    assert (state inside {IDLE, RUN, DONE})
        else $error("Invalid state: %0d", state);
end

// Concurrent assertions
property p_valid_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> valid && $stable(data);
endproperty
assert property (p_valid_stable) else $error("Valid not held");

property p_request_ack;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:10] ack;
endproperty
assert property (p_request_ack) else $error("No ack within 10 cycles");

// Cover property
cover property (@(posedge clk) state == IDLE ##1 state == RUN);

// Sequence
sequence s_burst;
    valid ##1 valid[*3:8] ##1 last;
endsequence

property p_burst_complete;
    @(posedge clk) $rose(valid) |-> s_burst;
endproperty

// Bind assertions to module
bind dma_channel dma_sva u_sva (.*);
```

### Coverage

```markdown
## Coverage Plan

### Functional Coverage
| Covergroup | Sample | Coverpoints |
|------------|--------|-------------|
| cg_fsm | @(posedge clk) | state, transition |
| cg_config | @config_write | mode, size, enable |
| cg_data | @transfer | data ranges, patterns |

### Cross Coverage
| Cross | Points | Purpose |
|-------|--------|---------|
| state x mode | FSM states, operating mode | Mode-specific behavior |
| size x burst | Transfer size, burst type | All size/burst combos |
```

**Coverage Templates:**
```systemverilog
covergroup cg_fsm @(posedge clk);
    cp_state: coverpoint state {
        bins idle   = {IDLE};
        bins active = {FETCH, XFER};
        bins done   = {DONE};
        bins error  = {ERROR};
        illegal_bins invalid = default;
    }

    cp_transition: coverpoint state {
        bins idle_to_fetch = (IDLE => FETCH);
        bins fetch_to_xfer = (FETCH => XFER);
        bins xfer_to_done  = (XFER => DONE);
    }
endgroup

covergroup cg_config @(posedge config_valid);
    cp_mode: coverpoint mode {
        bins single = {0};
        bins burst  = {1};
        bins chain  = {2};
    }

    cp_size: coverpoint size {
        bins small  = {[1:16]};
        bins medium = {[17:256]};
        bins large  = {[257:4096]};
    }

    cross_mode_size: cross cp_mode, cp_size;
endgroup
```

### Classes (Verification)

```markdown
## Class Hierarchy (for Verification)

### Transaction Classes
| Class | Extends | Purpose |
|-------|---------|---------|
| dma_txn | uvm_sequence_item | DMA transaction |
| burst_txn | dma_txn | Burst transfer |

### Component Classes
| Class | Extends | Purpose |
|-------|---------|---------|
| dma_driver | uvm_driver | Drive DUT |
| dma_monitor | uvm_monitor | Observe interface |
| dma_scoreboard | uvm_scoreboard | Check results |
```

**Class Templates:**
```systemverilog
// Transaction class
class dma_transaction extends uvm_sequence_item;
    rand bit [31:0] src_addr;
    rand bit [31:0] dst_addr;
    rand bit [15:0] length;
    rand bit [1:0]  mode;

    constraint c_aligned {
        src_addr[1:0] == 2'b00;
        dst_addr[1:0] == 2'b00;
    }

    constraint c_length {
        length inside {[1:4096]};
    }

    `uvm_object_utils_begin(dma_transaction)
        `uvm_field_int(src_addr, UVM_ALL_ON)
        `uvm_field_int(dst_addr, UVM_ALL_ON)
        `uvm_field_int(length, UVM_ALL_ON)
    `uvm_object_utils_end
endclass

// Simple class (non-UVM)
class Packet;
    bit [7:0] data[];
    bit [31:0] addr;

    function new(int size);
        data = new[size];
    endfunction

    function void randomize_data();
        foreach (data[i]) data[i] = $urandom();
    endfunction
endclass
```

### DPI (Direct Programming Interface)

```markdown
## DPI Integration

### Imported C Functions
| SV Name | C Name | Return | Args | Purpose |
|---------|--------|--------|------|---------|
| c_crc32 | crc32 | int | data[], len | CRC calculation |
| c_model | ref_model | int | in, out* | Reference model |

### Exported SV Functions
| SV Name | C Name | Purpose |
|---------|--------|---------|
| sv_callback | callback | C calls SV |
```

**DPI Templates:**
```systemverilog
// Import C function
import "DPI-C" function int c_crc32(
    input byte data[],
    input int  length
);

// Import C function with output
import "DPI-C" function void c_reference_model(
    input  int  data_in,
    output int  data_out
);

// Export SV function to C
export "DPI-C" function sv_get_status;

function int sv_get_status();
    return current_status;
endfunction

// Usage
initial begin
    byte packet[] = '{8'h01, 8'h02, 8'h03, 8'h04};
    int crc = c_crc32(packet, 4);
    $display("CRC = %08x", crc);
end
```

---

## Synthesis Planning

### Synthesis Strategy

```markdown
## Synthesis Plan

### Target
| Attribute | Value |
|-----------|-------|
| Target | FPGA / ASIC |
| Device | Xilinx Artix-7 / ASIC 28nm |
| Clock | 100 MHz |
| Area budget | 10k LUTs / 50k gates |

### Synthesis Tool
| Tool | Command |
|------|---------|
| Yosys (open) | `yosys -p "read_verilog *.sv; synth_xilinx -top module"` |
| Vivado | `vivado -mode batch -source synth.tcl` |
| Design Compiler | `dc_shell -f synth.tcl` |

### Timing Constraints (SDC)
| Constraint | Value |
|------------|-------|
| Clock period | 10ns (100MHz) |
| Input delay | 2ns |
| Output delay | 2ns |
| False paths | async resets, CDC |
| Multicycle | [if any] |
```

**SDC Template:**
```tcl
# Clock definition
create_clock -name clk -period 10.0 [get_ports clk]

# Input/output delays
set_input_delay -clock clk 2.0 [all_inputs]
set_output_delay -clock clk 2.0 [all_outputs]

# Reset is async - false path
set_false_path -from [get_ports rst_n]

# CDC false paths
set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]

# Multicycle path (if needed)
set_multicycle_path 2 -setup -from [get_pins */slow_reg*/Q]
```

### Resource Estimation

```markdown
| Resource | Estimate | Budget | Notes |
|----------|----------|--------|-------|
| LUTs | ~2000 | 10000 | FSM + logic |
| FFs | ~500 | 5000 | State + pipeline |
| BRAM | 2 | 10 | FIFOs |
| DSP | 0 | 4 | No math |
```

### Synthesis Checklist
- [ ] All code is synthesizable (no `initial`, `#delays`)
- [ ] No latches inferred
- [ ] Clock gating cells for power
- [ ] Reset strategy matches target
- [ ] Timing constraints defined
- [ ] Resource estimates acceptable

---

## Waveform & Debug Planning

### Debug Infrastructure

```markdown
## Debug Plan

### Simulation Dumps
| Format | Tool | Command |
|--------|------|---------|
| VCD | All | `$dumpfile("dump.vcd"); $dumpvars(0, tb);` |
| FST | Verilator | `--trace-fst` flag |
| FSDB | VCS | `$fsdbDumpfile` |

### Waveform Viewing
| Tool | Platform | Usage |
|------|----------|-------|
| GTKWave | All | `gtkwave dump.vcd` |
| Surfer | All (Rust) | `surfer dump.vcd` |
| DVE | VCS | `dve -vpd dump.vpd` |
| Vivado | Xilinx | Integrated |

### Key Signals to Observe
| Signal | Module | Why |
|--------|--------|-----|
| state | FSM | State transitions |
| valid/ready | interfaces | Handshake |
| data | datapath | Values |
| error | all | Failures |
```

**Waveform Dump Template:**
```systemverilog
initial begin
    // VCD dump
    $dumpfile("dump.vcd");
    $dumpvars(0, tb_top);         // All signals
    // Or selective:
    // $dumpvars(1, tb_top.u_dut); // One level
    // $dumpvars(0, tb_top.u_dut.state); // Specific signal
end

// FST for Verilator (faster, smaller)
// Use: verilator --trace-fst

// Conditional dump (large sims)
initial begin
    $dumpfile("dump.vcd");
    #1000;  // Skip reset
    $dumpvars(0, tb_top);
    #100000;
    $dumpoff;  // Stop dumping
end
```

### Debug Assertions

```systemverilog
// Debug helpers
always @(posedge clk) begin
    if (state == ERROR)
        $display("[%0t] ERROR state entered, cause=%b", $time, error_cause);
    if (fifo_overflow)
        $warning("[%0t] FIFO overflow!", $time);
end

// Transaction logging
always @(posedge clk) begin
    if (valid && ready)
        $display("[%0t] Transfer: addr=%h data=%h", $time, addr, data);
end
```

---

## Formal Verification Planning

### Formal Strategy

```markdown
## Formal Verification Plan

### Tool Selection
| Tool | Type | Usage |
|------|------|-------|
| SymbiYosys | Open source | Property checking |
| JasperGold | Commercial | Full formal |
| VC Formal | Commercial | Full formal |

### Properties to Prove
| Property | Type | Bounded/Unbounded |
|----------|------|-------------------|
| No deadlock | Safety | Unbounded |
| Request→Ack | Liveness | Bounded (100 cycles) |
| FIFO no overflow | Safety | Unbounded |
| FSM reachability | Cover | Bounded |

### Assumptions (Constraints)
| Assumption | Purpose |
|------------|---------|
| Valid inputs only | Constrain input space |
| Reset sequence | Proper initialization |
| Protocol compliance | Assume valid stimulus |
```

**SymbiYosys Template (.sby):**
```
[options]
mode bmc        # Bounded model checking
depth 100       # 100 cycles

[engines]
smtbmc z3

[script]
read -formal top.sv
prep -top top

[files]
top.sv
```

**Formal Properties:**
```systemverilog
// Assume valid inputs
assume property (@(posedge clk) disable iff (!rst_n)
    cmd inside {CMD_READ, CMD_WRITE, CMD_NOP});

// Assert safety property
assert property (@(posedge clk) disable iff (!rst_n)
    fifo_count <= FIFO_DEPTH);

// Assert liveness
assert property (@(posedge clk) disable iff (!rst_n)
    req |-> ##[1:100] ack);

// Cover reachability
cover property (@(posedge clk) state == DONE);
```

---

## Build System Planning

### Build Infrastructure

```markdown
## Build System

### Makefile Targets
| Target | Action |
|--------|--------|
| lint | Run Verilator lint |
| sim | Compile and simulate |
| synth | Run synthesis |
| formal | Run formal checks |
| clean | Remove generated files |
| all | lint + sim |

### File Lists
| File | Purpose |
|------|---------|
| rtl.f | RTL source files |
| tb.f | Testbench files |
| pkg.f | Packages (compile first) |
```

**Makefile Template:**
```makefile
# GateFlow Makefile
TOP = dma_top
TB = tb_$(TOP)

# Tool selection
SIM ?= verilator
SYNTH ?= yosys

# File lists
RTL_FILES = $(shell cat rtl.f)
TB_FILES = $(shell cat tb.f)

#--- Targets ---

.PHONY: lint sim synth formal clean

lint:
	verilator --lint-only -Wall $(RTL_FILES)

sim: lint
ifeq ($(SIM),verilator)
	verilator --binary -j 0 -Wall --trace \
		$(RTL_FILES) $(TB_FILES) \
		--top-module $(TB) -o sim
	./obj_dir/sim
else
	iverilog -g2012 -o sim.vvp $(RTL_FILES) $(TB_FILES)
	vvp sim.vvp
endif

synth:
	yosys -p "read_verilog -sv $(RTL_FILES); \
		synth_xilinx -top $(TOP); \
		write_json $(TOP).json"

formal:
	sby -f $(TOP).sby

waves:
	gtkwave dump.vcd &

clean:
	rm -rf obj_dir *.vvp *.vcd *.fst *.json

# Regression
test: lint
	@for t in tests/*.sv; do \
		echo "Running $$t..."; \
		$(MAKE) sim TB=$$t || exit 1; \
	done
	@echo "All tests passed!"
```

**Filelist Template (rtl.f):**
```
# Packages first (order matters)
rtl/pkg/dma_pkg.sv

# RTL modules (leaf to top)
rtl/dma_channel.sv
rtl/dma_arbiter.sv
rtl/dma_engine.sv
rtl/dma_reg_if.sv
rtl/dma_top.sv
```

**FuseSoC core file (for IP management):**
```yaml
CAPI=2:
name: ::dma:1.0.0
description: DMA Controller

filesets:
  rtl:
    files:
      - rtl/pkg/dma_pkg.sv: {is_include_file: false}
      - rtl/dma_channel.sv
      - rtl/dma_top.sv
    file_type: systemVerilogSource

  tb:
    files:
      - tb/tb_dma_top.sv
    file_type: systemVerilogSource

targets:
  default: &default
    filesets: [rtl]
    toplevel: dma_top

  sim:
    <<: *default
    filesets: [rtl, tb]
    toplevel: tb_dma_top
    default_tool: verilator
```

---

## FPGA-Specific Planning

### FPGA Considerations

```markdown
## FPGA Implementation Plan

### Target Device
| Attribute | Value |
|-----------|-------|
| Family | Xilinx Artix-7 |
| Part | xc7a35tcpg236-1 |
| Speed grade | -1 |
| Package | cpg236 |

### Resource Usage
| Resource | Available | Estimated | % |
|----------|-----------|-----------|---|
| LUT | 20800 | 2000 | 10% |
| FF | 41600 | 1000 | 2% |
| BRAM | 50 | 4 | 8% |
| DSP | 90 | 0 | 0% |

### Clocking
| Clock | Source | Frequency |
|-------|--------|-----------|
| clk_sys | PLL from 100MHz | 100 MHz |
| clk_mem | PLL from 100MHz | 200 MHz |

### Pin Assignments
| Signal | Pin | Standard | Notes |
|--------|-----|----------|-------|
| clk | E3 | LVCMOS33 | Board oscillator |
| rst_n | C2 | LVCMOS33 | Button |
| led[0] | H5 | LVCMOS33 | Status |
```

**Vivado Constraints (XDC):**
```tcl
# Clock
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports clk]
create_clock -period 10.0 -name sys_clk [get_ports clk]

# Reset
set_property -dict {PACKAGE_PIN C2 IOSTANDARD LVCMOS33} [get_ports rst_n]

# LEDs
set_property -dict {PACKAGE_PIN H5 IOSTANDARD LVCMOS33} [get_ports {led[0]}]

# Configuration
set_property CFGBVS VCCO [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]
```

### FPGA-Specific Coding

```systemverilog
// Block RAM inference
(* ram_style = "block" *)
logic [31:0] mem [0:1023];

// Distributed RAM
(* ram_style = "distributed" *)
logic [7:0] small_mem [0:15];

// DSP inference
(* use_dsp = "yes" *)
logic [31:0] product;
assign product = a * b;

// Register for timing
(* KEEP = "TRUE" *)
logic [31:0] pipeline_reg;
```

### FPGA Debug (ILA)

```markdown
## Debug Cores

### ILA Probes
| Signal | Width | Trigger |
|--------|-------|---------|
| state | 3 | state == ERROR |
| data | 32 | valid && ready |
| count | 16 | count > 1000 |

### VIO Controls
| Signal | Width | Purpose |
|--------|-------|---------|
| force_reset | 1 | Manual reset |
| test_mode | 2 | Select test |
```

```tcl
# ILA insertion (Vivado)
create_debug_core u_ila ila
set_property C_DATA_DEPTH 4096 [get_debug_cores u_ila]
set_property C_TRIGIN_EN false [get_debug_cores u_ila]

connect_debug_port u_ila/probe0 [get_nets {state[*]}]
connect_debug_port u_ila/probe1 [get_nets {data[*]}]
```

---

## Checklist Before Handoff

### Architecture
- [ ] Block diagram included
- [ ] All modules defined with hierarchy
- [ ] All interfaces specified (ports, widths, protocols)
- [ ] Clock domains identified, CDC planned
- [ ] Reset strategy documented
- [ ] All FSMs have state diagrams

### SystemVerilog
- [ ] Package structure planned
- [ ] Types defined (structs, enums)
- [ ] Instantiation patterns clear
- [ ] Generate blocks documented

### Implementation
- [ ] Implementation phases defined
- [ ] File list complete with agents assigned
- [ ] Dependencies mapped
- [ ] Register map complete (if applicable)

### Verification
- [ ] Verification strategy documented
- [ ] Assertion plan defined
- [ ] Coverage goals specified
- [ ] Debug infrastructure planned

### Synthesis & Build
- [ ] Target device/process specified
- [ ] Timing constraints planned
- [ ] Resource estimates acceptable
- [ ] Build system (Makefile) planned

### Approval
- [ ] User has reviewed plan
- [ ] User has approved plan

---

## Tools Available

- **Glob**: Find existing files
- **Grep**: Search code patterns
- **Read**: Read existing code
- **Write**: Write plan documents
- **Bash**: Run commands, check tools
- **Task**: Spawn gf-architect for codebase mapping
- **AskUserQuestion**: Clarify requirements
- **Skill**: Invoke gf-architect, hand off to gf

---

*Remember: A good plan prevents rework. Hardware bugs are expensive. Plan thoroughly, implement confidently.*
