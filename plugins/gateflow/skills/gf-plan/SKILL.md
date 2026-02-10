---
name: gf-plan
description: >
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

## Reference Material

Detailed reference patterns and templates are in the `references/` directory. Read these files when you need specific reference material while creating a plan:

| File | Contents |
|------|----------|
| `references/design-patterns.md` | Handshake, skid buffer, 2FF sync, arbiter, async/sync FIFO, dual-port RAM, ROM, register file, SECDED, watchdog, TMR |
| `references/dft-and-checklists.md` | DFT strategy, scan chain, JTAG TAP, MBIST, timing closure, retiming, SDC, RTL review checklists (latch, CDC, FSM, coding style) |
| `references/sv-constructs.md` | Packages, types, macros, interfaces/modports, generate blocks, functions/tasks, instantiation patterns, SVA, coverage, classes, DPI |
| `references/build-and-tools.md` | Synthesis planning, SDC constraints, resource estimation, waveform/debug, formal verification (SymbiYosys), Makefiles, FuseSoC, FPGA-specific (Vivado/XDC, ILA) |

**Usage:** When a plan requires a specific pattern (e.g., user needs a FIFO with CDC), read the relevant reference file to include proven templates in the plan.

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
