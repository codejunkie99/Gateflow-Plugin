---
name: gf-architect
description: >
  Codebase architect - Maps and documents SystemVerilog projects.
  This skill should be used when the user wants to understand a codebase structure,
  generate architecture documentation, or onboard to a new RTL project.
  Example requests: "map this codebase", "document the architecture", "show module hierarchy"
allowed-tools:
  - Grep
  - Glob
  - Read
  - Write
  - Bash
  - Task
---

# GF Architect

Maps SystemVerilog codebases using parallel subagents.

**CRITICAL: You orchestrate, Sonnet reads.** Never read codebase files directly. Always delegate file reading to Sonnet subagents - even for small codebases. You plan the work, spawn subagents, and synthesize their reports.

## Agent Count Strategy

| Codebase Tokens | Agents | Rationale |
|-----------------|--------|-----------|
| < 50k | 2 | Minimum for parallelism |
| 50k-300k | 3 | Balance load, related files together |
| 300k-600k | 4-5 | Efficient parallel analysis |
| 600k-1M | 6-8 | Stay under 150k per agent |
| > 1M | 8-10 | Cap at 10, use incremental updates |

**Rules:**
- **Minimum: 2 agents** (always parallelize, even for tiny codebases)
- **Maximum: 10 agents** (diminishing returns, synthesis overhead)
- **Large files (>80k tokens):** Dedicated agent with Grep-first strategy

## Quick Start

1. Check for existing map (incremental update if exists)
2. Scan codebase to get file list with token counts
3. **Determine agent count** using table above
4. Plan subagent assignments (group files, handle large files)
5. Spawn Sonnet subagents in parallel (ALL in single message)
6. Synthesize subagent reports into `.gateflow/map/` files
7. Update `CLAUDE.md` with summary

## Output Structure

```
.gateflow/map/
├── CODEBASE.md          # Main summary (AI-friendly index)
├── hierarchy.md         # Module tree diagram
├── signals.md           # Port and signal flow
├── clock-domains.md     # CDC analysis, resets
├── fsm.md              # State machine diagrams
├── packages.md         # Package dependencies
├── types.md            # Structs, unions, typedefs
├── functions.md        # Functions and tasks
├── macros.md           # Preprocessor directives
├── verification.md     # SVA, coverage, checkers
├── interfaces.md       # Interfaces, modports (if found)
├── classes.md          # UVM/OOP classes (if found)
├── generate.md         # Generate blocks (if found)
├── dpi.md              # DPI imports/exports (if found)
├── recipe.md           # Compile order, filelists
└── modules/            # Per-module detail pages
    └── <module_name>.md
```

---

## Workflow

### Step 1: Check for Existing Map

```bash
ls .gateflow/map/CODEBASE.md 2>/dev/null
```

**If exists:** Check for changes since last map:
```bash
# Read last commit from metadata
last_commit=$(cat .gateflow/map/.last_scan_commit 2>/dev/null)
git diff --name-only $last_commit HEAD -- "*.sv" "*.svh" 2>/dev/null
```
- If no changes: "Map is up to date"
- If changes: Proceed with incremental update (only remap changed files)

**If not exists:** Proceed to full mapping.

### Step 2: Scan Codebase & Token Budgeting

```bash
mkdir -p .gateflow/map/modules
```

**Scan files with token counts:**
```bash
find . \( -name "*.sv" -o -name "*.svh" \) -not -path "./.gateflow/*" | while read f; do
  tokens=$(wc -c < "$f" | awk '{print int($1/4)}')
  echo "$tokens $f"
done | sort -rn
```

**Build assignment table:**
| File | Tokens | Assignment |
|------|--------|------------|
| top.sv | 50000 | Agent 1 |
| uart_tx.sv | 8000 | Agent 1 |
| hmac_core.sv | 120000 | Agent 2 (LARGE - use Grep) |

### Step 3: Handle Large Files (>80k tokens)

**For files exceeding 80k tokens, use chunked analysis:**

1. **Use Grep to extract structure** (don't read full file):
```bash
# Get module declaration
grep -n "^\s*module\s" large_file.sv

# Get ports
grep -n "(input|output|inout)" large_file.sv

# Get instances
grep -n "^\s*\w\+\s\+\w\+\s*(" large_file.sv
```

2. **Read in sections** using offset/limit:
```
Read file with offset=0, limit=500 (header, ports)
Read file with offset=500, limit=500 (logic section 1)
... continue until covered
```

3. **Assign to dedicated subagent** with Grep-first strategy

### Step 4: Spawn Parallel Subagents

**CRITICAL: Spawn ALL subagents in a SINGLE message.**

Use Task tool with:
- `subagent_type: "Explore"`
- (omit model to inherit the user’s session model)

**Example - spawn 3 agents in ONE message:**

```
Task 1:
  description: "Analyze UART files"
  subagent_type: "Explore"
  prompt: |
    Read and analyze these SystemVerilog files:
    - rtl/uart_pkg.sv
    - rtl/uart_tx.sv
    - rtl/uart_rx.sv

    For EACH file, extract:
    1. Module/Package name
    2. Purpose (one-line)
    3. Ports table: name, direction, width
    4. Parameters: name, type, default
    5. Instances: what it instantiates
    6. FSM states (if any)
    7. Clock/Reset signals
    8. Package imports

    Return structured markdown.

Task 2:
  description: "Analyze SHA files"
  subagent_type: "Explore"
  prompt: |
    Read and analyze these SystemVerilog files:
    - rtl/sha2_pad.sv
    - rtl/sha2_core.sv

    [Same extraction request...]

Task 3:
  description: "Analyze large file with Grep"
  subagent_type: "Explore"
  prompt: |
    This file is large. Use Grep to extract structure first:
    - rtl/hmac_core.sv (120k tokens)

    1. Grep for module declaration
    2. Grep for ports
    3. Grep for instances
    4. Read specific sections if needed

    Return structured markdown.
```

### Step 5: Synthesize Reports

After all subagents complete:

1. **Merge** all reports
2. **Build hierarchy** from instance data
3. **Create diagrams** (Mermaid)
4. **Identify cross-cutting concerns** (clocks, CDC)
5. **Write output files**

---

## Output File Specifications

### CODEBASE.md (Main Index)

```markdown
---
last_mapped: YYYY-MM-DDTHH:MM:SSZ
total_files: N
total_tokens: N
commit: abc123
---

# Codebase Map: [Project Name]

> Auto-generated by GateFlow Architect

## Quick Stats
| Modules | Packages | Interfaces | FSMs | Clocks |
|---------|----------|------------|------|--------|
| N       | N        | N          | N    | N      |

## Module Index
| Module | Type | File | Ports |
|--------|------|------|-------|
| uart_ctrl | top | rtl/uart_ctrl.sv | clk,rst_n,tx_*,rx_* |
| uart_tx | leaf | rtl/uart_tx.sv | clk,rst_n,data[7:0] |

## Package Index
| Package | File | Exports |
|---------|------|---------|
| uart_pkg | rtl/uart_pkg.sv | state_t, BAUD_RATE |

## Key Files
- [Hierarchy](hierarchy.md) - Module tree
- [Signals](signals.md) - Port connections
- [Clock Domains](clock-domains.md) - CDC analysis
- [FSMs](fsm.md) - State machines
- [Packages](packages.md) - Dependencies
- [Types](types.md) - Structs, enums
- [Verification](verification.md) - Assertions

## Navigation Guide
**To trace data flow**: Start at top module, follow instances
**To add new register**: Modify [module]_reg_top.sv
**To add assertion**: See verification.md for patterns
```

### hierarchy.md

```markdown
# Module Hierarchy

## Top Modules
Modules never instantiated by others: [list]

## Hierarchy Tree

\`\`\`mermaid
flowchart TD
    top[hmac]
    top --> core[u_core: hmac_core]
    top --> regs[u_regs: hmac_reg_top]
    core --> sha[u_sha: sha2_multimode]
\`\`\`

## Instance Table
| Parent | Instance | Module | Parameters |
|--------|----------|--------|------------|
| hmac | u_core | hmac_core | - |
| hmac | u_regs | hmac_reg_top | - |
```

### signals.md

```markdown
# Signal Flow Analysis

## Port Summary by Module

### hmac_core
| Port | Dir | Width | Connected To |
|------|-----|-------|--------------|
| clk_i | input | 1 | top.clk |
| data_o | output | [31:0] | regs.wdata |

## Data Flow Diagram

\`\`\`mermaid
flowchart LR
    subgraph Input
        msg[msg_fifo]
    end
    subgraph Core
        pad[sha2_pad]
        hash[sha2_core]
    end
    subgraph Output
        digest[digest_reg]
    end
    msg --> pad --> hash --> digest
\`\`\`

## Unconnected Ports
- [none or list]
```

### clock-domains.md

```markdown
# Clock Domain Analysis

## Clocks Detected
| Clock | Modules |
|-------|---------|
| clk_i | all |

## Resets Detected
| Reset | Type | Modules |
|-------|------|---------|
| rst_ni | async active-low | all |

## Clock Domain Map

\`\`\`mermaid
flowchart LR
    subgraph clk_i_domain["clk_i domain"]
        core[hmac_core]
        regs[hmac_reg_top]
    end
\`\`\`

## CDC Crossings
| Source | Dest | Signal | Sync Type |
|--------|------|--------|-----------|
| [none or list] |
```

### fsm.md

```markdown
# State Machines

## FSM: tx_state in uart_tx

**States:** IDLE, START, DATA, STOP
**Encoding:** 2-bit

\`\`\`mermaid
stateDiagram-v2
    [*] --> IDLE
    IDLE --> START: tx_valid
    START --> DATA: 1 cycle
    DATA --> DATA: bit_cnt < 7
    DATA --> STOP: bit_cnt == 7
    STOP --> IDLE: 1 cycle
\`\`\`

**Transitions:**
| From | To | Condition |
|------|-----|-----------|
| IDLE | START | tx_valid |
| START | DATA | always |
| DATA | STOP | bit_cnt == 7 |
```

### packages.md

```markdown
# Packages

## uart_pkg
**File:** rtl/uart_pkg.sv

**Exports:**
- Types: state_t, config_t
- Parameters: BAUD_RATE, DATA_BITS
- Functions: calc_divisor()

## Import Graph

\`\`\`mermaid
flowchart TD
    pkg[uart_pkg]
    tx[uart_tx.sv] -->|import| pkg
    rx[uart_rx.sv] -->|import| pkg
\`\`\`
```

### types.md

```markdown
# Type Definitions

## Structs

### request_t
**File:** pkg/types_pkg.sv:15
\`\`\`systemverilog
typedef struct packed {
    logic [7:0] addr;
    logic [31:0] data;
} request_t;
\`\`\`
**Width:** 40 bits

## Enums

| Name | Values | Width | File |
|------|--------|-------|------|
| state_t | IDLE,RUN,DONE | 2-bit | uart_pkg.sv:10 |

## Typedefs

| Alias | Base Type | File |
|-------|-----------|------|
| data_t | logic[31:0] | types.sv:5 |
```

### functions.md

```markdown
# Functions and Tasks

## Functions

### calc_crc
**File:** rtl/crc_pkg.sv:20
**Return:** logic [15:0]
**Args:** input logic [7:0] data
**Used by:** uart_tx, uart_rx

## Tasks

### send_byte
**File:** tb/uart_tb.sv:50
**Args:** input byte data
```

### macros.md

```markdown
# Preprocessor Directives

## Defines
| Macro | Value | File |
|-------|-------|------|
| DATA_WIDTH | 32 | defines.svh:1 |

## Include Graph

\`\`\`mermaid
flowchart TD
    top[top.sv] -->|include| defs[defines.svh]
    uart[uart.sv] -->|include| defs
\`\`\`

## Conditional Compilation
| Condition | Files |
|-----------|-------|
| \`ifdef SIMULATION | tb/*.sv |
```

### verification.md

```markdown
# Verification Constructs

## Assertions (SVA)

### uart_tx assertions
| Property | Type | Description |
|----------|------|-------------|
| p_no_overflow | assert | FIFO never overflows |
| p_valid_stable | assert | valid held until ready |

## Covergroups

### cg_opcodes
**File:** tb/coverage.sv:30
**Coverpoints:** opcode, size
**Crosses:** opcode x size

## Bind Statements
| Target | Checker | File |
|--------|---------|------|
| uart_tx | uart_sva | bind.sv:5 |
```

### interfaces.md (if found)

```markdown
# Interfaces

## axi_if
**File:** rtl/axi_if.sv
**Parameters:** ADDR_WIDTH, DATA_WIDTH

### Signals
| Name | Type | Width |
|------|------|-------|
| awvalid | logic | 1 |
| awaddr | logic | [ADDR_WIDTH-1:0] |

### Modports
| Name | Signals |
|------|---------|
| master | output: aw*, w*, input: b* |
| slave | input: aw*, w*, output: b* |
```

### classes.md (if UVM found)

```markdown
# Classes

## Class Hierarchy

\`\`\`mermaid
classDiagram
    uvm_driver <|-- uart_driver
    uvm_monitor <|-- uart_monitor
\`\`\`

## uart_driver
**File:** tb/uart_driver.sv
**Extends:** uvm_driver
```

### generate.md (if found)

```markdown
# Generate Blocks

## uart_fifo generate loop
**File:** rtl/uart_fifo.sv:50

\`\`\`systemverilog
genvar i;
generate
    for (i = 0; i < DEPTH; i++) begin : gen_mem
        // memory slice
    end
endgenerate
\`\`\`
```

### dpi.md (if found)

```markdown
# DPI Functions

## Imports
| SV Name | C Name | Return | Args |
|---------|--------|--------|------|
| c_calc | calc | int | int a, int b |

## Exports
| SV Name | C Name |
|---------|--------|
| sv_notify | notify |
```

### recipe.md

```markdown
# Build Recipe

## Compile Order
1. Packages (no deps)
2. Interfaces
3. Leaf modules
4. Top modules

\`\`\`mermaid
flowchart LR
    pkg[uart_pkg.sv] --> leaf[uart_tx.sv]
    pkg --> leaf2[uart_rx.sv]
    leaf --> top[uart_ctrl.sv]
    leaf2 --> top
\`\`\`

## Filelists Found
| File | Entries |
|------|---------|
| rtl.f | 15 files |

## Include Paths
- ./rtl
- ./include
```

### Per-Module Pages (modules/*.md)

```markdown
# Module: uart_tx

## Overview
UART transmitter with configurable baud rate.

## Location
- **File:** rtl/uart_tx.sv
- **Lines:** 1-145

## Parameters
| Name | Type | Default | Description |
|------|------|---------|-------------|
| CLK_FREQ | int | 100000000 | System clock Hz |
| BAUD | int | 115200 | Baud rate |

## Ports
| Name | Dir | Width | Description |
|------|-----|-------|-------------|
| clk | input | 1 | System clock |
| rst_n | input | 1 | Active-low reset |
| tx_data | input | [7:0] | Byte to send |
| tx_valid | input | 1 | Data valid |
| tx_ready | output | 1 | Ready for data |
| tx | output | 1 | Serial output |

## Instances
None (leaf module)

## FSM
State type: tx_state_t {IDLE, START, DATA, STOP}
[Link to fsm.md#uart_tx]

## Clock/Reset
- Clock: clk (single domain)
- Reset: rst_n (async active-low)

## Assertions
- p_valid_hold: valid held until ready
```

---

## Regex Patterns Reference

```
# Design Units
^\s*module\s+(\w+)              # Module
^\s*interface\s+(\w+)           # Interface
^\s*package\s+(\w+)             # Package
^\s*program\s+(\w+)             # Program
^\s*class\s+(\w+)               # Class
^\s*checker\s+(\w+)             # Checker

# Ports & Parameters
(input|output|inout)\s+(logic|wire|reg)?\s*(\[.*?\])?\s*(\w+)
parameter\s+(int|logic|integer)?\s*(\w+)\s*=
localparam\s+

# Instances
^\s*(\w+)\s*(#\s*\([^)]*\))?\s+(\w+)\s*\(

# Always blocks
always_ff\s*@|always_comb|always_latch|always\s*@

# Types
typedef\s+enum
typedef\s+struct\s+packed
typedef\s+union

# Functions/Tasks
function\s+(automatic\s+)?
task\s+(automatic\s+)?

# Preprocessor
`define\s+(\w+)
`include\s+"([^"]+)"
`ifdef|`ifndef|`elsif

# Verification
assert\s+property|assume\s+property|cover\s+property
covergroup\s+(\w+)
sequence\s+(\w+)
property\s+(\w+)
bind\s+\w+

# Generate
generate|genvar

# Interface features
modport\s+\w+
clocking\s+\w+

# OOP/UVM
class\s+\w+|extends\s+\w+|virtual\s+class
constraint\s+\w+
rand\s+|randc\s+

# DPI
import\s+"DPI|export\s+"DPI
```

---

## Save Metadata After Mapping

```bash
# Save commit hash
git rev-parse HEAD > .gateflow/map/.last_scan_commit

# Save timestamp
date -u +"%Y-%m-%dT%H:%M:%SZ" > .gateflow/map/.last_scan

# Save file hashes for non-git change detection
find . -name "*.sv" -o -name "*.svh" | xargs md5 > .gateflow/map/.file_hashes
```

---

## Incremental Update Mode

When updating existing map:

1. Get changed files: `git diff --name-only <last_commit> HEAD -- "*.sv"`
2. Spawn subagents ONLY for changed file groups
3. Merge new analysis with existing map files
4. Update frontmatter timestamps
5. Regenerate affected diagrams

---

## Quality Warnings

Report in CODEBASE.md under "## Warnings":
- Inferred latches (always without default)
- Missing resets on sequential logic
- Unconnected ports
- CDC crossings without synchronizers
- Unused signals/parameters
- Missing top module

---

## Token Budget Reference

| Model | Context | Safe Budget |
|-------|---------|-------------|
| Sonnet | 200k | 150k per agent |
| Haiku | 200k | 100k per agent |

**Always use Sonnet** for analysis quality. The 150k budget leaves 50k headroom for agent reasoning and output.

---

## Troubleshooting

**File too large for single agent:**
- Use Grep to extract structure first
- Read in chunks with offset/limit
- Assign dedicated subagent

**Too many files:**
- Increase subagent count
- Focus on RTL, skip testbenches
- Use glob patterns to filter

**No git available:**
- Fall back to file hash comparison
- Store .file_hashes for change detection
