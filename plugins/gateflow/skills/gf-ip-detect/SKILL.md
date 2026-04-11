---
name: gf-ip-detect
description: >
  Auto-detect IP blocks within FPGA and hardware codebases. Scans for
  module instantiations, identifies missing implementations, matches
  standard IP patterns, and dispatches agents to fill gaps.
  Example: "scan for missing IP blocks", "detect what needs implementing",
  "find unimplemented modules", "auto-fill IP blocks"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
  - AskUserQuestion
---

# GF-IP-Detect — IP Block Auto-Detection and Auto-Fill

Scans hardware codebases to find IP blocks, identify gaps, and dispatch
agents to implement missing pieces.

## What This Detects

### 1. Missing Module Implementations
Modules instantiated but never defined in the project:
```bash
# Find all module instantiations
grep -rn "^\s*\w\+\s\+\w\+\s*(" rtl/ tb/ --include="*.sv" --include="*.v" --include="*.vhd"

# Find all module definitions
grep -rn "^\s*module\s\+\w\+" rtl/ --include="*.sv" --include="*.v"

# Diff = missing implementations
```

### 2. Stub Modules (Empty or TODO)
Modules defined but with no real implementation:
```bash
# Find modules with TODO/FIXME/stub markers
grep -rn "TODO\|FIXME\|STUB\|NOT IMPLEMENTED" rtl/ --include="*.sv"

# Find modules with empty bodies (just endmodule after ports)
```

### 3. Standard IP Pattern Matching
Detect common hardware patterns that could use verified IP blocks:

| Pattern Detected | Matching IP Block | Confidence |
|-----------------|-------------------|------------|
| FIFO-like read/write with full/empty | `fifo_sync` or `fifo_async` | High |
| 2+ flip-flop chain (synchronizer) | `cdc_2ff` | High |
| Req/ack handshake across clocks | `cdc_handshake` | High |
| UART-like shift register with baud | `uart` | Medium |
| SPI-like SCLK/MOSI/MISO/CS_N | `spi_master` | High |
| AXI-like valid/ready with addr/data | `axi4lite_slave` | Medium |
| Counter with debounce logic | `debouncer` | Medium |

### 4. Interface Gaps
Ports declared in a top module but not connected to any implementation:
```bash
# Find top module ports
# Check which ports connect to instantiated submodules
# Unconnected ports = potential missing IP
```

### 5. Vendor IP Placeholders
Detect instantiations of vendor-specific IP that could have open-source alternatives:
```bash
# Xilinx primitives
grep -rn "IBUF\|OBUF\|BUFG\|MMCME2\|PLLE2\|BRAM" rtl/ --include="*.sv"

# Lattice primitives
grep -rn "SB_IO\|SB_GB\|SB_PLL\|SB_RAM" rtl/ --include="*.sv"
```

---

## Detection Workflow

### Step 1: Scan Codebase

```
Read all .sv/.v/.vhd files in project
        |
Extract: module definitions (name, ports, parameters)
        |
Extract: module instantiations (what's used)
        |
Extract: signal patterns (FIFO, CDC, protocol)
        |
Build dependency graph
```

### Step 2: Identify Gaps

For each instantiated module:
1. Is it defined in the project? → if no, **MISSING**
2. Is it a known IP block from GateFlow library? → suggest `/gf-ip add`
3. Is it a vendor primitive? → flag for review
4. Is it defined but empty/stub? → **NEEDS IMPLEMENTATION**

For each signal pattern:
1. Does it match a standard IP pattern? → suggest replacement
2. Is the implementation ad-hoc? → suggest verified IP block
3. Is there a CDC crossing without synchronizer? → **CRITICAL: suggest cdc_2ff**

### Step 3: Report

```
---GATEFLOW-RESULT---
STATUS: PASS | NEEDS_ACTION
SCAN_RESULTS:
  total_modules: 15
  defined: 12
  missing: 2
  stubs: 1
  
MISSING_MODULES:
  - name: fifo_controller
    instantiated_in: rtl/top.sv:42
    ports: [clk, rst_n, wr_en, wr_data, rd_en, rd_data, full, empty]
    suggested_ip: fifo_sync (92% match)
    
  - name: spi_peripheral
    instantiated_in: rtl/top.sv:67
    ports: [clk, rst_n, sclk, mosi, miso, cs_n, tx_data, rx_data]
    suggested_ip: spi_master (88% match)

STUBS:
  - name: uart_wrapper
    file: rtl/uart_wrapper.sv:1
    status: "Module defined but body is empty (TODO marker at line 15)"
    suggested_action: "Implement using uart IP block as base"

PATTERN_MATCHES:
  - pattern: "Ad-hoc 2FF synchronizer at rtl/sync.sv:10"
    suggestion: "Replace with verified cdc_2ff IP block"
    
  - pattern: "CDC crossing without synchronizer at rtl/top.sv:55"
    severity: CRITICAL
    suggestion: "Add cdc_2ff between clk_a and clk_b domains"

IP_OPPORTUNITIES:
  - "3 modules could use GateFlow IP blocks (fifo_sync, spi_master, cdc_2ff)"
  - "1 stub module needs implementation (uart_wrapper)"
  - "1 critical CDC issue detected"
---END-GATEFLOW-RESULT---
```

### Step 4: Auto-Fill (with user approval)

Present findings and ask:
```
Found 2 missing modules and 1 stub:

1. fifo_controller → 92% match with fifo_sync IP block
   Action: /gf-ip add fifo_sync and rename to fifo_controller? [Y/n]

2. spi_peripheral → 88% match with spi_master IP block
   Action: /gf-ip add spi_master and adapt ports? [Y/n]

3. uart_wrapper → Empty stub, matches uart IP pattern
   Action: Generate implementation using uart IP as base? [Y/n]

4. CRITICAL: CDC crossing at top.sv:55 without synchronizer
   Action: Insert cdc_2ff synchronizer? [Y/n]
```

---

## Auto-Fill Dispatch

When user approves auto-fill, dispatch appropriate agents:

### For IP Block Matches
```
Use Task tool:
  subagent_type: "gateflow:sv-codegen"
  prompt: |
    Implement module <name> based on the <ip_block> IP block.
    Adapt ports to match the instantiation in <file>:<line>.
    Original ports: <detected_ports>
    IP block ports: <ip_ports>
    Generate the module, then create a testbench.
```

### For Stubs
```
Use Task tool:
  subagent_type: "gateflow:sv-codegen"
  prompt: |
    Implement the stub module at <file>.
    The module signature is already defined:
    <module_signature>
    
    Based on the port names and context, this appears to be a <type>.
    Implement full functionality, following the existing codebase patterns.
```

### For CDC Issues
```
Use Task tool:
  subagent_type: "gateflow:sv-refactor"
  prompt: |
    Add CDC synchronization at <file>:<line>.
    Signal <signal> crosses from <src_clk> to <dst_clk> domain
    without synchronization.
    
    Insert a cdc_2ff synchronizer (from GateFlow IP library).
    Ensure the synchronizer is properly reset.
```

---

## Pattern Detection Rules

### FIFO Detection
```
Confidence: HIGH if module has:
- wr_en/write + rd_en/read signals
- full + empty signals  
- data_in/wr_data + data_out/rd_data signals
- Single clock → fifo_sync
- Dual clock → fifo_async
```

### CDC Detection
```
Confidence: HIGH if:
- Signal assigned in always_ff @(posedge clk_a)
- Signal read in always_ff @(posedge clk_b) where clk_a != clk_b
- No synchronizer between domains

Confidence: MEDIUM if:
- 2+ flip-flop chain detected but not using standard sync pattern
```

### Protocol Detection
```
SPI: sclk + mosi + miso + cs_n (any naming variant)
UART: tx/rx + baud-related parameter
I2C: scl + sda (bidirectional)
AXI: *valid + *ready + *addr + *data patterns
```

### Vendor IP Detection
```
Xilinx: IBUF, OBUF, BUFG, MMCME2, PLLE2, BRAM_TDP, DSP48E1
Lattice: SB_IO, SB_GB, SB_PLL40, SB_SPRAM, SB_RAM
Gowin: IBUF, OBUF, rPLL, SDPB, pROM
Intel: altpll, altsyncram, altddio
```

---

## Integration with /gf Orchestrator

The `/gf` orchestrator can invoke IP detection:
- Before any new feature implementation (check what exists)
- After codebase mapping (enrich with IP analysis)
- When user says "what's missing" or "scan for gaps"

## Integration with /gf-architect

Combine with codebase mapping:
1. `/gf-architect` maps the module hierarchy
2. `/gf-ip-detect` overlays IP analysis on the map
3. Result: hierarchy + IP opportunities + CDC issues

---

## Commands

- "Scan for missing IP blocks" → full detection + report
- "Auto-fill missing modules" → detect + dispatch agents
- "What IP blocks does my project need?" → detection + suggestions
- "Find CDC issues" → focused CDC crossing analysis
- "Replace ad-hoc code with verified IP" → pattern match + swap

---

## Extended Vendor IP Detection

Additional primitives to detect beyond existing list:
- **Xilinx UltraScale+:** URAM288, DSP48E2, BUFGCE, MMCME4_ADV, GTHE4_CHANNEL, STARTUPE3
- **Intel Agilex:** IOPLL, RAM20K, M20K, MLAB, tennm_ph2_iopll
- **Lattice ECP5:** EHXPLLL, DP16KD, TRELLIS_FF, DCUA, EXTREFB
- **Gowin (extended):** rPLL, PLLVR, SDPB, DPB, pROM, EMCU, DHCEN
- **Microchip PolarFire:** LSRAM, uSRAM, MACC, CCC, SERDES_IF
- **Efinix:** EFX_PLL, EFX_RAM_5K, EFX_DPRAM_5K, EFX_GBUFCE

## False Positive Reduction

| Pattern | False Positive When | Action |
|---|---|---|
| 2FF chain | Inside shift register (3+ stages) | Skip |
| 2FF chain | Both FFs same clock | Skip |
| FIFO signals | Inside module named `*fifo*` | Skip |
| valid/ready | AXI bus already using IP block | Skip |
| SPI signals | Inside testbench files (tb_*, *_tb.sv) | Skip |
| Vendor primitive | In comments or string literals | Skip |

## Severity Scoring

| Severity | Criteria | Examples |
|---|---|---|
| CRITICAL | Data corruption, metastability | CDC without synchronizer |
| HIGH | Missing module, empty stubs | Instantiated but undefined |
| MEDIUM | Ad-hoc reimplementation | Hand-rolled FIFO, manual 2FF |
| LOW | Style, minor optimization | Vendor primitive with OSS equivalent |
| INFO | Already correct | Verified IP properly used |

## Auto-Suggestion Integration

| Detected Pattern | Suggested Command | Parameters |
|---|---|---|
| Sync FIFO signals | `/gf-ip add fifo_sync` | WIDTH=detected, DEPTH=next_pow2 |
| Async FIFO signals | `/gf-ip add fifo_async` | WIDTH=detected, DEPTH=8 |
| 2FF CDC crossing | `/gf-ip add cdc_2ff` | default |
| Multi-bit CDC handshake | `/gf-ip add cdc_handshake` | WIDTH=detected |
| UART pattern | `/gf-ip add uart` | CLK_FREQ=detected, BAUD=115200 |
| SPI pattern | `/gf-ip add spi_master` | CLK_DIV=computed |
| AXI register pattern | `/gf-ip add axi4lite_slave` | ADDR_WIDTH=detected |
| Button debounce | `/gf-ip add debouncer` | DEBOUNCE_MS=20 |
