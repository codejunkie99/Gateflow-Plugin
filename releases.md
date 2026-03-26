# Releases

## 2.3.0 (2026-03-27) — Quality Pass + Missing Features

### Fixes
- Expanded 5 IP block READMEs from stubs to full docs with instantiation examples
- Added ports to 5 block.yaml files (axi4lite_slave, cdc_handshake, fifo_async, spi_master, uart)
- Added 4 missing protocol references (UART, Wishbone, AXI4-Full, AXI-Stream)
- Expanded Basys 3 constraints (all 16 LEDs, 16 switches, 7-segment display)
- Expanded Tang Nano 9K constraints (UART, SPI flash pins)
- Updated CLAUDE.md title to 'Open-Source Hardware Development Platform'
- Updated AGENTS.md with all 18 agents
- Updated orchestrator routing table with Phase 3-4 agents
- Updated /gf-doctor with tiered tool display (Core/Formal/Synth/P&R/VHDL/PCB)
- Removed empty gf-learn-v2 directory

### New Commands
- /gf-pcb — Generate KiCad schematic/PCB
- /gf-pinmap — Generate pin constraint files
- /gf-cocotb — Generate Python Cocotb testbenches
- /gf-fusesoc — Generate FuseSoC .core files

## 2.2.1 (2026-03-26) — IP Auto-Detection & Auto-Fill

### New Features
- **IP auto-detection** (`/gf-detect`): Scans codebases for missing module implementations, stub modules, and standard IP patterns
- **Auto-fill**: Detects gaps and dispatches agents to implement using verified IP library blocks
- **CDC violation scanning**: Identifies clock domain crossings without synchronizers (CRITICAL severity)
- **Pattern matching**: Recognizes FIFO, CDC, UART, SPI, AXI patterns in ad-hoc code and suggests verified replacements
- **Sub-agent capability**: sv-ip-scanner works as a skill other agents can invoke mid-task

### New Agent
- `sv-ip-scanner` — IP block detection and auto-fill agent

### New Command
- `/gf-detect` — Scan for missing IP, stubs, CDC issues (`--auto-fill` to implement)

## 2.2.0 (2026-03-26) — Community + KiCad + Ecosystem

### New Features
- **KiCad schematic/PCB generation** (`/gf-pcb`): AI-verified draft designs with DRC/ERC/AI review loop, confidence scoring, mandatory disclaimers
- **Cocotb support** (`gf-cocotb`): Python-based testbench generation as alternative to SystemVerilog TBs
- **FuseSoC integration** (`gf-fusesoc`): .core file generation with Edalize backends (Vivado, Quartus, Yosys)
- **CI/CD templates**: GitHub Actions and GitLab CI pipelines for lint → sim → formal → synthesis
- **Contextual learning**: Micro-lessons embedded in workflow output, concept tracking, generative exercises
- **Ecosystem integrations**: F4PGA (Xilinx 7-series open-source), OpenFPGA (custom architectures), OpenLane (ASIC tapeout)

### New Agent
- `pcb-designer` — KiCad schematic and PCB with self-improving verification

### Community
- Board contribution guide with verification checklist
- IP block contribution guide with verification pipeline
- CI/CD templates for hardware projects

## 2.1.0 (2026-03-26) — Multi-HDL + Platform + Pin Mapping

### New Features
- **VHDL support**: vhdl-codegen and vhdl-testbench agents for GHDL-compatible VHDL-2008
- **Pin mapping** (`/gf-pinmap`): Board-aware constraint file generation with safety checks
- **Place & Route** (`/gf-pnr`): nextpnr integration for iCE40/ECP5/Gowin
- **FPGA Flash** (`/gf-flash`): openFPGALoader programming
- **Protocol scaffolding**: AXI4-Lite, SPI, I2C, AXI4-Full, AXI-Stream, Wishbone references
- **OpenClaw integration**: Published as ClawHub skill for autonomous hardware design
- **Platform index**: Integration guides for 7 AI coding platforms + OpenClaw

### New Agents
- `vhdl-codegen` — VHDL entity/architecture generation
- `vhdl-testbench` — VHDL testbench with GHDL compatibility
- `sv-pinmap` — Pin assignment with safety rules

### New Commands
- `/gf-pnr` — Place & route with nextpnr
- `/gf-flash` — Flash FPGA via openFPGALoader

## 2.0.0 (2026-03-26) — Formal Verification + Synthesis + IP Library

### New Features
- **Formal verification from natural language** (`/gf-formal`): Describe what to prove in English, get SVA properties + SymbiYosys proofs. The killer feature.
- **Yosys synthesis** (`/gf-synth`): Synthesize designs with area/timing reports (LUTs, FFs, BRAM, DSP). Warns about unsupported SV constructs before failing.
- **IP block library** (`/gf-ip`): 8 verified, drop-in hardware components — each with RTL, self-checking testbench, formal properties, and documentation.
- **Curated board database** (`/gf-boards`): Pin assignments for Arty A7, Basys 3, iCEBreaker, Tang Nano 9K with full constraint files (.xdc/.pcf/.cst).

### IP Blocks Included
- `fifo_sync` — Synchronous FIFO (parameterized width/depth)
- `fifo_async` — Async FIFO with Gray code pointers (CDC)
- `cdc_2ff` — 2-flip-flop synchronizer
- `cdc_handshake` — Multi-bit handshake synchronizer
- `uart` — UART TX+RX with configurable baud rate
- `spi_master` — SPI master (all 4 CPOL/CPHA modes)
- `axi4lite_slave` — AXI4-Lite register slave with byte strobes
- `debouncer` — Button debouncer with edge detection

### New Agents
- `sv-formal` — Formal verification specialist (SVA + SymbiYosys)
- `sv-synth` — Synthesis optimization specialist (Yosys)

### New Commands
- `/gf-formal` — Run formal verification
- `/gf-ip` — Manage IP block library (add/list/info)
- `/gf-boards` — Query board pinouts and details

## 1.6.0 (2026-03-26)

- Sync all version strings to 1.6.0 across plugin.json and marketplace.json.
- Confirm BSL-1.1 license consistency across plugin and root.

## 1.5.3 (2026-02-18)

- Replace prompt-based PostToolUse hook with a deterministic Python script for reliable lint nudges.

## 1.5.2 (2026-02-15)

- Fix Stop hook JSON validation failures by replacing the prompt-based Stop hook with a deterministic command hook (`stop-hook.sh`).
- Bump plugin version to 1.5.2.

## 1.5.1 (2025-02-12)

- Prompt-based hooks: PreToolUse (SV file safety), PostToolUse (lint nudge), Stop (smart completion gate).

