# Releases

## 2.4.0 (2026-04-11) — Deep Skill Enrichment

The biggest content update in GateFlow history. Every skill in the plugin has been enriched with research-backed reference material, actionable templates, and structured return formats. 37 files changed, +3,139 lines added.

### Critical Fixes
- Rebuilt stale `gateflow.index` (added 11+ missing skills, removed nonexistent gf-summary)
- Removed hardcoded "Sonnet" model reference from gf-architect (now inherits session model)
- Inlined missing gf-errors 3-layer translation protocol into gf/SKILL.md
- Fixed dead routing targets in gf-router (gf-synth -> gateflow:sv-synth agent, gf-boards -> command)
- Deduplicated CLAUDE.md content (~3K tokens saved per session)

### Skill Enrichment — Verification & Synthesis (7 skills)
- **gf-formal**: SVA property patterns (overflow, handshake, one-hot, liveness, reset, FIFO), SymbiYosys .sby templates (BMC/prove/cover/multi-task), proof strategy decision tree, engine comparison, counterexample interpretation guide, 4 reference files
- **gf-cocotb**: FIFO/handshake/FSM test templates, multi-simulator Makefile, pytest runner, cocotbext protocol libraries (AXI/Wishbone/SPI/UART), Cocotb vs SV decision matrix, GATEFLOW-RESULT format
- **gf-pcb**: Full KiCad CLI reference (DRC/ERC/BOM/gerbers/drill/STEP), DRC/ERC error interpretation tables, AI review checklist (decoupling/power/high-speed/thermal/manufacturing), confidence scoring framework, manufacturing package script
- **gf-pnr**: Complete nextpnr flag reference (iCE40/ECP5/Gowin), full bitstream pipelines, timing analysis (Fmax/slack/critical path), utilization thresholds, common failures and fixes, constraint file format templates (PCF/LPF/CST)
- **gf-fusesoc**: Complete CAPI=2 .core schema with multi-target configs, file type reference, dependency management with version operators, FuseSoC CLI commands, tool backend options
- **gf-lint**: 20+ Verilator v5 new warning codes, warning suppression (inline + control file), SARIF machine-readable output, error message format and exit codes
- **gf-sim**: Verilator v5 multi-threaded simulation, FST vs VCD tracing, SVA assertion support, code coverage flags, SV construct support matrix, timeout patterns

### Skill Enrichment — Orchestration (4 skills)
- **gf**: Verilator/Yosys error dictionary (20 patterns with plain-English translations and fixes)
- **gf-router**: Context-dependent routing with confidence boosts, multi-intent detection for compound queries, adaptive confidence calibration formula
- **gf-expand**: Question templates for formal verification, synthesis, board targeting, protocol choice; quick-start defaults per scenario; follow-up decision trees
- **gf-build**: Kahn's algorithm for optimal parallel phase assignment, resource contention prevention rules, SHA256-based incremental build with dependency-aware cache invalidation, progress visualization

### Skill Enrichment — Architecture & Visualization (2 skills)
- **gf-architect**: Verilator v5 JSON AST mode for accurate mapping, RTL complexity metrics (cyclomatic + composite scoring), cross-module signal tracing algorithm, diff-aware mapping with CHANGES.md output, Mermaid dependency graph generation
- **gf-viz**: Signal path trace view, ASCII timing diagrams, structural diff view, port connection matrix, search functionality (find modules by clock/FSM/ports, signals by glob, unconnected ports, CDC crossings)

### Skill Enrichment — Learning & Verification Practices (3 skills)
- **gf-learn**: 5 new topic categories (arbiter, memory, protocol, verification, optimization), difficulty scaling algorithm with cross-topic transfer, 4-tier grading rubric with automated checks, progress persistence in JSON, challenge mode with timed scoring
- **gf-learn-ctx**: 15 new concept library entries (pipeline, backpressure, clock gating, Gray code, arbitration, DMA, etc.), cross-reference linking to IP blocks and skills, spaced repetition algorithm, 5 orchestration integration hooks
- **tb-best-practices**: UVM-lite compatibility for Verilator v5, complete Cocotb equivalents for every SV TB pattern, 4-phase coverage closure checklist, 10 common TB anti-patterns with fixes, simulation performance optimization guide

### Skill Enrichment — IP & Protocols (3 skills)
- **gf-protocols**: Actual scaffold code for AXI4-Lite slave, SPI master, UART TX, and I2C master (was empty stub with zero code), GATEFLOW-RESULT format
- **gf-ip**: Instantiation examples for all 8 IP blocks, IP block comparison/decision table, GATEFLOW-RESULT format for IP operations
- **gf-ip-detect**: Extended vendor IP detection (Xilinx UltraScale+, Intel Agilex, Microchip PolarFire, Efinix), false positive reduction rules, 5-level severity scoring, auto-suggestion integration mapping patterns to `/gf-ip add` commands

### Skill Enrichment — Hardware & Planning (3 skills)
- **gf-pinmap**: GATEFLOW-RESULT format, I/O standard reference table (LVCMOS33 through TMDS_33), 6 common pin mapping mistakes, PMOD connector mapping patterns (Type 2/3/6)
- **gf-project**: GATEFLOW-RESULT format, extended project.yaml schema (simulation/synthesis/verification/CI sections), project templates (iCE40/ECP5/sim-only/multi-board), health check validation
- **gf-plan**: Power estimation with activity factors and clock gating candidates, area estimation per RTL construct, latency budget rules, risk assessment template with severity matrix

### README
- Complete rewrite with bold builder voice showing full scope (20 agents, 25 skills, 19 commands, 8 IP blocks, 4 boards)
- Added v2.4.0 update SVG graphic

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

