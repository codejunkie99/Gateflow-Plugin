# GateFlow Integrations

Guides for using GateFlow across different platforms and ecosystems.

## AI Coding Platforms

| Platform | Support Level | Guide |
|----------|-------------|-------|
| Claude Code | Full (native plugin) | Built-in |
| OpenCode | MCP + Skills | See README Cross-Tool section |
| Cursor | Rules + Skills | See README Cross-Tool section |
| Cline | Rules | See README Cross-Tool section |
| Windsurf | Rules + Workflows | See README Cross-Tool section |
| Codex CLI | Skills | See README Cross-Tool section |
| Copilot CLI | Instructions | See README Cross-Tool section |

## AI Agent Frameworks

| Framework | Integration | Guide |
|-----------|------------|-------|
| OpenClaw | ClawHub skill via MCP | [openclaw.md](openclaw.md) |

## Hardware Ecosystem

| Tool | Integration | Status |
|------|------------|--------|
| openFPGALoader | `/gf-flash` command | Included |
| Yosys | `/gf-synth` skill | Included |
| nextpnr | `/gf-pnr` skill | Included |
| SymbiYosys | `/gf-formal` skill | Included |
| GHDL | VHDL simulation/synthesis | Phase 3 |
| Icarus Verilog | Verilog simulation | Phase 3 |
| F4PGA | Alternative FPGA toolchain | Phase 4 |
| OpenFPGA | Custom FPGA architectures | Phase 4 |
| OpenLane | ASIC tapeout (SKY130/GF180) | Phase 5 |
| KiCad | Schematic/PCB generation | Phase 4 |
| Cocotb | Python testbenches | Phase 4 |
| FuseSoC | Build system integration | Phase 4 |
