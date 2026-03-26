---
name: gf-doctor
description: Env check
allowed-tools:
  - Bash
---

# GateFlow Doctor Command

Verify tools and dependencies, organized by capability tier.

## Tiered Tool Display

Show tools grouped by what they unlock:

### Core (RTL + Lint + Sim)
- Verilator: [installed/missing] — `verilator --version`
- Verible: [installed/missing] — `verible-verilog-syntax --version`

### Formal Verification
- SymbiYosys: [installed/missing] — `sby --help`
- z3 solver: [installed/missing] — `z3 --version`

### Synthesis
- Yosys: [installed/missing] — `yosys --version`

### Place & Route + Flash
- nextpnr: [installed/missing] — `nextpnr-ice40 --version` (or ecp5/gowin)
- openFPGALoader: [installed/missing] — `openFPGALoader --version`

### VHDL Support
- GHDL: [installed/missing] — `ghdl --version`

### PCB Design
- KiCad: [installed/missing] — `kicad-cli --version`

### Python Verification
- Cocotb: [installed/missing] — `python3 -c "import cocotb"`

### Build System
- FuseSoC: [installed/missing] — `fusesoc --version`

Only show install instructions for tools in tiers the user has tried to use.
Show a summary: "X/Y tools installed. Run /gf-doctor --all for full list."

## Instructions

Run diagnostic checks for each dependency:

### 1. Verilator (required)
```bash
verilator --version
```
- Required for linting and simulation
- Minimum version: 5.0

### 2. Verible (optional)
```bash
verible-verilog-syntax --version 2>/dev/null || echo "Not installed"
```
- Optional (formatting and syntax checks)

## Report Format

Present a summary table:
| Tool | Status | Version |
|------|--------|---------|
| Verilator | ✅ OK | 5.x |
| Verible (optional) | ✅ OK | v0.0-xxxx |

## Missing Dependencies

If required tools are missing, inform the user they will be auto-installed on next session start (when supported), or they can install manually. If optional tools are missing, note they can be installed manually:

**Manual install (macOS):**
```bash
brew install verilator
brew tap chipsalliance/verible && brew install verible
```

**Manual install (Linux - Debian/Ubuntu):**
```bash
sudo apt-get install verilator
# Verible: download from https://github.com/chipsalliance/verible/releases
```

## Available Commands

After verification, list the available GateFlow commands:
- `/gf-lint` - Run lint
- `/gf-sim` - Run sim
- `/gf-gen` - Generate scaffolds
- `/gf-scan` - Index project
