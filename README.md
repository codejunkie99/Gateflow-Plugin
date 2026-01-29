# GateFlow Plugin for Claude Code
> AI-powered SystemVerilog development assistant — lint, generate, simulate, and debug HDL code with natural language.

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Claude Code Plugin](https://img.shields.io/badge/Claude%20Code-Plugin-purple.svg)](https://claude.ai/claude-code)

<img width="1619" height="787" alt="image" src="https://github.com/user-attachments/assets/f53240b4-5704-4c5a-8e0e-5d65546a0ad1" />

---

## What is GateFlow?

GateFlow brings professional SystemVerilog tooling to Claude Code. Ask questions about your RTL, generate modules with best practices, auto-fix lint errors, and analyze simulation waveforms — all through natural conversation.

**Perfect for:**
- FPGA/ASIC engineers wanting AI-assisted RTL development
- Verification engineers creating testbenches
- Students learning SystemVerilog
- Anyone tired of manually fixing width mismatches

---

## Why GateFlow?

**Loving hardware doesn't have to be gatekept.**

GateFlow was built with love to break down the barriers that keep people away from hardware design. Whether you're writing your first line of SystemVerilog or getting back into it after years away, we believe the tools should help you — not fight you.

No more cryptic error messages. No more hunting through documentation for the right syntax. Just describe what you want to build, and let's make it happen together.

We can't wait to see what you create. ❤️

---

## Quick Start

### One-Line Install (macOS/Linux)

```bash
curl -fsSL https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin-/main/install.sh | bash
```

This automatically installs Verilator (if missing) and sets up the plugin.

### Manual Installation

#### Prerequisites

| Tool | Required | macOS | Linux |
|------|----------|-------|-------|
| [Claude Code](https://claude.ai/claude-code) | Yes | See website | See website |
| [Node.js](https://nodejs.org/) >= 18 | Yes | `brew install node` or [nvm](https://github.com/nvm-sh/nvm) | `sudo apt install nodejs npm` or [nvm](https://github.com/nvm-sh/nvm) |
| [Verilator](https://verilator.org/) | Yes | `brew install verilator` | `sudo apt install verilator` |
| Verible | Optional | `brew install verible` | See [releases](https://github.com/chipsalliance/verible/releases) |
| Slang | Optional | Build from source | Build from source |

#### Steps

```bash
# 1. Clone the plugin
git clone https://github.com/codejunkie99/Gateflow-Plugin-.git
cd Gateflow-Plugin-

# 2. Build the MCP server
cd servers/gateflow-mcp
npm install
npm run build
cd ../..

# 3. Run Claude Code with the plugin
claude --plugin-dir $(pwd)
```

### Verify Installation

```bash
# Inside Claude Code, run:
/gf-doctor
```

You should see:
```
GateFlow Environment Check
==========================
[OK] Verilator 5.x
[OK] Node.js v20.x
[OK] Plugin loaded
```

---

## Usage

### Slash Commands

| Command | Description | Example |
|---------|-------------|---------|
| `/gf-scan` | Index your project | `/gf-scan` |
| `/gf-lint` | Check for errors | `/gf-lint src/*.sv` |
| `/gf-fix` | Auto-fix lint errors | `/gf-fix counter.sv` |
| `/gf-gen` | Generate code | `/gf-gen module alu` |
| `/gf-wave` | Analyze waveforms | `/gf-wave sim.vcd` |
| `/gf-doctor` | Check environment | `/gf-doctor` |

### Natural Language (Just Ask)

GateFlow understands context. Just describe what you need:

```
"Create a parameterized FIFO with configurable depth"

"Why is Verilator complaining about line 42?"

"Write a testbench for the counter module"

"Explain how the state machine in fsm.sv works"

"Modernize this Verilog-95 code to SystemVerilog"
```

### Example Session

```
$ claude --plugin-dir /path/to/Gateflow-Plugin-

You: /gf-scan
Claude: Found 8 modules, 2 packages in ./src

You: /gf-lint
Claude:
  counter.sv:15 - Width mismatch (8 vs 16 bits)
  fsm.sv:42 - Inferred latch for 'state_next'

You: Fix all the lint errors
Claude: [Analyzes code, applies fixes]
  ✓ counter.sv - Added explicit width cast
  ✓ fsm.sv - Added default assignment
  All errors fixed.

You: Generate a testbench for counter
Claude: [Creates tb_counter.sv with clock, reset, stimulus]
```

---

## Features

### 🔍 Smart Analysis
- Understand module hierarchy and dependencies
- Trace signal paths through your design
- Identify FSMs, pipelines, and common patterns

### 🛠 Auto-Fix
- Fix width mismatches automatically
- Resolve inferred latches
- Clean up unused signals
- Iterative fixing until lint-clean

### ⚡ Code Generation
- Generate synthesizable modules with best practices
- Create comprehensive testbenches
- Scaffold packages with types and utilities

### 📊 Waveform Analysis
- Parse VCD files from simulation
- Detect clock frequencies
- Identify timing anomalies
- Trace signal behavior

---

## Available Tools (MCP)

The plugin exposes 20+ tools that Claude can use:

| Category | Tools |
|----------|-------|
| **File Ops** | `gf_read_file`, `gf_write_file`, `gf_edit_lines`, `gf_search_code` |
| **Analysis** | `gf_find_module`, `gf_get_dependencies`, `gf_lint_file`, `gf_get_project_stats` |
| **Simulation** | `gf_run_simulation`, `gf_analyze_waveform`, `gf_find_vcd_files` |
| **Setup** | `gf_check_tool_status`, `gf_setup_verible`, `gf_setup_slang` |

---

## Project Structure

```
Gateflow-Plugin-/
├── .claude-plugin/
│   └── plugin.json          # Plugin manifest
├── commands/                 # Slash commands (/gf-*)
├── agents/                   # Specialized AI agents
├── skills/                   # Auto-activating knowledge
├── hooks/                    # Automation hooks
├── servers/
│   └── gateflow-mcp/        # MCP tool server
└── README.md
```

---

## Configuration (Optional)

Create `.claude/gateflow.local.md` in your project:

```yaml
---
verilator_flags: ["-Wall", "-Wno-UNUSED"]
auto_lint: true
---

# Project-specific notes
- Top module: chip_top
- Clock: 100MHz
```

---

## Troubleshooting

### "Verilator not found"
```bash
# Check if installed
verilator --version

# Install if missing
brew install verilator      # macOS
sudo apt install verilator  # Linux (Debian/Ubuntu)
```

### "MCP server not responding"
```bash
# Rebuild the server
cd servers/gateflow-mcp
npm run build
```

### "Plugin not loading"
```bash
# Verify plugin structure
ls -la .claude-plugin/plugin.json  # Should exist

# Run with debug
claude --plugin-dir /path/to/plugin --debug
```

---

## Contributing

Contributions welcome! Please read our contributing guidelines before submitting PRs.

---

## License

MIT License - see [LICENSE](LICENSE) for details.

---

## Links

- [Claude Code Documentation](https://docs.anthropic.com/claude-code)
- [Verilator](https://verilator.org/)
- [SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595)

---

<p align="center">
  <b>Built for hardware engineers who want to move faster.</b>
</p>
