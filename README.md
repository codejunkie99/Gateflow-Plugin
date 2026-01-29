# GateFlow Plugin for Claude Code
> AI-powered SystemVerilog development assistant — design, verify, debug, and deliver working RTL with natural language.

[![License: BSL 1.1](https://img.shields.io/badge/License-BSL%201.1-orange.svg)](LICENSE)
[![Claude Code Plugin](https://img.shields.io/badge/Claude%20Code-Plugin-purple.svg)](https://code.claude.com/)

<img width="1619" height="787" alt="image" src="https://github.com/user-attachments/assets/f53240b4-5704-4c5a-8e0e-5d65546a0ad1" />

---

## What is GateFlow?

GateFlow brings professional SystemVerilog tooling to Claude Code. Design RTL modules, generate testbenches, debug simulation failures, and get lint-clean code — all through natural conversation.

**Perfect for:**
- FPGA/ASIC engineers wanting AI-assisted RTL development
- Verification engineers creating testbenches and assertions
- Students learning SystemVerilog
- Anyone who wants working code, not just generated code

---

## Why GateFlow?

**Loving hardware doesn't have to be gatekept.**

GateFlow was built with love to break down the barriers that keep people away from hardware design. Whether you're writing your first line of SystemVerilog or getting back into it after years away, we believe the tools should help you — not fight you.

No more cryptic error messages. No more hunting through documentation for the right syntax. Just describe what you want to build, and let's make it happen together.

**The GateFlow difference:** We don't just generate code — we deliver *working* code. Lint-checked, simulated, verified.

We can't wait to see what you create. ❤️

---

## Quick Start

### Installation

**Option 1: Run directly from GitHub**
```bash
claude --plugin-dir https://github.com/codejunkie99/Gateflow-Plugin
```

**Option 2: Clone locally**
```bash
git clone https://github.com/codejunkie99/Gateflow-Plugin.git
claude --plugin-dir ./Gateflow-Plugin
```

**Option 3: Add to settings (persistent)**

Add to `~/.claude/settings.json` (global) or `.claude/settings.json` (project):
```json
{
  "plugins": [
    "https://github.com/codejunkie99/Gateflow-Plugin"
  ]
}
```

### Prerequisites

| Tool | Required | macOS | Linux |
|------|----------|-------|-------|
| [Claude Code](https://code.claude.com/) | Yes | See website | See website |
| [Verilator](https://verilator.org/) | Yes | `brew install verilator` | `sudo apt install verilator` |
| Verible | Optional | `brew install verible` | See [releases](https://github.com/chipsalliance/verible/releases) |

### Verify Installation

```bash
# Inside Claude Code, run:
/gf-doctor
```

---

## Usage

### Skills (Auto-Activating)

Skills activate automatically based on context. Just ask naturally:

| Skill | Trigger | What It Does |
|-------|---------|--------------|
| `/gf` | Any SV task | **Main orchestrator** — routes to agents, runs verification, iterates until working |
| `/gf-plan` | "plan", "design", "architect" | Creates comprehensive RTL implementation plans with diagrams |
| `/gf-architect` | "map codebase", "analyze project" | Generates codebase map with hierarchy, FSMs, clocks, CDC |

### Commands (Slash Commands)

| Command | Description |
|---------|-------------|
| `/gf-scan` | Index your project structure |
| `/gf-map` | Generate comprehensive codebase map |
| `/gf-lint` | Run lint checks on files |
| `/gf-fix` | Auto-fix lint errors |
| `/gf-gen` | Generate module scaffolds |
| `/gf-sim` | Run simulation |
| `/gf-doctor` | Check environment setup |

### Natural Language (Just Ask)

GateFlow understands context. Describe what you need:

```
"Create a FIFO and test it"
→ Generates FIFO, creates testbench, runs simulation, fixes issues, delivers working code

"Why is my output X?"
→ Analyzes code, traces signal path, identifies root cause

"Plan a DMA controller"
→ Creates detailed design plan with block diagrams, FSMs, interfaces, verification strategy

"Add assertions to check the handshake protocol"
→ Generates SVA properties for valid/ready handshake

"Explain how the FSM in uart_tx.sv works"
→ Analyzes state machine, explains transitions, creates state diagram
```

### Example Session

```
$ claude --plugin-dir https://github.com/codejunkie99/Gateflow-Plugin

You: Create a parameterized counter with enable and test it

Claude: Creating counter module...
✓ Created counter.sv

Running lint check...
✓ Lint clean

Creating testbench...
✓ Created tb_counter.sv

Running simulation...
✓ All tests pass (12 checks)

Done! Created:
- rtl/counter.sv (8-bit parameterized counter with enable)
- tb/tb_counter.sv (Self-checking testbench)
```

---

## Agents

GateFlow includes specialized agents for different tasks:

| Agent | Expertise | Use Case |
|-------|-----------|----------|
| `sv-codegen` | RTL architect | Creating new modules, FSMs, FIFOs, arbiters |
| `sv-testbench` | Verification engineer | Writing testbenches, stimulus, self-checking logic |
| `sv-debug` | Debug specialist | Simulation failures, X-values, timing issues |
| `sv-verification` | Verification methodologist | SVA assertions, coverage, formal properties |
| `sv-understanding` | RTL analyst | Explaining code, tracing signals, architecture docs |
| `sv-refactor` | Code quality engineer | Fixing lint, cleanup, optimization |
| `sv-developer` | Full-stack RTL | Complex multi-file features |

Agents are automatically invoked by the `/gf` orchestrator based on your request.

---

## Features

### 🎯 Working Code, Not Just Generated Code
The `/gf` orchestrator doesn't just generate — it verifies:
```
Create → Lint → Fix → Test → Fix → Deliver
```

### 📐 Hardware Design Planning
`/gf-plan` creates professional design documents:
- Block diagrams (Mermaid)
- Module hierarchy
- Interface specifications
- FSM state diagrams
- Clock domain analysis
- Verification strategy
- Implementation phases

### 🗺️ Codebase Intelligence
`/gf-architect` maps your entire project:
- Module hierarchy and dependencies
- Signal flow analysis
- FSM extraction
- Clock domain crossing detection
- Package and type definitions

### 🔧 Comprehensive Coverage
- **Memory patterns**: FIFOs, dual-port RAM, register files
- **Error handling**: ECC, watchdogs, TMR
- **DFT**: Scan chains, JTAG, BIST
- **Timing closure**: Retiming, pipelining, SDC
- **Verification**: SVA, coverage, formal

---

## Project Structure

```
Gateflow-Plugin/
├── .claude-plugin/
│   └── plugin.json        # Plugin manifest
├── agents/                # Specialized AI agents
│   ├── sv-codegen.md      # RTL generation
│   ├── sv-testbench.md    # Testbench creation
│   ├── sv-debug.md        # Debug & analysis
│   ├── sv-verification.md # Assertions & coverage
│   ├── sv-understanding.md# Code explanation
│   ├── sv-refactor.md     # Code cleanup
│   └── sv-developer.md    # Multi-file development
├── commands/              # Slash commands
│   ├── gf-doctor.md       # Environment check
│   ├── gf-scan.md         # Project indexing
│   ├── gf-map.md          # Codebase mapping
│   ├── gf-lint.md         # Lint checking
│   ├── gf-fix.md          # Auto-fix
│   ├── gf-gen.md          # Code generation
│   └── gf-sim.md          # Simulation
├── skills/                # Auto-activating skills
│   ├── gf/                # Main orchestrator
│   ├── gf-plan/           # Design planner
│   └── gf-architect/      # Codebase mapper
├── hooks/                 # Automation hooks
├── CLAUDE.md              # SystemVerilog reference
└── README.md
```

---

## Configuration (Optional)

Create `.claude/gateflow.local.md` in your project for project-specific settings:

```yaml
---
verilator_flags: ["-Wall", "-Wno-UNUSED"]
top_module: chip_top
clock_freq: 100MHz
---

# Project Notes
- Memory mapped registers at 0x1000
- AXI4-Lite interface for config
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

### "Plugin not loading"
```bash
# Verify plugin loads
claude --plugin-dir /path/to/Gateflow-Plugin

# Check plugin.json exists
ls .claude-plugin/plugin.json
```

### "Agent not found"
Make sure you're using the correct agent names with the `gateflow:` prefix when spawning manually:
```
gateflow:sv-codegen
gateflow:sv-testbench
```

---

## Contributing

Contributions welcome! Areas we'd love help with:
- Additional protocol support (AXI4, PCIe, USB)
- More design patterns
- Tool integrations (Yosys, Vivado, Quartus)
- Documentation and examples

---

## License

BSL 1.1 (Business Source License) - see [LICENSE](LICENSE) for details.

**You can:** Use, fork, contribute for non-commercial/personal/educational purposes.
**Commercial use:** Contact us for a license.
**After 2028:** Converts to Apache 2.0.

---

## Links

- [Claude Code Documentation](https://code.claude.com/docs)
- [Verilator](https://verilator.org/)
- [SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595)

---

<p align="center">
  <b>Built for hardware engineers who want to move faster.</b><br>
  <i>Design. Verify. Ship.</i>
</p>
