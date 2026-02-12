# GateFlow Plugin for Claude Code
> AI-powered SystemVerilog development assistant — design, verify, debug, and deliver working RTL with natural language.

[![GitHub Stars](https://img.shields.io/github/stars/codejunkie99/Gateflow-Plugin?style=social)](https://github.com/codejunkie99/Gateflow-Plugin/stargazers)
[![Version](https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcodejunkie99%2FGateflow-Plugin%2Fmain%2Fplugins%2Fgateflow%2F.claude-plugin%2Fplugin.json&query=%24.version&label=version&color=blue)](https://github.com/codejunkie99/Gateflow-Plugin/releases)
[![License: BSL-1.1](https://img.shields.io/badge/License-BSL%201.1-orange.svg)](LICENSE)
[![Claude Code Plugin](https://img.shields.io/badge/Claude%20Code-Plugin-purple.svg)](https://code.claude.com/)

<img width="1619" height="787" alt="image" src="https://github.com/user-attachments/assets/f53240b4-5704-4c5a-8e0e-5d65546a0ad1" />

---
## Table of Contents

| Start Here | Reference |
|------------|-----------|
| [What is GateFlow?](#what-is-gateflow) | [Skills Directory](#skills-directory) |
| [Why GateFlow?](#why-gateflow) | [Agents Directory](#agents-directory) |
| [Repo Navigation](#repo-navigation) | [Features](#features) |
| [Quick Start](#quick-start) | [Project Structure](#project-structure) |
| [Updating GateFlow](#updating-gateflow) | [Configuration (Optional)](#configuration-optional) |
| [Usage](#usage) | [Troubleshooting](#troubleshooting) |
| [Contributing](#contributing) | [License](#license) |
| [Links](#links) | [Updates](#updates) |

---

## Updates

| Version | Date | What Changed |
|---------|------|-------------|
| **1.5.1** | 2025-02-12 | Prompt-based hooks for PreToolUse (SV file safety), PostToolUse (lint nudge), Stop (smart completion gate) |
| **1.5.0** | 2025-02-11 | Terminal visualization with `/gf-viz` skill and `sv-viz` agent |
| **1.4.4** | 2025-02-11 | Individual component downloads, cross-tool install instructions (Codex, Cursor, Copilot, Cline, Windsurf) |
| **1.4.3** | 2025-02-10 | Split `gf-plan` references, validation fixes, docs improvements |

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

## Repo Navigation

Use these two dedicated spaces to quickly find what you need:

| Area | Purpose | Path |
|------|---------|------|
| Skills Space | Auto-activating workflows and orchestration logic | [`skills/`](skills) |
| Agents Space | Specialized SystemVerilog agent instructions | [`agents/`](agents) |

Top-level `skills/` and `agents/` are mirrored to the plugin source files for easier discovery.

Fast links:
- [Skills Directory](#skills-directory)
- [Agents Directory](#agents-directory)
- [Project Structure](#project-structure)

---

## Quick Start

### Installation

**Option 1: One-command install (recommended)**
```bash
claude plugin marketplace add codejunkie99/Gateflow-Plugin
claude plugin install gateflow
```

**Option 2: Clone and run directly**
```bash
git clone https://github.com/codejunkie99/Gateflow-Plugin.git
claude --plugin-dir ./Gateflow-Plugin/plugins/gateflow
```

**Option 3: Add to settings (persistent)**
```bash
# Clone to a permanent location
git clone https://github.com/codejunkie99/Gateflow-Plugin.git ~/.claude-plugins/gateflow-marketplace
```

Then add to `~/.claude/settings.json` (global) or `.claude/settings.json` (project):
```json
{
  "plugins": [
    "~/.claude-plugins/gateflow-marketplace/plugins/gateflow"
  ]
}
```

### Prerequisites

| Tool | Required | macOS | Linux |
|------|----------|-------|-------|
| [Claude Code](https://code.claude.com/) | Yes | See website | See website |
| [Verilator](https://verilator.org/) | Yes | `brew install verilator` | `sudo apt install verilator` |
| Verible (formatting/syntax) | Optional | `brew tap chipsalliance/verible && brew install verible` | See [releases](https://github.com/chipsalliance/verible/releases) |

### Verify Installation

```bash
# Inside Claude Code, run:
/gf-doctor
```

---

## Updating GateFlow

**Marketplace install (recommended):**

1) Open `/plugin`  
2) Marketplaces → select `gateflow` → **Update**  
3) Installed → select `gateflow` → **Mark for update** → **Update now**  
4) Restart Claude Code to reload the plugin

**Local/dev install:**

- `git pull` in your plugin folder, then restart Claude Code

---

## Individual Component Downloads

Don't need the full plugin? Grab just the skills, agents, or commands you want.

### How It Works

Each component is a standalone `.md` file. Download it and drop it into your own plugin's directory:

```
your-plugin/
├── .claude-plugin/
│   └── plugin.json
├── agents/          ← drop agent .md files here
├── commands/        ← drop command .md files here
└── skills/
    └── skill-name/  ← drop SKILL.md files here
        └── SKILL.md
```

### Skills

| Skill | Description | Download |
|-------|-------------|----------|
| `gf` | Main orchestrator — plan-first, parallel build, verify until working | [SKILL.md](plugins/gateflow/skills/gf/SKILL.md) |
| `gf-plan` | Comprehensive RTL implementation planning with diagrams | [SKILL.md](plugins/gateflow/skills/gf-plan/SKILL.md) |
| `gf-build` | Parallel component build orchestration | [SKILL.md](plugins/gateflow/skills/gf-build/SKILL.md) |
| `gf-architect` | Codebase map with hierarchy, FSMs, clocks, CDC | [SKILL.md](plugins/gateflow/skills/gf-architect/SKILL.md) |
| `gf-lint` | Structured Verilator lint checking | [SKILL.md](plugins/gateflow/skills/gf-lint/SKILL.md) |
| `gf-sim` | Structured simulation with auto DUT/TB detection | [SKILL.md](plugins/gateflow/skills/gf-sim/SKILL.md) |
| `gf-learn` | Learning mode — generates exercises, reviews solutions | [SKILL.md](plugins/gateflow/skills/gf-learn/SKILL.md) |
| `gf-router` | Intent classification and expand mode orchestration | [SKILL.md](plugins/gateflow/skills/gf-router/SKILL.md) |
| `gf-expand` | Clarifying questions with trade-offs before handoff | [SKILL.md](plugins/gateflow/skills/gf-expand/SKILL.md) |
| `gf-summary` | Summarize Verilator/lint output in readable format | [SKILL.md](plugins/gateflow/skills/gf-summary/SKILL.md) |
| `tb-best-practices` | Testbench best practices reference | [SKILL.md](plugins/gateflow/skills/tb-best-practices/SKILL.md) |

### Agents

| Agent | Expertise | Download |
|-------|-----------|----------|
| `sv-codegen` | RTL architect — creates synthesizable modules | [sv-codegen.md](plugins/gateflow/agents/sv-codegen.md) |
| `sv-testbench` | Verification engineer — testbenches and stimulus | [sv-testbench.md](plugins/gateflow/agents/sv-testbench.md) |
| `sv-debug` | Debug specialist — simulation failures, X-values | [sv-debug.md](plugins/gateflow/agents/sv-debug.md) |
| `sv-verification` | Verification methodologist — SVA, coverage, formal | [sv-verification.md](plugins/gateflow/agents/sv-verification.md) |
| `sv-understanding` | RTL analyst — explains and documents code | [sv-understanding.md](plugins/gateflow/agents/sv-understanding.md) |
| `sv-planner` | Architecture planner — design plans and diagrams | [sv-planner.md](plugins/gateflow/agents/sv-planner.md) |
| `sv-orchestrator` | Parallel builder — multi-component designs | [sv-orchestrator.md](plugins/gateflow/agents/sv-orchestrator.md) |
| `sv-refactor` | Code quality — lint fixes, cleanup, optimization | [sv-refactor.md](plugins/gateflow/agents/sv-refactor.md) |
| `sv-developer` | Full-stack RTL — complex multi-file features | [sv-developer.md](plugins/gateflow/agents/sv-developer.md) |
| `sv-tutor` | Teacher — reviews solutions, gives hints, teaches | [sv-tutor.md](plugins/gateflow/agents/sv-tutor.md) |

### Commands

| Command | Description | Download |
|---------|-------------|----------|
| `/gf-doctor` | Environment check | [gf-doctor.md](plugins/gateflow/commands/gf-doctor.md) |
| `/gf-scan` | Index project | [gf-scan.md](plugins/gateflow/commands/gf-scan.md) |
| `/gf-map` | Map codebase | [gf-map.md](plugins/gateflow/commands/gf-map.md) |
| `/gf-lint` | Run lint | [gf-lint.md](plugins/gateflow/commands/gf-lint.md) |
| `/gf-fix` | Fix lint | [gf-fix.md](plugins/gateflow/commands/gf-fix.md) |
| `/gf-gen` | Generate scaffolds | [gf-gen.md](plugins/gateflow/commands/gf-gen.md) |
| `/gf-sim` | Run simulation | [gf-sim.md](plugins/gateflow/commands/gf-sim.md) |

### Quick Download via curl

```bash
# Example: download just the sv-codegen agent
curl -O https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md

# Example: download just the gf-plan skill
mkdir -p skills/gf-plan
curl -o skills/gf-plan/SKILL.md https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-plan/SKILL.md

# Example: download a command
curl -O https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/commands/gf-lint.md
```

> **Note:** Some skills (like `gf-plan`) include reference files in a `references/` subdirectory. For full functionality, download the entire skill folder.

### Using GateFlow Components in Other Tools

GateFlow's skills and agents are plain Markdown files — they work across multiple AI coding tools, not just Claude Code. Here's how to use them in each:

#### OpenAI Codex CLI

Codex uses the same `SKILL.md` format. Drop skills directly into the Codex skills folder:

```bash
# Install a skill for Codex
mkdir -p ~/.codex/skills/gf-plan
curl -o ~/.codex/skills/gf-plan/SKILL.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-plan/SKILL.md

# Or at repo level
mkdir -p .agents/skills/gf-lint
curl -o .agents/skills/gf-lint/SKILL.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-lint/SKILL.md
```

Codex scans these directories (by precedence):
| Location | Scope |
|----------|-------|
| `.agents/skills/` | Current repo |
| `~/.codex/skills/` | User-global |
| `/etc/codex/skills/` | System-wide |

Restart Codex after adding new skills. You can also use the built-in installer:
```
$skill-installer install gf-plan from codejunkie99/Gateflow-Plugin
```

#### Cursor

Use agent files as custom instructions or drop them into your rules:

```bash
# Copy an agent's content into .cursorrules
curl -s https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md \
  >> .cursorrules

# Or use as a Cursor custom agent mode instruction
# Settings → Agent Modes → Add Custom Mode → paste agent content
```

#### GitHub Copilot CLI

Add agent content as custom instructions:

```bash
# Add to repo-level Copilot instructions
mkdir -p .github
curl -s https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md \
  >> .github/copilot-instructions.md
```

#### Cline

```bash
# Add to project-level rules
curl -s https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md \
  >> .clinerules
```

#### Windsurf

```bash
# Add as a Windsurf rule
mkdir -p .windsurf/rules
curl -o .windsurf/rules/sv-codegen.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md

# Or add as a workflow
mkdir -p .windsurf/workflows
curl -o .windsurf/workflows/gf-plan.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-plan/SKILL.md
```

#### Quick Reference

| Tool | Where to Put Files | Format |
|------|-------------------|--------|
| **Claude Code** | Plugin `skills/`, `agents/`, `commands/` dirs | Native (SKILL.md, agent .md) |
| **Codex CLI** | `~/.codex/skills/` or `.agents/skills/` | SKILL.md (same format) |
| **Cursor** | `.cursorrules` or custom agent mode | Append to rules file |
| **Copilot CLI** | `.github/copilot-instructions.md` | Append to instructions |
| **Cline** | `.clinerules` or MCP config | Append to rules file |
| **Windsurf** | `.windsurf/rules/` or `.windsurf/workflows/` | Individual .md files |

---

## Usage

### Skills (Auto-Activating)

Skills activate automatically based on context. Just ask naturally:

| Skill | Trigger | What It Does |
|-------|---------|--------------|
| `/gf` | Any SV task | **Main orchestrator** — plan-first, parallel build, verify until working |
| `/gf-plan` | "plan", "design", "architect" | Creates comprehensive RTL implementation plans with diagrams |
| `/gf-build` | "build", "multi-component", "SoC" | Parallel component build orchestration |
| `/gf-architect` | "map codebase", "analyze project" | Generates codebase map with hierarchy, FSMs, clocks, CDC |

By default, `/gf` uses parallel builds after planning. If you want a sequential flow, say "single-threaded" or "sequential build."

### Commands (Slash Commands)

| Command | Description |
|---------|-------------|
| `/gf-scan` | Index project |
| `/gf-map` | Map codebase |
| `/gf-lint` | Run lint |
| `/gf-fix` | Fix lint |
| `/gf-gen` | Generate scaffolds |
| `/gf-sim` | Run sim |
| `/gf-doctor` | Env check |

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
$ claude --plugin-dir ./Gateflow-Plugin/plugins/gateflow

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

## Skills Directory

The skills below are available at `skills/` (mirrored from `plugins/gateflow/skills/`).

| Skill | Path | Purpose |
|-------|------|---------|
| `gf` | `skills/gf/SKILL.md` | Main orchestrator and execution flow |
| `gf-architect` | `skills/gf-architect/SKILL.md` | Codebase mapping and architecture analysis |
| `gf-build` | `skills/gf-build/SKILL.md` | Multi-component build orchestration |
| `gf-expand` | `skills/gf-expand/SKILL.md` | Expand and flesh out design artifacts |
| `gf-learn` | `skills/gf-learn/SKILL.md` | Learning and explanation workflows |
| `gf-lint` | `skills/gf-lint/SKILL.md` | Lint-first fix workflows |
| `gf-plan` | `skills/gf-plan/SKILL.md` | Design planning with implementation phases |
| `gf-router` | `skills/gf-router/SKILL.md` | Request classification and routing |
| `gf-sim` | `skills/gf-sim/SKILL.md` | Simulation workflows |
| `gf-summary` | `skills/gf-summary/SKILL.md` | Summarization and reporting |
| `gf-viz` | `skills/gf-viz/SKILL.md` | Terminal visualization of RTL architecture |
| `tb-best-practices` | `skills/tb-best-practices/SKILL.md` | Testbench conventions and best practices |

## Agents Directory

The agents below are available at `agents/` (mirrored from `plugins/gateflow/agents/`).

| Agent | Path | Focus |
|-------|------|-------|
| `sv-codegen` | `agents/sv-codegen.md` | Generate RTL modules and architecture skeletons |
| `sv-debug` | `agents/sv-debug.md` | Debug simulation failures and root-cause issues |
| `sv-developer` | `agents/sv-developer.md` | End-to-end multi-file RTL implementation |
| `sv-orchestrator` | `agents/sv-orchestrator.md` | Coordinate parallel agent workflows |
| `sv-planner` | `agents/sv-planner.md` | Plan architecture and phased implementation |
| `sv-refactor` | `agents/sv-refactor.md` | Cleanup, modernization, and lint-driven refactors |
| `sv-testbench` | `agents/sv-testbench.md` | Build testbenches, stimuli, and checks |
| `sv-tutor` | `agents/sv-tutor.md` | Explain SystemVerilog concepts and code |
| `sv-understanding` | `agents/sv-understanding.md` | Analyze and explain existing RTL |
| `sv-verification` | `agents/sv-verification.md` | Assertions, coverage, and verification strategy |
| `sv-viz` | `agents/sv-viz.md` | Terminal visualization of RTL architecture diagrams |

Agents are automatically invoked by `/gf` based on request context.

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
- ASCII block diagrams for quick copy/paste
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
│   └── marketplace.json      # Marketplace manifest
├── agents/                   # Top-level mirrored agent entrypoints
│   ├── sv-codegen.md
│   ├── sv-debug.md
│   ├── sv-developer.md
│   ├── sv-orchestrator.md
│   ├── sv-planner.md
│   ├── sv-refactor.md
│   ├── sv-testbench.md
│   ├── sv-tutor.md
│   ├── sv-understanding.md
│   ├── sv-verification.md
│   └── sv-viz.md
├── skills/                   # Top-level mirrored skill entrypoints
│   ├── gf/
│   ├── gf-architect/
│   ├── gf-build/
│   ├── gf-expand/
│   ├── gf-learn/
│   ├── gf-lint/
│   ├── gf-plan/
│   ├── gf-router/
│   ├── gf-sim/
│   ├── gf-summary/
│   ├── gf-viz/
│   └── tb-best-practices/
├── plugins/
│   └── gateflow/             # Main plugin
│       ├── .claude-plugin/
│       │   └── plugin.json   # Plugin manifest
│       ├── agents/           # Specialized AI agents
│       │   ├── sv-codegen.md
│       │   ├── sv-debug.md
│       │   ├── sv-developer.md
│       │   ├── sv-orchestrator.md
│       │   ├── sv-planner.md
│       │   ├── sv-refactor.md
│       │   ├── sv-testbench.md
│       │   ├── sv-tutor.md
│       │   ├── sv-understanding.md
│       │   ├── sv-verification.md
│       │   └── sv-viz.md
│       ├── commands/         # Slash commands
│       │   ├── gf-doctor.md
│       │   ├── gf-scan.md
│       │   ├── gf-map.md
│       │   ├── gf-lint.md
│       │   ├── gf-fix.md
│       │   ├── gf-gen.md
│       │   └── gf-sim.md
│       ├── skills/           # Auto-activating skills
│       │   ├── gf/
│       │   ├── gf-architect/
│       │   ├── gf-build/
│       │   ├── gf-expand/
│       │   ├── gf-learn/
│       │   ├── gf-lint/
│       │   ├── gf-plan/
│       │   ├── gf-router/
│       │   ├── gf-sim/
│       │   ├── gf-summary/
│       │   ├── gf-viz/
│       │   └── tb-best-practices/
│       ├── hooks/            # Automation hooks
│       └── CLAUDE.md         # SystemVerilog reference
├── docs/
│   └── gateflow.index        # Compressed docs index
├── AGENTS.md                 # Docs index for non-Claude agents
├── CLAUDE.md                 # SystemVerilog reference
└── README.md
```

### Agent Compatibility

| File | For |
|------|-----|
| `CLAUDE.md` | Claude Code (primary reference) |
| `AGENTS.md` | Other AI agents (Cursor, Copilot, etc.) |

`AGENTS.md` provides a compressed docs index so non-Claude agents can discover GateFlow's knowledge base.

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
claude --plugin-dir /path/to/Gateflow-Plugin/plugins/gateflow

# Check plugin.json exists
ls /path/to/Gateflow-Plugin/plugins/gateflow/.claude-plugin/plugin.json
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

BSL-1.1 (Business Source License) - see [LICENSE](LICENSE) for details.

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
