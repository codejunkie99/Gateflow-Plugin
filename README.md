# GateFlow Plugin for Claude Code

> AI-powered SystemVerilog development assistant — design, verify, debug, and deliver working RTL with natural language.

[![GitHub Stars](https://img.shields.io/github/stars/codejunkie99/Gateflow-Plugin?style=social)](https://github.com/codejunkie99/Gateflow-Plugin/stargazers)
[![Version](https://img.shields.io/badge/dynamic/json?url=https%3A%2F%2Fraw.githubusercontent.com%2Fcodejunkie99%2FGateflow-Plugin%2Fmain%2Fplugins%2Fgateflow%2F.claude-plugin%2Fplugin.json&query=%24.version&label=version&color=blue)](https://github.com/codejunkie99/Gateflow-Plugin/releases)
[![License: BSL-1.1](https://img.shields.io/badge/License-BSL%201.1-orange.svg)](LICENSE)
[![Claude Code Plugin](https://img.shields.io/badge/Claude%20Code-Plugin-purple.svg)](https://code.claude.com/)

<img width="1619" height="787" alt="image" src="https://github.com/user-attachments/assets/f53240b4-5704-4c5a-8e0e-5d65546a0ad1" />

---

**Loving hardware doesn't have to be gatekept.**

GateFlow brings professional SystemVerilog tooling to Claude Code. Describe what you want to build and get lint-checked, simulated, verified code — not just generated code.

Whether you're writing your first `always_ff` or architecting a multi-module SoC, the tools should help you, not fight you.

We can't wait to see what you create. ❤️

---

- [Quick Start](#quick-start) — Install in one command
- [Usage](#usage) — Natural language, skills, and commands
- [Features](#features) — What makes GateFlow different
- [Components](#components) — All skills, agents, and commands
- [Individual Downloads](#individual-downloads) — Grab single components
- [Cross-Tool Compatibility](#cross-tool-compatibility) — Use with Codex, Cursor, Copilot, Cline, Windsurf
- [Configuration](#configuration) — Project-specific settings
- [Project Structure](#project-structure) — Repo layout
- [Troubleshooting](#troubleshooting) — Common issues
- [Updates](#updates) — Changelog
- [Releases](releases.md) — Detailed release notes
- [Contributing](#contributing) | [License](#license) | [Links](#links)

---

## Quick Start

### Install

```bash
# Option 1: Marketplace (recommended)
claude plugin marketplace add codejunkie99/Gateflow-Plugin
claude plugin install gateflow

# Option 2: Clone and run
git clone https://github.com/codejunkie99/Gateflow-Plugin.git
claude --plugin-dir ./Gateflow-Plugin/plugins/gateflow

# Option 3: Persistent (add to ~/.claude/settings.json)
git clone https://github.com/codejunkie99/Gateflow-Plugin.git ~/.claude-plugins/gateflow-marketplace
```

For Option 3, add to `~/.claude/settings.json` or `.claude/settings.json`:
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
| Verible | Optional | `brew tap chipsalliance/verible && brew install verible` | See [releases](https://github.com/chipsalliance/verible/releases) |

### Verify & Update

```bash
# Verify installation
/gf-doctor

# Update (marketplace)
# /plugin → Marketplaces → gateflow → Update → restart Claude Code

# Update (local)
# git pull in your plugin folder, then restart Claude Code
```

---

## Usage

### Just Ask

GateFlow understands context. Describe what you need in plain English:

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

### Skills (Auto-Activating)

Skills activate automatically based on context:

| Skill | Trigger | What It Does |
|-------|---------|--------------|
| `/gf` | Any SV task | **Main orchestrator** — plan-first, parallel build, verify until working |
| `/gf-plan` | "plan", "design", "architect" | RTL implementation plans with ASCII diagrams |
| `/gf-build` | "build", "multi-component", "SoC" | Parallel component build orchestration |
| `/gf-architect` | "map codebase", "analyze project" | Codebase map with hierarchy, FSMs, clocks, CDC |
| `/gf-viz` | "visualize", "show hierarchy" | Terminal ASCII visualization of RTL architecture |
| `/gf-learn` | "teach me", "exercise", "practice" | Learning mode with exercises and feedback |

### Commands

| Command | What It Does |
|---------|-------------|
| `/gf-lint` | Run Verilator lint with structured output |
| `/gf-fix` | Auto-fix lint errors |
| `/gf-sim` | Compile and run simulation |
| `/gf-gen` | Generate module/testbench scaffolds |
| `/gf-scan` | Index project files |
| `/gf-map` | Map codebase architecture |
| `/gf-doctor` | Check environment and dependencies |

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

## Features

### Working Code, Not Just Generated Code
The `/gf` orchestrator doesn't stop at generation — it verifies:
```
Create → Lint → Fix → Test → Fix → Deliver
```

### Hardware Design Planning
`/gf-plan` creates professional design documents:
- Block diagrams (ASCII and Mermaid)
- Module hierarchy and interface specs
- FSM state diagrams
- Clock domain analysis
- Verification strategy and implementation phases

### Codebase Intelligence
`/gf-architect` maps your entire project:
- Module hierarchy and dependencies
- Signal flow analysis and FSM extraction
- Clock domain crossing detection
- Package and type definitions

### Comprehensive Coverage
- **Memory**: FIFOs, dual-port RAM, register files
- **Error handling**: ECC, watchdogs, TMR
- **DFT**: Scan chains, JTAG, BIST
- **Timing**: Retiming, pipelining, SDC
- **Verification**: SVA, coverage, formal

### Smart Hooks
GateFlow watches your workflow and helps proactively:
- **After SV edits** — reminds you to lint
- **Before destructive commands** — warns if you're about to delete SV files
- **On session end** — checks if you forgot to lint or simulate modified files

---

## Components

### Skills (12)

| Skill | Description | Source |
|-------|-------------|--------|
| `gf` | Main orchestrator — plan, build, verify until working | [SKILL.md](plugins/gateflow/skills/gf/SKILL.md) |
| `gf-plan` | RTL implementation planning with diagrams | [SKILL.md](plugins/gateflow/skills/gf-plan/SKILL.md) |
| `gf-build` | Parallel component build orchestration | [SKILL.md](plugins/gateflow/skills/gf-build/SKILL.md) |
| `gf-architect` | Codebase map with hierarchy, FSMs, clocks, CDC | [SKILL.md](plugins/gateflow/skills/gf-architect/SKILL.md) |
| `gf-lint` | Structured Verilator lint checking | [SKILL.md](plugins/gateflow/skills/gf-lint/SKILL.md) |
| `gf-sim` | Simulation with auto DUT/TB detection | [SKILL.md](plugins/gateflow/skills/gf-sim/SKILL.md) |
| `gf-viz` | Terminal visualization of RTL architecture | [SKILL.md](plugins/gateflow/skills/gf-viz/SKILL.md) |
| `gf-learn` | Learning mode — exercises, reviews, hints | [SKILL.md](plugins/gateflow/skills/gf-learn/SKILL.md) |
| `gf-router` | Intent classification and routing | [SKILL.md](plugins/gateflow/skills/gf-router/SKILL.md) |
| `gf-expand` | Clarifying questions with trade-offs | [SKILL.md](plugins/gateflow/skills/gf-expand/SKILL.md) |
| `gf-summary` | Summarize Verilator/lint output | [SKILL.md](plugins/gateflow/skills/gf-summary/SKILL.md) |
| `tb-best-practices` | Testbench best practices reference | [SKILL.md](plugins/gateflow/skills/tb-best-practices/SKILL.md) |

### Agents (11)

| Agent | Expertise | Source |
|-------|-----------|--------|
| `sv-codegen` | RTL architect — synthesizable modules | [sv-codegen.md](plugins/gateflow/agents/sv-codegen.md) |
| `sv-testbench` | Verification engineer — testbenches and stimulus | [sv-testbench.md](plugins/gateflow/agents/sv-testbench.md) |
| `sv-debug` | Debug specialist — simulation failures, X-values | [sv-debug.md](plugins/gateflow/agents/sv-debug.md) |
| `sv-verification` | Verification methodologist — SVA, coverage, formal | [sv-verification.md](plugins/gateflow/agents/sv-verification.md) |
| `sv-understanding` | RTL analyst — explains and documents code | [sv-understanding.md](plugins/gateflow/agents/sv-understanding.md) |
| `sv-planner` | Architecture planner — design plans and diagrams | [sv-planner.md](plugins/gateflow/agents/sv-planner.md) |
| `sv-orchestrator` | Parallel builder — multi-component designs | [sv-orchestrator.md](plugins/gateflow/agents/sv-orchestrator.md) |
| `sv-refactor` | Code quality — lint fixes, cleanup, optimization | [sv-refactor.md](plugins/gateflow/agents/sv-refactor.md) |
| `sv-developer` | Full-stack RTL — complex multi-file features | [sv-developer.md](plugins/gateflow/agents/sv-developer.md) |
| `sv-tutor` | Teacher — reviews solutions, gives hints | [sv-tutor.md](plugins/gateflow/agents/sv-tutor.md) |
| `sv-viz` | Terminal visualization of RTL architecture | [sv-viz.md](plugins/gateflow/agents/sv-viz.md) |

### Commands (7)

| Command | Description | Source |
|---------|-------------|--------|
| `/gf-doctor` | Environment check | [gf-doctor.md](plugins/gateflow/commands/gf-doctor.md) |
| `/gf-scan` | Index project | [gf-scan.md](plugins/gateflow/commands/gf-scan.md) |
| `/gf-map` | Map codebase | [gf-map.md](plugins/gateflow/commands/gf-map.md) |
| `/gf-lint` | Run lint | [gf-lint.md](plugins/gateflow/commands/gf-lint.md) |
| `/gf-fix` | Fix lint | [gf-fix.md](plugins/gateflow/commands/gf-fix.md) |
| `/gf-gen` | Generate scaffolds | [gf-gen.md](plugins/gateflow/commands/gf-gen.md) |
| `/gf-sim` | Run simulation | [gf-sim.md](plugins/gateflow/commands/gf-sim.md) |

Agents are automatically invoked by `/gf` based on your request — you don't need to call them directly.

---

## Individual Downloads

Don't need the full plugin? Grab individual components.

<details>
<summary><b>How to download single components</b></summary>

Each component is a standalone `.md` file. Download and drop into your plugin directory:

```
your-plugin/
├── .claude-plugin/
│   └── plugin.json
├── agents/          ← agent .md files
├── commands/        ← command .md files
└── skills/
    └── skill-name/  ← SKILL.md files
        └── SKILL.md
```

### curl examples

```bash
# Download an agent
curl -O https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md

# Download a skill
mkdir -p skills/gf-plan
curl -o skills/gf-plan/SKILL.md https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-plan/SKILL.md

# Download a command
curl -O https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/commands/gf-lint.md
```

> **Note:** Some skills (like `gf-plan`) include reference files in a `references/` subdirectory. For full functionality, download the entire skill folder.

</details>

---

## Cross-Tool Compatibility

GateFlow's skills and agents are plain Markdown — they work across AI coding tools.

<details>
<summary><b>Setup instructions for Codex, Cursor, Copilot, Cline, Windsurf</b></summary>

### OpenAI Codex CLI

Codex uses the same `SKILL.md` format:

```bash
# User-global
mkdir -p ~/.codex/skills/gf-plan
curl -o ~/.codex/skills/gf-plan/SKILL.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-plan/SKILL.md

# Repo-level
mkdir -p .agents/skills/gf-lint
curl -o .agents/skills/gf-lint/SKILL.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-lint/SKILL.md
```

| Location | Scope |
|----------|-------|
| `.agents/skills/` | Current repo |
| `~/.codex/skills/` | User-global |
| `/etc/codex/skills/` | System-wide |

### Cursor

```bash
# Append to .cursorrules
curl -s https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md \
  >> .cursorrules

# Or: Settings → Agent Modes → Add Custom Mode → paste agent content
```

### GitHub Copilot CLI

```bash
mkdir -p .github
curl -s https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md \
  >> .github/copilot-instructions.md
```

### Cline

```bash
curl -s https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md \
  >> .clinerules
```

### Windsurf

```bash
# As a rule
mkdir -p .windsurf/rules
curl -o .windsurf/rules/sv-codegen.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/agents/sv-codegen.md

# As a workflow
mkdir -p .windsurf/workflows
curl -o .windsurf/workflows/gf-plan.md \
  https://raw.githubusercontent.com/codejunkie99/Gateflow-Plugin/main/plugins/gateflow/skills/gf-plan/SKILL.md
```

### Quick Reference

| Tool | Where to Put Files | Format |
|------|-------------------|--------|
| **Claude Code** | Plugin `skills/`, `agents/`, `commands/` | Native |
| **Codex CLI** | `~/.codex/skills/` or `.agents/skills/` | SKILL.md |
| **Cursor** | `.cursorrules` or custom agent mode | Append |
| **Copilot CLI** | `.github/copilot-instructions.md` | Append |
| **Cline** | `.clinerules` | Append |
| **Windsurf** | `.windsurf/rules/` or `.windsurf/workflows/` | Individual .md |

</details>

---

## Configuration

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

## Project Structure

```
Gateflow-Plugin/
├── plugins/gateflow/          # Main plugin source
│   ├── .claude-plugin/        #   Plugin manifest
│   ├── agents/                #   11 specialized AI agents
│   ├── commands/              #   7 slash commands
│   ├── skills/                #   12 auto-activating skills
│   ├── hooks/                 #   Automation hooks
│   └── CLAUDE.md              #   SystemVerilog reference
├── agents/                    # Mirrored agent entrypoints (symlinks)
├── skills/                    # Mirrored skill entrypoints (symlinks)
├── docs/                      # Compressed docs index
├── CLAUDE.md                  # SV reference (repo-level)
└── AGENTS.md                  # Docs index for non-Claude agents
```

| File | For |
|------|-----|
| `CLAUDE.md` | Claude Code (primary reference) |
| `AGENTS.md` | Other AI agents (Cursor, Copilot, etc.) |

---

## Troubleshooting

<details>
<summary><b>"Verilator not found"</b></summary>

```bash
verilator --version            # Check if installed
brew install verilator         # macOS
sudo apt install verilator     # Linux (Debian/Ubuntu)
```
</details>

<details>
<summary><b>"Plugin not loading"</b></summary>

```bash
claude --plugin-dir /path/to/Gateflow-Plugin/plugins/gateflow
ls /path/to/Gateflow-Plugin/plugins/gateflow/.claude-plugin/plugin.json
```
</details>

<details>
<summary><b>"Agent not found"</b></summary>

Use the `gateflow:` prefix when spawning agents manually:
```
gateflow:sv-codegen
gateflow:sv-testbench
```
</details>

---

## Updates

For detailed release notes, see [`releases.md`](releases.md).

| Version | Date | What Changed |
|---------|------|-------------|
| **1.5.2** | 2026-02-15 | Fix Stop hook JSON validation: replace prompt hook with deterministic command hook (non-blocking reminder) |
| **1.5.0** | 2025-02-11 | Terminal visualization with `/gf-viz` skill and `sv-viz` agent |
| **1.4.4** | 2025-02-11 | Individual component downloads, cross-tool install instructions |
| **1.4.3** | 2025-02-10 | Split `gf-plan` references, validation fixes, docs improvements |

---

## Contributing

Contributions welcome! Areas we'd love help with:
- Additional protocol support (AXI4, PCIe, USB)
- More design patterns
- Tool integrations (Yosys, Vivado, Quartus)
- Documentation and examples

---

## License

BSL-1.1 (Business Source License) — see [LICENSE](LICENSE) for details.

**You can:** Use, fork, contribute for non-commercial/personal/educational purposes.
**Commercial use:** Contact us for a license.
**After 2028:** Converts to Apache 2.0.

---

## Links

- [Claude Code Documentation](https://code.claude.com/docs)
- [Verilator](https://verilator.org/)
- [SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595)

---

## Star History

[![Star History Chart](https://api.star-history.com/svg?repos=codejunkie99/Gateflow-Plugin&type=date&legend=top-left)](https://www.star-history.com/#codejunkie99/Gateflow-Plugin&type=date&legend=top-left)

---

<p align="center">
  <b>Built for hardware engineers who want to move faster.</b><br>
  <i>Design. Verify. Ship.</i>
</p>
