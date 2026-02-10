# GateFlow

AI-powered SystemVerilog development assistant for Claude Code. Provides lint fixing, code generation, simulation, testbench creation, and end-to-end RTL workflows.

## Install

```bash
claude plugin add codejunkie99/Gateflow-Plugin
```

**Requires:** [Verilator](https://verilator.org) (run `/gf-doctor` to check)

## Commands

| Command | Description |
|---------|-------------|
| `/gf-lint` | Run Verilator lint with structured output |
| `/gf-sim` | Compile and simulate with Verilator |
| `/gf-fix` | Auto-fix lint warnings |
| `/gf-gen` | Generate scaffolds (modules, testbenches) |
| `/gf-scan` | Index project files |
| `/gf-map` | Map codebase architecture |
| `/gf-doctor` | Check environment and dependencies |

## Skills

| Skill | Description |
|-------|-------------|
| `/gf` | Primary orchestrator — end-to-end create, verify, iterate |
| `/gf-plan` | Design planner — architecture plans before coding |
| `/gf-build` | Parallel build engine |
| `/gf-architect` | Codebase mapper |
| `/gf-sim` | Simulation with structured result parsing |
| `/gf-lint` | Lint with structured result parsing |

## Agents

| Agent | Role |
|-------|------|
| `sv-codegen` | Creates synthesizable RTL modules |
| `sv-testbench` | Writes self-checking testbenches |
| `sv-debug` | Diagnoses simulation failures |
| `sv-refactor` | Fixes lint warnings, cleans up code |
| `sv-verification` | Adds SVA assertions and coverage |
| `sv-understanding` | Explains code architecture |
| `sv-planner` | Creates implementation plans |
| `sv-developer` | Handles complex multi-file changes |
| `sv-orchestrator` | Decomposes and builds in parallel |
| `sv-tutor` | Teaches SystemVerilog concepts |

## Workflow

```
User request → /gf
  → Ask clarifying questions
  → Plan with sv-planner
  → Build with sv-orchestrator (parallel)
  → Lint (gf-lint) → fix loop (sv-refactor)
  → Simulate (gf-sim) → fix loop (sv-debug → sv-refactor)
  → Deliver working code
```

## License

[BSL-1.1](LICENSE)
