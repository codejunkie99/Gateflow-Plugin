---
name: gf-tui
description: >
  GateFlow terminal console inspired by OpenClaw local TUI workflows. Shows
  workspace status, component inventory, tool health, map readiness, release
  readiness, and command shortcuts from one terminal surface.
user-invocable: true
triggers:
  - open GateFlow TUI
  - show GateFlow dashboard
  - terminal console
  - CLI TUI
  - OpenClaw-style TUI
---
allowed-tools:
  - Bash
  - Read

# GF-TUI -- Terminal Console

Launch a local terminal console for GateFlow.

## Modes

| Mode | Command | Use When |
|---|---|---|
| CLI | `python3 tools/gateflow_cli.py status` | You want a normal command surface |
| Shell | `python3 tools/gateflow_cli.py shell` | You want a local `gateflow>` prompt |
| Agent create | `python3 tools/gateflow_cli.py agents create "Name"` | You need a new custom agent |
| Interactive | `python3 tools/gateflow_tui.py` | You are in a real TTY and want keyboard navigation |
| Snapshot | `python3 tools/gateflow_tui.py --snapshot --plain` | Logs, CI, or non-interactive terminals |
| JSON | `python3 tools/gateflow_tui.py --json` | Scripts need machine-readable state |

## OpenClaw-Inspired Behavior

- Local workspace mode by default; no gateway is required.
- TTY-aware styling with plain and JSON fallbacks.
- Command-first local CLI for status and agent management.
- Press `a` in the dashboard to create a new agent interactively.
- Health/status surfaces are visible before action.
- Commands are shown as operator shortcuts rather than hidden docs.
- Release and config repair loops stay inside the terminal workflow.

## Console Sections

1. **Workspace** — root path and plugin version.
2. **Inventory** — agents, skills, commands, IP blocks, and boards.
3. **Health** — doctor command, release validation, map readiness, Verilator,
   Yosys, and SymbiYosys availability.
4. **Actions** — launch points for doctor, map, viz, lint, sim, formal, and
   release workflows.
5. **Agent creation** — `a` opens prompts for name, role, and description.

## Guardrails

- The TUI does not silently run destructive hardware actions.
- `/gf-flash` remains outside the default action list because programming a
  board should stay explicit.
- Missing tools are shown as warnings, not failures, because GateFlow can still
  generate and review RTL without every optional tool installed.

## Verification

Run:

```bash
python3 -m unittest tests/test_gateflow_tui.py
python3 -m unittest tests/test_gateflow_cli.py
python3 tools/gateflow_cli.py --plain status
python3 tools/gateflow_tui.py --snapshot --plain
python3 tools/gateflow_tui.py --json
```
