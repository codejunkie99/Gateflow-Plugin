---
name: gf-tui
description: Open the GateFlow terminal console
argument-hint: "[--snapshot] [--json] [--plain]"
allowed-tools:
  - Bash
  - Read
---

# GateFlow TUI Command

Open the local GateFlow terminal console and local CLI.

## Usage

```
/gf-tui
/gf-tui --snapshot
/gf-tui --json
```

## Execution

Run the command-first CLI from the repository root:

```bash
python3 tools/gateflow_cli.py status
python3 tools/gateflow_cli.py agents list
python3 tools/gateflow_cli.py agents create "CDC Reviewer" \
  --role "clock-domain crossing reviewer" \
  --description "Reviews synchronizers and CDC constraints"
python3 tools/gateflow_cli.py shell
```

Open the keyboard dashboard:

```bash
python3 tools/gateflow_tui.py
```

Inside the dashboard, press `a` to create a new agent.

Use snapshot mode when running in a non-interactive terminal:

```bash
python3 tools/gateflow_tui.py --snapshot --plain
```

## What It Shows

- plugin version and workspace path
- component inventory
- local hardware tool health
- map/release readiness
- interactive agent creation
- quick actions for `/gf-doctor`, `/gf-map`, `/gf-viz`, `/gf-lint`, `/gf-sim`,
  `/gf-formal`, and `/gf-release`
