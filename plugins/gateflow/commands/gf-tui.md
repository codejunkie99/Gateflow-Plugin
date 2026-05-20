---
name: gf-tui
description: Open the GateFlow terminal console
argument-hint: "[--snapshot] [--json] [--plain]"
allowed-tools:
  - Bash
  - Read
---

# GateFlow TUI Command

Open the local GateFlow terminal console.

## Usage

```
/gf-tui
/gf-tui --snapshot
/gf-tui --json
```

## Execution

Run from the repository root:

```bash
python3 tools/gateflow_tui.py
```

Use snapshot mode when running in a non-interactive terminal:

```bash
python3 tools/gateflow_tui.py --snapshot --plain
```

## What It Shows

- plugin version and workspace path
- component inventory
- local hardware tool health
- map/release readiness
- quick actions for `/gf-doctor`, `/gf-map`, `/gf-viz`, `/gf-lint`, `/gf-sim`,
  `/gf-formal`, and `/gf-release`
