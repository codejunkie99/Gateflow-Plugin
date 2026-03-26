---
name: gf-fusesoc
description: Generate FuseSoC .core file for the project
argument-hint: "[--target sim|synth]"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
---

# GateFlow FuseSoC Command

Generate a FuseSoC `.core` file from the current project.

## Usage

```
/gf-fusesoc                   # Auto-detect and generate
/gf-fusesoc --target synth    # Generate with synthesis target
```

## Output

- `<project>.core` — FuseSoC core file with filesets, targets, tool configs

Scans `rtl/`, `tb/`, constraints, and `.gateflow/project.yaml`.
