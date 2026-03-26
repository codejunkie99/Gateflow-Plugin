---
name: gf-ip
description: Manage IP block library
argument-hint: "add|list|info <block>"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
---

# GateFlow IP Library Command

## Usage

```
/gf-ip list                  # Show all available IP blocks
/gf-ip info fifo_sync        # Show block details and ports
/gf-ip add fifo_sync         # Install block into current project
```

## Execution

### list
Read all `${CLAUDE_PLUGIN_ROOT}/ip/*/block.yaml` files.
Display: name, description, verification status.

### info <block>
Read `${CLAUDE_PLUGIN_ROOT}/ip/<block>/block.yaml`.
Display: description, parameters, ports, formal proofs, dependencies.

### add <block>
1. Read block.yaml for metadata
2. Copy `rtl/*.sv` to project `rtl/` directory
3. Copy `tb/*.sv` to project `tb/` directory
4. Copy `formal/*` to project `formal/` directory
5. Update `.gateflow/project.yaml` — add to `ip_blocks` list
6. Report what was installed and how to instantiate
