---
name: gf-release
description: Validate GateFlow plugin readiness and prepare a versioned release
argument-hint: "[--version X.Y.Z] [--check-only]"
allowed-tools:
  - Bash
  - Read
  - Edit
  - Write
  - Glob
  - Grep
---

# GateFlow Release Command

Prepare and validate a GateFlow plugin release.

## Usage

```
/gf-release --check-only
/gf-release --version 2.5.0
```

## Workflow

1. Invoke the `gf-release` skill.
2. Run the deterministic validator:

```bash
python3 tools/validate_gateflow.py --version <version>
```

3. If validation fails, fix the reported package wiring issues before tagging.
4. Confirm `plugins/gateflow/.claude-plugin/plugin.json`, `.claude-plugin/marketplace.json`,
   `README.md`, `plugins/gateflow/README.md`, `docs/gateflow.index`, and `releases.md`
   all describe the same version and component counts.
5. For a real release, create a git tag and GitHub release only after validation passes.

## Output

Report:
- version being prepared
- component inventory
- validation failures, if any
- files that must change before release
- final tag command when ready
