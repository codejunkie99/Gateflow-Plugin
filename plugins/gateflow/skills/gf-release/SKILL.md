---
name: gf-release
description: >
  GateFlow release readiness workflow. Validates plugin manifests, marketplace
  metadata, docs index coverage, root mirrors, release notes, and component
  counts before a version tag is created. Use when preparing, checking, or
  cutting a GateFlow plugin release.
user-invocable: true
triggers:
  - prepare GateFlow release
  - cut a GateFlow release
  - validate plugin release
  - check marketplace metadata
  - bump GateFlow version
---
allowed-tools:
  - Bash
  - Read
  - Edit
  - Write
  - Glob
  - Grep

# GF-Release -- Release Readiness

Use this workflow before tagging or publishing GateFlow.

## Required Inputs

- Target version, for example `2.5.0`
- Whether this is check-only or a release-prep edit

If no version is provided, inspect `plugins/gateflow/.claude-plugin/plugin.json`
and propose the next semver version based on the changes:

| Change Type | Version Bump |
|---|---|
| Metadata, docs, or packaging fix | Patch |
| New command, skill, agent, IP, or board | Minor |
| Breaking plugin layout or workflow change | Major |

## Release Checks

Run the deterministic validator from the repo root:

```bash
python3 tools/validate_gateflow.py --version <target-version>
```

The validator must pass before creating a tag. It checks:
- plugin and marketplace JSON version consistency
- component counts in descriptions and READMEs
- `docs/gateflow.index` coverage for every command, skill, and agent
- root-level mirrors for every command-adjacent skill and agent file
- a release note entry for the target version

## Prep Workflow

1. Count actual components:

```bash
find plugins/gateflow/agents -maxdepth 1 -name '*.md' | wc -l
find plugins/gateflow/skills -maxdepth 2 -name 'SKILL.md' | wc -l
find plugins/gateflow/commands -maxdepth 1 -name '*.md' | wc -l
```

2. Update version strings:
- `plugins/gateflow/.claude-plugin/plugin.json`
- `.claude-plugin/marketplace.json`

3. Update release-facing docs:
- `README.md`
- `plugins/gateflow/README.md`
- `docs/gateflow.index`
- `releases.md`

4. Run validator and focused tests:

```bash
python3 -m unittest tests/test_validate_gateflow.py
python3 tools/validate_gateflow.py --version <target-version>
```

5. Only after validation passes, tag and release:

```bash
git tag v<target-version>
gh release create v<target-version> --title "GateFlow v<target-version>" --notes-file <notes-file>
```

## Report Format

```text
---GATEFLOW-RESULT---
STATUS: PASS | FAIL
VERSION: <target-version>
INVENTORY: <agents> agents, <skills> skills, <commands> commands, <ip> IP, <boards> boards
FILES: <changed release-facing files>
DETAILS: <summary or validation failures>
---END-GATEFLOW-RESULT---
```
