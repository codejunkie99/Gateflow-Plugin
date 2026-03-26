---
name: gf-audit
description: Audit plugin quality and optionally auto-fix issues
argument-hint: "[--fix] [--category agents|skills|ip|boards|docs]"
allowed-tools:
  - Read
  - Write
  - Edit
  - Bash
  - Glob
  - Grep
  - Task
---

# GateFlow Plugin Audit Command

Scan the entire plugin for gaps, inconsistencies, and missing content.

## Usage

```
/gf-audit                    # Full audit, report only
/gf-audit --fix              # Audit and auto-fix all issues
/gf-audit --category ip      # Audit only IP blocks
/gf-audit --category agents  # Audit only agents
/gf-audit --category docs    # Audit only documentation
```

## Execution

### Report Mode (default)
1. Spawn gf-auditor agent to scan everything
2. Present prioritized report (Critical → Low)
3. Ask user which issues to fix

### Fix Mode (--fix)
1. Spawn gf-auditor agent to scan
2. Spawn gf-pluginfixer agent with findings
3. Fix all issues automatically
4. Show summary of changes
5. Commit fixes

### Category Mode
Focus audit on one area:
- `agents` — Check agent files, routing, cross-references
- `skills` — Check skill files, triggers, return formats
- `ip` — Check IP blocks (RTL, TB, formal, metadata, docs)
- `boards` — Check board database (yaml, constraints, completeness)
- `docs` — Check README, releases, CLAUDE.md, AGENTS.md consistency

## Output

```
GateFlow Plugin Audit Results
━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Critical:  0
  High:      2
  Medium:    5
  Low:       3
  ─────────────
  Total:     10

[H1] README says 26 skills but 27 SKILL.md files found
     Fix: Update README count to 27

[H2] sv-formal agent not in orchestrator routing table
     Fix: Add to gf/SKILL.md Agent Routing section

...

Fix all issues? [Y/n/select]
```
