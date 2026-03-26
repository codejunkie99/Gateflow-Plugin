---
name: gf-formal
description: >
  Formal verification from natural language. Generates SVA properties,
  configures SymbiYosys, runs proofs, and explains results.
  Example: "formally verify the FIFO never overflows"
allowed-tools:
  - Bash
  - Read
  - Write
  - Glob
  - Grep
  - Task
---

# GF-Formal — Formal Verification Skill

## Tool Detection

```bash
which sby
```

If not found:
```
---GATEFLOW-RESULT---
STATUS: ERROR
DETAILS: SymbiYosys not installed. Install to enable formal verification.
  pip install symbiyosys
  Also need: yosys, z3 (or yices2)
  macOS: brew install yosys z3
  Linux: sudo apt install yosys z3
---END-GATEFLOW-RESULT---
```

## Workflow

1. Parse request — What properties to verify? Which module?
2. Read the design — Understand ports, signals, behavior
3. Spawn sv-formal agent — Generate properties + .sby config
4. Run SymbiYosys: `sby -f <config>.sby`
5. Parse results — Read sby output for pass/fail/counterexample
6. Report — 3-layer error translation if failed, clear summary if passed

## Result Format

```
---GATEFLOW-RESULT---
STATUS: PASS | FAIL | ERROR
PROOFS: N proved, M failed, K covers
FILES: [generated files]
DETAILS: [proof results or counterexample explanation]
---END-GATEFLOW-RESULT---
```

## Integration with /gf Orchestrator

Formal verification is an optional enhancement step:
- After simulation passes, for safety-critical designs
- When user explicitly requests formal verification
- For CDC, FIFO, or protocol designs
