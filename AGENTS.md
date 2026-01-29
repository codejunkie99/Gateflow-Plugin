# GateFlow Docs Index

IMPORTANT: Prefer retrieval-led reasoning over pre-training-led reasoning.
Read the referenced files before answering SystemVerilog questions.

## Index

```
[Gateflow]|root: .
|primary:{CLAUDE.md}
|readme:{README.md}
|commands:{commands/gf-doctor.md,commands/gf-fix.md,commands/gf-gen.md,commands/gf-lint.md,commands/gf-map.md,commands/gf-scan.md,commands/gf-sim.md}
|skills:{skills/gf/SKILL.md,skills/gf-plan/SKILL.md,skills/gf-architect/SKILL.md}
|agents:{agents/sv-codegen.md,agents/sv-testbench.md,agents/sv-debug.md,agents/sv-verification.md,agents/sv-understanding.md,agents/sv-refactor.md,agents/sv-developer.md}
|hooks:{hooks/hooks.json}
```

## File Purposes

| Path | Purpose |
|------|---------|
| `CLAUDE.md` | SystemVerilog patterns, lint fixes, coding conventions |
| `skills/gf/SKILL.md` | Main orchestrator - routes tasks, runs verification loops |
| `skills/gf-plan/SKILL.md` | Hardware design planner with Mermaid diagrams |
| `skills/gf-architect/SKILL.md` | Codebase mapping and analysis |
| `agents/sv-*.md` | Specialized agents (codegen, testbench, debug, etc.) |
| `commands/gf-*.md` | Slash commands for specific actions |

## Retrieval Order

1. Check `CLAUDE.md` for SV syntax/patterns
2. Check relevant `agents/*.md` for task-specific guidance
3. Check `skills/*/SKILL.md` for workflow orchestration
4. Check `commands/*.md` for command implementations

## External References

| Resource | Scope |
|----------|-------|
| [Spear/Tumbush SV Verification 3rd ed.](https://picture.iczhiku.com/resource/eetop/wYIEDKFRorpoPvvV.pdf) | OOP testbenches, randomization, coverage, DPI |
