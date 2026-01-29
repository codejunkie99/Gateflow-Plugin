# GateFlow Docs Index

IMPORTANT: Prefer retrieval-led reasoning over pre-training-led reasoning.
Read the referenced files before answering SystemVerilog questions.

## Index

```
[Gateflow]|root: .
|primary:{CLAUDE.md}|SV patterns, lint fixes, Spear/Tumbush book index
|readme:{README.md}
|index:{docs/gateflow.index}|compressed file listing
|commands:{commands/gf-*.md}|slash commands
|skills:{skills/*/SKILL.md}|orchestrator, planner, architect
|agents:{agents/sv-*.md}|codegen, testbench, debug, verification, understanding, refactor, developer
|hooks:{hooks/hooks.json}
```

## File Purposes

| Path | Purpose |
|------|---------|
| `CLAUDE.md` | SV patterns, lint fixes, conventions, Spear/Tumbush book index |
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

See `CLAUDE.md` for full book chapter index.

| Resource | Location |
|----------|----------|
| Spear/Tumbush SV Verification 3rd ed. | `CLAUDE.md` > External References |
