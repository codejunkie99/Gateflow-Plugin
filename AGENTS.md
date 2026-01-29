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

```
[SystemVerilog for Verification, 3rd ed. — Spear/Tumbush]
|source: PDF (2012), ~500 pages
|scope: verification-focused SV (OOP testbenches, randomization, coverage, DPI)
|url: https://picture.iczhiku.com/resource/eetop/wYIEDKFRorpoPvvV.pdf
|chapters:
|1 Verification Guidelines (p.2)
|2 Data Types (p.26)
|3 Procedural Statements and Routines (p.70)
|4 Connecting the Testbench and Design (p.90)
|5 Basic OOP (p.132)
|6 Randomization (p.170)
|7 Threads and Interprocess Communication (p.266)
|8 Advanced OOP and Testbench Guidelines (p.274)
|9 Functional Coverage (p.324)
|10 Advanced Interfaces (p.364)
|11 A Complete SystemVerilog Testbench (p.386)
|12 Interfacing with C/C++ (p.416)
```
