---
name: gf-map
description: Map codebase
allowed-tools:
  - Glob
  - Read
  - Write
  - Task
  - Bash
  - Grep
---

# GateFlow Map Command

Generate a comprehensive map of a SystemVerilog codebase with parallel analysis agents.

## Instructions

1. Find all SystemVerilog files in the project:
   ```
   Use Glob to find **/*.sv and **/*.svh files
   ```

2. Create the output directory:
   ```bash
   mkdir -p .gateflow/map/modules
   ```

3. Spawn the `gf-architect` agent using the Task tool:
   - Pass the list of discovered files
   - The agent will spawn 10 sub-agents in parallel for analysis
   - Results are written to `.gateflow/map/`

4. Report completion with summary:
   - Number of modules found
   - Number of packages
   - Top module(s) identified
   - Any warnings (missing files, parse errors)

## Output Structure

```
.gateflow/map/
├── CODEBASE.md          # AI-friendly summary (AGENTS.md style)
├── hierarchy.md         # Module tree with Mermaid
├── signals.md           # Signal flow diagrams
├── fsm.md              # State machine diagrams
├── clock-domains.md    # CDC analysis
├── packages.md         # Package dependencies
├── types.md            # Structs, unions, typedefs
├── functions.md        # Functions and tasks
├── macros.md           # Preprocessor directives
├── verification.md     # SVA, coverage, assertions
├── recipe.md           # Filelists, compile order
├── interfaces.md       # Interfaces, modports, clocking (if found)
├── classes.md          # Classes, UVM hierarchy (if found)
├── generate.md         # Generate blocks (if found)
├── dpi.md              # DPI imports/exports (if found)
└── modules/            # Per-module detail pages
    └── <module_name>.md
```

## Analysis Method

Uses hybrid approach:
1. **Token budgeting** - Count tokens per file, group into ~150k chunks
2. **Parallel agents** - Spawn 2-10 agents based on codebase size
3. **Regex parsing** - Fast structured extraction of ports, instances, types
4. **Merge** - Combine agent context + regex structure

## Incremental Updates

On subsequent runs:
- Detects existing `.gateflow/map/CODEBASE.md`
- Checks git history for changes since last scan
- Only re-analyzes modified files
- Merges updates with existing map
- Saves commit hash for next incremental run

First run: Full scan (may use significant tokens for large codebases)
Later runs: Fast incremental update (only changed files)
