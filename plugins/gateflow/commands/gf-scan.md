---
name: gf-scan
description: Index project
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Scan Command

Index all SystemVerilog files in the current project to build a module database.

## Instructions

1. Use Verilator to quickly parse all SV files and surface modules:
   ```bash
   verilator --lint-only -Wall *.sv 2>&1 | head -50
   ```

2. Alternatively, manually discover SV files:
   - Use Glob to find all `**/*.sv` and `**/*.svh` files
   - Read each file to extract module declarations
   - Report the module hierarchy

3. Present results showing:
   - Total files found
   - Module names and their locations
   - Include file dependencies
   - Any parsing errors encountered
