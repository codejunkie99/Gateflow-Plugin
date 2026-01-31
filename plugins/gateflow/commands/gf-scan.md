---
name: gf-scan
description: Index and scan SystemVerilog files in the project
allowed-tools:
  - Bash
  - Read
  - Glob
---

# GateFlow Scan Command

Index all SystemVerilog files in the current project to build a module database.

## Instructions

1. Run the gateflow scan command:
   ```bash
   gateflow scan
   ```

2. If gateflow is not installed, use Verilator directly to list modules:
   ```bash
   verilator --lint-only -Wall *.sv 2>&1 | head -50
   ```

3. Alternatively, manually discover SV files:
   - Use Glob to find all `**/*.sv` and `**/*.svh` files
   - Read each file to extract module declarations
   - Report the module hierarchy

4. Present results showing:
   - Total files found
   - Module names and their locations
   - Include file dependencies
   - Any parsing errors encountered
