---
name: gf-watch
description: Watch SystemVerilog files and auto-lint on changes
allowed-tools:
  - Bash
---

# GateFlow Watch Command

Start a file watcher that automatically lints SystemVerilog files when they change.

## Instructions

1. **Start watch mode**:
   ```bash
   gateflow watch
   ```

2. If gateflow CLI is not available, explain manual approach:
   - Use `fswatch` or `inotifywait` to monitor `.sv` files
   - On change, run `verilator --lint-only -Wall <changed-file>`
   - Display results in real-time

3. **Watch behavior**:
   - Monitors all `*.sv` and `*.svh` files in project
   - Debounces rapid changes (waits 500ms)
   - Shows lint results after each save
   - Highlights new errors vs. existing ones

4. **Exit**: Press Ctrl+C to stop watching

## Note

This command starts a long-running process. It's best used in a separate terminal or run in background.
