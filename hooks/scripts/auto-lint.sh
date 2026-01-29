#!/bin/bash
# Read JSON from stdin and run verilator on SV files

# Debug: log that hook was called
echo "[auto-lint] Hook triggered" >> /tmp/gateflow-debug.log

INPUT=$(cat)
echo "[auto-lint] Input: $INPUT" >> /tmp/gateflow-debug.log
# Try both formats: tool.input.file_path (hooks) and tool_input.file_path (legacy)
FILE_PATH=$(echo "$INPUT" | python3 -c "
import sys, json
d = json.load(sys.stdin)
# Hook format: tool.input.file_path
fp = d.get('tool', {}).get('input', {}).get('file_path', '')
# Fallback: tool_input.file_path
if not fp:
    fp = d.get('tool_input', {}).get('file_path', '')
print(fp)
" 2>/dev/null)

# Check if it's an SV file
case "$FILE_PATH" in
  *.sv|*.svh|*.v|*.vh)
    verilator --lint-only -Wall "$FILE_PATH" 2>&1 || true
    ;;
esac

exit 0
