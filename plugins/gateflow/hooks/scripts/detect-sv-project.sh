#!/bin/bash
# SessionStart hook: Detect SystemVerilog project and inject context

# Search for SV files in the current working directory
SV_FILES=$(find . -maxdepth 5 -type f \( -name "*.sv" -o -name "*.svh" -o -name "*.v" -o -name "*.vh" \) 2>/dev/null | head -20)

if [ -n "$SV_FILES" ]; then
    # Count files by type
    SV_COUNT=$(echo "$SV_FILES" | grep -c '\.sv$' 2>/dev/null || echo "0")
    SVH_COUNT=$(echo "$SV_FILES" | grep -c '\.svh$' 2>/dev/null || echo "0")
    V_COUNT=$(echo "$SV_FILES" | grep -c '\.v$' 2>/dev/null || echo "0")
    VH_COUNT=$(echo "$SV_FILES" | grep -c '\.vh$' 2>/dev/null || echo "0")

    # Build file summary
    FILE_SUMMARY=""
    [ "$SV_COUNT" -gt 0 ] && FILE_SUMMARY="${FILE_SUMMARY}${SV_COUNT} .sv "
    [ "$SVH_COUNT" -gt 0 ] && FILE_SUMMARY="${FILE_SUMMARY}${SVH_COUNT} .svh "
    [ "$V_COUNT" -gt 0 ] && FILE_SUMMARY="${FILE_SUMMARY}${V_COUNT} .v "
    [ "$VH_COUNT" -gt 0 ] && FILE_SUMMARY="${FILE_SUMMARY}${VH_COUNT} .vh "

    cat << EOF
{
  "systemMessage": "SystemVerilog project detected (${FILE_SUMMARY}files). GateFlow agents available for RTL development: codegen, testbench, debug, verification, refactoring. Just describe what you need."
}
EOF
else
    cat << EOF
{
  "systemMessage": "GateFlow ready. Create or add SystemVerilog files to get started."
}
EOF
fi

exit 0
