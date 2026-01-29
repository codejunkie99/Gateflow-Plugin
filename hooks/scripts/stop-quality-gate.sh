#!/bin/bash
# Stop hook: Quality gate check for SystemVerilog files

# Check for modified SV files in git status
MODIFIED_SV=$(git status --porcelain 2>/dev/null | grep -E '\.(sv|svh|v|vh)$' | head -10)

if [ -n "$MODIFIED_SV" ]; then
    MODIFIED_LIST=$(echo "$MODIFIED_SV" | awk '{print $2}' | tr '\n' ', ' | sed 's/,$//')
    cat << EOF
{
  "systemMessage": "SV files modified: ${MODIFIED_LIST}. Consider running /gf-lint to verify."
}
EOF
fi

exit 0
