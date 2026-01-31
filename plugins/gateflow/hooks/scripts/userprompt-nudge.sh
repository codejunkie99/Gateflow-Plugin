#!/bin/bash
# UserPromptSubmit hook: soft hint for SV-related prompts (non-blocking).

INPUT=$(cat)

PROMPT=$(echo "$INPUT" | python3 - <<'PY'
import json
import sys

def extract_prompt(data):
    if not isinstance(data, dict):
        return ""
    # Direct keys
    for key in ("user_prompt", "prompt", "userPrompt", "input"):
        val = data.get(key)
        if isinstance(val, str) and val.strip():
            return val
    # Nested common containers
    for key in ("tool", "hook", "event", "params", "data"):
        node = data.get(key)
        if isinstance(node, dict):
            for sub in ("user_prompt", "prompt", "userPrompt", "input"):
                val = node.get(sub)
                if isinstance(val, str) and val.strip():
                    return val
    return ""

try:
    payload = json.load(sys.stdin)
except Exception:
    print("")
    sys.exit(0)

print(extract_prompt(payload))
PY
)

if [ -z "$PROMPT" ]; then
    exit 0
fi

LOWER=$(printf "%s" "$PROMPT" | tr '[:upper:]' '[:lower:]')

# If user already invoked GateFlow, do nothing.
if echo "$LOWER" | grep -qE '(^|[[:space:]])/gf([[:space:]]|$|-)'; then
    exit 0
fi

if echo "$LOWER" | grep -qE '\.(svh?|vh)\b|\.(sv|v)\b|systemverilog|verilog|\brtl\b|\btestbench\b|\bfifo\b|\bfsm\b|\baxi\b|\buart\b|\buvm\b'; then
    cat << EOF
{
  "systemMessage": "SystemVerilog task detected. Use /gf for end-to-end RTL + lint + sim, or /gf-plan to design first."
}
EOF
fi

exit 0
