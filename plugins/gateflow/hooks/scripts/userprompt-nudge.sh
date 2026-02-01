#!/bin/bash
# UserPromptSubmit hook: soft hint for SV-related prompts (non-blocking).

INPUT=$(cat)

PROMPT=$(GATEFLOW_HOOK_INPUT="$INPUT" python3 - <<'PY'
import json
import os
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

raw = os.environ.get("GATEFLOW_HOOK_INPUT", "")
try:
    payload = json.loads(raw)
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

MARKER=$(python3 - <<'PY'
import hashlib
import os

digest = hashlib.sha256(os.getcwd().encode("utf-8")).hexdigest()[:12]
print(f"/tmp/gateflow-svproj-{digest}")
PY
)

SV_PROJECT=0
if [ -f "$MARKER" ]; then
    SV_PROJECT=1
else
    if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
        if git ls-files -- '*.sv' '*.svh' '*.v' '*.vh' | head -n 1 | grep -q .; then
            SV_PROJECT=1
        fi
    else
        if find . -maxdepth 4 -type f \( -name "*.sv" -o -name "*.svh" -o -name "*.v" -o -name "*.vh" \) -print -quit 2>/dev/null | grep -q .; then
            SV_PROJECT=1
        fi
    fi

    if [ "$SV_PROJECT" -eq 1 ]; then
        touch "$MARKER" 2>/dev/null || true
    fi
fi

if [ "$SV_PROJECT" -eq 1 ] || echo "$LOWER" | grep -qE '\.(svh?|vh)\b|\.(sv|v)\b|systemverilog|verilog|\brtl\b|\btestbench\b'; then
    cat << EOF
{
  "systemMessage": "SystemVerilog task detected. Use /gf to plan first (with ASCII diagram) before implementation, or /gf-plan for planning only."
}
EOF
fi

exit 0
