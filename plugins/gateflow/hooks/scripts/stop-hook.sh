#!/usr/bin/env bash
set -euo pipefail

# GateFlow Stop hook: always emit valid JSON.
#
# Prompt-based Stop hooks can fail JSON parsing if the model returns non-text or empty output.
# This hook is intentionally non-blocking; it may emit a reminder when SV/V activity is detected.

input="$(cat || true)"

transcript_path="$(
  python3 - <<'PY' <<<"$input" 2>/dev/null || true
import json, sys
data = json.load(sys.stdin)
print(data.get("transcript_path", "") or "")
PY
)"

if [ -n "${transcript_path}" ] && [ -f "${transcript_path}" ]; then
  # Heuristic only: look for common RTL file extensions in the transcript.
  if grep -E -q '\\.(svh|sv|vh|v)([^a-zA-Z0-9_]|$)' "${transcript_path}" 2>/dev/null; then
    printf '%s\n' '{"decision":"approve","systemMessage":"GateFlow: SV activity detected. Consider running /gf-lint or /gf-sim before wrapping up."}'
    exit 0
  fi
fi

printf '%s\n' '{"decision":"approve"}'

