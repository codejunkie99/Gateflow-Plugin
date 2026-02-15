#!/usr/bin/env python3
"""GateFlow UserPromptSubmit hook (deterministic).

This replaces a prompt-based hook which could return empty/non-JSON (or an
unexpected schema like {"ok": false, ...}) and block user prompts.

Behavior:
- Never blocks user prompts.
- Emits a small systemMessage nudge only when the prompt looks SV/V related.
"""

from __future__ import annotations

import json
import re
import sys
from typing import Any, Dict


SV_EXT_RE = re.compile(r"\.(?:svh?|vh?|v)(?=$|[^A-Za-z0-9_])", re.IGNORECASE)
GF_CMD_RE = re.compile(r"(^|\\s)/gf(?:\\s|$|-)", re.IGNORECASE)

SV_KEYWORDS = (
    "systemverilog",
    "verilog",
    "rtl",
    "testbench",
    "verilator",
    "vcd",
    "waveform",
    "uvm",
    "sva",
    "always_ff",
    "always_comb",
    "always_latch",
)


def _extract_prompt(payload: Dict[str, Any]) -> str:
    for key in ("prompt", "user_prompt", "userPrompt", "input"):
        val = payload.get(key)
        if isinstance(val, str) and val.strip():
            return val

    for key in ("hook", "event", "params", "data"):
        node = payload.get(key)
        if not isinstance(node, dict):
            continue
        for sub in ("prompt", "user_prompt", "userPrompt", "input"):
            val = node.get(sub)
            if isinstance(val, str) and val.strip():
                return val

    return ""


def _looks_like_sv_prompt(prompt: str) -> bool:
    if SV_EXT_RE.search(prompt):
        return True
    lower = prompt.lower()
    return any(k in lower for k in SV_KEYWORDS)


def main() -> int:
    try:
        payload: Dict[str, Any] = json.load(sys.stdin)
    except Exception:
        sys.stdout.write("{}")
        return 0

    prompt = _extract_prompt(payload)
    if not prompt:
        sys.stdout.write("{}")
        return 0

    # If the user is explicitly using GateFlow commands, don't spam.
    if GF_CMD_RE.search(prompt):
        sys.stdout.write("{}")
        return 0

    if _looks_like_sv_prompt(prompt):
        out = {
            "systemMessage": "SystemVerilog task detected. Consider using /gf to plan first."
        }
        sys.stdout.write(json.dumps(out))
        return 0

    sys.stdout.write("{}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

