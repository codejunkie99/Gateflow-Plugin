#!/usr/bin/env python3
"""GateFlow PostToolUse hook for Write/Edit events.

Deterministic check: if the file just written/edited has a SystemVerilog or
Verilog extension, remind the user to lint. For all other file types, silently
pass through.
"""

from __future__ import annotations

import json
import sys
from typing import Any, Dict


SV_EXTENSIONS = (".sv", ".svh", ".v", ".vh")


def main() -> int:
    try:
        payload: Dict[str, Any] = json.load(sys.stdin)
    except Exception:
        sys.stdout.write("{}")
        return 0

    tool_input = payload.get("tool_input", {}) or {}
    file_path = tool_input.get("file_path", "") if isinstance(tool_input, dict) else ""

    if isinstance(file_path, str) and file_path.lower().endswith(SV_EXTENSIONS):
        out = {
            "systemMessage": (
                "SV file modified. Run /gf-lint to check for issues, "
                "or continue if you plan to lint later."
            )
        }
        sys.stdout.write(json.dumps(out))
    else:
        sys.stdout.write("{}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
