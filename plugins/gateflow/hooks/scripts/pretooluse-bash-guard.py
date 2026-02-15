#!/usr/bin/env python3
"""GateFlow PreToolUse hook guard for Bash commands.

This is intentionally deterministic (no LLM call) to avoid noisy hook failures.
It asks for confirmation when a Bash command appears likely to delete/overwrite
SystemVerilog/Verilog source files.
"""

from __future__ import annotations

import json
import os
import re
import sys
from typing import Any, Dict


SV_EXT_RE = re.compile(r"\.(?:svh?|vh?|v)(?=$|[^A-Za-z0-9_])", re.IGNORECASE)


def _looks_like_sv_project(cwd: str) -> bool:
    # Keep this cheap: check only a couple common directories.
    candidates = [cwd, os.path.join(cwd, "rtl"), os.path.join(cwd, "tb")]
    for d in candidates:
        try:
            for name in os.listdir(d):
                lower = name.lower()
                if lower.endswith((".sv", ".svh", ".v", ".vh")):
                    return True
        except Exception:
            continue
    return False


def _has_sv_path(cmd: str) -> bool:
    return SV_EXT_RE.search(cmd) is not None


def _is_destructive_git(cmd_l: str, sv_project: bool, mentions_sv: bool) -> bool:
    if "git " not in cmd_l:
        return False

    # These are destructive for the working tree; we only trigger if we can
    # reasonably believe it's an SV project, or the command explicitly mentions
    # SV/V file paths.
    if (sv_project or mentions_sv) and "git reset" in cmd_l and "--hard" in cmd_l:
        return True

    if (sv_project or mentions_sv) and "git clean" in cmd_l and (
        " -f" in cmd_l or "--force" in cmd_l
    ):
        return True

    if "git checkout" in cmd_l and (sv_project or mentions_sv):
        # `git checkout -- <path>` or forced checkout are most likely to discard changes.
        if " -- " in cmd_l or " checkout --" in cmd_l or " -f" in cmd_l or "--force" in cmd_l:
            return True

    if "git restore" in cmd_l:
        # Restore is inherently a revert; only ask when it targets SV/V or in an SV project
        # with forceful flags.
        if mentions_sv:
            return True
        if sv_project and ("--staged" in cmd_l or "--source" in cmd_l or "--worktree" in cmd_l):
            return True

    return False


def _overwrites_via_redirection(cmd: str, mentions_sv: bool) -> bool:
    if not mentions_sv:
        return False
    # Catch: `> file.sv`, `>> file.sv`, `>| file.sv`, and common `tee file.sv`.
    if re.search(r"(?:^|[^0-9])>>?\s*[^\\n]*\.(?:svh?|vh?|v)(?=$|[^A-Za-z0-9_])", cmd, re.IGNORECASE):
        return True
    if re.search(r"\btee\b[^\n]*\.(?:svh?|vh?|v)(?=$|[^A-Za-z0-9_])", cmd, re.IGNORECASE):
        return True
    return False


def _deletes_sv(cmd_l: str, sv_project: bool, mentions_sv: bool) -> bool:
    if "rm" not in cmd_l:
        return False

    # Directly references SV/V files.
    if mentions_sv and re.search(r"\brm\b", cmd_l):
        return True

    # Recursively deleting common SV directories.
    if sv_project and re.search(r"\brm\b[^\n]*(?:-rf|-fr|--recursive)[^\n]*(?:\brtl\b|\btb\b|/rtl/|/tb/)", cmd_l):
        return True

    return False


def _should_ask(cmd: str, cwd: str) -> bool:
    cmd_l = cmd.lower()
    mentions_sv = _has_sv_path(cmd)
    sv_project = _looks_like_sv_project(cwd) if cwd else False

    return (
        _overwrites_via_redirection(cmd, mentions_sv)
        or _deletes_sv(cmd_l, sv_project, mentions_sv)
        or _is_destructive_git(cmd_l, sv_project, mentions_sv)
    )


def main() -> int:
    try:
        payload: Dict[str, Any] = json.load(sys.stdin)
    except Exception:
        # Malformed input: do nothing (never block tool usage due to hook failure).
        sys.stdout.write("{}")
        return 0

    tool_name = payload.get("tool_name", "")
    tool_input = payload.get("tool_input", {}) or {}
    cmd = tool_input.get("command", "") if isinstance(tool_input, dict) else ""
    cwd = payload.get("cwd", "") or ""

    if tool_name != "Bash" or not isinstance(cmd, str) or not cmd.strip():
        sys.stdout.write("{}")
        return 0

    if _should_ask(cmd, cwd):
        out: Dict[str, Any] = {
            "hookSpecificOutput": {"permissionDecision": "ask"},
            "systemMessage": (
                "This command looks like it may delete/overwrite .sv/.svh/.v/.vh files. "
                "Please confirm before I run it."
            ),
        }
        sys.stdout.write(json.dumps(out))
        return 0

    sys.stdout.write("{}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

