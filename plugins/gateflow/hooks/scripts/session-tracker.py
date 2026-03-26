#!/usr/bin/env python3
"""Track GateFlow session data for progressive disclosure."""
import json
import os
import sys
from pathlib import Path

PROFILE_DIR = Path.home() / ".gateflow"
PROFILE_FILE = PROFILE_DIR / "profile.json"

def load_profile():
    if PROFILE_FILE.exists():
        try:
            return json.loads(PROFILE_FILE.read_text())
        except (json.JSONDecodeError, OSError):
            pass
    return {
        "session_count": 0,
        "commands_used": {},
        "tips_shown": {},
        "concepts_introduced": [],
        "default_board": None,
        "preferred_hdl": "systemverilog"
    }

def save_profile(profile):
    PROFILE_DIR.mkdir(parents=True, exist_ok=True)
    PROFILE_FILE.write_text(json.dumps(profile, indent=2))

def main():
    profile = load_profile()
    profile["session_count"] = profile.get("session_count", 0) + 1
    save_profile(profile)

    count = profile["session_count"]
    if count == 1:
        msg = "Welcome to GateFlow! Describe what you want to build, or type /gf-demo to see it in action."
    elif count <= 3:
        msg = f"GateFlow session #{count}. Describe your hardware task or use /gf-demo."
    else:
        msg = None

    if msg:
        print(json.dumps({"message": msg, "type": "info"}))
    else:
        print(json.dumps({}))

if __name__ == "__main__":
    main()
