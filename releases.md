# Releases

## 1.6.0 (2026-03-26)

- Sync all version strings to 1.6.0 across plugin.json and marketplace.json.
- Confirm BSL-1.1 license consistency across plugin and root.

## 1.5.3 (2026-02-18)

- Replace prompt-based PostToolUse hook with a deterministic Python script for reliable lint nudges.

## 1.5.2 (2026-02-15)

- Fix Stop hook JSON validation failures by replacing the prompt-based Stop hook with a deterministic command hook (`stop-hook.sh`).
- Bump plugin version to 1.5.2.

## 1.5.1 (2025-02-12)

- Prompt-based hooks: PreToolUse (SV file safety), PostToolUse (lint nudge), Stop (smart completion gate).

