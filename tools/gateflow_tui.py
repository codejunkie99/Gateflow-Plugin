#!/usr/bin/env python3
"""OpenClaw-style terminal console for GateFlow."""

from __future__ import annotations

import argparse
import curses
import importlib.util
import json
import os
import shutil
import sys
from pathlib import Path


ACCENT = "\033[38;2;255;90;45m"
SUCCESS = "\033[38;2;47;191;113m"
WARN = "\033[38;2;255;176;32m"
ERROR = "\033[38;2;226;61;45m"
MUTED = "\033[38;2;139;127;119m"
RESET = "\033[0m"


def _load_validator():
    path = Path(__file__).with_name("validate_gateflow.py")
    spec = importlib.util.spec_from_file_location("validate_gateflow", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def _tool_status(name: str) -> str:
    return "installed" if shutil.which(name) else "missing"


def _map_status(root: Path) -> dict:
    map_file = root / ".gateflow" / "map" / "CODEBASE.md"
    if map_file.exists():
        return {"status": "ready", "detail": str(map_file)}
    return {"status": "missing", "detail": "run /gf-map"}


def build_payload(root: Path) -> dict:
    root = root.resolve()
    validator = _load_validator()
    inventory = validator.discover_inventory(root)
    plugin = _read_json(root / "plugins" / "gateflow" / ".claude-plugin" / "plugin.json")
    plugin_version = plugin.get("version", "unknown")
    release = validator.run_checks(root, expected_version=plugin_version)

    health = {
        "doctor": "ready" if (root / "plugins/gateflow/commands/gf-doctor.md").exists() else "missing",
        "release": "ready" if not release.errors else f"{len(release.errors)} issues",
        "map": _map_status(root),
        "verilator": _tool_status("verilator"),
        "yosys": _tool_status("yosys"),
        "sby": _tool_status("sby"),
    }

    actions = [
        ("/gf-doctor", "Check local hardware toolchain"),
        ("/gf-map", "Build RTL architecture map"),
        ("/gf-viz", "Explore hierarchy and FSM views"),
        ("/gf-lint", "Run Verilator lint"),
        ("/gf-sim", "Run simulation"),
        ("/gf-formal", "Run SymbiYosys proofs"),
        ("/gf-release", "Validate plugin release readiness"),
    ]

    return {
        "mode": "OpenClaw-style local mode",
        "workspace": str(root),
        "plugin": {"name": plugin.get("name", "gateflow"), "version": plugin_version},
        "inventory": {
            "agents": len(inventory.agents),
            "skills": len(inventory.skills),
            "commands": len(inventory.commands),
            "ip_blocks": len(inventory.ip_blocks),
            "boards": len(inventory.boards),
        },
        "health": health,
        "actions": [{"command": command, "description": description} for command, description in actions],
    }


def _color(text: str, color: str, plain: bool) -> str:
    return text if plain or os.environ.get("NO_COLOR") else f"{color}{text}{RESET}"


def _status(value: str | dict, plain: bool) -> str:
    if isinstance(value, dict):
        value = value.get("status", "unknown")
    if value in {"ready", "installed"}:
        return _color(value, SUCCESS, plain)
    if value in {"missing", "unknown"} or "issues" in value:
        return _color(value, WARN, plain)
    return value


def _hide_cursor(curses_module=curses) -> bool:
    try:
        curses_module.curs_set(0)
    except curses_module.error:
        return False
    return True


def _terminal_styles(curses_module=curses) -> dict[str, int]:
    styles = {
        "accent": getattr(curses_module, "A_BOLD", 0),
        "ok": 0,
        "warn": 0,
        "muted": getattr(curses_module, "A_DIM", 0),
        "footer": 0,
    }
    try:
        curses_module.init_pair(1, curses_module.COLOR_RED, -1)
        curses_module.init_pair(2, curses_module.COLOR_GREEN, -1)
        curses_module.init_pair(3, curses_module.COLOR_YELLOW, -1)
        curses_module.init_pair(4, curses_module.COLOR_CYAN, -1)
        styles.update(
            {
                "accent": curses_module.color_pair(1) | getattr(curses_module, "A_BOLD", 0),
                "ok": curses_module.color_pair(2),
                "warn": curses_module.color_pair(3),
                "footer": curses_module.color_pair(4),
            }
        )
    except (curses_module.error, ValueError):
        pass
    return styles


def _layout_mode(width: int) -> str:
    return "stacked" if width < 100 else "columns"


def _fit_text(text: str, max_width: int) -> str:
    if max_width <= 0:
        return ""
    if len(text) <= max_width:
        return text
    if max_width <= 3:
        return "." * max_width
    return text[: max_width - 3].rstrip() + "..."


def _short_path(path: str, max_width: int) -> str:
    if len(path) <= max_width:
        return path
    name = Path(path).name
    parent = Path(path).parent.name
    compact = f".../{parent}/{name}" if parent else f".../{name}"
    return _fit_text(compact, max_width)


def _dashboard_rows(payload: dict, width: int, selected: int, message: str) -> list[tuple[str, str]]:
    max_width = max(20, width - 1)
    inv = payload["inventory"]
    health = payload["health"]
    rows: list[tuple[str, str]] = []

    def row(text: str = "", style: str = "normal") -> None:
        rows.append((_fit_text(text, max_width), style))

    row(f"GateFlow Terminal  {payload['plugin']['name']} {payload['plugin']['version']}", "accent")
    row(payload["mode"], "muted")
    row("─" * max_width, "muted")
    row()
    row("Actions", "heading")
    for index, action in enumerate(payload["actions"], start=1):
        marker = ">" if index - 1 == selected else " "
        style = "selected" if index - 1 == selected else "normal"
        row(f"{marker} {index}. {action['command']:<11} {action['description']}", style)
    row()
    row("Workspace", "heading")
    row(f"  path    {_short_path(payload['workspace'], max_width - 10)}")
    row(f"  plugin  {payload['plugin']['name']} {payload['plugin']['version']}", "accent")
    row()
    row("Inventory", "heading")
    row(f"  {inv['agents']} agents   {inv['skills']} skills   {inv['commands']} commands")
    row(f"  {inv['ip_blocks']} IP blocks   {inv['boards']} boards")
    row()
    row("Health", "heading")
    row(f"  doctor    {health['doctor']:<10} release  {health['release']}")
    row(f"  map       {health['map']['status']:<10} verilator {health['verilator']}")
    row(f"  yosys     {health['yosys']:<10} sby       {health['sby']}")
    row()
    row("─" * max_width, "muted")
    row(message or "↑/↓ select   Enter show command   r refresh   q quit", "footer")
    return rows


def render_snapshot(root: Path, plain: bool = False) -> str:
    payload = build_payload(root)
    inv = payload["inventory"]
    health = payload["health"]
    actions = payload["actions"]

    lines = [
        _color("GateFlow Terminal", ACCENT, plain),
        f"{payload['mode']}",
        "",
        "Workspace",
        f"  path      {payload['workspace']}",
        f"  plugin    {payload['plugin']['name']} {payload['plugin']['version']}",
        "",
        "Inventory",
        f"  agents    {inv['agents']}",
        f"  skills    {inv['skills']}",
        f"  commands  {inv['commands']}",
        f"  IP blocks {inv['ip_blocks']}",
        f"  boards    {inv['boards']}",
        "",
        "Health",
        f"  doctor    {_status(health['doctor'], plain)}",
        f"  release   {_status(health['release'], plain)}",
        f"  map       {_status(health['map'], plain)} ({health['map']['detail']})",
        f"  verilator {_status(health['verilator'], plain)}",
        f"  yosys     {_status(health['yosys'], plain)}",
        f"  sby       {_status(health['sby'], plain)}",
        "",
        "Actions",
    ]
    width = max(len(action["command"]) for action in actions)
    for index, action in enumerate(actions, start=1):
        lines.append(f"  {index}. {action['command']:<{width}}  {action['description']}")
    lines.extend(["", "Run without --snapshot in a TTY for interactive navigation. Press q to exit."])
    return "\n".join(lines) + "\n"


def _draw(stdscr, payload: dict, selected: int, message: str) -> None:
    stdscr.erase()
    height, width = stdscr.getmaxyx()
    actions = payload["actions"]
    inv = payload["inventory"]
    health = payload["health"]
    mode = _layout_mode(width)

    def add(y: int, x: int, text: str, attr=0) -> None:
        if 0 <= y < height:
            max_width = max(0, width - x - 1)
            stdscr.addnstr(y, x, _fit_text(text, max_width), max_width, attr)

    styles = _terminal_styles()
    accent = styles["accent"]
    ok = styles["ok"]
    warn = styles["warn"]
    muted = styles["muted"]

    add(0, 0, " GateFlow Terminal ", accent)
    add(0, 20, payload["mode"], muted)
    add(1, 0, "─" * (width - 1), muted)

    if mode == "stacked":
        style_attrs = {
            "accent": accent,
            "footer": styles["footer"],
            "heading": curses.A_BOLD,
            "muted": muted,
            "normal": 0,
            "selected": curses.A_REVERSE,
        }
        for y, (text, style) in enumerate(_dashboard_rows(payload, width, selected, message)):
            add(y, 0, text, style_attrs.get(style, 0))
        stdscr.refresh()
        return

    add(3, 2, "Actions", curses.A_BOLD)
    right_x = 52 if mode == "columns" else 2
    action_desc_width = (right_x - 18) if mode == "columns" else (width - 18)
    for idx, action in enumerate(actions):
        attr = curses.A_REVERSE if idx == selected else 0
        y = 5 + idx
        add(y, 2, f"{idx + 1}. {action['command']}", attr)
        add(y, 16, _fit_text(action["description"], action_desc_width), attr)

    if mode == "columns":
        workspace_y = 3
        inventory_y = 8
        health_y = 13
    else:
        workspace_y = 6 + len(actions)
        inventory_y = workspace_y + 5
        health_y = inventory_y + 5

    add(workspace_y, right_x, "Workspace", curses.A_BOLD)
    add(workspace_y + 2, right_x, payload["workspace"])
    add(workspace_y + 3, right_x, f"{payload['plugin']['name']} {payload['plugin']['version']}", accent)

    add(inventory_y, right_x, "Inventory", curses.A_BOLD)
    add(inventory_y + 2, right_x, f"{inv['agents']} agents   {inv['skills']} skills   {inv['commands']} commands")
    add(inventory_y + 3, right_x, f"{inv['ip_blocks']} IP blocks   {inv['boards']} boards")

    add(health_y, right_x, "Health", curses.A_BOLD)
    rows = [
        ("doctor", health["doctor"]),
        ("release", health["release"]),
        ("map", health["map"]["status"]),
        ("verilator", health["verilator"]),
        ("yosys", health["yosys"]),
        ("sby", health["sby"]),
    ]
    for offset, (name, value) in enumerate(rows):
        attr = ok if value in {"ready", "installed"} else warn
        add(health_y + 2 + offset, right_x, f"{name:<10} {value}", attr)

    footer = message or "↑/↓ select   Enter show command   r refresh   q quit"
    add(height - 2, 0, "─" * (width - 1), muted)
    add(height - 1, 1, footer, styles["footer"])
    stdscr.refresh()


def run_interactive(root: Path) -> int:
    payload = build_payload(root)

    def wrapped(stdscr) -> None:
        _hide_cursor()
        stdscr.keypad(True)
        selected = 0
        message = ""
        while True:
            _draw(stdscr, payload, selected, message)
            key = stdscr.getch()
            if key in {ord("q"), 27}:
                break
            if key in {curses.KEY_UP, ord("k")}:
                selected = max(0, selected - 1)
            elif key in {curses.KEY_DOWN, ord("j")}:
                selected = min(len(payload["actions"]) - 1, selected + 1)
            elif key in {ord("\n"), curses.KEY_ENTER, 10, 13}:
                action = payload["actions"][selected]
                message = f"Run in Claude Code: {action['command']}  ({action['description']})"
            elif key == ord("r"):
                payload.update(build_payload(root))
                message = "Refreshed"

    curses.wrapper(wrapped)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="Repository root")
    parser.add_argument("--snapshot", action="store_true", help="Print a static console view")
    parser.add_argument("--json", action="store_true", help="Print machine-readable state")
    parser.add_argument("--plain", action="store_true", help="Disable ANSI styling")
    parser.add_argument("--local", action="store_true", help="Use local workspace mode")
    args = parser.parse_args(argv)

    if args.json:
        print(json.dumps(build_payload(args.root), indent=2, sort_keys=True))
        return 0
    if args.snapshot or not sys.stdin.isatty():
        print(render_snapshot(args.root, plain=args.plain), end="")
        return 0
    return run_interactive(args.root)


if __name__ == "__main__":
    sys.exit(main())
