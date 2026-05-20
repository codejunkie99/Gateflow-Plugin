#!/usr/bin/env python3
"""Command-first local CLI for the GateFlow plugin."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shlex
import sys
import textwrap
from pathlib import Path
from typing import NamedTuple, TextIO


TOOLS_DIR = Path(__file__).resolve().parent

ACCENT = "\033[38;2;255;132;45m"
INFO = "\033[38;2;68;201;224m"
SUCCESS = "\033[38;2;59;201;128m"
WARN = "\033[38;2;255;191;71m"
ERROR = "\033[38;2;234;80;64m"
MUTED = "\033[38;2;147;143;135m"
RESET = "\033[0m"

DEFAULT_TOOLS = ["Read", "Glob", "Grep", "Edit", "Bash"]
VALID_COLORS = {
    "blue",
    "cyan",
    "green",
    "orange",
    "pink",
    "purple",
    "red",
    "yellow",
}


class AgentCreateResult(NamedTuple):
    path: Path
    slug: str
    created: bool


def _color(text: str, color: str, plain: bool) -> str:
    return text if plain or os.environ.get("NO_COLOR") else f"{color}{text}{RESET}"


def _fit_cell(text: str, width: int) -> str:
    text = " ".join(text.split())
    if len(text) <= width:
        return text
    if width <= 3:
        return "." * width
    return text[: width - 3].rstrip() + "..."


def _load_tui():
    path = TOOLS_DIR / "gateflow_tui.py"
    spec = importlib.util.spec_from_file_location("gateflow_tui", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def slugify_agent_name(name: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", name.strip().lower()).strip("-")
    if not slug:
        raise ValueError("agent name must contain at least one letter or number")
    return slug


def _wrap_yaml(value: str, indent: str = "  ") -> str:
    lines = textwrap.wrap(value.strip(), width=76) or ["Custom GateFlow agent."]
    return "\n".join(f"{indent}{line}" for line in lines)


def render_agent_markdown(
    *,
    name: str,
    role: str,
    description: str,
    color: str,
    tools: list[str],
) -> str:
    slug = slugify_agent_name(name)
    title = " ".join(part.capitalize() for part in slug.split("-"))
    tool_lines = "\n".join(f"  - {tool}" for tool in tools)
    description_block = _wrap_yaml(description)

    return f"""---
name: {slug}
description: >
{description_block}
color: {color}
tools:
{tool_lines}
---

# {title}

You are a GateFlow agent focused on {role}.

## When To Use

Use this agent when the task needs: {description}

## Workflow

1. Read the relevant RTL, testbench, constraints, or plugin files.
2. State the concrete objective before changing files.
3. Make the smallest useful change that advances the hardware workflow.
4. Verify with the relevant GateFlow command, simulator, lint tool, or release check.
5. Report the files changed and the next command the user should run.

## Return Format

```text
---GATEFLOW-RETURN---
STATUS: complete|needs_clarification|blocked
SUMMARY: [what changed]
FILES_CREATED: [new files]
FILES_MODIFIED: [changed files]
NEXT_TARGET: [next GateFlow command or agent]
---END-GATEFLOW-RETURN---
```
"""


def create_agent(
    *,
    root: Path,
    name: str,
    role: str,
    description: str,
    color: str = "cyan",
    tools: list[str] | None = None,
    force: bool = False,
) -> AgentCreateResult:
    slug = slugify_agent_name(name)
    if color not in VALID_COLORS:
        raise ValueError(f"unsupported color '{color}'. Choose: {', '.join(sorted(VALID_COLORS))}")
    selected_tools = tools or DEFAULT_TOOLS
    agent_dir = root / "plugins" / "gateflow" / "agents"
    path = agent_dir / f"{slug}.md"
    if path.exists() and not force:
        raise FileExistsError(f"agent already exists: {path}")

    agent_dir.mkdir(parents=True, exist_ok=True)
    path.write_text(
        render_agent_markdown(
            name=name,
            role=role,
            description=description,
            color=color,
            tools=selected_tools,
        ),
        encoding="utf-8",
    )
    return AgentCreateResult(path=path, slug=slug, created=True)


def list_agents(root: Path) -> list[dict[str, str]]:
    agents = []
    for path in sorted((root / "plugins" / "gateflow" / "agents").glob("*.md")):
        content = path.read_text(encoding="utf-8", errors="replace")
        name_match = re.search(r"^name:\s*(.+)$", content, re.MULTILINE)
        color_match = re.search(r"^color:\s*(.+)$", content, re.MULTILINE)
        desc_match = re.search(r"^description:\s*>\s*\n((?:  .+\n?)*)", content, re.MULTILINE)
        description = ""
        if desc_match:
            description = " ".join(line.strip() for line in desc_match.group(1).splitlines()).strip()
        agents.append(
            {
                "name": name_match.group(1).strip() if name_match else path.stem,
                "color": color_match.group(1).strip() if color_match else "default",
                "description": description,
                "path": str(path),
            }
        )
    return agents


def shell_help() -> str:
    return """GateFlow local CLI

Commands:
  status                 Show plugin inventory and local health
  agents                 List GateFlow agents
  agents create NAME     Create a new agent from flags
  create-agent NAME      Interactive shortcut for creating a new agent
  tui                    Open the keyboard dashboard
  help                   Show this help
  quit                   Exit

Examples:
  agents create "CDC Reviewer" --role "CDC reviewer" --description "Reviews synchronizers"
  create-agent "Timing Closer"
"""


def _print_status(root: Path, *, as_json: bool, plain: bool, output: TextIO) -> int:
    tui = _load_tui()
    payload = tui.build_payload(root)
    if as_json:
        print(json.dumps(payload, indent=2, sort_keys=True), file=output)
        return 0

    inv = payload["inventory"]
    health = payload["health"]
    print(_color(f"GateFlow {payload['plugin']['version']}", ACCENT, plain), file=output)
    print(_color(payload["mode"], MUTED, plain), file=output)
    print(f"workspace  {payload['workspace']}", file=output)
    print(
        f"inventory  {inv['agents']} agents  {inv['skills']} skills  "
        f"{inv['commands']} commands  {inv['ip_blocks']} IP blocks",
        file=output,
    )
    for key in ("doctor", "release", "verilator", "yosys", "sby"):
        value = health[key]
        color = SUCCESS if value in {"ready", "installed"} else WARN
        print(f"{key:<10} {_color(str(value), color, plain)}", file=output)
    print(f"{'map':<10} {_color(health['map']['status'], WARN, plain)}", file=output)
    return 0


def _print_agents(root: Path, *, as_json: bool, plain: bool, output: TextIO) -> int:
    agents = list_agents(root)
    if as_json:
        print(json.dumps(agents, indent=2, sort_keys=True), file=output)
        return 0
    if not agents:
        print(_color("no agents found", WARN, plain), file=output)
        return 0
    print(_color("GateFlow agents", ACCENT, plain), file=output)
    for agent in agents:
        description = _fit_cell(agent["description"] or "no description", 66)
        print(f"{agent['name']:<22} {agent['color']:<7} {description}", file=output)
    return 0


def _agent_create_from_args(args, output: TextIO) -> int:
    try:
        result = create_agent(
            root=args.root,
            name=args.name,
            role=args.role,
            description=args.description,
            color=args.color,
            tools=args.tool,
            force=args.force,
        )
    except (FileExistsError, ValueError) as error:
        print(_color(f"error: {error}", ERROR, args.plain), file=sys.stderr)
        return 2
    print(_color("created", SUCCESS, args.plain), result.path, file=output)
    return 0


def run_shell(root: Path, *, plain: bool, input_stream: TextIO = sys.stdin, output: TextIO = sys.stdout) -> int:
    print(_color("GateFlow CLI", ACCENT, plain), file=output)
    print("type 'help' for commands, 'quit' to exit", file=output)
    while True:
        print(_color("gateflow> ", INFO, plain), end="", file=output, flush=True)
        line = input_stream.readline()
        if not line:
            return 0
        command = line.strip()
        if not command:
            continue
        if command in {"quit", "exit", "q"}:
            return 0
        if command == "help":
            print(shell_help(), file=output)
            continue
        if command == "status":
            _print_status(root, as_json=False, plain=plain, output=output)
            continue
        if command in {"agents", "agents list"}:
            _print_agents(root, as_json=False, plain=plain, output=output)
            continue
        if command == "tui":
            return _load_tui().run_interactive(root)
        if command.startswith("create-agent"):
            parts = shlex.split(command)
            name = parts[1] if len(parts) > 1 else input("agent name: ").strip()
            role = input("role: ").strip() or "custom GateFlow specialist"
            description = input("description: ").strip() or role
            result = create_agent(
                root=root,
                name=name,
                role=role,
                description=description,
                color="cyan",
                tools=DEFAULT_TOOLS,
                force=False,
            )
            print(_color("created", SUCCESS, plain), result.path, file=output)
            continue
        print(_color(f"unknown command: {command}", ERROR, plain), file=output)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="gateflow", description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="Repository root")
    parser.add_argument("--plain", action="store_true", help="Disable ANSI styling")
    subcommands = parser.add_subparsers(dest="command")

    status = subcommands.add_parser("status", help="Show local GateFlow status")
    status.add_argument("--json", action="store_true", help="Print machine-readable status")

    agents = subcommands.add_parser("agents", help="Manage GateFlow agents")
    agent_commands = agents.add_subparsers(dest="agent_command")
    agent_list = agent_commands.add_parser("list", help="List agents")
    agent_list.add_argument("--json", action="store_true", help="Print machine-readable agents")
    create = agent_commands.add_parser("create", help="Create a new agent")
    create.add_argument("name", help="Agent display name, e.g. 'CDC Reviewer'")
    create.add_argument("--role", default="custom GateFlow specialist", help="Agent role line")
    create.add_argument("--description", default="Custom GateFlow workflow agent", help="Trigger description")
    create.add_argument("--color", default="cyan", choices=sorted(VALID_COLORS), help="Claude agent color")
    create.add_argument("--tool", action="append", default=None, help="Allowed tool, repeatable")
    create.add_argument("--force", action="store_true", help="Overwrite an existing agent")

    subcommands.add_parser("tui", help="Open the keyboard dashboard")
    subcommands.add_parser("shell", help="Open the interactive command shell")
    return parser


def main(argv: list[str] | None = None, output: TextIO = sys.stdout) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    args.root = args.root.resolve()

    if args.command is None:
        if sys.stdin.isatty():
            return run_shell(args.root, plain=args.plain, output=output)
        return _print_status(args.root, as_json=False, plain=args.plain, output=output)
    if args.command == "status":
        return _print_status(args.root, as_json=args.json, plain=args.plain, output=output)
    if args.command == "agents":
        if args.agent_command in {None, "list"}:
            return _print_agents(args.root, as_json=getattr(args, "json", False), plain=args.plain, output=output)
        if args.agent_command == "create":
            return _agent_create_from_args(args, output)
    if args.command == "tui":
        return _load_tui().run_interactive(args.root)
    if args.command == "shell":
        return run_shell(args.root, plain=args.plain, output=output)
    parser.print_help(output)
    return 2


if __name__ == "__main__":
    sys.exit(main())
