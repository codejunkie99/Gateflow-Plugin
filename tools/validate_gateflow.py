#!/usr/bin/env python3
"""Validate GateFlow plugin release metadata and package wiring."""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import NamedTuple


class Inventory(NamedTuple):
    agents: list[str]
    skills: list[str]
    commands: list[str]
    ip_blocks: list[str]
    boards: list[str]


class ValidationResult(NamedTuple):
    inventory: Inventory
    errors: list[str]
    warnings: list[str]


def discover_inventory(root: Path) -> Inventory:
    plugin = root / "plugins" / "gateflow"
    agents = sorted(path.stem for path in (plugin / "agents").glob("*.md"))
    skills = sorted(path.parent.name for path in (plugin / "skills").glob("*/SKILL.md"))
    commands = sorted(path.stem for path in (plugin / "commands").glob("*.md"))
    ip_blocks = sorted(path.name for path in (plugin / "ip").iterdir() if path.is_dir())
    boards = sorted(path.name for path in (plugin / "boards").iterdir() if path.is_dir())
    return Inventory(agents, skills, commands, ip_blocks, boards)


def _read_json(path: Path, errors: list[str]) -> dict:
    try:
        with path.open(encoding="utf-8") as handle:
            return json.load(handle)
    except FileNotFoundError:
        errors.append(f"missing JSON file: {path}")
    except json.JSONDecodeError as exc:
        errors.append(f"invalid JSON in {path}: {exc}")
    return {}


def _read_text(path: Path, errors: list[str]) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        errors.append(f"missing text file: {path}")
    return ""


def _expect_text(path: Path, text: str, needle: str, errors: list[str]) -> None:
    if needle not in text:
        errors.append(f"{path} is missing expected text: {needle}")


def _check_manifest(root: Path, inventory: Inventory, version: str, errors: list[str]) -> None:
    plugin_path = root / "plugins" / "gateflow" / ".claude-plugin" / "plugin.json"
    market_path = root / ".claude-plugin" / "marketplace.json"
    plugin_json = _read_json(plugin_path, errors)
    market_json = _read_json(market_path, errors)

    if plugin_json.get("version") != version:
        errors.append(f"{plugin_path} version is {plugin_json.get('version')}, expected {version}")

    market_plugin = (market_json.get("plugins") or [{}])[0]
    if market_plugin.get("version") != version:
        errors.append(f"{market_path} plugin version is {market_plugin.get('version')}, expected {version}")

    fragments = [
        f"{len(inventory.agents)} agents",
        f"{len(inventory.skills)} skills",
        f"{len(inventory.ip_blocks)} IP blocks",
    ]
    for fragment in fragments:
        if fragment not in plugin_json.get("description", ""):
            errors.append(f"{plugin_path} description missing '{fragment}'")
        if fragment not in market_plugin.get("description", ""):
            errors.append(f"{market_path} description missing '{fragment}'")


def _check_docs(root: Path, inventory: Inventory, version: str, errors: list[str]) -> None:
    readme_path = root / "README.md"
    plugin_readme_path = root / "plugins" / "gateflow" / "README.md"
    releases_path = root / "releases.md"
    index_path = root / "docs" / "gateflow.index"

    readme = _read_text(readme_path, errors)
    plugin_readme = _read_text(plugin_readme_path, errors)
    releases = _read_text(releases_path, errors)
    index = _read_text(index_path, errors)

    _expect_text(readme_path, readme, f"### Skills ({len(inventory.skills)})", errors)
    _expect_text(readme_path, readme, f"### Agents ({len(inventory.agents)})", errors)
    _expect_text(readme_path, readme, f"### Commands ({len(inventory.commands)})", errors)
    _expect_text(plugin_readme_path, plugin_readme, f"### {len(inventory.agents)} Agents", errors)
    _expect_text(plugin_readme_path, plugin_readme, f"### {len(inventory.skills)} Skills", errors)
    _expect_text(plugin_readme_path, plugin_readme, f"### {len(inventory.commands)} Commands", errors)
    _expect_text(releases_path, releases, f"## {version} ", errors)

    for agent in inventory.agents:
        _expect_text(index_path, index, f"agents/{agent}.md", errors)
    for skill in inventory.skills:
        _expect_text(index_path, index, f"skills/{skill}/SKILL.md", errors)
    for command in inventory.commands:
        _expect_text(index_path, index, f"commands/{command}.md", errors)


def _check_root_mirrors(root: Path, inventory: Inventory, errors: list[str]) -> None:
    for agent in inventory.agents:
        mirror = root / "agents" / f"{agent}.md"
        expected = f"../plugins/gateflow/agents/{agent}.md"
        _check_symlink(mirror, expected, errors)

    for skill in inventory.skills:
        mirror = root / "skills" / skill / "SKILL.md"
        expected = f"../../plugins/gateflow/skills/{skill}/SKILL.md"
        _check_symlink(mirror, expected, errors)


def _check_symlink(path: Path, expected_target: str, errors: list[str]) -> None:
    if not path.is_symlink():
        errors.append(f"{path} is missing or is not a symlink")
        return
    target = os.readlink(path)
    if target != expected_target:
        errors.append(f"{path} points to {target}, expected {expected_target}")


def run_checks(root: Path, expected_version: str = "2.5.2") -> ValidationResult:
    root = root.resolve()
    inventory = discover_inventory(root)
    errors: list[str] = []
    warnings: list[str] = []

    _check_manifest(root, inventory, expected_version, errors)
    _check_docs(root, inventory, expected_version, errors)
    _check_root_mirrors(root, inventory, errors)

    return ValidationResult(inventory, errors, warnings)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="Repository root")
    parser.add_argument("--version", default="2.5.2", help="Expected release version")
    args = parser.parse_args(argv)

    result = run_checks(args.root, expected_version=args.version)
    inventory = result.inventory
    print(
        "GateFlow inventory: "
        f"{len(inventory.agents)} agents, "
        f"{len(inventory.skills)} skills, "
        f"{len(inventory.commands)} commands, "
        f"{len(inventory.ip_blocks)} IP blocks, "
        f"{len(inventory.boards)} boards"
    )

    if result.errors:
        print("FAIL GateFlow validation")
        for error in result.errors:
            print(f"- {error}")
        return 1

    print("PASS GateFlow validation")
    return 0


if __name__ == "__main__":
    sys.exit(main())
