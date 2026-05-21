import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from io import StringIO
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "tools" / "gateflow_cli.py"


def load_cli():
    spec = importlib.util.spec_from_file_location("gateflow_cli", CLI)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class GateFlowCliTests(unittest.TestCase):
    def test_create_agent_writes_claude_agent_file(self):
        cli = load_cli()

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            result = cli.create_agent(
                root=root,
                name="Timing Closer",
                role="timing closure specialist",
                description="Closes timing on FPGA builds",
                color="cyan",
                tools=["Read", "Edit", "Bash"],
                force=False,
            )

            self.assertEqual(root / "plugins/gateflow/agents/timing-closer.md", result.path)
            content = result.path.read_text(encoding="utf-8")
            self.assertIn("name: timing-closer", content)
            self.assertIn("color: cyan", content)
            self.assertIn("  - Bash", content)
            self.assertIn("timing closure specialist", content)
            self.assertIn("Closes timing on FPGA builds", content)

    def test_cli_agents_create_outputs_created_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            completed = subprocess.run(
                [
                    sys.executable,
                    str(CLI),
                    "--root",
                    tmp,
                    "--plain",
                    "agents",
                    "create",
                    "CDC Reviewer",
                    "--role",
                    "clock-domain crossing reviewer",
                    "--description",
                    "Reviews synchronizers and CDC constraints",
                    "--tool",
                    "Read",
                    "--tool",
                    "Grep",
                ],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertEqual("", completed.stderr)
            self.assertEqual(0, completed.returncode)
            self.assertIn("created", completed.stdout)
            self.assertIn("cdc-reviewer.md", completed.stdout)
            self.assertTrue((Path(tmp) / "plugins/gateflow/agents/cdc-reviewer.md").exists())

    def test_cli_status_json_returns_plugin_payload(self):
        completed = subprocess.run(
            [sys.executable, str(CLI), "--root", str(ROOT), "status", "--json"],
            text=True,
            capture_output=True,
            check=False,
        )

        self.assertEqual("", completed.stderr)
        self.assertEqual(0, completed.returncode)
        payload = json.loads(completed.stdout)
        self.assertEqual("gateflow", payload["plugin"]["name"])
        self.assertIn("actions", payload)

    def test_shell_help_mentions_agent_creation(self):
        cli = load_cli()

        help_text = cli.shell_help()

        self.assertIn("create-agent", help_text)
        self.assertIn("agents create", help_text)

    def test_agents_list_clips_long_descriptions(self):
        cli = load_cli()

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cli.create_agent(
                root=root,
                name="Long Description Agent",
                role="agent list display test",
                description="Reviews " + "very " * 30 + "long agent descriptions",
                color="green",
                tools=["Read"],
                force=False,
            )
            output = StringIO()

            result = cli._print_agents(root, as_json=False, plain=True, output=output)

            lines = output.getvalue().splitlines()
            self.assertEqual(0, result)
            self.assertLessEqual(max(len(line) for line in lines), 100)
            self.assertIn("...", output.getvalue())


if __name__ == "__main__":
    unittest.main()
