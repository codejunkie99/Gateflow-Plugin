import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TUI = ROOT / "tools" / "gateflow_tui.py"


def load_tui():
    spec = importlib.util.spec_from_file_location("gateflow_tui", TUI)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class GateFlowTuiTests(unittest.TestCase):
    def test_snapshot_contains_openclaw_style_operator_surfaces(self):
        tui = load_tui()

        snapshot = tui.render_snapshot(ROOT, plain=True)

        self.assertIn("GateFlow Terminal", snapshot)
        self.assertIn("Workspace", snapshot)
        self.assertIn("Health", snapshot)
        self.assertIn("Actions", snapshot)
        self.assertIn("/gf-doctor", snapshot)
        self.assertIn("/gf-release", snapshot)
        self.assertIn("OpenClaw-style local mode", snapshot)

    def test_json_mode_returns_machine_readable_inventory(self):
        tui = load_tui()

        payload = tui.build_payload(ROOT)

        self.assertEqual("gateflow", payload["plugin"]["name"])
        self.assertEqual("2.5.0", payload["plugin"]["version"])
        self.assertEqual(20, payload["inventory"]["agents"])
        self.assertEqual(27, payload["inventory"]["skills"])
        self.assertEqual(21, payload["inventory"]["commands"])
        self.assertIn("doctor", payload["health"])

    def test_cli_snapshot_mode(self):
        completed = subprocess.run(
            [sys.executable, str(TUI), "--snapshot", "--plain"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )

        self.assertEqual("", completed.stderr)
        self.assertEqual(0, completed.returncode)
        self.assertIn("GateFlow Terminal", completed.stdout)


if __name__ == "__main__":
    unittest.main()
