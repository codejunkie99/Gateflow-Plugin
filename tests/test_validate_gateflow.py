import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "tools" / "validate_gateflow.py"


def load_validator():
    spec = importlib.util.spec_from_file_location("validate_gateflow", VALIDATOR)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class GateFlowValidatorTests(unittest.TestCase):
    def test_inventory_matches_release_target(self):
        validator = load_validator()

        inventory = validator.discover_inventory(ROOT)

        self.assertEqual(20, len(inventory.agents))
        self.assertEqual(27, len(inventory.skills))
        self.assertEqual(21, len(inventory.commands))
        self.assertEqual(8, len(inventory.ip_blocks))
        self.assertEqual(4, len(inventory.boards))
        self.assertIn("gf-release", inventory.skills)
        self.assertIn("gf-release", inventory.commands)
        self.assertIn("gf-tui", inventory.skills)
        self.assertIn("gf-tui", inventory.commands)

    def test_repository_passes_release_checks(self):
        validator = load_validator()

        result = validator.run_checks(ROOT, expected_version="2.5.2")

        self.assertEqual([], result.errors)

    def test_cli_reports_success(self):
        completed = subprocess.run(
            [sys.executable, str(VALIDATOR), "--version", "2.5.2"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )

        self.assertEqual("", completed.stderr)
        self.assertEqual(0, completed.returncode)
        self.assertIn("PASS GateFlow validation", completed.stdout)


if __name__ == "__main__":
    unittest.main()
