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
        self.assertEqual("2.5.2", payload["plugin"]["version"])
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

    def test_hide_cursor_ignores_unsupported_terminals(self):
        tui = load_tui()

        class FakeCurses:
            error = RuntimeError

            @staticmethod
            def curs_set(_visibility):
                raise RuntimeError("curs_set() returned ERR")

        self.assertFalse(tui._hide_cursor(FakeCurses))

    def test_terminal_styles_fall_back_without_color_pairs(self):
        tui = load_tui()

        class FakeCurses:
            error = RuntimeError
            COLOR_RED = 1
            COLOR_GREEN = 2
            COLOR_YELLOW = 3
            COLOR_CYAN = 4
            A_BOLD = 10
            A_DIM = 20

            @staticmethod
            def init_pair(_pair, _foreground, _background):
                raise ValueError("Color pair is greater than COLOR_PAIRS-1")

            @staticmethod
            def color_pair(_pair):
                raise AssertionError("color_pair should not be used when init_pair fails")

        styles = tui._terminal_styles(FakeCurses)

        self.assertEqual(FakeCurses.A_BOLD, styles["accent"])
        self.assertEqual(0, styles["ok"])
        self.assertEqual(0, styles["warn"])
        self.assertEqual(FakeCurses.A_DIM, styles["muted"])
        self.assertEqual(0, styles["footer"])

    def test_narrow_terminals_use_stacked_layout(self):
        tui = load_tui()

        self.assertEqual("stacked", tui._layout_mode(80))
        self.assertEqual("columns", tui._layout_mode(120))

    def test_text_is_ellipsized_to_fit_column(self):
        tui = load_tui()

        value = tui._fit_text("Validate plugin release readiness", 18)

        self.assertEqual("Validate plugin...", value)
        self.assertLessEqual(len(value), 18)

    def test_narrow_draw_stacks_panels_below_actions(self):
        tui = load_tui()
        payload = tui.build_payload(ROOT)

        class FakeScreen:
            def __init__(self):
                self.rows = [" " * 80 for _ in range(32)]

            def erase(self):
                pass

            def getmaxyx(self):
                return (32, 80)

            def addnstr(self, y, x, text, max_width, _attr=0):
                line = self.rows[y]
                clipped = text[:max_width]
                self.rows[y] = line[:x] + clipped + line[x + len(clipped) :]

            def refresh(self):
                pass

        screen = FakeScreen()

        tui._draw(screen, payload, selected=6, message="")

        action_row = next(row for row in screen.rows if "/gf-release" in row)
        workspace_row = next(index for index, row in enumerate(screen.rows) if "Workspace" in row)

        self.assertNotIn("Workspace", action_row)
        self.assertGreater(workspace_row, 11)


if __name__ == "__main__":
    unittest.main()
