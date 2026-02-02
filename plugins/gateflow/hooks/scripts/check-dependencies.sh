#!/bin/bash
# GateFlow dependency check (no auto-install)
# Runs on SessionStart - reports missing deps with manual guidance

PLUGIN_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
MARKER_FILE="$PLUGIN_ROOT/.deps-installed"
OS="$(uname -s)"

show_welcome() {
    cat << 'EOF'

    ╔═══════════════════════════════════════════════════════════════╗
    ║                                                               ║
    ║        ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐        ║
    ║     ───┤FF├──┤FF├──┤FF├──┤FF├──┤FF├──┤FF├──┤FF├──┤FF├───     ║
    ║        └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘        ║
    ║          │     │     │     │     │     │     │     │          ║
    ║        ╔═╧═════╧═════╧═════╧═════╧═════╧═════╧═════╧═╗        ║
    ║        ║                                             ║        ║
    ║        ║   ╔═╗ ╔═╗ ╔════╗ ╔═══╗ ╔═══╗ ╦   ╔═══╗ ╦ ╦  ║        ║
    ║        ║   ║ ╦ ╠═╣   ║   ╠═    ╠═    ║   ║   ║ ║║║  ║        ║
    ║        ║   ╚═╝ ╩ ╩   ╩   ╚═══╝ ╩     ╩═╝ ╚═══╝ ╚╩╝  ║        ║
    ║        ║                                             ║        ║
    ║        ╚═════════════════════════════════════════════╝        ║
    ║                          clk ↑                                ║
    ║    ┌─────┐    ┌─────┐    ┌─────┐    ┌─────┐    ┌─────┐       ║
    ║ ───┘     └────┘     └────┘     └────┘     └────┘     └───    ║
    ║                                                               ║
    ║         AI-Powered SystemVerilog Development Assistant        ║
    ║                                                               ║
    ║                   made with love of hardware <3               ║
    ║                            by Avid                            ║
    ║                                                               ║
    ╚═══════════════════════════════════════════════════════════════╝

EOF
}

show_complete() {
    cat << 'EOF'

    ┌─────────────────────────────────────────────────────┐
    │  ✓ GateFlow ready! Your RTL workflow awaits.        │
    │                                                     │
    │  Quick start:                                       │
    │    /gf-gen module <name>  - Generate a module       │
    │    /gf-lint <file>        - Lint your code          │
    │    /gf-sim <file>         - Run simulation          │
    │    /gf-doctor             - Check environment       │
    │                                                     │
    │  Happy synthesizing! ⚡                              │
    └─────────────────────────────────────────────────────┘

EOF
}

MISSING=()

# Check Verilator (required)
if ! command -v verilator &> /dev/null; then
    MISSING+=("verilator")
fi

# Check Verible (required)
if ! command -v verible-verilog-syntax &> /dev/null; then
    MISSING+=("verible")
fi

# All tools present - silent on subsequent runs
if [ ${#MISSING[@]} -eq 0 ]; then
    if [ ! -f "$MARKER_FILE" ]; then
        show_welcome
        show_complete
    fi
    touch "$MARKER_FILE"
    exit 0
fi

# Required dependency missing → report and exit without installing or marking success
show_welcome
echo "⚠ GateFlow: Required tools missing: ${MISSING[*]}"
if [ "$OS" = "Darwin" ]; then
    echo "   Install Verilator: brew install verilator"
    echo "   Install Verible: brew tap chipsalliance/verible && brew install verible"
elif [ "$OS" = "Linux" ]; then
    if command -v apt-get &> /dev/null; then
        echo "   Install Verilator: sudo apt-get update && sudo apt-get install -y verilator"
    else
        echo "   Install Verilator: https://verilator.org/guide/latest/install.html"
    fi
    echo "   Install Verible: https://github.com/chipsalliance/verible/releases"
else
    echo "   Install Verilator from https://verilator.org"
    echo "   Install Verible from https://github.com/chipsalliance/verible/releases"
fi

exit 0
