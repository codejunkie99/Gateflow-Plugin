#!/bin/bash
# GateFlow dependency check (no auto-install)
# Runs on SessionStart - reports missing deps with manual guidance

PLUGIN_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
MARKER_FILE="$PLUGIN_ROOT/.deps-installed"
OS="$(uname -s)"

show_welcome() {
    cat << 'BANNER'

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
    ╚═══════════════════════════════════════════════════════════════╝

BANNER
}

show_complete() {
    cat << 'DONE'

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

DONE
}

REQUIRED_MISSING=()
OPTIONAL_MISSING=()

# Check Verilator (required)
if ! command -v verilator &> /dev/null; then
    REQUIRED_MISSING+=("verilator")
fi

# Check Verible (optional)
if ! command -v verible-verilog-syntax &> /dev/null; then
    OPTIONAL_MISSING+=("verible")
fi

# All tools present - silent on subsequent runs
if [ ${#REQUIRED_MISSING[@]} -eq 0 ] && [ ${#OPTIONAL_MISSING[@]} -eq 0 ]; then
    if [ ! -f "$MARKER_FILE" ]; then
        show_welcome
        show_complete
    fi
    touch "$MARKER_FILE"
    exit 0
fi

# Required dependency missing → report and exit without marking success
if [ ${#REQUIRED_MISSING[@]} -ne 0 ]; then
    show_welcome
    echo "⚠ GateFlow: Missing required tools: ${REQUIRED_MISSING[*]}"
    if [ ${#OPTIONAL_MISSING[@]} -ne 0 ]; then
        echo "ℹ GateFlow: Optional tools missing: ${OPTIONAL_MISSING[*]}"
    fi
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
fi

# Optional tools missing only
if [ ! -f "$MARKER_FILE" ]; then
    show_welcome
fi

echo "ℹ GateFlow: Optional tools missing: ${OPTIONAL_MISSING[*]}"
if [ "$OS" = "Darwin" ]; then
    echo "   Install Verible: brew tap chipsalliance/verible && brew install verible"
elif [ "$OS" = "Linux" ]; then
    echo "   Install Verible: https://github.com/chipsalliance/verible/releases"
else
    echo "   Install Verible: https://github.com/chipsalliance/verible/releases"
fi

show_complete
touch "$MARKER_FILE"
exit 0
