#!/bin/bash
# GateFlow dependency check and auto-install
# Runs on SessionStart - installs missing deps automatically

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

show_installing() {
    cat << 'EOF'
    ┌─────────────────────────────────────────────────────┐
    │  ⚡ Setting up your hardware development environment │
    └─────────────────────────────────────────────────────┘
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

# All good - silent on subsequent runs
if [ ${#MISSING[@]} -eq 0 ]; then
    # First successful run - show welcome
    if [ ! -f "$MARKER_FILE" ]; then
        show_welcome
        show_complete
    fi
    touch "$MARKER_FILE"
    exit 0
fi

# Already tried to install once - brief warning
if [ -f "$MARKER_FILE" ]; then
    echo "⚠ GateFlow: Missing tools: ${MISSING[*]}"
    echo "  Install manually or delete .deps-installed to retry"
    exit 0
fi

# First run - show welcome and install
show_welcome
show_installing
echo ""

# Auto-install
if [ "$OS" = "Darwin" ]; then
    if ! command -v brew &> /dev/null; then
        echo "    ✗ Homebrew not found"
        echo "      Install from https://brew.sh then restart Claude"
        touch "$MARKER_FILE"
        exit 0
    fi

    for dep in "${MISSING[@]}"; do
        case "$dep" in
            verilator)
                echo "    → Installing Verilator..."
                if brew install verilator &> /dev/null; then
                    echo "    ✓ Verilator installed"
                else
                    echo "    ✗ Verilator install failed"
                fi
                ;;
            verible)
                echo "    → Installing Verible..."
                brew tap chipsalliance/verible &> /dev/null || true
                if brew install verible &> /dev/null; then
                    echo "    ✓ Verible installed"
                else
                    echo "    ✗ Verible install failed"
                fi
                ;;
        esac
    done

elif [ "$OS" = "Linux" ]; then
    if command -v apt-get &> /dev/null; then
        for dep in "${MISSING[@]}"; do
            case "$dep" in
                verilator)
                    echo "    → Installing Verilator..."
                    if sudo apt-get update -qq && sudo apt-get install -y verilator &> /dev/null; then
                        echo "    ✓ Verilator installed"
                    else
                        echo "    ✗ Verilator install failed"
                    fi
                    ;;
                verible)
                    echo "    ℹ Verible: Download from GitHub releases"
                    echo "      https://github.com/chipsalliance/verible/releases"
                    ;;
            esac
        done
    else
        echo "    ℹ Auto-install not supported on this system"
        echo "      Verilator: https://verilator.org/guide/latest/install.html"
        echo "      Verible: https://github.com/chipsalliance/verible/releases"
    fi
fi

touch "$MARKER_FILE"
show_complete
exit 0
