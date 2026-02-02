#!/bin/bash
# GateFlow dependency installer
# Runs on plugin initialization (--init)

set -e

echo "GateFlow: Checking dependencies..."

# Detect OS
OS="$(uname -s)"
REQUIRED_MISSING=()
OPTIONAL_MISSING=()

# Check for Verilator (required)
if ! command -v verilator &> /dev/null; then
    REQUIRED_MISSING+=("verilator")
fi

# Check for Verible (optional)
if ! command -v verible-verilog-syntax &> /dev/null; then
    OPTIONAL_MISSING+=("verible")
fi

if [ ${#REQUIRED_MISSING[@]} -eq 0 ]; then
    if [ ${#OPTIONAL_MISSING[@]} -eq 0 ]; then
        echo "GateFlow: All dependencies installed"
    else
        echo "GateFlow: Required dependencies installed"
        echo "GateFlow: Optional missing: ${OPTIONAL_MISSING[*]}"
        echo "GateFlow: Set GATEFLOW_INSTALL_OPTIONAL=1 to install optional tools"
    fi
    exit 0
fi

echo "GateFlow: Missing required dependencies: ${REQUIRED_MISSING[*]}"
if [ ${#OPTIONAL_MISSING[@]} -ne 0 ]; then
    echo "GateFlow: Optional missing: ${OPTIONAL_MISSING[*]}"
fi

INSTALL_LIST=("${REQUIRED_MISSING[@]}")
if [ "${GATEFLOW_INSTALL_OPTIONAL:-0}" = "1" ] && [ ${#OPTIONAL_MISSING[@]} -ne 0 ]; then
    INSTALL_LIST+=("${OPTIONAL_MISSING[@]}")
fi

# Install missing dependencies
if [ "$OS" = "Darwin" ]; then
    # macOS - use Homebrew
    if ! command -v brew &> /dev/null; then
        echo "GateFlow: Homebrew not found. Please install from https://brew.sh"
        exit 1
    fi

    for dep in "${INSTALL_LIST[@]}"; do
        case "$dep" in
            verilator)
                echo "GateFlow: Installing Verilator..."
                brew install verilator
                ;;
            verible)
                echo "GateFlow: Installing Verible..."
                brew tap chipsalliance/verible 2>/dev/null || true
                brew install verible
                ;;
        esac
    done

elif [ "$OS" = "Linux" ]; then
    # Linux - detect package manager
    if command -v apt-get &> /dev/null; then
        # Debian/Ubuntu
        for dep in "${INSTALL_LIST[@]}"; do
            case "$dep" in
                verilator)
                    echo "GateFlow: Installing Verilator..."
                    sudo apt-get update && sudo apt-get install -y verilator
                    ;;
                verible)
                    echo "GateFlow: Verible requires manual installation on Linux"
                    echo "GateFlow: See https://github.com/chipsalliance/verible/releases"
                    ;;
            esac
        done
    elif command -v dnf &> /dev/null; then
        # Fedora/RHEL
        for dep in "${INSTALL_LIST[@]}"; do
            case "$dep" in
                verilator)
                    echo "GateFlow: Installing Verilator..."
                    sudo dnf install -y verilator
                    ;;
                verible)
                    echo "GateFlow: Verible requires manual installation on Linux"
                    echo "GateFlow: See https://github.com/chipsalliance/verible/releases"
                    ;;
            esac
        done
    else
        echo "GateFlow: Unsupported package manager. Please install manually:"
        echo "  - Verilator: https://verilator.org/guide/latest/install.html"
        echo "  - Verible: https://github.com/chipsalliance/verible/releases"
        exit 1
    fi
else
    echo "GateFlow: Unsupported OS: $OS"
    exit 1
fi

echo "GateFlow: Dependency installation complete"
